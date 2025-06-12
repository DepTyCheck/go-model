#!/usr/bin/env python3

import asyncio
import os
import re
import signal
import tempfile

from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from typing import Callable, Optional, Sequence, TypeVar


T1 = TypeVar("T1")
T2 = TypeVar("T2")


def assume_some(arg: T1 | None) -> T1:
    if arg is None:
        raise RuntimeError("Unexpected None")
    return arg


def map_option(f: Callable[[T1], T2], x: Optional[T1]) -> Optional[T2]:
    if x is None:
        return None
    return f(x)


def or_default(x: Optional[T1], default: T1) -> T1:
    return x if x is not None else default


@dataclass(slots=True, frozen=True)
class ExternalAppError(Exception):
    cmd: Sequence[str | Path]
    code: Optional[int | str]
    stdout: bytes
    stderr: bytes

    def _render(self, part: bytes, header: str) -> str:
        if not part:
            return ""
        text = part.decode(errors="replace")
        return f"{header}\n{text}\n"

    def render(self) -> str:
        if self.cmd:
            tmp = " ".join(
                x.as_posix() if isinstance(x, Path) else x for x in self.cmd
            )
            cmd = f"Error while running external command:\n  {tmp}\n\n"
        else:
            cmd = ""
        code = "" if self.code is None else f"Code: {self.code}\n\n"
        stdout = self._render(self.stdout, "stdout:")
        stderr = self._render(self.stderr, "stderr:")
        return f"{cmd}{code}{stdout}{stderr}"


subproc_semaphore = asyncio.BoundedSemaphore(4)


async def run_app(
    *cmd: str | Path,
    cwd: Optional[Path] = None,
    timeout: Optional[float] = None,
    sigkill: bool = False,
) -> bytes:
    async with subproc_semaphore:
        proc = await asyncio.create_subprocess_exec(
            *cmd,
            stdout=asyncio.subprocess.PIPE,
            stderr=asyncio.subprocess.PIPE,
            cwd=cwd,
            preexec_fn=os.setsid,
        )
        try:
            out, err = await asyncio.wait_for(
                proc.communicate(), timeout=timeout
            )
            code = assume_some(proc.returncode)
            if code == 0:
                return out
            else:
                raise ExternalAppError(cmd, code, out, err)
        except (TimeoutError, KeyboardInterrupt):
            os.killpg(proc.pid, signal.SIGKILL if sigkill else signal.SIGTERM)
            out = await assume_some(proc.stdout).read()
            err = await assume_some(proc.stderr).read()
            raise ExternalAppError(cmd, "timeout", out, err)


NORMAL_CODE_PAT = re.compile(rb"//\* NORMAL CODE \*//\n(.*?)//\*", re.DOTALL)
VERBOSE_CODE_PAT = re.compile(rb"//\* VERBOSE CODE \*//\n(.*?)//\*", re.DOTALL)
DESC_PAT = re.compile(rb"//\* DESCRIPTION \*//\n(.*?)$", re.DOTALL)

NORMAL_SRC = "normal.go"
VERBOSE_SRC = "verbose.go"
DESC_FILE = "desc.txt"

EXE_SUFFIX = ".out"
NORMAL_EXE = "normal.out"
VERBOSE_EXE = "verbose.out"


async def generate_example(
    *,
    dest: Optional[Path] = None,
    model_fuel: int,
    timeout: Optional[float] = None,
    exe: Sequence[str] = ("./build/exec/go-model",),
) -> Path:
    cmd = (*exe, "--model-fuel", str(model_fuel), "-n", "1")
    output = await run_app(*cmd, timeout=timeout, sigkill=True)
    normal = NORMAL_CODE_PAT.search(output)
    verbose = VERBOSE_CODE_PAT.search(output)
    desc = DESC_PAT.search(output)
    if normal is None or verbose is None or desc is None:
        raise ExternalAppError((), "Can't parse model output", output, b"")
    dir = Path(tempfile.mkdtemp(dir=dest, prefix="go-"))
    (dir / NORMAL_SRC).write_bytes(normal.group(1))
    (dir / VERBOSE_SRC).write_bytes(verbose.group(1))
    (dir / DESC_FILE).write_bytes(desc.group(1))
    return dir


async def compile(file: Path):
    out = file.with_suffix(EXE_SUFFIX)
    await run_app("go", "build", "-o", out.as_posix(), file.as_posix())


@dataclass(slots=True, frozen=True)
class Config:
    model_fuel: int
    n_examples: int
    dest: Optional[Path]
    n_workers: Optional[int]
    model_timeout: Optional[float]
    test_timeout: Optional[float]


async def test(conf: Config) -> Path:
    dir = await generate_example(
        dest=conf.dest, model_fuel=conf.model_fuel, timeout=conf.model_timeout
    )
    await compile(dir / NORMAL_SRC)
    await compile(dir / VERBOSE_SRC)
    await run_app(dir / NORMAL_EXE, timeout=conf.test_timeout)
    await run_app(dir / VERBOSE_EXE, timeout=conf.test_timeout)
    return dir


ERROR_PAT = re.compile(rb"^[\w./\-]*:\d+:\d+: ([^:]*)", re.MULTILINE)


def parse_output(err: ExternalAppError, errors: Counter[str]):
    found = False
    for line in err.stderr.splitlines():
        m = ERROR_PAT.search(line)
        if m is None:
            continue
        kind = m.group(1).decode(errors="replace")
        errors[kind] += 1
        found = True
    if not found and isinstance(err.code, str):
        errors[err.code] += 1


def parse_args() -> Config:
    parser = ArgumentParser()
    parser.add_argument("-f", "--fuel", "--model-fuel", help="model fuel")
    parser.add_argument("-n", "--examples", help="number of examples")
    parser.add_argument("--model-timeout", help="generator timeout in seconds")
    parser.add_argument("--test-timeout", help="generator timeout in seconds")
    parser.add_argument("-w", "--workers", help="number of worker threads")
    parser.add_argument("-o", "--output", help="destination directory")
    args = parser.parse_args()

    model_fuel = args.fuel
    if model_fuel is None:
        raise RuntimeError(f"Option --fuel is requred")

    n_examples = int(args.examples) if args.examples is not None else 64
    dest = Path(
        args.output
        if args.output is not None
        else tempfile.mkdtemp(prefix="go-")
    )

    return Config(
        model_fuel=model_fuel,
        n_examples=n_examples,
        dest=dest,
        n_workers=map_option(int, args.workers),
        model_timeout=map_option(float, args.model_timeout),
        test_timeout=map_option(float, args.test_timeout),
    )


async def main():
    global subproc_semaphore

    conf = parse_args()

    if conf.n_workers is not None:
        subproc_semaphore = asyncio.BoundedSemaphore(conf.n_workers)

    tasks = (test(conf) for _ in range(conf.n_examples))

    n_ok = n_fail = 0
    errors = Counter()

    try:
        for fut in asyncio.as_completed(tasks):
            try:
                result = await fut
                n_ok += 1
                print(f"[o] OK: {result.as_posix()}")
            except ExternalAppError as err:
                n_fail += 1
                print("[x] FAIL:")
                print(err.render())
                parse_output(err, errors)
    finally:
        print("-" * 60)
        print(f"OK: {n_ok}; Fail: {n_fail}")
        if errors:
            print("Errors found:")
            for err, cnt in errors.items():
                print(f"{err}: {cnt}")


if __name__ == "__main__":
    asyncio.run(main())
