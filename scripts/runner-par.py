#!/usr/bin/env python3

import asyncio
import os
from random import shuffle
import re
import signal
import tempfile

from argparse import ArgumentParser
from collections import Counter
from dataclasses import dataclass
from pathlib import Path
from types import CoroutineType
from typing import Any, Callable, Iterable, Optional, Sequence, TypeVar


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
    sigkill: bool = False,
    timeout: Optional[float] = None,
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
            code = proc.returncode
            if code == 0:
                return out
            else:
                raise ExternalAppError(cmd, code, out, err)
        except BaseException as ex:
            try:
                os.killpg(
                    proc.pid, signal.SIGKILL if sigkill else signal.SIGTERM
                )
            except ProcessLookupError:
                pass
            if isinstance(ex, TimeoutError):
                out = await assume_some(proc.stdout).read()
                err = await assume_some(proc.stderr).read()
                raise ExternalAppError(cmd, "timeout", out, err) from ex
            else:
                raise


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


async def process_tasks(tasks: Iterable[CoroutineType[Any, Any, str]]) -> None:
    n_ok = n_fail = 0
    errors = Counter()

    try:
        for fut in asyncio.as_completed(tasks):
            try:
                result = await fut
                n_ok += 1
                print(f"[o] OK: {result}")
            except ExternalAppError as err:
                n_fail += 1
                print("[x] FAIL:")
                print(err.render())
                parse_output(err, errors)
            except Exception as e:
                n_fail += 1
                print("[x] FAIL:")
                print(e)
    finally:
        print("-" * 60)
        print(f"OK: {n_ok}; Fail: {n_fail}")
        if errors:
            print("Errors found:")
            for err, cnt in errors.items():
                print(f"{err}: {cnt}")


NORMAL_CODE_PAT = re.compile(rb"//\* NORMAL CODE \*//\n(.*?)//\*", re.DOTALL)
VERBOSE_CODE_PAT = re.compile(rb"//\* VERBOSE CODE \*//\n(.*?)//\*", re.DOTALL)
DESC_PAT = re.compile(rb"//\* DESCRIPTION \*//\n(.*?)$", re.DOTALL)

NORMAL_SRC = "normal.go"
VERBOSE_SRC = "verbose.go"
DESC_FILE = "desc.txt"
NORMAL_EXE = "normal"
VERBOSE_EXE = "verbose"
CAPTURE_PREFIX = "cap"


async def generate1(
    path: Path,
    model_fuel: int,
    *,
    timeout: Optional[float],
    exe: Sequence[str] = ("./build/exec/go-model",),
) -> Path:
    cmd = (*exe, "--model-fuel", str(model_fuel), "-n", "1")
    output = await run_app(*cmd, sigkill=True, timeout=timeout)
    normal = NORMAL_CODE_PAT.search(output)
    verbose = VERBOSE_CODE_PAT.search(output)
    desc = DESC_PAT.search(output)
    if normal is None or verbose is None or desc is None:
        raise ExternalAppError((), "Can't parse model output", output, b"")
    dir = Path(tempfile.mkdtemp(dir=path, prefix="ex-"))
    (dir / NORMAL_SRC).write_bytes(normal.group(1))
    (dir / VERBOSE_SRC).write_bytes(verbose.group(1))
    (dir / DESC_FILE).write_bytes(desc.group(1))
    return dir


async def compile1(file: Path) -> None:
    out = file.with_suffix("")
    await run_app("go", "build", "-o", out.as_posix(), file.as_posix())


async def capture1(dir: Path, executable: Path) -> None:
    out = await run_app(executable)
    if out:
        prefix = f"{CAPTURE_PREFIX}_{executable.name}_"
        fd, _ = tempfile.mkstemp(prefix=prefix, dir=dir)
        os.write(fd, out)
        os.close(fd)


async def check1(cap: Path) -> None:
    desc = cap.parent / DESC_FILE
    await run_app("python3", "scripts/check-order.py", desc, cap)


async def gen(
    path: Path,
    model_fuel: int,
    n_examples: int,
    compile_: bool,
    timeout: Optional[float],
):
    async def task() -> str:
        dir = await generate1(path, model_fuel, timeout=timeout)
        if compile_:
            await compile1(dir / NORMAL_SRC)
            await compile1(dir / VERBOSE_SRC)
        return dir.as_posix()

    await process_tasks(task() for _ in range(n_examples))


async def compile(path: Path) -> None:
    async def task(dir: Path) -> str:
        normal = dir / NORMAL_SRC
        if normal.is_file():
            await compile1(normal)
        verbose = dir / VERBOSE_SRC
        if verbose.is_file():
            await compile1(verbose)
        return dir.as_posix()

    await process_tasks(task(dir) for dir in path.iterdir())


async def capture(path: Path, times: int, verbose: bool, erase: bool) -> None:
    if erase:
        for old in path.glob(f"*/{CAPTURE_PREFIX}_*"):
            os.remove(old)

    async def task(dir, i):
        name = VERBOSE_EXE if verbose else NORMAL_EXE
        exe = dir / name
        if exe.is_file():
            await capture1(dir, exe)
        return f"{dir.as_posix()} [{i}/{times}]"

    tasks = [
        task(dir, i) for i in range(1, times + 1) for dir in path.iterdir()
    ]
    shuffle(tasks)
    await process_tasks(tasks)


async def check(path: Path):
    async def task(cap: Path) -> str:
        await check1(cap)
        return cap.as_posix()

    await process_tasks(task(cap) for cap in path.glob(f"*/{CAPTURE_PREFIX}_*"))


async def main() -> None:
    global subproc_semaphore

    prs = ArgumentParser()
    subprs = prs.add_subparsers(
        required=True, dest="action", metavar="action", title="actions"
    )

    def common_subparser(name: str, help: str) -> ArgumentParser:
        p = subprs.add_parser(name, help=help)
        p.add_argument("path", help="working directory", type=Path)
        p.add_argument("-w", "--workers", help="number of threads", type=int)
        return p

    prs_gen = common_subparser("gen", "generate examples")
    prs_gen.add_argument(
        "-f", "--fuel", help="model fuel", type=int, required=True
    )
    prs_gen.add_argument(
        "-n", "--examples", help="number of examples", type=int, required=True
    )
    prs_gen.add_argument(
        "-t",
        "--model-timeout",
        help="timeout for generating 1 example",
        type=float,
    )
    prs_gen.add_argument(
        "-C",
        "--no-compile",
        help="don't compile generated examples",
        action="store_false",
    )

    common_subparser("compile", "compile examples")

    prs_capt = common_subparser("capture", "run examples and capture output")
    prs_capt.add_argument(
        "-v",
        "--run-verbose",
        help="run verbose.go instead of normal.go",
        action="store_true",
    )
    prs_capt.add_argument(
        "-e", "--erase-old", help="erase previous records", action="store_true"
    )
    prs_capt.add_argument(
        "times", help="how many times run each examples", type=int
    )

    common_subparser("check", "check captured output")

    args = prs.parse_args()
    if args.workers is not None:
        subproc_semaphore = asyncio.BoundedSemaphore(args.workers)

    match args.action:
        case "gen":
            await gen(
                args.path,
                args.fuel,
                args.examples,
                args.no_compile,
                args.model_timeout,
            )
        case "compile":
            await compile(args.path)
        case "capture":
            await capture(
                args.path, args.times, args.run_verbose, args.erase_old
            )
        case "check":
            await check(args.path)


if __name__ == "__main__":
    asyncio.run(main())
