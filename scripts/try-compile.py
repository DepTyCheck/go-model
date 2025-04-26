#!/usr/bin/env python3

from argparse import ArgumentParser
from collections import Counter
from collections.abc import Iterable
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from signal import SIGKILL
from tempfile import TemporaryDirectory, mkstemp
from typing import Callable, Sequence, TypeVar, overload

import math
import multiprocessing
import os
import re
import subprocess as sp


_A = TypeVar("_A")
_C = TypeVar("_C")


@overload
def option(
    x: _A | None,
    f: Callable[[_A], _C],
) -> _C | None:
    if x is None:
        return None
    return f(x)


@overload
def option(x: _A | None, f: Callable[[_A], _C], default: _C) -> _C:
    if x is None:
        return default
    return f(x)


def option(x, f, default=None):
    if x is None:
        return default
    return f(x)


RETURNCODE_TIMEOUT = -2


def run_external_tool(
    cmd: Sequence[str], *, cwd: str | None = None, timeout: float | None = None
) -> tuple[int, bytes, bytes]:
    with sp.Popen(
        cmd, stdout=sp.PIPE, stderr=sp.PIPE, cwd=cwd, preexec_fn=os.setsid
    ) as proc:
        try:
            out, err = proc.communicate(timeout=timeout)
            return proc.returncode, out, err
        except sp.TimeoutExpired:
            os.killpg(proc.pid, SIGKILL)
            out, err = proc.communicate(timeout=timeout)
            return RETURNCODE_TIMEOUT, out, err


@dataclass
class Config:
    gen_timeout: float | None
    test_timeout: float | None
    n_workers: int
    n_examples: int
    model_fuel: int

    @property
    def examples_per_worker(self) -> int:
        return math.ceil(self.n_examples / self.n_workers)


@dataclass
class Failure:
    example: bytes
    cause: bytes
    returncode: int | None

    def __bool__(self) -> bool:
        return False


divider = re.compile(b"\n*// -*\n*")


def generate_examples(cfg: Config) -> list[bytes]:
    cmd = ["build/exec/go-model", "-n", str(cfg.examples_per_worker)]
    if cfg.model_fuel is not None:
        cmd.extend(("--model-fuel", str(cfg.model_fuel)))
    code, out, err = run_external_tool(cmd, timeout=cfg.gen_timeout)
    if code != 0 and code != RETURNCODE_TIMEOUT:
        raise RuntimeError(f"Error while generating example:\n  {err}")
    results = divider.split(out)
    results.remove(b"")
    return results


def generate_examples_par(cfg: Config) -> Iterable[bytes]:
    with ProcessPoolExecutor(cfg.n_workers) as exe:
        futures = (exe.submit(generate_examples, cfg) for _ in range(cfg.n_workers))
        for fut in as_completed(futures):
            yield from fut.result()


def check_via(
    example: bytes, cmd: Sequence[str], cwd: str, cfg: Config
) -> Failure | None:
    code, _, err = run_external_tool(cmd, cwd=cwd, timeout=cfg.test_timeout)
    if code == 0:
        return None
    else:
        return Failure(example, err, code)


def check_example(example: bytes, testdir: str, cfg: Config) -> Failure | None:
    if isinstance(example, Failure):
        return example

    tempfd, tempname = mkstemp(suffix=".go", dir=testdir)
    try:
        os.write(tempfd, example)
        os.close(tempfd)

        output = f"{tempname}.out"
        cmd = ("go", "build", "-o", output, tempname)

        if (c := check_via(example, cmd, testdir, cfg)) is not None:
            return c
        if (c := check_via(example, (output,), testdir, cfg)) is not None:
            return c
        return None
    finally:
        os.remove(tempname)


def check_examples_par(
    examples: Iterable[bytes], cfg: Config
) -> Iterable[Failure | None]:
    with TemporaryDirectory("deptycheck-go_") as testdir:
        with ProcessPoolExecutor(cfg.n_workers) as exe:
            futures = (exe.submit(check_example, ex, testdir, cfg) for ex in examples)
            for fut in as_completed(futures):
                yield fut.result()


compilation_error = re.compile(rb"\./[\w./]*:\d+:\d+: ([^:]*)")


def parse_output(output: bytes, errors: Counter):
    for line in output.splitlines():
        m = compilation_error.fullmatch(line)
        if m is None:
            continue
        kind = m.groups()[0]
        errors[kind] += 1


def render_example(code: str) -> str:
    lines = code.splitlines()
    width = len(str(len(lines)))
    return "\n".join(
        [f"{line_no:>{width}d}|{line}" for line_no, line in enumerate(lines, 1)]
    )


def parse_args() -> Config:
    parser = ArgumentParser()
    parser.add_argument("--gen-timeout", help="generator timeout in seconds")
    parser.add_argument("--test-timeout", help="generator timeout in seconds")
    parser.add_argument("-w", "--workers", help="number of worker threads")
    parser.add_argument("-n", "--examples", help="number of examples")
    parser.add_argument("-f", "--fuel", help="model fuel")
    args = parser.parse_args()

    return Config(
        gen_timeout=option(args.gen_timeout, float),
        test_timeout=option(args.test_timeout, float),
        n_examples=option(args.examples, int, 128),
        n_workers=option(args.workers, int, multiprocessing.cpu_count()),
        model_fuel=args.fuel,
    )


def main() -> None:
    cfg = parse_args()

    print("Start generating and checking examples")

    examples = generate_examples_par(cfg)

    n_ok = n_fail = 0
    errors = Counter()
    try:
        for res in check_examples_par(examples, cfg):
            if res is None:
                n_ok += 1
            else:
                n_fail += 1
                parse_output(res.cause, errors)
                print(f">>> Can't compile example (returncode = {res.returncode})")
                print(render_example(res.example.decode()))
                print()
                print(res.cause.decode())
                print()
    finally:
        print(f"OK: {n_ok}; Fail: {n_fail}")
        if errors:
            print("Errors found:")
            for er, cnt in errors.items():
                print(f"{er.decode()}: {cnt}")

    if n_fail != 0:
        exit(1)


if __name__ == "__main__":
    main()
