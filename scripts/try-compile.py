#!/usr/bin/env python3

from argparse import ArgumentParser
from collections import Counter
from collections.abc import Iterable
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from tempfile import TemporaryDirectory, mkstemp

import math
import multiprocessing
import os
import re
import subprocess as sp
from typing import Callable, Sequence, TypeVar, overload


_A = TypeVar("_A")
_C = TypeVar("_C")


@overload
def none_or_map(
        x: _A | None,
        f: Callable[[_A], _C],
) -> _C | None:
    if x is None:
        return None
    return f(x)


@overload
def none_or_map(
        x: _A | None,
        f: Callable[[_A], _C],
        default: Callable[[], _C]
)-> _C:
    if x is None:
        return default()
    return f(x)


def none_or_map(x, f, default = None):
    if x is None:
        return default
    return f(x)


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


class Success:
    __slots__ = ()

    def __bool__(self) -> bool:
        return True


SUCCESS = Success()


divider = re.compile(b"\n*// -*\n*")


def generate_examples(cfg: Config) -> list[bytes]:
    cmd = ["build/exec/go-model", "-n", str(cfg.n_examples)]
    if cfg.model_fuel is not None:
        cmd.extend(("--model-fuel", str(cfg.model_fuel)))
    pack_run = sp.run(cmd, stdout=sp.PIPE, check=True)
    results = divider.split(pack_run.stdout)
    results.remove(b"")
    if len(results) != cfg.n_examples:
        raise RuntimeError("Can't properly split generated examples")
    return results


def generate_examples_par(cfg: Config) -> Iterable[bytes]:
    with ProcessPoolExecutor(cfg.n_workers) as exe:
        futures = (exe.submit(generate_examples, cfg) for _ in range(cfg.n_workers))
        try:
            for fut in as_completed(futures, cfg.gen_timeout):
                yield from fut.result()
        except TimeoutError:
            print("TimeoutError: can't generate enough examples")


def check_via(
    example: bytes, cmd: Sequence[str], cwd: str, cfg: Config
) -> Failure | Success:
    try:
        go_build = sp.run(cmd, stderr=sp.PIPE, cwd=cwd, timeout=cfg.test_timeout)
        if go_build.returncode == 0:
            return SUCCESS
        else:
            return Failure(example, go_build.stderr, go_build.returncode)
    except TimeoutError:
        return Failure(example, b"TimeoutError", -1)


def check_example(example: bytes, testdir: str, cfg: Config) -> Failure | Success:
    if isinstance(example, Failure):
        return example

    tempfd, tempname = mkstemp(suffix=".go", dir=testdir)
    try:
        os.write(tempfd, example)
        os.close(tempfd)

        output = f"{tempname}.out"
        cmd = ("go", "build", "-o", output, tempname)

        return (
            check_via(example, cmd, testdir, cfg)
            and check_via(example, (output,), testdir, cfg)
            and SUCCESS
        )
    finally:
        os.remove(tempname)


def check_examples_par(
    examples: Iterable[bytes], cfg: Config
) -> Iterable[Failure | Success]:
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
        gen_timeout=none_or_map(args.gen_timeout, float),
        test_timeout=none_or_map(args.test_timeout, float),
        n_examples=none_or_map(args.examples, int, lambda: 128),
        n_workers=none_or_map(args.workers, int, multiprocessing.cpu_count),
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
            if isinstance(res, Success):
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
