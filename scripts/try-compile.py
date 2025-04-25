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


@dataclass
class Failure:
    example: bytes
    compiler_returncode: int
    compiler_stderr: bytes


divider = re.compile(b"\n*// -*\n*")


def generate_examples(count: int, fuel: int | None) -> list[bytes]:
    cmd = ["build/exec/go-model", "-n", str(count)]
    if fuel is not None:
        cmd.extend(("--model-fuel", str(fuel)))
    pack_run = sp.run(cmd, stdout=sp.PIPE, check=True)
    results = divider.split(pack_run.stdout)
    results.remove(b"")
    if len(results) != count:
        raise RuntimeError("Can't properly split generated examples")
    return results


def generate_examples_par(
    count: int, *, max_workers: int, fuel: int | None
) -> Iterable[bytes]:
    examples_per_proc = math.ceil(count / max_workers)
    with ProcessPoolExecutor(max_workers) as exe:
        futures = (
            exe.submit(generate_examples, examples_per_proc, fuel)
            for _ in range(max_workers)
        )
        for fut in as_completed(futures):
            yield from fut.result()


def check_example(example: bytes, testdir: str) -> Failure | None:
    tempfd, tempname = mkstemp(suffix=".go", dir=testdir)
    try:
        os.write(tempfd, example)
        os.close(tempfd)

        output = f"{tempname}.out"
        cmd = ("go", "build", "-o", output, tempname)

        go_build = sp.run(cmd, stderr=sp.PIPE, cwd=testdir)
        if go_build.returncode != 0:
            return Failure(example, go_build.returncode, go_build.stderr)

        go_run = sp.run((output,), stderr=sp.PIPE, cwd=testdir)
        if go_run.returncode != 0:
            return Failure(example, go_run.returncode, go_run.stderr)

        return None
    finally:
        os.remove(tempname)


def check_examples_par(
    examples: Iterable[bytes], *, max_workers: int | None = None
) -> Iterable[Failure | None]:
    with TemporaryDirectory("deptycheck-go_") as testdir:
        with ProcessPoolExecutor(max_workers) as exe:
            futures = (exe.submit(check_example, ex, testdir) for ex in examples)
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


def main():
    parser = ArgumentParser()
    parser.add_argument("-t", "--threads")
    parser.add_argument("-e", "--examples")
    parser.add_argument("-f", "--fuel")
    args = parser.parse_args()

    n_examples = 128 if args.examples is None else int(args.examples)
    n_threads = (
        multiprocessing.cpu_count() if args.threads is None else int(args.threads)
    )
    fuel = args.fuel

    print("Start generating and checking examples")

    examples = generate_examples_par(n_examples, max_workers=n_threads, fuel=fuel)

    n_ok = n_fail = 0
    errors = Counter()
    try:
        for res in check_examples_par(examples, max_workers=n_threads):
            if res is None:
                n_ok += 1
            else:
                n_fail += 1
                parse_output(res.compiler_stderr, errors)
                print(
                    f">>> Can't compile example (returncode = {res.compiler_returncode})"
                )
                print(render_example(res.example.decode()))
                print()
                print(res.compiler_stderr.decode())
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
