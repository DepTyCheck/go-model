#!/usr/bin/env python3

from collections import Counter
from collections.abc import Iterable
from concurrent.futures import ProcessPoolExecutor, as_completed
from dataclasses import dataclass
from tempfile import TemporaryDirectory, NamedTemporaryFile

import math
import os
import re
import subprocess as sp


@dataclass
class Failure:
    example: bytes
    compiler_returncode: int
    compiler_stderr: bytes


divider = re.compile(b"\n*// -*\n*")


def generate_examples(count: int) -> list[bytes]:
    cmd = ("build/exec/go-model", "-n", str(count))
    pack_run = sp.run(cmd, stdout=sp.PIPE, check=True)
    results = divider.split(pack_run.stdout)
    results.remove(b"")
    if len(results) != count:
        raise RuntimeError("Can't properly split generated examples")
    return results


def generate_examples_par(
    count: int, *, max_workers: int | None = None
) -> Iterable[bytes]:

    if max_workers is None:
        max_workers = os.process_cpu_count()

    examples_per_proc = math.ceil(count / max_workers)
    with ProcessPoolExecutor(max_workers) as exe:
        futures = (
            exe.submit(generate_examples, examples_per_proc) for _ in range(max_workers)
        )
        for fut in as_completed(futures):
            yield from fut.result()


def check_example(example: bytes, testdir: str) -> Failure | None:
    with NamedTemporaryFile(
        suffix=".go", dir=testdir, delete_on_close=False
    ) as tempfile:
        tempfile.write(example)
        tempfile.close()

        output = f"{tempfile.name}.out"
        cmd = ("go", "build", "-o", output, tempfile.name)

        go_build = sp.run(cmd, stderr=sp.PIPE, cwd=testdir)
        if go_build.returncode != 0:
            return Failure(example, go_build.returncode, go_build.stderr)

        go_run = sp.run((output,), stderr=sp.PIPE, cwd=testdir)
        if go_run.returncode != 0:
            return Failure(example, go_run.returncode, go_run.stderr)

        return None


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
    # sp.run(("pack", "build"), check=True)

    print("Start generating and checking examples")

    examples = generate_examples_par(256)

    n_ok = n_fail = 0
    errors = Counter()
    try:
        for res in check_examples_par(examples):
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
