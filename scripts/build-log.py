#!/usr/bin/env python3


import subprocess as sp

from datetime import datetime
from pathlib import Path


filename = format(datetime.now(), "%y%m%d_%H%M")
path = Path("logs") / filename
proc = sp.Popen(
    ("/usr/bin/time", "-v", "stdbuf", "-oL", "pack",  "build"),
    stdout=sp.PIPE,
    stderr=sp.PIPE,
    text=True
)

if proc.stdout is None or proc.stderr is None:
    raise RuntimeError("Can't open stdout or stderr")

try:
    with open(path, "w") as output:
        for line in proc.stdout:
            output.write(line)
            print(line, end="")

    code = proc.wait()
except KeyboardInterrupt:
    code = 127
    proc.send_signal(2)

with open(path, "a") as output:
    content = proc.stderr.read()
    output.write(content)
    print(content, end="")

if code != 0:
    path.rename(path.with_name(f"{filename}.exit{code}"))

exit(code)
