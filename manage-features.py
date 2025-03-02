#!/usr/bin/env python3

import re

from dataclasses import dataclass
from enum import Enum
from pathlib import Path
from typing import Literal, Never


class Status(Enum):
    COMMENTED_OUT = 0
    UNCOMMENTED = 1

    def invert(self):
        if self == Status.COMMENTED_OUT:
            return Status.UNCOMMENTED
        else:
            return Status.COMMENTED_OUT


type Features = dict[str, Status]


decl_pat = re.compile(r"^([+\-])\s*(\w+)\s*(\-\-.*)?")
empty_line_pat = re.compile(r"\s*(\-\-.*)?")

directive_pat = re.compile(r"\s*\-\-\s+@(WHEN|UNLESS|END)\s+(\w+)\s*")

line_pat = re.compile(r"(\s*)(\-\- @ )?(.*)")


def parse_error(path: Path, line_no: int, msg: str) -> Never:
    raise RuntimeError(
        f"Parse error at {path.as_posix()}, line {line_no}:\n" f"    {msg}\n"
    )


def read_config(path: Path) -> Features:
    features = {}
    with open(path, "r") as conf:
        for line_no, line in enumerate(conf, 1):
            line = line.rstrip()
            if empty_line_pat.fullmatch(line) is not None:
                continue
            decl = decl_pat.fullmatch(line)
            if decl is None:
                parse_error(path, line_no, "wrong format")
            sign, name, *_ = decl.groups()
            if name in features:
                raise RuntimeError(f"Feature {name} already mentioned")
            if sign == "+":
                features[name] = Status.UNCOMMENTED
            else:
                features[name] = Status.COMMENTED_OUT
    return features


def update_error(path: Path, line_no: int, msg: str) -> Never:
    raise RuntimeError(
        f"Error while updating {path.as_posix()}, line {line_no}:\n" f"    {msg}\n"
    )


@dataclass
class Directive:
    keyword: Literal["WHEN", "UNLESS", "END"]
    name: str


def parse_line(line: str) -> Directive | None:
    if (m := directive_pat.fullmatch(line)) is not None:
        keyword_str, name = m.groups()
        keyword: Literal["WHEN", "UNLESS", "END"] = keyword_str  # type: ignore
        return Directive(keyword, name)
    return None


def update_line(line: str, new_status: Status) -> str:
    m = line_pat.fullmatch(line)
    if m is None:
        raise RuntimeError(f"Can't parse line: {line}")
    spaces, leader, text = m.groups()

    old_status = Status.UNCOMMENTED if leader is None else Status.COMMENTED_OUT
    if old_status == new_status:
        print("Skip:", line)
        return line

    if new_status == Status.UNCOMMENTED:
        print("Uncomment:", line)
        return f"{spaces}{text}"
    else:
        print("Comment out:", line)
        if text == "":
            return line
        else:
            return f"{spaces}-- @ {text}"


def update_file(path: Path, features: Features):
    content = path.read_text().splitlines()
    need_rewrite = False
    current_block: str | None = None
    new_status: Status = Status.UNCOMMENTED

    for i in range(len(content)):
        line_no, line = i + 1, content[i]
        cmd = parse_line(line)
        match current_block, cmd:
            case None, None:
                pass
            case None, _:
                if cmd.keyword == "END":
                    update_error(path, line_no, "Expected WHEN or UNLESS")
                if cmd.name not in features:
                    update_error(path, line_no, f"Unknown feature {cmd.name}")
                current_block = cmd.name
                if cmd.keyword == "WHEN":
                    new_status = features[current_block]
                else:
                    new_status = features[current_block].invert()
            case _, None:
                new_line = update_line(line, new_status)
                if new_line != line:
                    need_rewrite = True
                    content[i] = new_line
            case _, _:
                msg = f"Expected END or UNLESS for {current_block}"
                if cmd.name != current_block:
                    update_error(path, line_no, msg)
                if cmd.keyword == "END":
                    current_block = None
                elif cmd.keyword == "UNLESS":
                    new_status = features[cmd.name].invert()
                else:
                    update_error(path, line_no, msg)

    if current_block is not None:
        update_error(path, len(content), f"Block {current_block} is not closed")

    if need_rewrite:
        path.write_text("\n".join(content))


def traverse(root: Path, features: Features):
    for dir, _, files in root.walk():
        for file in files:
            file = dir / file
            update_file(Path(file), features)


def main():
    here = Path.cwd()
    config = here / "features.txt"
    try:
        features = read_config(config)
    except FileNotFoundError:
        raise RuntimeError("Can't find features.txt in the current directory") from None

    if (src := here / "src").exists():
        traverse(src, features)
    if (test := here / "test").exists():
        traverse(test, features)
    for ipkg in here.glob("*.ipkg"):
        update_file(ipkg, features)
    for toml in here.glob("*.toml"):
        update_file(toml, features)


if __name__ == "__main__":
    main()
