#!/usr/bin/env python3

import sys

from abc import ABC, abstractmethod
from pathlib import Path
from typing import Any, Callable, Optional, TypeVar


T = TypeVar("T")


def assert_type(t: type[T], x: Any) -> T:
    if not isinstance(x, t):
        raise RuntimeError(f"Expected type {t}, got {type(x)}")
    return x


class Segment(ABC):
    @abstractmethod
    def search(self, item: str) -> bool:
        pass

    @abstractmethod
    def search_ordered(self, fst: str, snd: str) -> bool:
        pass

    @abstractmethod
    def debug(self, offset: int) -> None:
        pass


class Linear(Segment):
    __slots__ = ("items", "cont")

    def __init__(self) -> None:
        super().__init__()
        self.items: list[str] = []
        self.cont: Optional[Segment] = None

    def search(self, item: str) -> bool:
        return (
            item in self.items
            or self.cont is not None and self.cont.search(item)
        )

    def search_ordered(self, fst: str, snd: str) -> bool:
        try:
            idx1 = self.items.index(fst)
        except ValueError:
            return self.cont is not None and self.cont.search_ordered(fst, snd)

        try:
            self.items.index(snd, idx1 + 1)
        except ValueError:
            return self.cont is not None and self.cont.search(snd)

        return True

    def debug(self, offset: int) -> None:
        for x in self.items:
            print(" " * offset, x)
        if self.cont is not None:
            self.cont.debug(offset)


class Branch(Segment):
    def __init__(self) -> None:
        super().__init__()
        self.then_: Linear = Linear()
        self.else_: Linear = Linear()
        self.cont: Linear = Linear()

    def search(self, item: str) -> bool:
        return (
            self.then_.search(item)
            or self.else_.search(item)
            or self.cont.search(item)
        )

    def search_ordered(self, fst: str, snd: str) -> bool:
        return (
            self.then_.search_ordered(fst, snd)
            or self.else_.search_ordered(fst, snd)
            or self.cont.search_ordered(fst, snd)
            or self.cont.search(snd)
            and (self.then_.search(fst) or self.else_.search(fst))
        )

    def debug(self, offset: int) -> None:
        print(" " * offset, "IF ... THEN")
        self.then_.debug(offset + 4)
        print(" " * offset, "ELSE")
        self.else_.debug(offset + 4)
        print(" " * offset, "ENDIF")
        self.cont.debug(offset)


class Go(Segment):
    def __init__(self) -> None:
        super().__init__()
        self.main: Linear = Linear()
        self.other: Linear = Linear()

    def search(self, item: str) -> bool:
        return self.main.search(item) or self.other.search(item)

    def search_ordered(self, fst: str, snd: str) -> bool:
        return (
            self.main.search_ordered(fst, snd)
            or self.other.search_ordered(fst, snd)
            or self.main.search(fst) and self.other.search(snd)
            or self.other.search(fst) and self.main.search(snd)
        )

    def debug(self, offset: int) -> None:
        print(" " * offset, "GO")
        self.other.debug(offset + 4)
        print(" " * offset, "ENDGO")
        self.main.debug(offset)


class Chan:
    slots = ("_root", "_active")

    def __init__(self) -> None:
        self._active: Linear = Linear()
        self._root: Linear = self._active
        self._stack: list[tuple[int, Linear]] = []

    def has_id(self, id: int) -> bool:
        return bool(self._stack and self._stack[-1][0] == id)

    def on_open(self) -> None:
        self._active.items.append(f'OPEN')

    def on_send(self, value: str) -> None:
        self._active.items.append(f'SEND {value}')

    def on_recv(self, label: str) -> None:
        self._active.items.append(f'RECV {label}')

    def on_if(self, id: int) -> bool:
        self._stack.append((id, self._active))
        branch = Branch()
        self._active.cont = branch
        self._active = branch.then_
        return True

    def on_else(self, id: int) -> bool:
        if not self.has_id(id):
            return False
        self._active = assert_type(Branch, self._stack[-1][1].cont).else_
        return True

    def on_endif(self, id: int) -> bool:
        if not self.has_id(id):
            return False
        self._active = assert_type(Branch, self._stack.pop()[1].cont).cont
        return True

    def on_go(self, id: int) -> bool:
        self._stack.append((id, self._active))
        go = Go()
        self._active.cont = go
        self._active = go.other
        return True

    def on_endgo(self, id: int) -> bool:
        if not self.has_id(id):
            return False
        self._active = assert_type(Go, self._stack.pop()[1].cont).main
        return True

    def debug(self) -> None:
        self._root.debug(0)

    def search_ordered(self, fst: str, snd: str) -> bool:
        return self._root.search_ordered(fst, snd)


def parse_order(content: list[str], filename: str = "string") -> dict[int, Chan]:
    known_chans: dict[int, Chan] = {}

    def each_chan(f: Callable[[Chan, int], bool], id: int) -> None:
        for chan in known_chans.values():
            f(chan, id)

    id = 0
    for i, line in enumerate(content, 1):
        match line.split():
            case []: pass
            case ["OPEN", "CHAN", chan]:
                chan = int(chan)
                if chan in known_chans:
                    known_chans[chan].on_open()
                else:
                    known_chans[chan] = Chan()
            case ["SEND", "TO", chan, value]:
                known_chans[int(chan)].on_send(value)
            case ["RECV", "FROM", chan, label1, _]:
                known_chans[int(chan)].on_recv(label1)
            case ["IF", _]:
                id += 1
                each_chan(Chan.on_if, id)
            case ["ELSE"]: each_chan(Chan.on_else, id)
            case ["ENDIF"]:
                each_chan(Chan.on_endif, id)
                id -= 1
            case ["GO"]:
                id += 1
                each_chan(Chan.on_go, id)
            case ["ENDGO"]:
                each_chan(Chan.on_endgo, id)
                id -= 1
            case _:
                print(
                    f"{filename}:{i}:0: Can't parse description file\n"
                    f"  {line}\n",
                    file=sys.stderr
                )
    return known_chans


def may_be_empty(*_) -> bool:
    return True
    # for path in graph.all_paths("OPEN", recv_op):
    #     cnt = 0
    #     for action in path:
    #         if "SEND" in action:
    #             cnt += 1
    #         elif "RECV" in action:
    #             cnt -= 1
    #     if cnt < 0:
    #         return True
    # return False


def may_have_value(chan: Chan, value: str, recv_op: str) -> bool:
    if value == "FAILED":
        raise RuntimeError("may_have_value can't check FAILED value")
    send_op = f"SEND {value}"
    send_unknown = "SEND UNKNOWN"
    return (
        chan.search_ordered(send_op, recv_op)
        or chan.search_ordered(send_unknown, recv_op)
    )


def check_order(
    chans: dict[int, Chan],
    prog_output: list[str],
    filename: str
) -> bool:
    last_ops: dict[int, str] = {}
    ok = True

    for i, line in enumerate(prog_output, 1):
        match line.split():
            case ["RECV", "FROM", chan_id, label1, value]:
                id = int(chan_id.strip('v'))
                chan = chans[id]
                op = f"RECV {label1}"

                if value == "FAILED" and not may_be_empty(chan, op):
                    print(
                        f"{filename}:{i}:0: Channel can't be empty\n"
                        f"  {line}\n",
                        file=sys.stderr
                    )
                    ok = False

                if value != "FAILED" and not may_have_value(chan, value, op):
                    print(
                        f"{filename}:{i}:0: Can get this value from the cannel\n"
                        f"  {line}\n",
                        file=sys.stderr
                    )
                    ok = False

                last = last_ops.get(id, None)
                if last is not None and not chan.search_ordered(last, op):
                    print(
                        f"{filename}:{i}:0: Impossible sequence of operations\n"
                        f"  `{last}` then `{op}`\n",
                        file=sys.stderr
                    )
                    ok = False

                last_ops[id] = op

    return ok


def parse_file(file: Path) -> dict[int, Chan]:
    content = file.read_text().splitlines()
    return parse_order(content, file.as_posix())


def check_file(chans: dict[int, Chan], file: Path) -> bool:
    content = file.read_text().splitlines()
    return check_order(chans, content, file.as_posix())


def main() -> None:
    if len(sys.argv) != 3:
        print("Usage: check-order.py DESC PROG-OUTPUT", file=sys.stderr)
        exit(1)
    order = parse_file(Path(sys.argv[1]))
    if not check_file(order, Path(sys.argv[2])):
        exit(2)


if __name__ == "__main__":
    main()
