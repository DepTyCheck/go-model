#!/usr/bin/env python3

from abc import ABC, abstractmethod
import sys

from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Callable, Iterable, Optional, TypeVar

from sage.graphs.digraph import DiGraph


T = TypeVar("T")


def assert_type(t: type[T], x: Any) -> T:
    if not isinstance(x, t):
        raise RuntimeError(f"Expected type {t}, got {type(x)}")
    return x


def add_edge_checked(graph: DiGraph, a: Optional[str], b: Optional[str]):
    if a is None or b is None:
        return
    graph.add_edge(a, b)


class Segment(ABC):
    def __init__(self) -> None:
        super().__init__()
        self._last : tuple[str, ...] | None = None

    @abstractmethod
    def compute_last(self) -> tuple[str, ...]:
        pass

    def last(self) -> tuple[str, ...]:
        if self._last is None:
            self._last = self.compute_last()
        return self._last

    @abstractmethod
    def fill_graph(self, graph: DiGraph, prev: tuple[str, ...]) -> None:
        pass

    @abstractmethod
    def debug(self, offset: int) -> None:
        pass


class Linear(Segment):
    __slots__ = ("items", "child")

    def __init__(self) -> None:
        super().__init__()
        self.items: list[str] = []
        self.cont: Optional[Segment] = None

    def compute_last(self) -> tuple[str, ...]:
        if self.cont is not None:
            return self.cont.last()
        elif self.items:
            return (self.items[-1],)
        else:
            return ()

    def fill_graph(self, graph: DiGraph, prev: tuple[str, ...]) -> None:
        for i in range(len(self.items) - 1):
            a, b = self.items[i:i+2]
            add_edge_checked(graph, a, b)
        if self.items:
            last = (self.items[-1],)
            for p in prev:
                add_edge_checked(graph, p, self.items[0])
        else:
            last = prev
        if self.cont is not None:
            self.cont.fill_graph(graph, last)

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

    def compute_last(self) -> tuple[str, ...]:
        return (
            self.cont.last()
            or self.then_.last() + self.else_.last()
        )

    def fill_graph(self, graph: DiGraph, prev: tuple[str, ...]) -> None:
        self.then_.fill_graph(graph, prev)
        self.else_.fill_graph(graph, prev)
        self.cont.fill_graph(graph, prev + self.then_.last() + self.else_.last())

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

    def compute_last(self) -> tuple[str, ...]:
        return self.main.last() + self.other.last()

    def fill_graph(self, graph: DiGraph, prev: tuple[str, ...]) -> None:
        last_main = self.main.last()
        last_other = self.other.last()
        self.main.fill_graph(graph, prev + last_other)
        self.other.fill_graph(graph, prev + last_main)

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

    def fill_graph(self, graph: DiGraph) -> None:
        self._root.fill_graph(graph, ())

    def debug(self) -> None:
        self._root.debug(0)


def parse_order(content: list[str], filename: str = "string") -> dict[int, DiGraph]:
    known_chans: dict[int, Chan] = {}
    graphs = {}

    def graph(chan: int) -> DiGraph:
        if chan not in graphs:
            graphs[chan] = DiGraph(loops=True)
        return graphs[chan]

    def each_chan(f: Callable[[Chan, int], bool], id: int) -> None:
        to_del = []
        for key, chan in known_chans.items():
            if not f(chan, id):
                to_del.append(key)
                chan.fill_graph(graph(key))
        for key in to_del:
            del known_chans[key]

    id = 0
    for i, line in enumerate(content, 1):
        match line.split():
            case []: pass
            case ["OPEN", "CHAN", chan]:
                chan = int(chan)
                if chan not in known_chans:
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
    for key, chan in known_chans.items():
        chan.fill_graph(graph(key))

    return graphs


def shortest_path_checked(graph: DiGraph, u, v) -> list:
    if u not in graph or v not in graph:
        return []
    return graph.shortest_path(u, v)


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


def may_be_after(graph: DiGraph, first: str, second: str) -> bool:
    return len(shortest_path_checked(graph, first, second)) > 1


def may_have_value(graph: DiGraph, value: str, recv_op: str) -> bool:
    if value == "FAILED":
        raise RuntimeError("may_have_value can't check FAILED value")
    send_op = f"SEND {value}"
    send_unknown = "SEND UNKNOWN"
    return (
        bool(shortest_path_checked(graph, send_op, recv_op))
        or bool(shortest_path_checked(graph, send_unknown, recv_op))
    )


def check_order(
    graphs: dict[int, DiGraph],
    prog_output: list[str],
    filename: str
) -> bool:
    last_ops: dict[int, str] = {}
    ok = True

    for i, line in enumerate(prog_output, 1):
        match line.split():
            case ["RECV", "FROM", chan, label1, value]:
                chan = int(chan)
                graph = graphs[chan]
                op = f"RECV {label1}"

                if value == "FAILED" and not may_be_empty(graphs[chan], op):
                    print(
                        f"{filename}:{i}:0: Channel can't be empty\n"
                        f"  {line}\n",
                        file=sys.stderr
                    )
                    ok = False

                if value != "FAILED" and not may_have_value(graphs[chan], value, op):
                    print(
                        f"{filename}:{i}:0: Can get this value from the cannel\n"
                        f"  {line}\n",
                        file=sys.stderr
                    )
                    ok = False

                last = last_ops.get(chan, None)
                if last is not None and not may_be_after(graph, last, op):
                    print(
                        f"{filename}:{i}:0: Impossible sequence of operations\n"
                        f"  `{last}` then `{op}`\n",
                        file=sys.stderr
                    )
                    ok = False

                last_ops[int(chan)] = op

    return ok


def parse_file(file: Path) -> dict[int, DiGraph]:
    content = file.read_text().splitlines()
    return parse_order(content, file.as_posix())


def check_file(graph: dict[int, DiGraph], file: Path) -> bool:
    content = file.read_text().splitlines()
    return check_order(graph, content, file.as_posix())



def main() -> None:
    if len(sys.argv) != 3:
        print("Usage: check-order.py DESC PROG-OUTPUT", file=sys.stderr)
        exit(1)
    order = parse_file(Path(sys.argv[1]))
    if not check_file(order, Path(sys.argv[2])):
        exit(2)


if __name__ == "__main__":
    main()
