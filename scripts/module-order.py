#!/usr/bin/env python3
"""List every local proof module in dependency order for offline verification."""

import re
from pathlib import Path


def main() -> None:
    root = Path(__file__).resolve().parent.parent
    modules = {f"Fluctuations.{p.stem}": p for p in (root / "Fluctuations").glob("*.lean")}
    complete: set[str] = set()
    active: set[str] = set()
    order: list[str] = []

    def visit(name: str) -> None:
        if name in complete:
            return
        if name in active:
            raise SystemExit(f"Cyclic local Lean imports at {name}")
        active.add(name)
        source = modules[name].read_text(encoding="utf-8")
        for dependency in re.findall(r"^import\s+(Fluctuations\.\w+)\s*$", source, re.MULTILINE):
            if dependency not in modules:
                raise SystemExit(f"Missing local Lean module {dependency}, imported by {name}")
            visit(dependency)
        active.remove(name)
        complete.add(name)
        order.append(name.removeprefix("Fluctuations."))

    for name in sorted(modules):
        visit(name)
    print("\n".join(order))


if __name__ == "__main__":
    main()
