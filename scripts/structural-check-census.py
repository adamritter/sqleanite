#!/usr/bin/env python3
"""Measure the cost of the page-local write path's structural premises.

`CoreLazyWrite.insertPlan_refines` is conditional on `WellFormedTree`, whose two
expensive fields are `TreeDisjoint` (sibling subtrees occupy disjoint page sets)
and `TreeSound` (separators genuinely bound every key in the subtree they name).
`docs/LAZY_WRITE_DESIGN.md` argued both are checkable far more cheaply than the
whole-database open they would replace, and quoted 653 ms at 1,000,000 rows.

That measurement read each leaf's **first and last** cell only. First/last
bounds every key in the leaf *only if the leaf is internally sorted*, which is
exactly one of the things a structural check is supposed to establish rather than
assume, so it is weaker than the `TreeSound` premise it was cited for. This tool
exists so the honest version is reproducible: it measures the endpoint scan and
the full per-leaf key-monotonicity scan separately, on the same file, and reports
both alongside the violation counts.

Nothing here is verified. It is a measurement instrument for a proof obligation,
not a checker the engine trusts: the engine's own checker, when it is written,
has to be Lean with a soundness theorem. Numbers from this tool tell you what
that checker will cost.

Usage:
  structural-check-census.py FILE [--table NAME] [--repeat N] [--cold]
"""

import argparse
import os
import struct
import sys
import time

INTERIOR_TABLE = 5
LEAF_TABLE = 13


def read_varint(data, offset):
    """SQLite's big-endian base-128 varint. Returns (value, bytes consumed)."""
    value = 0
    for index in range(8):
        byte = data[offset + index]
        value = (value << 7) | (byte & 0x7F)
        if byte < 0x80:
            return value, index + 1
    # Ninth byte contributes all eight of its bits.
    return (value << 8) | data[offset + 8], 9


class Pager:
    def __init__(self, path, cold=False):
        self.handle = open(path, "rb")
        header = self.handle.read(100)
        if header[:16] != b"SQLite format 3\x00":
            raise SystemExit(f"{path}: not a SQLite database")
        raw_size = struct.unpack(">H", header[16:18])[0]
        self.page_size = 65536 if raw_size == 1 else raw_size
        self.page_count = struct.unpack(">I", header[28:32])[0]
        if self.page_count == 0:
            self.page_count = os.path.getsize(path) // self.page_size
        self.reads = 0
        if cold:
            os.posix_fadvise(self.handle.fileno(), 0, 0, os.POSIX_FADV_DONTNEED)

    def page(self, number):
        """One-based page read, as SQLite numbers them."""
        self.reads += 1
        self.handle.seek((number - 1) * self.page_size)
        data = self.handle.read(self.page_size)
        if len(data) != self.page_size:
            raise SystemExit(f"short read for page {number}")
        return data

    def close(self):
        self.handle.close()


def page_header_offset(number):
    return 100 if number == 1 else 0


def cell_pointers(page, number):
    base = page_header_offset(number)
    page_type = page[base]
    if page_type == INTERIOR_TABLE:
        header_length = 12
    elif page_type == LEAF_TABLE:
        header_length = 8
    else:
        return page_type, []
    count = struct.unpack(">H", page[base + 3 : base + 5])[0]
    start = base + header_length
    pointers = [
        struct.unpack(">H", page[start + 2 * index : start + 2 * index + 2])[0]
        for index in range(count)
    ]
    return page_type, pointers


def interior_children(page, number):
    """Children in key order: each cell's left child, then the rightmost."""
    base = page_header_offset(number)
    _, pointers = cell_pointers(page, number)
    children = []
    for pointer in pointers:
        children.append(struct.unpack(">I", page[pointer : pointer + 4])[0])
    children.append(struct.unpack(">I", page[base + 8 : base + 12])[0])
    return children


def leaf_keys(page, number):
    """Every rowid in a table-leaf page, in cell-pointer order."""
    _, pointers = cell_pointers(page, number)
    keys = []
    for pointer in pointers:
        _, consumed = read_varint(page, pointer)
        rowid, _ = read_varint(page, pointer + consumed)
        keys.append(rowid)
    return keys


def leaf_endpoint_keys(page, number):
    """The first and last rowid only -- the weaker scan, kept for comparison.

    A one-cell leaf has to yield one key, not the same key twice: reporting it
    twice makes the strict-increase test fire on `key <= key` and shows up as a
    violation the full scan does not see. That is a checker bug and not a file
    defect, and it is exactly the failure mode the design document warned about
    for visiting leaves in the wrong order.
    """
    _, pointers = cell_pointers(page, number)
    if not pointers:
        return []
    selected = [pointers[0]] if len(pointers) == 1 else [pointers[0], pointers[-1]]
    keys = []
    for pointer in selected:
        _, consumed = read_varint(page, pointer)
        rowid, _ = read_varint(page, pointer + consumed)
        keys.append(rowid)
    return keys


def root_page(pager, table):
    """Resolve a table name to its root page through the sqlite_schema table."""
    page_one = pager.page(1)
    page_type, pointers = cell_pointers(page_one, 1)
    if page_type != LEAF_TABLE:
        raise SystemExit(
            "sqlite_schema spans multiple pages; pass --root instead of --table"
        )
    for pointer in pointers:
        payload_size, consumed = read_varint(page_one, pointer)
        offset = pointer + consumed
        _, consumed = read_varint(page_one, offset)
        offset += consumed
        payload = page_one[offset : offset + payload_size]
        header_size, consumed = read_varint(payload, 0)
        serial_types = []
        cursor = consumed
        while cursor < header_size:
            serial, consumed = read_varint(payload, cursor)
            serial_types.append(serial)
            cursor += consumed
        values = []
        for serial in serial_types:
            if serial == 0:
                values.append(None)
            elif 1 <= serial <= 6:
                width = [0, 1, 2, 3, 4, 6, 8][serial]
                values.append(
                    int.from_bytes(payload[cursor : cursor + width], "big", signed=True)
                )
                cursor += width
            elif serial >= 13 and serial % 2 == 1:
                width = (serial - 13) // 2
                values.append(payload[cursor : cursor + width].decode("utf-8", "replace"))
                cursor += width
            elif serial >= 12:
                width = (serial - 12) // 2
                values.append(payload[cursor : cursor + width])
                cursor += width
            else:
                values.append(None)
        if len(values) >= 4 and values[0] == "table" and values[1] == table:
            return int(values[3])
    raise SystemExit(f"no such table: {table}")


def walk_interiors(pager, root):
    """Tree-order leaf list, reading interior pages only.

    Page numbering does not follow key order, so the leaves must be visited in
    depth-first tree order. Sorting by page number instead reports every leaf as
    a violation, which reads as a corrupt file rather than as a broken checker.
    """
    leaves = []
    interiors = 0
    stack = [root]
    while stack:
        number = stack.pop()
        page = pager.page(number)
        page_type = page[page_header_offset(number)]
        if page_type == INTERIOR_TABLE:
            interiors += 1
            children = interior_children(page, number)
            stack.extend(reversed(children))
        elif page_type == LEAF_TABLE:
            leaves.append(number)
        else:
            raise SystemExit(f"page {number} is not a table b-tree page")
    return leaves, interiors


def scan(pager, leaves, full):
    """Key-order violations across the tree. `full` scans every cell."""
    violations = 0
    cells = 0
    previous = None
    for number in leaves:
        page = pager.page(number)
        keys = leaf_keys(page, number) if full else leaf_endpoint_keys(page, number)
        cells += len(keys)
        for key in keys:
            if previous is not None and key <= previous:
                violations += 1
            previous = key
    return violations, cells


def duplicate_pages(leaves, interiors_seen):
    seen = set()
    duplicates = 0
    for number in leaves + interiors_seen:
        if number in seen:
            duplicates += 1
        seen.add(number)
    return duplicates, len(seen)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("path")
    parser.add_argument("--table", default="usertable")
    parser.add_argument("--root", type=int, default=None)
    parser.add_argument("--repeat", type=int, default=3)
    parser.add_argument("--cold", action="store_true")
    args = parser.parse_args()

    pager = Pager(args.path, cold=args.cold)
    root = args.root if args.root is not None else root_page(pager, args.table)

    size_mb = os.path.getsize(args.path) / (1024 * 1024)
    print(f"file            {args.path}")
    print(f"size            {size_mb:.2f} MB, {pager.page_count} pages "
          f"of {pager.page_size} bytes")
    print(f"root page       {root}")

    walk_ms = []
    endpoint_ms = []
    full_ms = []
    for _ in range(max(1, args.repeat)):
        start = time.perf_counter()
        leaves, interiors = walk_interiors(pager, root)
        walk_ms.append((time.perf_counter() - start) * 1000)

        start = time.perf_counter()
        endpoint_violations, endpoint_cells = scan(pager, leaves, full=False)
        endpoint_ms.append((time.perf_counter() - start) * 1000)

        start = time.perf_counter()
        full_violations, full_cells = scan(pager, leaves, full=True)
        full_ms.append((time.perf_counter() - start) * 1000)

    median = lambda values: sorted(values)[len(values) // 2]
    duplicates, distinct = duplicate_pages(leaves, [])
    print(f"interior pages  {interiors}")
    print(f"leaf pages      {len(leaves)} ({distinct} distinct, "
          f"{duplicates} duplicated)")
    print(f"rows            {full_cells}")
    print()
    print(f"{'step':<44}{'median ms':>12}")
    print(f"{'-' * 56}")
    print(f"{'tree-order walk of interior pages':<44}{median(walk_ms):>12.0f}")
    print(f"{'first/last cell of every leaf (weak)':<44}"
          f"{median(endpoint_ms):>12.0f}")
    print(f"{'every cell of every leaf (TreeSound)':<44}"
          f"{median(full_ms):>12.0f}")
    print(f"{'-' * 56}")
    print(f"{'total, endpoints only':<44}"
          f"{median(walk_ms) + median(endpoint_ms):>12.0f}")
    print(f"{'total, full monotonicity':<44}"
          f"{median(walk_ms) + median(full_ms):>12.0f}")
    print()
    print(f"ordering violations, endpoint scan   {endpoint_violations}")
    print(f"ordering violations, full scan       {full_violations}")
    print(f"page reads per pass                  "
          f"{interiors + 2 * len(leaves)}")
    pager.close()
    return 0 if full_violations == 0 else 1


if __name__ == "__main__":
    sys.exit(main())
