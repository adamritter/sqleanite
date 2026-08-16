#!/usr/bin/env python3
"""Count SQLite page types in one or more database files.

Exists because file size alone does not say *why* a database is large. A census
localized a 4.5x space gap immediately: at 130,000 rows we emitted 43,326
interior table pages where C SQLite emitted 47, because the physical page tree is
a 2-3 tree and each interior node with two or three child pointers occupies a
whole page. Open-work item 2 in `PAPER_PLAN.md` states its acceptance in terms of
this percentage, so it needs to be measurable rather than reconstructed by hand.

Page one is the header page and is skipped. A page whose first byte is not a known
B-tree type is counted as other: freelist trunk and leaf pages, overflow pages and
pointer maps all live there, and distinguishing them needs the freelist chain
rather than a byte, which is more than this tool is for.

Usage:
  page-census.py FILE [FILE ...]
  page-census.py --page-size 8192 FILE
"""

import argparse
import sys

# First byte of a B-tree page. Values are from the SQLite file format.
PAGE_TYPES = {
    2: "interior-index",
    5: "interior-table",
    10: "leaf-index",
    13: "leaf-table",
}


def census(path, page_size):
    with open(path, "rb") as handle:
        data = handle.read()
    if len(data) < page_size:
        return None
    total = len(data) // page_size
    counts = {name: 0 for name in PAGE_TYPES.values()}
    counts["other"] = 0
    for index in range(1, total):
        marker = data[index * page_size]
        counts[PAGE_TYPES.get(marker, "other")] += 1
    return total, counts


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("files", nargs="+")
    parser.add_argument("--page-size", type=int, default=4096)
    args = parser.parse_args()

    order = ["leaf-table", "interior-table", "leaf-index", "interior-index", "other"]
    width = max(len(name) for name in args.files)
    print("%-*s %9s %9s %s" % (width, "file", "bytes/MB", "pages", "  ".join(order)))

    for path in args.files:
        result = census(path, args.page_size)
        if result is None:
            print("%-*s  (smaller than one page)" % (width, path), file=sys.stderr)
            continue
        total, counts = result
        counted = sum(counts.values()) or 1
        cells = []
        for name in order:
            value = counts[name]
            cells.append("%d(%.0f%%)" % (value, 100.0 * value / counted))
        megabytes = total * args.page_size / 1048576.0
        print("%-*s %9.1f %9d %s" % (width, path, megabytes, total, "  ".join(cells)))

    print()
    print("interior pages should be a low single-digit percentage of the total.")
    print("about half means the physical tree has fanout two or three, not real fanout.")


if __name__ == "__main__":
    main()
