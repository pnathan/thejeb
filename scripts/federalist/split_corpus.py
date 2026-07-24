#!/usr/bin/env python3
"""
Split the Project Gutenberg Federalist Papers (pg18.txt) into one file per
essay: sources/federalist/fed_NNN.txt, with a provenance header.

Each essay body begins with a line `THE FEDERALIST.` followed by `No.
<roman>.`, the title, the journal, and the author (HAMILTON / JAY /
MADISON / ...). We split on `THE FEDERALIST.`, parse the number and author,
and write one file per essay.
"""
import argparse
import os
import re
import sys

ROMAN = {'I': 1, 'V': 5, 'X': 10, 'L': 50, 'C': 100, 'D': 500, 'M': 1000}


def from_roman(s: str) -> int:
    total, prev = 0, 0
    for ch in reversed(s):
        v = ROMAN[ch]
        total += -v if v < prev else v
        prev = max(prev, v)
    return total


DELIM = re.compile(r'^THE FEDERALIST\.\s*$', re.M)
NUM = re.compile(r'^\s*No\.\s+([IVXLCDM]+)\.', re.M)
AUTHORS = ("HAMILTON AND MADISON", "HAMILTON OR MADISON",
           "HAMILTON", "MADISON", "JAY")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--raw", required=True)
    ap.add_argument("--out", required=True)
    args = ap.parse_args()

    text = open(args.raw, encoding="utf-8", errors="replace").read()
    start = re.search(r'\*\*\* START OF THE PROJECT GUTENBERG.*?\*\*\*', text)
    end = re.search(r'\*\*\* END OF THE PROJECT GUTENBERG', text)
    body = text[start.end() if start else 0: end.start() if end else len(text)]

    starts = [m.start() for m in DELIM.finditer(body)]
    if not starts:
        sys.exit("no essay delimiters found")

    os.makedirs(args.out, exist_ok=True)
    seen: dict[int, int] = {}
    written = 0
    manifest = []
    for k, pos in enumerate(starts):
        endpos = starts[k + 1] if k + 1 < len(starts) else len(body)
        essay = body[pos:endpos].strip()
        mnum = NUM.search(essay)
        if not mnum:
            continue
        num = from_roman(mnum.group(1))
        head = essay[:400].upper()
        author = next((a for a in AUTHORS if a in head), "UNKNOWN")
        seen[num] = seen.get(num, 0) + 1
        suffix = "" if seen[num] == 1 else chr(ord('a') + seen[num] - 1)
        name = f"fed_{num:03d}{suffix}"
        fn = os.path.join(args.out, f"{name}.txt")
        with open(fn, "w", encoding="utf-8") as f:
            f.write(f"# Source: The Federalist Papers, No. {num} "
                    f"({author.title()}); Project Gutenberg eBook #18, public domain\n")
            f.write("# Topic: the design and defense of the proposed U.S. Constitution\n\n")
            f.write(essay + "\n")
        manifest.append((name, num, author, len(essay)))
        written += 1

    print(f"wrote {written} essays to {args.out}")
    nums = sorted(n for _, n, _, _ in manifest)
    print(f"numbers: {nums[0]}..{nums[-1]}  (distinct {len(set(nums))}, files {written})")
    missing = [i for i in range(1, 86) if i not in set(nums)]
    if missing:
        print(f"WARNING missing numbers: {missing}")
    sizes = sorted(s for _, _, _, s in manifest)
    print(f"essay chars: min {sizes[0]}, median {sizes[len(sizes)//2]}, max {sizes[-1]}")
    from collections import Counter
    print("authors:", dict(Counter(a for _, _, a, _ in manifest)))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
