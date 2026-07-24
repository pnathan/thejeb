#!/usr/bin/env python3
"""
Fetch public-domain Anti-Federalist essays from teachingamericanhistory.org
and write one clean text file per essay to sources/antifederalist/.

TAH document pages are Elementor/WordPress; the transcription lives in the
`theme-post-content` widget and ends where the study-questions widget
begins. We slice that region, strip tags (stdlib html.parser), unescape
entities, and collapse whitespace.
"""
import argparse
import html
import os
import re
import sys
import time
import urllib.request
from html.parser import HTMLParser

BASE = "https://teachingamericanhistory.org/document/{slug}/"
UA = "Mozilla/5.0 (compatible; thejeb-corpus/1.0)"


class Stripper(HTMLParser):
    def __init__(self):
        super().__init__()
        self.parts = []
        self.skip = 0
    def handle_starttag(self, tag, attrs):
        if tag in ("script", "style"):
            self.skip += 1
        if tag in ("p", "br", "div", "li", "h1", "h2", "h3", "blockquote"):
            self.parts.append("\n")
    def handle_endtag(self, tag):
        if tag in ("script", "style") and self.skip:
            self.skip -= 1
        if tag in ("p", "div", "li", "blockquote"):
            self.parts.append("\n")
    def handle_data(self, data):
        if not self.skip:
            self.parts.append(data)
    def text(self):
        return html.unescape("".join(self.parts))


FOOTER = ("collections", "study questions", "teacher programs",
          "related documents", "view collection", "previous document",
          "next document", "sign up", "subscribe", "no study questions",
          "explore past programs", "document study", "join our newsletter",
          "footnotes", "©", "all rights reserved")
OPENING = re.compile(
    r'^(to the (citizens|people|members|freemen|inhabitants|honorable|public)'
    r'|dear sir|gentlemen|mr\. printer|messieurs|sir[,:])', re.I)


def extract_body(page: str) -> str:
    # Strip <style>/<script> from the WHOLE page first (partial blocks leak).
    page = re.sub(r'(?is)<(style|script)[^>]*>.*?</\1>', ' ', page)
    p = Stripper()
    p.feed(page)
    lines = [re.sub(r'[ \t]+', ' ', ln).strip() for ln in p.text().splitlines()]
    lines = [ln for ln in lines if ln]

    # Start: the essay's opening address; else the line after the last
    # standalone "Document" heading (TAH puts the primary text there).
    start = next((i for i, ln in enumerate(lines) if OPENING.match(ln)), None)
    if start is None:
        docs = [i for i, ln in enumerate(lines) if ln.lower() == "document"]
        start = (docs[-1] + 1) if docs else 0

    # End: first footer/nav marker after the start.
    end = len(lines)
    for i in range(start, len(lines)):
        low = lines[i].lower()
        if any(low == f or low.startswith(f) for f in FOOTER):
            end = i
            break

    body, blank = [], 0
    for ln in lines[start:end]:
        if "{" in ln or "}" in ln or re.match(r'^[.#@][\w-]', ln):
            continue
        if re.match(r'^[a-z-]+\s*:\s*[^;]+;\s*$', ln):
            continue
        body.append(ln)
    return "\n".join(body).strip()


def fetch(slug: str) -> str:
    req = urllib.request.Request(BASE.format(slug=slug), headers={"User-Agent": UA})
    with urllib.request.urlopen(req, timeout=30) as r:
        return r.read().decode("utf-8", errors="replace")


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--slugs", required=True, help="file with one TAH slug per line")
    ap.add_argument("--out", required=True)
    ap.add_argument("--min-chars", type=int, default=2500)
    ap.add_argument("--sleep", type=float, default=1.0)
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    slugs = [s.strip() for s in open(args.slugs) if s.strip() and not s.startswith("#")]
    ok, skip = 0, 0
    for slug in slugs:
        try:
            page = fetch(slug)
            body = extract_body(page)
        except Exception as e:
            print(f"  FAIL {slug}: {e}", file=sys.stderr); skip += 1; continue
        if len(body) < args.min_chars:
            print(f"  SKIP {slug}: only {len(body)} chars", file=sys.stderr); skip += 1
            time.sleep(args.sleep); continue
        name = "af_" + slug.replace("-", "_")
        with open(os.path.join(args.out, f"{name}.txt"), "w", encoding="utf-8") as f:
            f.write(f"# Source: Anti-Federalist essay '{slug}' "
                    f"(teachingamericanhistory.org; public-domain 1787-88 text)\n")
            f.write("# Topic: the design and defense of the proposed U.S. Constitution\n\n")
            f.write(body + "\n")
        ok += 1
        print(f"  ok {slug}: {len(body)} chars")
        time.sleep(args.sleep)
    print(f"wrote {ok} essays to {args.out}  (skipped {skip})")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
