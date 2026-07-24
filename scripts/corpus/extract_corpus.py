#!/usr/bin/env python3
"""
General multi-document STE extraction pipeline with per-document chunking.

  corpus/*.txt
    --(pass 1, haiku, PER CHUNK)--> open (variable,value,quote) claims
    --(aggregate per document)-->   pass1.json
    --(pass 2, sonnet, ONCE)-->     canonical schema + synonyms  -> schema.json
    --(pass 3, haiku, PER DOC)-->   one frame per document        -> frames.json

`frames.json` has the exact shape the verified Lean `tides` exe reads
(`{"frames": {docid: {var: {value, quote}}}}`), so the STE verdict is
computed by the proved algorithm (Ste.FiniteInstance) over the loaded data.

Each document is one STE "voice". Long documents are chunked for pass 1 so
extraction stays focused; the chunk-level claims are unioned into the
document's claim set. Model calls run in parallel (--jobs).

Usage:
  extract_corpus.py --corpus sources/federalist --out build/federalist \
      --topic "the design and defense of the proposed U.S. Constitution" \
      [--chunk-chars 9000] [--jobs 6] [--limit N] [--resume]
"""
import argparse
import concurrent.futures as cf
import json
import os
import re
import subprocess
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))


def extract_json(s: str):
    """First balanced top-level JSON object, string-aware. None on failure."""
    i = s.find("{")
    if i < 0:
        return None
    depth = 0; instr = False; esc = False
    for j in range(i, len(s)):
        c = s[j]
        if instr:
            if esc: esc = False
            elif c == "\\": esc = True
            elif c == '"': instr = False
            continue
        if c == '"': instr = True
        elif c == "{": depth += 1
        elif c == "}":
            depth -= 1
            if depth == 0:
                try:
                    return json.loads(s[i:j + 1])
                except Exception:
                    return None
    return None


def claude(prompt: str, model: str, retries: int = 3, timeout: int = 180):
    for a in range(retries):
        try:
            p = subprocess.run(
                ["claude", "-p", "--model", model, "--output-format", "json"],
                input=prompt, capture_output=True, text=True, timeout=timeout)
            env = json.loads(p.stdout) if p.stdout.strip() else None
        except Exception:
            env = None
        if env and not env.get("is_error") and env.get("result"):
            obj = extract_json(env["result"])
            if obj is not None:
                return obj
        time.sleep(2 * (a + 1))
    return None


def strip_header(text: str) -> str:
    lines = text.splitlines()
    k = 0
    while k < len(lines) and (lines[k].startswith("#") or lines[k].strip() == ""):
        k += 1
    return "\n".join(lines[k:]).strip()


def chunk_text(text: str, max_chars: int):
    paras = re.split(r"\n\s*\n", text)
    chunks, cur = [], ""
    for para in paras:
        if cur and len(cur) + len(para) + 2 > max_chars:
            chunks.append(cur); cur = para
        else:
            cur = (cur + "\n\n" + para) if cur else para
    if cur:
        chunks.append(cur)
    return chunks or [text]


def load_prompt(prompts_dir: str, name: str, topic: str) -> str:
    with open(os.path.join(prompts_dir, name)) as f:
        return f.read().replace("{TOPIC}", topic)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--corpus", required=True, nargs="+",
                    help="one or more corpus directories (docs are pooled)")
    ap.add_argument("--out", required=True)
    ap.add_argument("--topic", required=True)
    ap.add_argument("--prompts", default=os.path.join(HERE, "prompts"))
    ap.add_argument("--chunk-chars", type=int, default=9000)
    ap.add_argument("--doc-cap", type=int, default=45000)
    ap.add_argument("--jobs", type=int, default=6)
    ap.add_argument("--limit", type=int, default=0, help="cap #docs (0 = all)")
    ap.add_argument("--haiku", default="haiku")
    ap.add_argument("--sonnet", default="sonnet")
    ap.add_argument("--resume", action="store_true",
                    help="reuse pass1.json / schema.json if present")
    args = ap.parse_args()

    os.makedirs(args.out, exist_ok=True)
    paths = []
    for d in args.corpus:
        paths += [os.path.join(d, f) for f in sorted(os.listdir(d))
                  if f.endswith(".txt")]
    if args.limit:
        paths = paths[:args.limit]
    docs = {os.path.splitext(os.path.basename(p))[0]: strip_header(
        open(p, encoding="utf-8", errors="replace").read()) for p in paths}
    print(f"corpus: {len(docs)} documents from {', '.join(args.corpus)}", flush=True)

    p1_prompt = load_prompt(args.prompts, "pass1_open.md", args.topic)
    p2_prompt = load_prompt(args.prompts, "pass2_unify.md", args.topic)
    p3_prompt = load_prompt(args.prompts, "pass3_constrained.md", args.topic)

    pass1_path = os.path.join(args.out, "pass1.json")
    schema_path = os.path.join(args.out, "schema.json")
    frames_path = os.path.join(args.out, "frames.json")

    # ---- Pass 1: open extraction, per chunk, parallel ----
    if args.resume and os.path.exists(pass1_path):
        doc_claims = json.load(open(pass1_path))["documents"]
        print(f"pass1: reused {pass1_path}", flush=True)
    else:
        tasks = []  # (docid, chunk_index, chunk_text)
        for docid, text in docs.items():
            for ci, ch in enumerate(chunk_text(text, args.chunk_chars)):
                tasks.append((docid, ci, ch))
        print(f"pass1: {len(tasks)} chunks across {len(docs)} docs "
              f"(jobs={args.jobs})", flush=True)
        doc_claims = {d: [] for d in docs}
        done = 0

        def do_chunk(t):
            docid, ci, ch = t
            obj = claude(f"{p1_prompt}\n\n----- CHUNK -----\n{ch}", args.haiku)
            return docid, (obj or {}).get("claims", []) if obj else []

        with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
            for docid, claims in ex.map(do_chunk, tasks):
                doc_claims[docid].extend(claims)
                done += 1
                if done % 20 == 0:
                    print(f"  pass1 {done}/{len(tasks)} chunks", flush=True)
        json.dump({"documents": doc_claims}, open(pass1_path, "w"), indent=2)
        print(f"pass1: -> {pass1_path}", flush=True)

    # ---- build observed (variable,value) table ----
    counts, example = {}, {}
    for docid, claims in doc_claims.items():
        seen_here = set()
        for c in claims:
            v, val = c.get("variable"), c.get("value")
            if not v or not val:
                continue
            key = (v, val)
            if key not in seen_here:
                counts[key] = counts.get(key, 0) + 1
                seen_here.add(key)
            example.setdefault(key, c.get("quote", ""))
    observed = [{"variable": v, "value": val, "count": n,
                 "example_quote": example[(v, val)]}
                for (v, val), n in sorted(counts.items(), key=lambda kv: -kv[1])]
    print(f"observed: {len(observed)} distinct (variable,value) pairs", flush=True)

    # ---- Pass 2: schema unification, once ----
    if args.resume and os.path.exists(schema_path):
        schema = json.load(open(schema_path))
        print(f"pass2: reused {schema_path}", flush=True)
    else:
        schema = claude(f"{p2_prompt}\n\n----- OBSERVED -----\n"
                        f"{json.dumps({'observed': observed}, indent=2)}",
                        args.sonnet, timeout=300)
        if not schema or "variables" not in schema:
            sys.exit("pass2 failed to produce a schema")
        json.dump(schema, open(schema_path, "w"), indent=2)
        print(f"pass2: -> {schema_path}  "
              f"({len(schema['variables'])} variables)", flush=True)

    var_names = [v["name"] for v in schema["variables"]]
    schema_blob = json.dumps(schema, indent=2)

    # ---- Pass 3: schema-constrained, per document, parallel ----
    print(f"pass3: {len(docs)} documents (jobs={args.jobs})", flush=True)
    frames = {}
    done = 0

    def do_doc(item):
        docid, text = item
        prompt = (f"{p3_prompt}\n\n----- SCHEMA -----\n{schema_blob}\n\n"
                  f"----- DOCUMENT -----\n{text[:args.doc_cap]}")
        obj = claude(prompt, args.haiku)
        frame = (obj or {}).get("frame", {}) if obj else {}
        # keep only canonical variables; normalize missing -> silent
        clean = {}
        for vn in var_names:
            cell = frame.get(vn)
            if isinstance(cell, dict) and cell.get("value") not in (None, "silent"):
                clean[vn] = {"value": cell["value"],
                             "quote": cell.get("quote", "")}
            else:
                clean[vn] = {"value": "silent"}
        return docid, clean

    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        for docid, clean in ex.map(do_doc, list(docs.items())):
            frames[docid] = clean
            done += 1
            if done % 20 == 0:
                print(f"  pass3 {done}/{len(docs)} docs", flush=True)

    out = {"schema_version": ", ".join(var_names),
           "topic": args.topic, "frames": frames}
    json.dump(out, open(frames_path, "w"), indent=2)
    print(f"pass3: -> {frames_path}  ({len(frames)} document frames)", flush=True)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
