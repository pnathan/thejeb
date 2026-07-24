# Tides corpus — extraction pass 1 (Claude Haiku, open extraction)

You are extracting structured *frames* from historical source passages about ONE topic:
**the physical cause of the ocean tides**. Do NOT reason about who is right. Extract only
what each author asserts, grounded in their own words.

## Input
Read every file `sources/tides/*.txt`. Each file is one author's passage (the first comment
lines give provenance; ignore them as content).

## Task
This is an OPEN pass: invent whatever *variables* (attributes of the topic) best capture the
claims. For each author, output the claims they make about the tides as (variable, value, quote)
triples, where:
- `variable` is a short snake_case attribute name of your choosing (e.g. `primary_cause`);
- `value` is a short snake_case token (e.g. `moon`, `earth_motion`, `attraction`);
- `quote` is the exact sentence fragment from that author's passage that licenses the claim.
Only assert a variable for an author when their text actually supports it. Silence is fine —
omit variables an author does not address.

Also output, in `proposed_variables`, the union of variable names you used with a one-line gloss
and the set of values you assigned to each — this is a *candidate* schema, not final.

## Output
Return ONLY a JSON object, no prose, of the form:
{
  "authors": {
    "pliny":   {"claims": [{"variable": "...", "value": "...", "quote": "..."}, ...]},
    "bede":    {...}, "kepler": {...}, "galileo": {...},
    "descartes": {...}, "newton": {...}, "laplace": {...}
  },
  "proposed_variables": {
    "<variable>": {"gloss": "...", "values_seen": ["...", ...]}, ...
  }
}
Use exactly these seven author keys: pliny, bede, kepler, galileo, descartes, newton, laplace.
