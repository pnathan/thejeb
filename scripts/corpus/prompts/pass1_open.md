# Corpus extraction — pass 1 (open extraction, per chunk)

You are extracting structured *frames* from source documents about ONE topic:
**{TOPIC}**. Do NOT judge who is right. Extract only what THIS text asserts about
the topic, grounded in its own words.

## Input
Below is ONE chunk (a portion) of a single document. It may not contain claims
about every aspect of the topic — that is fine.

## Task
This is an OPEN pass: invent whatever *variables* (attributes / relations of the
topic) best capture the claims actually made in this chunk. For each claim output
a `(variable, value, quote)` triple, where:
- `variable` is a short snake_case attribute name (e.g. `primary_mechanism`);
- `value` is a short snake_case token (e.g. `strong_union`, `rejected`);
- `quote` is the exact sentence fragment from this chunk that licenses the claim.
Only assert a variable when the text actually supports it. Silence is fine — omit
what this chunk does not address. Do not repeat near-duplicate claims.

## Output
Return ONLY a JSON object, no prose, no code fences:
{
  "claims": [
    {"variable": "...", "value": "...", "quote": "..."},
    ...
  ]
}
If the chunk makes no substantive claim about the topic, return {"claims": []}.
