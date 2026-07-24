# Corpus extraction — pass 3 (schema-constrained, per document)

You re-extract ONE document's frame against a FIXED canonical schema, so every
document lives in the same variable/value vocabulary. Topic: **{TOPIC}**.

## Inputs
- The canonical schema (a list of variables, each with a closed `domain` of
  allowed values, plus a `synonyms` map).
- ONE document's full text.

## Task
For each canonical variable, decide THIS document's value:
- if the text supports one of the domain values, output that value plus the
  licensing `quote`;
- if the document does not address that variable, output the literal string
  `"silent"` and omit the quote.
Use ONLY values from that variable's `domain` (or `"silent"`). Do not invent
values. When the wording differs from a domain token, map it via `synonyms`. If a
document makes conflicting statements on one variable, pick the position it most
strongly endorses.

## Output
Return ONLY a JSON object, no prose, no code fences:
{
  "frame": {
    "<variable>": {"value": "<domain value | silent>", "quote": "<... | omit if silent>"},
    ...
  }
}
Include an entry for every canonical variable.
