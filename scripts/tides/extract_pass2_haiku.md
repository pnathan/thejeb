# Tides corpus — extraction pass 2 (Claude Haiku, schema-constrained)

You re-extract each author's frame against a FIXED canonical schema, so that all seven frames
live in the same variable/value vocabulary.

## Inputs
- The canonical schema: `sources/tides/extraction/schema.json` (a list of variables, each with a
  closed `domain` of allowed values, plus a `synonyms` map).
- The passages: `sources/tides/*.txt` (one author each).

## Task
For each of the seven authors (pliny, bede, kepler, galileo, descartes, newton, laplace) and each
canonical variable, decide the author's value:
- if the passage supports one of the domain values, output that value plus the licensing `quote`;
- if the author does not address that variable, output the literal string `"silent"` and omit the
  quote.
Use ONLY values from that variable's `domain` (or `"silent"`). Do not invent values. When the
passage's wording differs from a domain token, map it via the schema's `synonyms`.

## Output
Return ONLY a JSON object:
{
  "schema_version": "<copy the schema's variable-name list, comma-joined>",
  "frames": {
    "pliny":   {"<var>": {"value": "<domain value | silent>", "quote": "<... | omit if silent>"}, ...},
    "bede": {...}, "kepler": {...}, "galileo": {...},
    "descartes": {...}, "newton": {...}, "laplace": {...}
  }
}
Every author must have an entry for every canonical variable.
