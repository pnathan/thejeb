# Corpus extraction — pass 2 (schema unification)

You are given the pass-1 open extraction over many documents discussing ONE
topic: **{TOPIC}**. Different documents used overlapping but inconsistent variable
and value names. Produce ONE canonical schema.

## Input
A JSON list `observed` of the `(variable, value)` pairs seen across the whole
corpus, each with a `count` (how many documents used it) and an `example_quote`.

## Task
1. Merge synonymous variables into a single canonical variable (snake_case). Keep
   the schema small and meaningful — prefer ~6–10 variables that capture the
   substantive, *contestable* relations of the topic (positions on which documents
   could actually agree or disagree).
2. For each canonical variable, give a closed `domain` of snake_case values (the
   union of the distinct positions seen, normalized). Do NOT include a "silent"
   token — silence is handled downstream by omission. Keep domains tight: two
   documents taking the same position must map to the same value; genuinely
   different positions must stay distinct (this is what makes disagreement
   measurable).
3. Provide a `synonyms` map from every observed (variable,value) name to the
   canonical (variable,value) it maps to, so extraction can normalize
   deterministically. Drop vague or non-contestable variables rather than forcing
   them in.

## Output
Return ONLY a JSON object, no prose, no code fences:
{
  "variables": [
    {"name": "<canonical>", "domain": ["<v1>", "<v2>", ...], "description": "..."},
    ...
  ],
  "synonyms": {
    "variable": {"<obs_var>": "<canonical_var>", ...},
    "value":    {"<obs_var>::<obs_val>": "<canonical_var>::<canonical_val>", ...}
  }
}
