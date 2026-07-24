# Tides corpus — schema unification (Claude Sonnet)

You are given the pass-1 open extraction over seven authors discussing the cause of the ocean
tides (file `sources/tides/extraction/pass1.json`). Different authors' frames used overlapping
but inconsistent variable and value names. Produce ONE canonical schema.

## Task
1. Merge synonymous variables into a single canonical variable (snake_case). Keep the schema
   small and meaningful — prefer ~6-9 variables that capture the substantive relations of the
   topic (e.g. primary cause, the moon's role, the sun's role, the mechanism, whether the
   author's theory requires the Earth to move, the spring/neap dependence, whether it is
   quantitative).
2. For each canonical variable, give a closed `domain` of snake_case values (the union of the
   distinct positions seen across authors, normalized). Do NOT include a "silent" token in the
   domain — silence is handled downstream by omission.
3. Provide a `synonyms` map from every pass-1 (variable,value) name to the canonical
   (variable,value) it maps to, so pass 3 can normalize deterministically.

Keep domains tight: two theories that are the same position must map to the same value; genuinely
different positions must stay distinct (this is what makes the disagreement measurable).

## Output
Return ONLY a JSON object:
{
  "variables": [
    {"name": "<canonical>", "domain": ["<v1>", "<v2>", ...], "description": "..."},
    ...
  ],
  "synonyms": {
    "variable": {"<pass1_var>": "<canonical_var>", ...},
    "value":    {"<pass1_var>::<pass1_val>": "<canonical_var>::<canonical_val>", ...}
  }
}
