# 2840 Route B stage bridge input

This record exports the complete Python recurrence stages for Route B cell
4096 at orders 4 and 7. Each stage contains exact rationalized binary interval
endpoints for `phase`, `exp`, `denominator`, `reciprocal`, and `transition`.

The artifact is the concrete input for the next Lean rational replay step. It
does not certify that the boxes dominate the Lean interval definitions. That
requires checking the stage boxes against the Lean recurrence in order:

```text
phase -> exp -> denominator -> reciprocal -> transition
```

Source script: `scripts/seed_cell_stage_bridge_2840.py`.
Artifact: `results/2840_route_b_cell4096_stage_bridge.json`.

The existing Python convention control passed 34 checks on this cell, with
worst canonical-versus-legacy endpoint difference about `2.09e-39`; that is a
Python internal control and is not a Lean theorem.

The earlier 2836/2837 JSON artifacts were also normalized from a trailing
literal `\\n` into valid JSON. Both now pass a standard parser, so later bridge
checks can consume them without a format exception.
