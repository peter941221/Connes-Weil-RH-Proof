# 3266: Route A formal weighted-original family screen

Status
------

Diagnostic only. This record does not provide a Lean certificate, a
full-line tail bound, `producer_go`, `SourceRH`, or RH.

Method
------

The screen uses the concrete owner from record 3204 and the formal weighted
original-function evaluator from record 3238. For each family at cell 17168,
it evaluates the zeroth derivative of the weighted original function and
rounds the complex real-part endpoint outward. It then reports contiguous
blocks and every contiguous family interval with a strictly negative upper
endpoint.

This intentionally does not use record 3244's legacy `jets[0]` path. In that
older evaluator, `jets[0]` was the weighted second derivative. The formal
target here is the weighted original function, implemented by
`original_jets` in `scripts/routea_concrete_owner_weighted_original_taylor6_3238.py`.

Result boundary
---------------

The output is a family-level midpoint screen, not a finite-window integral
certificate. A negative family interval is only a candidate grouping for the
next enclosure step; it does not prove that the complete 40960-cell integral
is negative.

Reproduction
------------

    python scripts/routea_cell17168_original_family_screen_3266.py

Output
------

    results/3266_routea_original_family_screen_17168.json

The same script was also replayed at the strongest formal-object diagnostic
cell reported by record 3238, index 16923, producing
`results/3266_routea_original_family_screen_16923.json`.
