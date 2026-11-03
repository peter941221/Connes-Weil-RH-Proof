# Record 3273: Weighted-Original 40960-Cell Sidecar

## Result

The formal Route-A target from record 3238 now has a complete 40960-row
exact-rational sidecar. Each row records the same 40960-cell grid used by the
weighted-original evaluator, the midpoint value upper, the second- and
fourth-derivative uppers, the sixth-derivative envelope, and the Taylor-6 cell
upper.

The replay audit passes with:

```text
cells                  = 40960
formula_rows           = 40960
grid_continuous        = true
formula_replay_exact   = true
aggregate_replay_exact = true
total_upper_negative    = true
minimum_cell           = 16923
```

The aggregate upper is approximately `-1.4151657848627206e-8` and is an
exact rational in the JSON result. The calculation uses the formal weighted
original function, sigma `-1/2`, 192-bit Arb precision, and upward rounding
to the `10^-80` grid.

## Artifacts

```text
results/3238_weighted_original_taylor6_40960.json
results/3238_weighted_original_taylor6_40960.jsonl
results/3273_routea_weighted_original_jsonl_audit.json
scripts/routea_concrete_owner_weighted_original_taylor6_3238.py
scripts/audit_routea_weighted_original_jsonl_3273.py
```

The generator now supports `--cell-output`, so the aggregate total and all
40960 row records are produced by one evaluator run. The audit replays every
row using exact rational arithmetic, checks midpoint and grid continuity,
recomputes both Taylor formulas, verifies every rounded field, and checks the
row sum against the recorded total.

## Formal boundary

This is not yet a Lean proof of the finite aggregate. The JSONL is an
external certificate candidate, not a theorem: Lean does not import it, and
the audit does not prove the midpoint enclosures in the kernel. The remaining
formal obligation is to generate and verify Lean-side per-cell enclosure
proofs for the same weighted-original value upper array, then feed that array
to the existing `3213` aggregate interface.

```text
external 40960-row replay       PASS
             |
             v
Lean per-cell midpoint proofs   OPEN
             |
             v
Lean 40960-cell aggregate       OPEN
```

No full-line tail, B5 readback, `producer_go`, `SourceRH`, or RH claim is made.
