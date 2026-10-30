# 3199 Route A Taylor-6 JSONL Replay

Status: the external 3187 cell sidecar passes exact replay.

The checker `scripts/audit_routea_taylor6_jsonl_3199.py` uses Python
`Fraction` arithmetic to validate the complete sidecar:

```text
40960 rows
    |
    +--> continuous grid and exact radius endpoints
    +--> exact midpoint and step checks
    +--> exact Taylor cell-upper formula replay
    +--> exact sixth-order remainder replay
    +--> exact row-sum equality with the aggregate JSON
    +--> 10^-80 upward-grid checks for 163840 coefficient fields
```

The result is an external numerical replay audit, not a Lean proof. It does
not prove that the rows are upper bounds for the same `correctedPhysical`
owner, and it does not supply the full-line tail needed by the 3191 bridge.

Evidence:

- `results/3199_routea_taylor6_jsonl_audit.json`
- `results/3187_signed_taylor6_interval_40960.jsonl`
- `scripts/audit_routea_taylor6_jsonl_3199.py`
