# Record 3205: concrete-owner Taylor-6 JSONL replay

The 3204 concrete-owner JSONL sidecar has an exact rational replay audit.

```text
cells:                 40960
formula rows:          40960
rounded coefficient fields: 163840
grid continuity:       PASS
cell/remainder replay: PASS
aggregate replay:      PASS
total upper negative:  true
```

The checker validates the exact Taylor-6 formula for every row, the complete
window coverage, and every serialized `10^-80` upward-rounded coefficient
upper. This is stronger than a summary JSON because the aggregate is rebuilt
from the individual cell records.

It remains an external diagnostic: Lean has not consumed the rows, the
full-line tail is absent, and no `SourceRH`, RH, or producer GO claim follows.

Evidence: `scripts/audit_routea_concrete_owner_taylor6_jsonl_3205.py`,
`results/3204_concrete_owner_taylor6_40960.jsonl`, and
`results/3205_concrete_owner_taylor6_jsonl_audit.json`.