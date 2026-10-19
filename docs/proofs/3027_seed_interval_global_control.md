# 3027 Global seed interval-jet convention control

The canonical recurrence from `C1SeedIntervalJet2734` was replayed against the
legacy `p3_certified_strip_constants_2720.py` evaluator on all 8192 cells.

Command:

```text
python scripts/seed_interval_jet_global_control_3027.py
```

Result:

```text
status = CONTROL-PASS
cells = 8192
all_contained = true
max normalized deviation < 1.1e-37 across orders 0..7
```

This removes the global convention mismatch risk observed by the one-cell
2734 control. It remains a numerical mpmath interval control and does not
prove the Python evaluator-to-Lean soundness bridge, D4/D7, SourceRH, or RH.
