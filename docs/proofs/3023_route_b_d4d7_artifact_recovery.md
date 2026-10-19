# 3023 Route B D4/D7 artifact recovery

The previous blocker statement that no 8192-cell envelope existed was wrong.
The repository already contains:

```text
results/2730_seed_derivative_bounds.json
results/2804_seed_cell_ledger.json
scripts/seed_derivative_bounds_2730.py
scripts/check_seed_cell_ledger_2804.py
```

Replayed controls:

```text
python scripts/seed_derivative_bounds_2730.py
python scripts/check_seed_cell_ledger_2804.py
```

Observed results:

```text
2730: cells = 8192
2730: D4 upper = 1400.650853119245 < 1500
2730: D7 upper = 592705254.0438685 < 2000000000
2730: first/second order controls pass
2804: row_count, indices, adjacency, aggregate_4, aggregate_7 pass
```

The remaining gap is formal provenance. The artifacts explicitly disclaim
evaluator-to-Lean soundness and do not prove finite integral, SourceRH, or RH.
The next implementation target is therefore an artifact-to-Lean certificate
for the 2730 majorant recurrence and the 2804 aggregate rows.
