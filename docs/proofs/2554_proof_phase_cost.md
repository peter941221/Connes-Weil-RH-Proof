Record 2554: cumulative proof costs on a complete production node

The node5440,sigma+1/2 input from record2553 is checked in three cumulative
forms: exact paired exponential replay; replay plus actual function error;
and the complete third-derivative transfer. All variants keep the same
thirty sets of rational definitions and imports. Only theorem bodies differ.

Generate with scripts/generate_proof_cost_2554.py. Run
scripts/run_proof_cost_2554.sh under one heavy resource lease in the Linux
verification environment; LEAN_LAKE selects lake if necessary. The runner
loads the matched baseline first and invokes lake env lean directly for
each variant. Validate with scripts/validate_proof_cost_2554.py --mirror PATH.
The environment has 16 logical CPUs; user time sums CPU work across threads.

```text
+----------------------+----------+----------+-------------+
| Cumulative scope     | Wall (s) | User (s) | RSS (KiB)   |
+----------------------+----------+----------+-------------+
| Exact state replay   |    30.17 |    72.27 |     5751700 |
| Actual function      |    32.09 |    93.15 |     6017220 |
| Actual third deriv.  |    34.76 |   141.73 |     6311020 |
+----------------------+----------+----------+-------------+
```

The CPU differences are 20.88 s for the function connection and 48.58 s
for the derivative connection. These differences are routing evidence,
not isolated tactic timings: definitions and imports remain in every run,
and scheduling changes elapsed time. Exact replay alone is already costly;
optimizing only symbolic derivative normalization would leave that cost.
The next cheap decision is to compare cbv with the existing kernel-only
decide strategy on unchanged inputs, before designing a new evaluator.

All ninety terminal declarations have exactly propext, Classical.choice
and Quot.sound. The pure rational equalities also carry these standard
axioms through the current cbv proof mechanism; being a rational statement
does not imply an empty axiom list. Independent arithmetic checks the
actual generated payload, and regeneration and mirror source/configuration
identity pass. Evidence: results/2554_proof_cost_readback.json.

The first readback attempt incorrectly required the pure replay source to
contain an analytic sigma expression. That source deliberately omits the
analytic theorem; its sigma is instead checked through the independently
derived exact input and derivative factor. The reader was corrected at
that interface and rerun. No payload or Lean proof changed.

These phase measurements add no whole-cell, full-grid, coefficient-owner
membership or RH claim.
