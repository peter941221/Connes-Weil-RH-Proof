# 3028 Canonical charge containment failure

The global canonical-vs-legacy recurrence control (3027) passes, but direct
comparison of canonical interval charges with the exported 2804 ledger fails
at tiny positive differences:

```text
order 4: excess = 1.45717103669437617717560052923e-39, cell 7890
order 7: excess = 6.68056949459322436528792348834e-33, cell 1360
```

The displayed canonical/exported ratio rounds to `1.0`, but the exact directed
comparison is false. Therefore the 2804 ledger cannot yet be consumed as a
Lean pointwise charge certificate.

Decision: retain the failure. The next repair must add an explicit rounding or
endpoint allowance, recompute its total aggregate cost, and prove that the
D4/D7 margins absorb it. Do not change the gate to a relative tolerance.
