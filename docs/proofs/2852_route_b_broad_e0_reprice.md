# 2852 Route B broad-e0 reprice

This record regenerates the cell-4096 order-7 recurrence stages using the
Lean-proved initial box `[1/32,1/4]`. It stores exp, denominator, reciprocal,
and transition boxes and reports each transition width against the old Python
tight target.

The artifact is the input for a subsequent Lean arithmetic replay and charge
comparison. It is not itself a Lean certificate or a global ledger result.
