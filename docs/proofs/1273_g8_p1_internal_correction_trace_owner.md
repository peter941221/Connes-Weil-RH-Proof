# G8 P1 — internal-correction trace owner

Date: 2026-09-10

Consumer: the healthy-`CompactLog`, selected-detector, same-owner B5/P2
readback `G8SameOwnerReadbackData`.

For the literal G8 cutoff leg `A_n`, write `C_n = J† A_n` and let
`K_forward` be the existing physical-endpoint internal correction.  This
brick constructs the concrete source-basis Hilbert--Schmidt pair with legs
`C_n` and `K_forward C_n`.  Its trace product is exactly

```text
C_n† K_forward C_n,
```

and is trace class on the same named healthy source owner.  The correction
therefore remains inside the finite-cutoff kernel in the forthcoming scalar
P0 trace ledger; it is not an externally chosen renormalizing scalar.

Combined with records 1271 and 1272, every term in the formal P0 identity
has a concrete trace owner.  This gives no finite visible-prime identity,
no channel limit or sign, and no `qw` conclusion.

Evidence: `ConnesWeilRH.Dev.C1G8AdjointShearGram` and its paired Audit module
completed in `build-logs/1273_g8_p1_internal_correction_pair_retry.log`
(3922 jobs, zero `error:` and `sorryAx`; only
`[propext, Classical.choice, Quot.sound]`).

Next: derive the exact ordinary-trace form of P0, retaining the literal
cutoff, owner, scale, and finite family in every summand.
