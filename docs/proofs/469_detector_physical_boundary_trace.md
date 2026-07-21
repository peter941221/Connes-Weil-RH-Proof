# Proof 469: Detector physical-boundary trace

## Result

Proof 468 gives one physical Hilbert--Schmidt pair for every displacement
atom.  Proof 469 cycles that pair from the global logarithmic carrier onto its
actual target carrier.  If `L` and `R` are the two legs of the complete
`sourceThreeBranchPairData`, then the transported pair has boundary cycle

```text
-R U_(-z) B L^dagger.
```

The repeated band projection disappears only through its proved
self-adjointness and idempotence.  Genuine Hilbert--Schmidt cyclicity gives

```text
Tr_global(B[W,P]U_(-z)B)
  = Tr_boundary(-R U_(-z) B L^dagger).
```

The right side is also exposed as one signed diagonal `tsum` along the named
boundary basis.  The two legs `L,R` still contain the complete outer,
reflected second-support, and prolate ledger; no component has been estimated
separately and no absolute value has been taken.

## Boundary

This is an exact trace formula on the physical factor carrier, not yet a
closed integral kernel formula.  It does not prove compact-support tail
vanishing, trace/renewal-`tsum` exchange, the uniform Gate 3U bound, the
finite-S sign, Burnol's identity, or `_root_.RiemannHypothesis`.  The next
producer must unfold the complete `L/R` boundary kernel far enough to apply
compact root support while retaining the signed three-branch combination.
