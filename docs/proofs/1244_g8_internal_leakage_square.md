# Proof 1244 — G8 internal leakage-square channel

Status: FORMAL-ALGEBRA (Lean), 2026-09-10.

The fourth term in the G8 source compression is now reduced exactly to the
physical leakage square.  Writing `J` for the source inclusion,
`L_S` for `sourcePhysicalCoframeLeakage`, and `W_g` for the selected detector,
the theorem proves

```text
J† (J L_S†) W_g (L_S J†) J = L_S† W_g L_S.
```

The proof uses only the already-owned factorization
`N_S = J L_S†`, the adjoint-of-composition identity, and
`J†J = I`.  It does not use cyclic trace rearrangement, a limit, or a
numerical estimate.  Thus the fourth G8 channel is genuinely internal and
has the intended positive Gram form; it is not an external subtraction.

Audit evidence: `/home/peter/rh/build-logs/1244_g8_leakage_final.log`.
The owning module and paired audit build successfully (3921 jobs); the audit
prints standard axioms only for both the identity and its positivity theorem,
with no `sorryAx` or new axiom.

The remaining G8 gap is quantitative: trace/readback data for the baseline,
the two cross channels, and this leakage square must still be assembled on
one finite-visible-prime owner and shown to converge to `qw`.
