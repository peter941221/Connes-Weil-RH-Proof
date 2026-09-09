# 1240 - G7 owner-compression no-go

Date: 2026-09-09.

Status: `FORMAL-STRUCTURAL`; closes the G7 candidate from record
[`1239`](1239_nm_square_zero_shear_gram_completion.md).  Consumer: the
healthy-`CompactLog`, selected-detector, same-owner B5 gate.

The formal oblique-shear owner supplies a source projection `R`, source
inclusion `J`, and square-zero shear `N_S` with

```text
N_S R = 0,   R J = J.
```

Hence `N_S J = 0`.  For any detector operator `W_g`, the proposed positive
Gram completion satisfies the exact same-owner identity

```text
J^* (I + N_S)^* W_g (I + N_S) J = J^* W_g J.
```

So the construction contains no finite-S shear response after compression to
the owner on which the selected detector and `qw` are defined.  Keeping the
ambient trace instead changes the owner and does not repair the route.

This is a symbolic consequence of existing Lean identities in
`CCM24FiniteSGatePhysicalObliqueShearReduction`; no numerical evidence and no
new interface are involved.  G7 is therefore closed as a no-go, and the next
candidate must change the operator placement or provide a new owner-level
factorization before any implementation is justified.

RH is not claimed.
