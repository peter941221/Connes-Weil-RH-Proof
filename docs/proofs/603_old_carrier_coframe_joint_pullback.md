# Proof 603: old-carrier coframe joint pullback

## Result

The complete signed old-carrier telescope now has an exact scalar-normalized
pullback. Define the synchronized boundary-moment gap

```text
G_(p,S)
  = Z_S * T_(p,S)^dagger
    - T_(p,S)^dagger * Z_(p::S),
```

where `Z_S` is the complete raw coframe boundary moment. Lean proves

```text
signedTelescope_(p,S)
  = G_(p,S) * oldFrame_(p,S)^dagger
```

and, with the true scalar-normalized inverse `V_p`,

```text
signedTelescope_(p,S) * V_p^dagger * newFrame_(p,S)
  = rho_p^(-1) * G_(p,S) * reverseTransition_(p,S)^dagger.
```

The scalar `rho_p` is retained explicitly. No individual row is declared to
annihilate the new-frame range, and no transition skew is discarded.

## Why this matters

The generic range-factorization route would require the left side to vanish.
The new identity shows that this is equivalent to a genuine synchronized
moment covariance statement for `G_(p,S)`, not a projection-compression fact.
Thus the remaining source theorem must control the complete gap, or provide a
joint ambient/boundary decomposition before taking norms.

The existing three-row divide-and-conquer adapter remains valid, but this
pullback is the correct source-facing object for a joint producer.

## Lean owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullback.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierCoframeJointPullbackAudit.lean
```

The focused owner build passed with `3365` jobs. The import-facing audit is
the next verification target. The new owner contains no `sorry`, `admit`, or
user axiom; its audit must use only
`[propext, Classical.choice, Quot.sound]`.

## Boundary

This closes the exact joint pullback ledger, not the family-uniform quotient.
The remaining Bone 1 producer is still a uniform factorization of the full
signed telescope through the two-channel old-carrier analysis.
