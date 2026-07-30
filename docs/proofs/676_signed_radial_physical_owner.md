# Proof 676: signed radial physical owner

Proof 676 recombines the exact interior and boundary channels from Proofs 673
through 675.

For

```text
E   = radialSupportProjection unitSoninScale
Q_S = parameterizedFourierSupportProjection unitSoninScale 1 S
K_S = parameterizedProlateRemainder unitSoninScale 1 S
W_p = radialCompressedPositiveTranslation p
```

the complete owner is defined as

```text
radialSignedPhysicalOwner(p,S)
  = -cc20ThreeBranchCommutator E Q_S K_S W_p
    + radialSoninBoundaryCrossing p S.
```

The exact source identity is

```text
suffixPrimeTranslationProjectionCommutator p S
  = radialSignedPhysicalOwner p S.
```

The boundary term remains in the owner with its original orientation. No
triangle inequality, branchwise estimate, positivity claim, or Gate 3U sign
is asserted.

The focused audit is axiom-clean with the repository baseline
`[propext, Classical.choice, Quot.sound]`; the finite-S sign, Burnol's
identity, and `_root_.RiemannHypothesis` remain open.
