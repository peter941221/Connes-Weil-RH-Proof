# Proof 679: two-carrier split of the radial physical owner

Proof 679 combines the upper and complementary radial readouts into one
canonical signed normal form. For `E = radialSupportProjection unitSoninScale`
and `F = radialComplement unitSoninScale`, it proves

```text
radialSignedPhysicalOwner p S
  = E (radialSignedPhysicalOwner p S)
    + F (radialSignedPhysicalOwner p S)
```

Using Proofs 677 and 678, the same object reads as

```text
radialSignedPhysicalOwner p S
  = E (-cc20ThreeBranchCommutator E Q_S K_S W_p)
    + radialSoninBoundaryCrossing p S.
```

This keeps the upper physical ledger and the lower boundary channel on the
same finite-S domain. It is an exact algebraic normal form only: no norm,
trace, positivity, Gate 3U sign, finite-S sign, Burnol identity, or RH
implication is asserted.
