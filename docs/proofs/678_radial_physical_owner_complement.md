# Proof 678: complementary radial physical-owner readout

Proof 678 completes the lower-radial side of the carrier ledger from Proof
677. Let

```text
E = radialSupportProjection unitSoninScale
F = radialComplement unitSoninScale = I - E.
```

The source proves

```text
F E = 0,
F radialInteriorSoninCommutator p S = 0,
F radialSoninBoundaryCrossing p S = radialSoninBoundaryCrossing p S,
F radialSignedPhysicalOwner p S = radialSoninBoundaryCrossing p S.
```

Together with Proof 677's upper readout, the signed owner has the exact
two-channel carrier decomposition:

```text
E owner = interior three-branch channel,
F owner = radial boundary channel.
```

This is a carrier identity only. It supplies no norm estimate, trace
interchange, positivity, Gate 3U sign, finite-S sign, Burnol identity, or RH
implication.
