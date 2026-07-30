# Proof 677: radial physical-owner compression

Proof 677 makes the carrier boundary explicit. With

```text
E = radialSupportProjection unitSoninScale
F = radialComplement unitSoninScale = I - E
```

the source proves the exact orthogonal identity

```text
E F = 0.
```

Since the radial boundary channel is `F U_p P_S`, it follows that

```text
E (radialSoninBoundaryCrossing p S) = 0.
```

Therefore the left-compressed signed owner reads back as

```text
E (radialSignedPhysicalOwner p S)
  = E (-cc20ThreeBranchCommutator E Q_S K_S W_p).
```

This is only a carrier-compression identity. The uncompressed owner still
contains the boundary channel, and no norm, positivity, trace, Gate 3U, or
finite-S sign statement is made.
