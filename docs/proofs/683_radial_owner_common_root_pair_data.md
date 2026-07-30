# Proof 683: common-root pair-data contract for the radial owner

The new module
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerCommonRootPairData.lean`
adds `RadialSignedPhysicalOwnerPairData`.  It requires two actual
Hilbert--Schmidt pair owners on the same finite-S source basis:

```text
threeBranchData.traceProduct = cc20ThreeBranchCommutator E Q_S K_S W_p
boundaryData.traceProduct    = radialSoninBoundaryCrossing p S.
```

The signed pair is their orthogonal `WithLp 2` sum, with the minus sign kept in
the first right leg.  Proof 681 then gives the exact owner readback

```text
signedPairData.traceProduct = radialSignedPhysicalOwner p S.
```

After supplying a target Hilbert basis and bounded left/right maps, the module
constructs a `RadialSignedOwnerRootS2Producer` using the existing common-root
constructor and proves its response equality.  The radial boundary pair is an
explicit source premise: the existing compact detector crossing cannot be
substituted for the bare positive-translation channel.  The inherited Julia
row is bookkeeping only, so this does not close Gate 3U or prove the finite-S
sign or RH.
