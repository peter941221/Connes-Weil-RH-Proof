# Proof 681: finite-S endpoint alignment for the radial owner

The new module
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerFiniteSEndpointAlignment.lean`
proves that the `alpha = 1` parameterized Fourier-support projection and
prolate remainder in the signed radial owner are exactly the
`targetFourierSupportProjection` and `targetProlateRemainder` selected by the
same `FinitePrimePowerFamily`.

The resulting readback is

```text
radialSignedPhysicalOwner p family.visiblePrimes
  = -cc20ThreeBranchCommutator E Q_S K_S W_p
    + radialSoninBoundaryCrossing p family.visiblePrimes.
```

This removes a parameterization/carrier mismatch only.  It does not construct
the common Hilbert--Schmidt root, prove its route-uniform energy, bound a left
factor, close Gate 3U, prove the finite-S sign, or imply RH.

Verification is performed in the Ubuntu-24.04 WSL2 mirror with the shared Lake
lock:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerFiniteSEndpointAlignment

flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Dev.CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerFiniteSEndpointAlignmentAudit
```
