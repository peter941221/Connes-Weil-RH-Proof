# Proof 682: root-sandwich endpoint alignment

The new module
`CCM24FiniteSCompletedJuliaRawPhysicalOldCarrierAntiresonantInteriorFrameLossRadialPhysicalOwnerRootSandwichFiniteSEndpointAlignment.lean`
rewrites a `RadialSignedOwnerRootS2Producer` response at the finite-S endpoint.
It requires the explicit producer-side equality
`producer.S = family.visiblePrimes`, then uses Proof 681 to obtain

```text
base.response
  = leftSandwich * (-cc20ThreeBranchCommutator E Q_S K_S W_p)
      * rightSandwich
    + leftSandwich * radialSoninBoundaryCrossing p S * rightSandwich.
```

The three-branch term and the radial boundary term remain in one signed
same-domain owner.  This is only an endpoint/carrier readback: it does not
construct the common Hilbert--Schmidt root, prove the missing boundary
factorization, establish a route-uniform Gate 3U estimate, or imply the finite-S
sign or RH.
