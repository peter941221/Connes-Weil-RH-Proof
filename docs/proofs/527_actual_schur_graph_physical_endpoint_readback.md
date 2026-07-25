# Proof 527: graph physical endpoint readback

## Result

Proof 526 gives an ambient graph-cascade residual.  Proof 527 pushes that
residual through the actual source inclusion and source band projection:

    graphPhysicalCoframe(S)
      = actualSchurForwardCoframe(S) + graphResidualCoframe(S).

After adding the existing metric coframe, it defines a graph physical
endpoint and proves

    physicalEndpoint
      = graphPhysicalEndpoint + graphEndpointResidual.

The endpoint residual is exactly the signed difference

    graphEndpointResidual
      = physicalInverseResidual - graphResidualCoframe.

This is the first endpoint-level assembly of the new graph cascade with the
existing physical endpoint.  It does not identify the result with the
post-Q mismatch, provide a family-uniform bound, prove Gate 3U, prove the
finite-S sign, supply Burnol's identity, or prove RH.

## Lean owners

    ConnesWeilRH/Source/CCM25Concrete/
      CCM24FiniteSActualSchurGraphPhysicalEndpointReadback.lean
    ConnesWeilRH/Dev/
      CCM24FiniteSActualSchurGraphPhysicalEndpointReadbackAudit.lean
