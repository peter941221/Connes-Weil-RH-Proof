# 2389 — scalar composite consumer

Date: 2026-10-02.

The Lean layer now provides
`correctedPhysical_stripNorm_le_of_nodeUpper_scalar2389`: explicit nodewise
upper bounds plus a scalar upper bound on their composite sum imply the final
`stripNorm` scalar bound with the existing curvature term. This is the direct
consumer shape for the 2385/2386 price ledger; it introduces no stored numeric
conclusion and does not assert the scalar hypothesis.
