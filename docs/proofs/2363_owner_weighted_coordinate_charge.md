# 2363 - Owner-level weighted coordinate charge

日期：2026-10-02。

The weighted coordinate-transfer theorem is now instantiated for the live
`correctedPhysical` owner. Existing `ownerDerivativeBudget2350` bounds the
zeroth and first derivatives, and its nonnegativity is proved directly from
the defining positive sum. On any ordered segment contained in
`[-storedWidth 4², storedWidth 4²]`, the resulting charge is

`exp(|sigma| storedWidth 4²) *
 (|sigma| ownerDerivativeBudget2350 0 +
  ownerDerivativeBudget2350 1) * (x - a)`.

The Lean audit passes. The theorem does not yet establish that every actual
`linspace`/affine node pair lies in one such oriented segment with the desired
endpoint assignment, and it does not certify the numerical accumulation or
trapezoid remainder. Producer GO remains false.

Status: `OWNER_ANALYTIC_BRIDGE_ONLY`.
