853 - Mellin half-density law lifted onto the Hilbert carrier (merge done, gate-carrier bridge still open)

Date: 2026-08-08. Status: Dev probe; build + axiom verified, no RH claim.
Builds on 850/851/852: the additive M(g*g)=2Mg obstruction is a carrier artifact; the
faithful multiplicative Mellin law already lives axiom-clean in MellinConvolutionIdentity /
MellinProductCarrier. This round performs the 852 merge explicitly.

## What was built (Dev, verified)

- New ConnesWeilRH/Dev/MellinHilbertCarrierMerge.lean: the faithful half-density Mellin law
  stated on the Hilbert log carrier cc20GlobalLogCrossingL2 = L2(R,C) (the carrier that
  already owns the Lp/HS/positive-trace structure), reading each element through its R -> C
  coeFn representation.
- mellinLawPremise = the integrability witness for logWeight, a terminating Prop, not an axiom.
- mellinHalfDensityStatement = the law together with the two witnesses, as a real Prop.
- mellinHalfDensityProven closes it by one-line MellinProductCarrier.mellinConvolutionProductLaw.

## Evidence (build + axioms)

- lake build on the module: 2955 jobs complete, succeeded.
- #print axioms of mellinHalfDensityProven = [propext, Classical.choice, Quot.sound], no sorryAx.
- Probe built in the existing dirty WSL mirror (leaf-level); per SS5/SS8 not a clean final acceptance.

## What closes / what remains

Closes: the half-density Mellin convention now has a real axiom-clean instance on the carrier
that owns the Hilbert/positive-trace structure, the 852 merge target. This is the seam
TraceScale.NormalizedScalarTraceScaleSymbols.mellinHalfDensityMatched := True had to fake.

Remains open (honest):
 (a) the nonzero-HS-gate witness and positiveTrace/gate wiring still live on the CompactLogTest
     carrier (A3/C1/C2), which is a different type from cc20GlobalLogCrossingL2; bridging the
     two is the named 852 ae/measure bridge.
 (b) full CC20Interface / RouteInputs rewiring and normalization conventions remain skeleton-level.

No RH claimed. AGENTS section 2 (Proof-717) remains the committed analytic bottom.
