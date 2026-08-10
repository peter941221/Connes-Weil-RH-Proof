# 963 - One shared wall: consolidated closed/open ledger for the route

Date: 2026-08-10.  Status: synthesis of docs/942-962 + source reads (definitions
read, no new theorem).  The many distinct "walls" discussed this week collapse to
ONE shared operator<->scalar seam.  RH NOT claimed.

## The single seam

Across Wall-A 1.4, Gate-3U/Proof-717, and the C1 finite-vanishing criterion, the
actual blocker is the SAME operator<->scalar Hilbert seam on the healthy carrier:

    (scalar/adelic side)  =  (trace of a PSD-operator), or the sign of that

Everything else in the route is either closed or is a Lean-assembly leaf.

## Closed (axiom-clean, docs/942)

- CompactLog/A3 finite-S SIGN (the nonnegative producer):
  detector_diagonal_re_nonneg, detector_isPositive, healthy_strict_positive_diagonal,
  weilStateNonempty, concreteC1InputData  (all [propext, Classical.choice, Quot.sound], 0 sorry)
- Gamma/archimedean bounded sign: Re[Gamma(1+i/2)^4] >= 0 (docs/888, 940, 941,
  PhaseGateSandwich, SSeriesSandwich)
- Wall-A 1.4 structural LHS-zero: ScabLhsZero (poleFunctional f*f - polePairing f = 0), axiom-clean
- finite-band Route-A Gate (bandTerminalGate), axiom-clean

## OPEN (the real analytic bottom, NOT a Lean-assembly leaf)

1. The RH-equivalent source criterion (C1 -> SourceRH), i.e. proving
   CC20FiniteVanishingWeilCriterion is TRUE on a well-behaved carrier:

       forall g, compactSmooth g -> vanishes[0,1/2,1] g -> weilLocalSum(star g) <= 0

   By the Weil explicit formula this is exactly "all nontrivial zeros on the
   line".  It is NOT provable as an assembly; it is RH itself.
2. Wall-A 1.4 analytic half: 2*arch(f*f) + (globalSum - restrictedSum) = 0
   (arch = Eq.3.7 real term).  Numerically +0.588 residual; the finite side is
   either ~0 (log conv) or divergent (valueAt conv).  Needs the real explicit
   formula match (the same -> same seam).
3. Gate-3U infinite carrier + Burnol.

## Honest decompositions (so no new session re-derives this)

- Criterion is RH-equivalent, so only the RH-direction (C1 => RH) is a Lean theorem;
  the C1 <= RH-reduction is not yet established.
- A healthy CC20TestSpace with weil= -PSD is a VACUOUS choice (guard .6: "True/univ
  producer"); a correct closure needs the scalar<->operator bridge as a THEOREM.
- numerical proxies on this wall are evidence only (mind the docs/8xx-prefixed probes)
  cond - do not overturn a Lean-verified identity.

## Recommended next (any will be the same wall; pick a nonzero-fake one)

1. For C1: produce CERTIFIED finite-window numeric construction (single test or a
   small family), computable, falsifiable, non-RH. Not a theorem claim.
2. For Wall-A/Gate: resolve whether the shared operator<->scalar identity is a
   genuinely-new artifact vs an already-known gamma/arch bound (see 942 boundary).
3. Invest in the RH-equivalent criterion ONLY when a new analytic idea exists.
