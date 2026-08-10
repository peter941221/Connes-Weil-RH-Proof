# 962 - Option-2 (healthy CC20TestSpace): exact seam, and the honest resistance

Date: 2026-08-10.  Status: design/audit (no Lean yet).  RH not claimed.
Sequel to docs/960.  The healthy `CC20TestSpace C` would make
`CC20FiniteVanishingWeilCriterion C` a theorem.

## What `CC20TestSpace` needs

    structure CC20TestSpace where
      Test : Type
      toRouteTest : Test -> TestFunction
      mellinAt : Test -> C -> C
      starConvolution : Test -> Test
      weilLocalSum : Test -> R
      compactSupportSmooth : Test -> Prop

and the criterion is `forall g, compactSmooth g -> vanishing(g) -> weilLocalSum(starConvolution g) <= 0`.

## Honest healthy-candidate design and its resistance

The closed A3 positive content is a PSD operator on `cc20GlobalLogCrossingL2`:
`detector_diagonal_re_nonneg`: for all u, 0 <= Re<u, detector u>  (detector = F2^0 F).
So define on the healthy crossing space

    weilLocalSum(h) := - Re<h, detector- h>

Then for ANY h (hence for `h = starConvolution g`) the target `<= 0` follows
immediately.  So the Criterion is satisfyable IF this `weil` is the route's real
positive sign and IF `Test`, `mellinAt`, `starConvolution`, `toRouteTest` are the
honest route operations on the healthy space.

## The resistance: why just picking `weil := -detector` is NOT allowed by the guards

AGENTS.6 forbids "True/univ producer fields or stored conclusions" and states a
weak theorem built by choosing the definition to make it true does not remove a
real dependency.

`weil= -Re<h,Dh>` makes the criterion hold for ALL h (no vanishing ever used).  That
is *vacuous* unless the equality

    weilLocalSum(starConvolution g)  =  - Re<g, F g>   for the ROUTE's weil/operator

is established as a THEOREM (not chosen by fiat).  That equality is exactly the
arch/hilbert bridge: it identifies the scalar arch-pole/Manle-side `weilLocalSum`
with the A3 PSD operator quadratic form.  It is a genuine analytic-identity, the
same qualitative wall as Wall-A 1.4 / the Arch half.

- If Option-2 just sets `weil := -detector` and declares the criterion, it is a
  fake (guard .6).  It would let `CC20 -> SourceRH -> RiemannHypothesis` discharge
  on an as-yet-unjustified identification of the scalar and operator carrier - a
  violation.
- The honest version of option2 = construct the fields + prove the Weil-detector
  identity as a THEOREM.  The PSD side exists (A3/A24 seam `operatorGate_detector`),
  but the left-hand scalar `weilLocalSum` is only concretely defined on the
  normalized additive model (`= -polePairing`), NOT on the healthy operator.

## Consequence

Option 2 is NOT a cheap "build a space and it works".  The real leap is the
**scalar <-> operator Hilbert bridge on the healthy carrier** (weilLocalSum = -Re-cond-
detector).  Until that identity is a Lean theorem, a healthy `CC20TestSpace` either
is not instantiable (no weil on the carrier) or is instantiated vacuously (guard).

Recommended: (i) try to prove the scalar-operator bridge as a fresh module (real
analytic / trace-class content), or (ii) postpone C1 and revisit the shared finite-
band/anal [Gate-3U.-/Burnol] since both walls are the same operator<->scalar seam.
