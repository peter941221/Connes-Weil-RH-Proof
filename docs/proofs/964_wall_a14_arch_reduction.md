# 964 - Wall-A 1.4 collapses to ONE scalar `arch(f*f) = 0`; healthy-carrier SCB is refuted unless arch = 0

Date: 2026-08-10.  Status: algebra-level reduction proven axiom-clean; the arch!=0 side is numeric/evidence only (not a Lean theorem).  RH NOT claimed.

## New in this turn

`ConnesWeilRH/Dev/Wall14ArchReduction.lean` proves the ring-level reduction
(axiom-clean, `[propext, Classical.choice, Quot.sound]`, 0 sorry, WSL-green):

```
wall14_target_iff_arch_zero_of_global_eq_restricted
  (W : WeilFormSymbols) (f : TestFunction) (a b : Real)
  (hsum : a = b)
  (hfunc : W.poleFunctional (W.convolutionStar f f) = W.polePairing f) :
  ScabPoleArchTarget W f a b <-> W.archimedeanTerm (W.convolutionStar f f) = 0
```

and its healthy-carrier composition

```
healthy_scb_arch_zero_of_global_eq_restricted (f) (globalSum restrictedSum)
  (hsum : globalSum = restrictedSum) :
  ScabPoleArchTarget HealthyArchData.healthySymbols f globalSum restrictedSum <-> arch(f*f) = 0
```

where `hfunc` is supplied by `ScabLhsZero.lhs_zero` on the healthy carrier, plus the
formal refutation hinge

```
healthy_target_refuted_of_arch_ne_zero (f) (globalSum restrictedSum)
  (hsum) (harch : Not (arch(f*f) = 0)) :
  Not (ScabPoleArchTarget HealthyArchData.healthySymbols f globalSum restrictedSum)
```

so the whole "Wall-A 1.4 dead/not" decision is pinned on the single scalar
`arch(f*f) != 0`.

## Why this collapses the whole Wall-A 1.4 to one scalar

On the healthy carrier the per-common finite-prime index set is `{2}` (docs/963;
`WellFormHealthyRepoint.healthyPerCommonSupport`), so for `lambda >= sqrt 2`:

    restrictedSum = globalSum   (both are the single term at index 2)

The SCAL/SCB balance (docs/952/956) reduces to

    poleFunctional(f*f) - polePairing(f) = 2*arch(f*f) + (globalSum - restrictedSum)

`ScabLhsZero.lhs_zero` proves the left side is identically 0 (structural).  So,
for `lambda >= sqrt 2` with `globalSum = restrictedSum`, the whole balance is
EXACTLY equivalent to `arch(f*f) = 0`.

## The surviving question is one real scalar

Whether `arch(f*f) = 0` holds on the healthy carrier:

```text
arch(f*f) = (log(4*pi) + eulerMascheroni) * Re((f*f)(0)) + Integral_{y>0} ...
```

- Positive leading coefficient `log(4*pi) + gamma` (both > 0).
- `Re((f*f)(0)) = ||f||^2 >= 0`, strictly > 0 when f != 0 (nonnegativity in the library).
- docs/958 (mpmath 80-dps probe on the route `commonBump` proxy) reads
  `arch = +0.294`, `2*arch = +0.588`.

So the healthy-carrier balance fails: `2*arch + (global-restricted) = +0.588 + 0 != 0`.

## Honest status / 判死 boundary

- CLOSED (proof): Wall-A 1.4 algebraically reduces to `arch(f*f) = 0` on the
  healthy carrier.  The structural half and the global=restricted half are
  proven; the whole target is a single named scalar.
- EVIDENCE (not Lean): `arch(f*f) != 0` on the route common test, by the
  positive explicit-formula coefficient and the docs/958 numeric (+0.294).
- NOT closed in Lean: a theorem `arch(f*f) != 0` requires bounding the real
  Eq.3.7 integral, a genuine analytic bottom (the same operator<->scalar seam as
  docs/963).  Until that Lean proof exists, the "dead" verdict is supported-by-
  evidence, not a confirmed counterexample.

## Recommended next

1. Lean-prove `arch(f*f) != 0` (needs the archimedean-integral sign / a lower
   bound for the Eq.3.7 term against `(log(4*pi)+gamma)*||f||^2`).
2. If that closes, the healthy-carrier SCB is a theorem-refuted route; if it
   fails because arch actually is 0 for some healthy test, find which test.
3. Otherwise keep attacking the same operator<->scalar seam (docs/963) for the
   RH-equivalent C1 criterion.

RH NOT claimed.

## Self-created explicit witness (2026-08-10)

`ConnesWeilRH/Dev/Wall14SelfTestWitness.lean` (axiom-clean, WSL-green) pins the
refutation to a concrete, computable test `witnessTest = unitFourierCoreBumpSchwartz`
(the mathlib `ContDiffBump 0`, smooth/even/compact, `test(0)=1`).  It re-instantions
`healthy_target_refuted_of_arch_ne_zero` at this explicit test, so the dead/not
verdict now hangs on ONE explicit scalar `arch(witnessTest^2) != 0` (leading term
`(log(4*pi)+gamma)*norm^2 > 0`; the integral is the remaining analytic bound).