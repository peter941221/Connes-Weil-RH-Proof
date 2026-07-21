# Proof 445: Moving-band endpoint integral

Date: 2026-07-20

## Result

The root-smoothed moving Sonin band now has an explicit endpoint-integral
owner.  For the finite-S list selected by the same arithmetic family,

```text
integral_0^1 actualMovingSoninRootFlow(alpha) d alpha
  = - rootSandwichedBandResponse.
```

The source file is:

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSMovingBandEndpointIntegral.lean
```

The focused audit is:

```text
ConnesWeilRH/Dev/
  CCM24FiniteSMovingBandEndpointIntegralAudit.lean
```

## Pointwise branch deletion

At every synchronized time `alpha` with `|alpha| <= 1`, the existing radial
invariance theorem gives

```text
completedMovingCrossing(alpha)
  = - projectionLeftCrossing(P_alpha, generator_alpha).
```

After the selected root sandwich, the Hermitian moving flow is therefore

```text
actualMovingSoninRootFlow(alpha)
  = - completedRootCrossing(alpha)
    - completedRootCrossing(alpha)^*.
```

This equality is proved before integration.  The outer radial crossing is not
estimated separately and is not reintroduced as a primewise norm term.

## Endpoint theorem

The endpoint theorem applies Mathlib's Banach-space interval fundamental
theorem to the operator-valued map

```text
alpha |-> actualRootSandwichedSoninBand owner lambda alpha family.visiblePrimes.
```

Its derivative is the negative complete moving flow, using the existing
operator-norm derivative theorem.  The only explicit analytic input is

```text
IntervalIntegrable
  (fun alpha => actualMovingSoninRootFlow owner lambda alpha
    family.visiblePrimes)
  volume 0 1.
```

This is a regularity obligation for the synchronized flow.  It is not a
positivity, trace, Gate 3U, or RH premise, and no conclusion about the missing
uniform bound is claimed here.

## Route impact

The active endpoint chain is now:

```text
actual finite-S band response
  -> endpoint integral of the complete moving flow
  -> pointwise radial crossing deletion
  -> one synchronized Sonin crossing plus adjoint
  -> signed Gate 3U estimate.
```

The remaining producer must still prove the interval-integrability witness and
bound the integrated signed crossing uniformly in the canonical family.  The
finite-S sign, negative-owner integration, Burnol identity, and RH remain
open.

## Axiom and build target

The focused audit checks all three new declarations.  The expected audited
axioms are exactly:

```text
[propext, Classical.choice, Quot.sound]
```
