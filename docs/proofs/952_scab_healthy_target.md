# 952 - healthy SCB reduced to a named scalar pole/arch target

Date: 2026-08-10.  Status: data-bearing wiring + pure-ring reduction (WSL-verified),
NOT a proof of the analytic identity.  RH NOT claimed.

## What

New file ConnesWeilRH/Dev/ScabHealthyTarget.lean pins the lane-A load-bearing
balance SourceScopedArchimedeanContributionBalance (SCB, the restricted=global
arch balance) on the healthy carrier into one named, data-bearing scalar target:

    ScabPoleArchTarget healthySymbols f a b :
        poleFunctional(convolutionStar f) - polePairing(f)
          = 2*archimedeanTerm(convolutionStar f) + (a - b)

The arch read-off is pinned to the real CCM25 Eq.3.7 value via
HealthyArchData.healthyArchData f (this is the sourceArchimedeanTerm read-off);
scb_iff_arch_target is the pure-ring equivalence SCB iff target.

## Why

The un-differentiated SCB is false on the concrete carrier (archimedeanTerm=0,
L657DiagProbe.probe_balance_false).  The healthy carrier is the only living
object.  Pinning the exact scalar equality a proof must show gives Wall-A 1.4
a single, unambiguous Lean target rather than a bundle of sub-identities.

## Verification

- Build: lake build ConnesWeilRH.Dev.ScabHealthyTarget : 2959 jobs green (28s).
- print axioms healthyArch_readOff / scb_iff_arch_target =
  [propext, Classical.choice, Quot.sound]; 0 sorry, 0 new project axiom.
- Vendor "local changes" warnings = AGENTS 8b red herring (mathlib scripts/ only).

## Honest bottom

The scalar identity itself (pole/pole + 2*arch + (global - restricted)) is the
Weil-explicit-formula content and is NOT proved here; it needs the real analytic
argument (Stirling/Gamma-zeros/vonMangoldt sums on the healthy carrier).  RH NOT claimed.

See also: docs/947 (walls), docs/950, docs/951 (ScabNormalForm).
