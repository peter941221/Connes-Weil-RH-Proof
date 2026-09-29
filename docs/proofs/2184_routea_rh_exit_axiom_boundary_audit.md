# 2184 — Route A RH-exit axiom-boundary audit

Date: 2026-09-29  
Status: integrity pass; existing unconditional-looking RH skeleton is not a
Route-A producer GO.

## Finding

The repository contains declarations named `unconditional_rh_skeleton` and
`unconditional_rh_contract_skeleton`, but their dependency file
`Dev/UnconditionalSkeleton.lean` still declares project-root axioms, including
the normalized finite-prime source data and the normalized CC20 Proposition-C1
source criterion root. These are not the permitted library trio
`[propext, Classical.choice, Quot.sound]`.

The theorem bodies at the end merely consume those root packages:

```text
unconditional_rh_skeleton
  -> rhDefinitionBridgeToMathlibFromTheorems
  -> cc20FiniteVanishingExitFromTheorems
```

This is therefore not admissible evidence for the Route-A signed physical
kernel GO. It does not instantiate the actual `OrbitG8Geometry`, its exact
visible-prime range, or the signed C3′ margin.

By contrast, the Route-A master exits in `C1PinnedOrbitExit` and
`C1G8MasterExit` are axiom-clean conditional consumers: they retain an
explicit producer hypothesis. The missing producer remains visible and is
not discharged by the skeleton.

## Decision

`UNCONDITIONAL-SKELETON-NOT-ROUTE-A-GO`.

No RH claim is promoted. A final GO still requires the exact selected-owner
signed margin and an axiom audit containing only the allowed library axioms.

