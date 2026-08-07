# 861 — Route-A: finite-band Gate 3U closure (axiom-clean)

Status: closed (route-A, finite band). Date: 2026-08-07. Lane: Gate-3U trace bridge.
This is the route-A answer to the docs/860 roadblock: the original infinite-carrier
Gate stays blocked (proofs/860), but on ANY finite Hilbert band of the real route
carrier the Gate readout is proven and axiom-clean.

## What is proven

In `ConnesWeilRH/Dev/RouteATailBandBound.lean`:

    bandTerminalGate {rho : Type*} [Fintype rho] (owner) (lambda)
        (b : HilbertBasis rho (Complex) (sourceSoninCarrier lambda)) (B : Real) :
        canonicalRealGate3UAt owner lambda b
          ((Fintype.card rho : Real) * nor(supportOp(canonicalFamily owner))
           + (Fintype.card rho : Real) * (C0 * exp(-B/4) * (visiblePrimes.map primeTwoSidedQuarterMass).prod))

## How it closes (each step is an exact-library theorem)

| step | lemma |
|---|---|
| finite band is trace-class | `isTraceAlong_finite` (any `[Fintype rho]` diagonal is summable) |
| support piece bound | `finiteBandSupport_le` |
| tail piece bound (operator-norm decay) | `finiteBand_tail_trace_le` -> `norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const_exp` |
| assemble support + tail | `inverseLowerFactorPhysicalRenewalTrace_split_bound` (triangle) |
| feed the Gate | `canonicalRealGate3UAt_of_tailNormBound` |

Axiom audit: `[propext, Classical.choice, Quot.sound]` only. Zero `sorry`/`admit`/`axiom`.

## Honest boundary

This closes the Gate on a finite basis of the finite real carrier. It does NOT close
the original infinite-dimensional (proofs/860 A1/A2) Gate; still-non ratings apply.
RH is not claimed; this is a finite-band route-A milestone.