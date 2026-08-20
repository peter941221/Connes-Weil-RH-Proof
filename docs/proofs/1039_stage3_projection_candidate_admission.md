# 1039 — Stage-3 projection-square candidate admission spec

Status: **specification / gate definition** (no RH-facing theorem claimed yet).
Date: 2026-08-19. Companion module: `ConnesWeilRH/Dev/C1Stage3ProjectionKernel.lean`.

> **Concrete-g closure achieved (2026-08-19).** Stage 3 is now closed for the first
> concrete vanishing test `narrowArchRoot` via an *alternative, non-circular* route:
> `ConnesWeilRH/Dev/C1Stage3ConcreteProducer.lean` builds a genuine
> `PositiveTracePairLimitFamily` from the independent Lane-R sign proof
> `narrowArchRoot_qw_nonneg`, and the existing consumers extract both
> `0 ≤ qw narrowArchRoot` and spectral nonnegativity of its square (axiom-clean, no
> `sorryAx`). This de-risks but does **not** replace the projection-square analytic
> route below: that general route (Gates 1-4) is still required for arbitrary vanishing
> squares = global spectral nonnegativity. See MEMORY.md change log 2026-08-19.

## What it is

This page fixes the admission gates for the **projection-square candidate** to the
Stage-3 same-owner positive-trace producer, i.e. the construction of a genuine
`PositiveTracePairLimitFamily` (`C1PositiveTraceLimitBridge`) whose trace reads back
to `C1SameOwnerWeil.qw g`.  It is an admission spec: it states exactly what a
candidate must prove before it may be promoted to a producer, and names the exact
existing brick each gate leans on.

## Why this candidate

The three earlier routes are ruled out by closed Lean theorems:

| Route | Killed by | Line |
|-------|-----------|------|
| Plain expanding-window cutoff | `cutoffPositiveBasisData_trace_re_eq_window_length_mul_mass` → trace = window-length × ‖g‖², linear for non-zero g | `C1PositiveTraceCutoffGrowth.lean:388` |
| Dominated-diagonal witness | `not_nonempty_cutoffDominatedTraceWitness_of_test_ne_zero` | `C1PositiveTraceCutoffGrowth.lean:434` |
| Mellin-conjugated detector | bulk slope + wrong `m=2` coefficient (kill-test 1036) | `docs/proofs/1036_...md` |

The projection square keeps positivity for free (`A†A ≥ 0`) and reuses a concrete
positivity brick that is **not** in the frozen route list.

## The candidate kernel (already landed in active namespace)

```text
K_S = P_radial · P_semilocal(S) · P_radial − Gram_Sonin     on cc20GlobalLogCrossingL2
      ^^^^^ positive:  concreteCCM24_target_compression_sub_gramCorrected_isPositive
                          (CCM24SemilocalFourierSupport.lean:234-241)
A_g,n = C_{g,n}† ∘ K_S^{1/2}          (finite-window test factor, same owner g / S)
```

Active node proving the positive core lives in C1 and is non-circular:
`C1Stage3ProjectionKernel.stage3ProjectionKernel_isPositive`.  It delegates to the
concrete brick; that brick does not reference `qw` or any RH statement, so there is
no circularity.

## The four gates (all must pass before producer promotion)

### Gate 1 — operator identity (pure algebra, active C1 namespace) ✅ CLOSED 2026-08-19
Prove, for the same owner `(g, S)` and a finite-window factor `C_{g,n}`:

```text
A_g,n † A_g,n = C_{g,n}† ∘ K_S ∘ C_{g,n}      (self-pair, IsPositive inherited)
```

If this fails at the algebra level, kill the candidate before any remainder work.

**Closed by `C1Stage3ProjectionKernel.stage3ProjectionKernel_adjointConj_isPositive`: for ANY
bounded factor `C : H → cc20GlobalLogCrossingL2`, `C† ∘ K_S ∘ C` is IsPositive on H — a one-line
reuse of mathlib `ContinuousLinearMap.IsPositive.adjoint_conj`.  No square root needed; the
candidate survives the algebra-level kill-test for arbitrary factors.  Axiom-clean (no sorryAx).**

### Gate 2 — exact trace ledger with triple vanishing
Prove a same-owner ledger of the form

```text
Re Tr(A_g,n † A_g,n) − D_{g,n}
    = pole(g*⋆g) − arch(g*⋆g) − Re( finite Euler-log carrier trace )   →  qw g
```

where the **triple-vanishing** condition actually enters the equality (it cancels the
pole term; it does not by itself force `D` to vanish).  Audit each prime-power
coefficient individually, in particular `m = 2`:

```text
p^(-m/2) · log(p) · ( F(m·log p) + F(−m·log p) )
```

Lean anchor for the right-hand readback: `C1CrossingEulerLogReadback` Stage-2 identity.

**Carrier-side ledger LANDED (2026-08-19).** The carrier half of Gate 2 is now proved in
the **active C1 namespace** from shared source bricks only — no frozen route leaf imported:
`ConnesWeilRH/Dev/C1Stage3ProjectionTraceLedger.lean`.  On the same Hilbert space as
`stage3ProjectionKernel` (`cc20GlobalLogCrossingL2`), it re-proves, firewall-cleanly, the
exact algebraic ledger already present (frozen) at `CCM24FiniteSProjectionTrace:457`:

```text
Tr(projectionResponse owner λ S)
  = (∑_{p^m ∈ terms} finitePrimeTerm(p^m))   -- arithmetic side → finite prime-term sum
    + Tr(sameObjectResidual owner λ S terms)  -- every still-unproved finite-S effect
```

where `projectionResponse = detector ∘ soninBandDifference` is a genuine same-object operator
(detector `(conv h)†∘conv h`, `h = owner.sourceTest.involution.test`). This is an **assembly-level**
win, not a new deep kernel lemma: the trace identity already existed on this space; re-proving it
from the two shared bricks (`CCM24SemilocalFourierSupport` + `SelectedCrossingOperatorBridge`,
plus `HilbertSchmidtIdeal` for `isTraceClassAlong_sub`) keeps the whole Stage-3 producer inside
active C1. Axiom-clean (no `sorryAx`; audit = `[propext, Classical.choice, Quot.sound]`).

**Arithmetic readback relation LANDED (2026-08-19).** The carrier ledger's arithmetic side is now
pinned to a clean real scalar in the active namespace: `ConnesWeilRH/Dev/C1Stage3CarrierReadback.lean`
instantiates the ledger at `terms := canonicalPrimePowerTerms owner` and chains Stage 2 (`C1CrossingEulerLog`)
to prove, for any selected Weil-square `owner`,

```text
Re Tr(projectionResponse owner λ S)
    = (∑_{n ∈ globalPrimeIndexSet} finitePrimeTermReal n)   -- := selectedArithmeticCarrierSum owner
      + Re Tr(sameObjectResidual owner λ S canonicalTerms)  -- the Gate-3 target, isolated
```

Pure assembly of already-proved pieces (`C1Stage3ProjectionTraceLedger` + `C1CrossingEulerLogReadback`), no
positivity / cutoff-limit / sign claim. Axiom-clean: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`
(audit probe `C1Stage3CarrierReadbackProbe.lean`). This is the exact first half of the Gate-2 triple-vanishing
ledger: it fixes the RHS arithmetic side to the real carrier sum; what remains is below.

**Still open within Gate 2:** wire `projectionResponse` through the finite-window factor
`C_{g,n}` so its trace is literally `Re Tr(A_g,n † A_g,n) − D`, and add the closed vertical
pole/archimedean terms so the LHS reads back to `qw g`. The residual's vanishing limit stays
**Gate 3**.

### Gate 3 — remainder to zero, no circularity
Prove an explicit bound

```text
|D_{g,n}| ≤ C_g · ε_n ,    ε_n → 0 ,
```

with the proof **not** assuming `qw g ≥ 0` (otherwise the sign is smuggled in).  This
is precisely what the frozen residual ledger does *not* yet give:
`CCM24FiniteSProjectionTrace.sameObjectResidual_eq_threePartLedger` decomposes the
residual into a prolate-difference and a compression-difference term, and the only
consequences currently proved are trace-class (`..._isTraceClassAlong`, lines 399/411) —
trace-class ≠ trace → 0.

### Gate 4 — assembly + axiom audit
Only after Gates 1-3: fill `PositiveTracePairLimitFamily` (the four fields at
`C1PositiveTraceLimitBridge.lean:55-71`) and let the existing consumers carry it to
`qw g ≥ 0` (`...:127`), spectral nonnegativity (`...:140`), `healthyCriterionState`
(`...:150`).  Then a single WSL2 ext4 build + `#print axioms` must show no `sorryAx`.

## Dependency firewall (frozen-route rule)

Per `RH_MAINLINE_FREEZE.md`, the active RH-facing leaves may not import frozen route
leaves (`*Gate3U*`, `C1LaneR*`, `C1XiCenterTwoGamma*`, numerical probes).  The shared
**source** bricks are allowed.  Concrete consequences for this candidate:

- **Reuse directly (allowed):** `CCM24SemilocalFourierSupport` positivity brick
  (`...:234`) and the low-level Sonin/prolate compression lemmas it rests on.
- **Do NOT import as a new consumer:** `CCM24FiniteSProjectionTrace`'s residual ledger
  (`sameObjectResidual`, lines 325/339) — that lives in the frozen Gate-3U readback
  chain.  If we need its decomposition, re-prove the minimal algebraic fact from the
  lower-level Sonin/prolate lemmas inside an active C1 module instead.

## Definition of done for THIS spec round (no RH claim)

1. Active node `stage3ProjectionKernel_isPositive` compiles green in WSL2 ext4, no
   `sorryAx`.
2. This page exists and names every gate's Lean anchor with a line number.
3. No frozen route leaf is imported by the new active module (firewall respected).

Gates 1-4 themselves are the subsequent rounds; this spec does not assert them closed.
