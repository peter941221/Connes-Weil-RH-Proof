# 985 - C1 phase-1 state (SUPERSEDED and corrected)

Date: 2026-08-12. Status: corrected source audit. RH NOT claimed.

This memo supersedes every earlier state in this file that described the
healthy C1 owner as archimedean-only or the explicit Weil value as a `{2}`
truncation. Those were intermediate implementations and are no longer the code
imported by the route audit.

## Result

The C1 object layer has made substantive progress, but the RH theorem has not.
The coordinate map, complete compact-log Weil functional, all visible
prime-power terms, one-square convention, and source/CC20 sign convention are
now represented on one owner and checked by Lean. The universal
finite-vanishing sign and Yoshida detectors on that same owner remain open.

```text
CompactLogTest F(u)
        |
        |  x = exp(u)
        v
positive route test F(log x), x > 0                 CLOSED
        |
        +--> Mellin(route F, s) = bilateral Laplace(F, s)  CLOSED
        |
        +--> Psi(F) = pole - arch - all visible prime powers CLOSED as a definition/readback
        |
        +--> QW(g) = Psi(g^* * g), exactly one square        CLOSED as a definition/readback
        |
        +--> for every vanishing g, 0 <= QW(g)               OPEN, RH-level
        |
        +--> Yoshida detector on this same owner              OPEN
```

## Current evidence

+--------------------------------------+----------+-----------------------------------------------+
| Layer                                | State    | Lean evidence                                 |
+--------------------------------------+----------+-----------------------------------------------+
| log-to-positive coordinate map       | CLOSED   | `C1LogPositiveBridge.toPositiveRouteTest`     |
| Mellin/Laplace coordinate identity   | CLOSED   | `mellin_toPositiveRouteTest_eq_laplaceAt`     |
| complete same-owner Weil functional  | CLOSED   | `C1SameOwnerWeil.psi` / `finitePrimeSum`      |
| canonical component readbacks        | CLOSED   | `*_square_eq_selected` theorems               |
| one-square and sign convention       | CLOSED   | `healthyWeilSquareReadoff`                    |
| exact criterion expansion            | CLOSED   | `healthyCriterionState_iff_all_vanishing_...` |
| universal finite-vanishing sign      | OPEN     | must prove `∀ g, vanishing g → 0 ≤ qw g`      |
| same-owner Yoshida detector          | OPEN     | old normalized-owner theorem is not transport |
+--------------------------------------+----------+-----------------------------------------------+

The exact open statement is exposed by:

```lean
theorem healthyCriterionState_iff_all_vanishing_qw_nonnegative
    (F : Finset CriticalVanishingPoint) :
    healthyCriterionState F ↔
      ∀ g : CompactLogTest,
        ConnesWeilRH.Source.CC20VanishesOn healthyCC20TestSpace F g →
          0 ≤ C1SameOwnerWeil.qw g := by
```

This theorem unfolds the criterion; it does not prove its right-hand side.

## Three corrected failure mechanisms

1. Same Lean type did not mean same coordinate. `CompactLogTest.test` is a
   function of `u = log x`, while route `TestFunction` is a function of `x`.
   `C1LogPositiveBridge` now performs the inverse coordinate map explicitly.

2. The generic CC20 criterion already applies `starConvolution`. The previous
   intermediate implementation squared again inside `weilLocalSum`.
   `healthyWeilSquareReadoff` now proves that exactly one square reaches `QW`.

3. Per-common support `{2}` was not the global prime-power sum. Compact support
   now computes `globalPrimeIndexSet F`, and `finitePrimeSum F` contains every
   nonzero visible prime-power term of that same `F`.

## What remains load-bearing

Defining `Psi` is not an explicit-formula theorem. The route still needs an
all-test analytic/trace identity that relates this complete functional to a
positive operator or spectral expression on the same owner. That identity is
the plausible producer for the open universal sign. Separately, the Yoshida
detector theorem must be rebuilt for `healthyCC20TestSpace`; the theorem for
`normalizedCC20TestSpace` cannot be reused by type coincidence.

The generic exit is already present:

```lean
theorem cc20_proposition_c1_from_yoshida_detector
    (C : CC20TestSpace)
    (F : Finset CriticalVanishingPoint)
    (_hfinite : SourceFiniteSetAdmissibility F)
    (_hdisjoint :
      SourceFiniteSetDisjointFromNontrivialZeros
        RHDefinitionBridge.standard F)
    (hexists : CC20YoshidaDetectorExists C F)
    (hcriterion : CC20FiniteVanishingWeilCriterion C F) :
    RHDefinitionBridge.standard.SourceRH := by
```

Therefore the next work is mathematical producer work, not more interface
plumbing. RH NOT claimed.
