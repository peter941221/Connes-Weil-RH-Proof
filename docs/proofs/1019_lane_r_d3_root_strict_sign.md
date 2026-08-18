# 1019 - Lane R D3-root strict sign

Date: 2026-08-18.

## Verdict

The explicit narrow-support D3 root now has a strict sign:

```lean
narrowArchRoot_archimedeanTerm_neg :
  C1SameOwnerWeil.archimedeanTerm narrowArchRoot.convolutionSquare < 0

narrowArchRoot_qw_pos :
  0 < C1SameOwnerWeil.qw narrowArchRoot
```

The proof is axiom-clean.  The audit probe reports only
`[propext, Classical.choice, Quot.sound]` for every new public declaration.

This is one concrete prime-free Lane R witness.  It is not the universal
spectral nonnegativity statement, does not produce a Yoshida detector (the
detector-side prime-free sign would require positive archimedean term), and
does not prove RH.

## Strictness chain

The proof closes the formerly missing nonzero step without numerical
differentiation:

```text
wideTest.test 0 = 1
  -> Re Laplace(wideTest, 2) > 0
  -> Laplace(wideTest, 2) != 0
  -> tripleVanishingRoot(wideTest).test != 0
  -> Re F(0) > 0,  F = root.convolutionSquare
  -> archimedeanTerm(F) < 0
  -> qw(root) = -archimedeanTerm(F) > 0
```

`tripleVanishingRoot_test_ne_zero_of_laplaceAt_two` uses the exact D3
transform law at `s = 2`; the scalar multiplier is nonzero there.  The base
Laplace positivity is an ordinary integral positivity argument for the
nonnegative compactly supported function
`exp (2*x) * wideBump w x`, which equals `1` at the origin.

## Budget API

`archimedeanTerm_le_narrow_budget` now exposes the estimate rather than
discarding its mass factor:

```text
arch(F) <=
  (log(4*pi) + gamma + R - (1/2)*log(1/R)) * Re(F(0)).
```

`archimedeanTerm_neg_of_narrow_budget` turns a strict scalar budget and a
strictly positive square mass into strict archimedean negativity.  For
`R = exp(-4*(C+1))`, `narrowArchRadius_budget_lt` proves the scalar budget is
strictly negative using only `C > 0` and `R < 1`.

## Verification

WSL2 owner and probe build:

```text
lake build ConnesWeilRH.Dev.C1LaneRNarrowArch
  ConnesWeilRH.Dev.C1LaneRStrictness
  ConnesWeilRH.Dev.C1LaneRStrictnessProbe
```

The final build completed at 3619 jobs.  Existing linter warnings were
replayed; no `sorryAx`, project RH axiom, or unconditional RH theorem was
introduced.

## Scope boundary

The result strengthens one explicit prime-free leaf from non-strict to
strict.  The prime-inclusive case and the universal Lane R sign remain open.
