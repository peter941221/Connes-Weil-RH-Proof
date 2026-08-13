# 1007 — Xi Zero-Index Completeness (Gate 2 spectral side)

Date: 2026-08-13. Status: CLOSED axiom-clean. RH NOT claimed.

## Outcome

The zero-spectral index of Gate 2 is now the *exact* zero set of the
completed xi function, not merely a subset. Three theorems land in
`ConnesWeilRH/Source/CC20ZetaCounting.lean`:

```lean
theorem completedRiemannXi_ne_zero_of_one_le_re {s : ℂ} (hs : 1 ≤ s.re) :
    completedRiemannXi s ≠ 0

theorem sourceNontrivialZero_of_completedRiemannXi_eq_zero
    {z : ℂ} (hxi : completedRiemannXi z = 0) :
    RHDefinitionBridge.standard.sourceNontrivialZero z

theorem completedRiemannXi_eq_zero_iff_sourceNontrivialZero (z : ℂ) :
    completedRiemannXi z = 0 ↔
      RHDefinitionBridge.standard.sourceNontrivialZero z
```

WSL2 isolated mirror `c1-xi-zero-20260813`: build green (3496 jobs, EXIT=0),
`#print axioms` = `[propext, Classical.choice, Quot.sound]`, 0 `sorryAx`.

## Why this is the right brick

Gate 2 (Burnol/Riemann-Weil explicit formula) equates the same-owner
arithmetic functional with the spectrum-summed zero expression:

```text
C1SameOwnerWeil.psi F = spectralWeilValue F
```

The spectral sum lives over `sourceNontrivialZeroSet`. Before this closure
the repository only had the forward direction `source zero -> xi zero`; the
index was a subset. A contour/Hadamard proof of the explicit formula would
need to index the *exact* xi zero set. This theorem closes that seam.

The trick that kills the negative-even zeta zeros: they are not
automatically excised by the source definition; the functional equation
reflects any candidate negative-even zero across to

```text
Re(1 - (-2(n+1))) = 1 + 2(n+1) >= 1,
```

which sits in the zero-free closed right half-plane proved by the
zeta-nonvanishing half-plane theorem.

## Lean notes

- The real part of a complex ring expression must be proved *inside* `ℂ`
  first, then rewritten and closed with `norm_num`; `ring` on `.re` does
  not fire:
  ```lean
  have hcomplex : (1 : ℂ) - (-2 * (n+1) : ℂ) =
      ((1 : ℝ) + 2 * ((n : ℝ) + 1) : ℂ) := by push_cast; ring
  have hre : ((1 : ℂ) - (-2 * (n+1) : ℂ)).re = 1 + 2 * ((n:ℝ)+1) := by
    rw [hcomplex]; norm_num
  ```
- `simpa [completedRiemannXi] using hxi` trips the `linter.unnecessarySimpa`;
  project style prefers `simp [completedRiemannXi] at hxi`.

## Files changed

```text
M ConnesWeilRH/Source/CC20ZetaCounting.lean   (+72)
+ A ConnesWeilRH/Dev/C1XiZeroIndexProbe.lean   (#print axioms audit)
```

Downstream modules re-built green (no breakage):
`C1SpectralWeil`, `C1XiGrowth`, `C1SpectralSummability`,
`C1SpectrWeilFirstProbe`, `UnconditionalSkeleton`.

## Gate 2 remaining

The final Gate 2 stanza is the genuine analytic explicit-formula equality
`psi F = spectralWeilValue F`. This is the classic Burnol formula
(docs/109 gives the exact term-by-term normalization alignment). The
obstruction is real: mathlib v4.30.0 has no Riemann-zeta Hadamard product /
contour-residue machinery. RH NOT claimed.