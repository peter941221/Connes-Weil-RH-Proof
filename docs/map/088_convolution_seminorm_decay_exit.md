# 088: Convolution Seminorm Decay and Iterated Base Exit

**Status**: Active binding route record.
**Date**: 2026-09-22.
**Upstream**: `087`, Record 1839.
**Exit**: `ConnesWeilRH.Dev.C1P2ConvolutionSeminormBound.riemannHypothesis_of_iteratedBase_decay_and_harmonicBudget`.

---

## 1. Route Summary

This record completes the decoupling of the raw factor seminorm $S = \mathrm{seminorm}(\phi)$
by establishing exact L^1-to-L^\infty convolution contraction:

```text
rawFactorSeminorm geometry <=
  ||(convolutionIterate geometry.base geometry.orbitIndex).test.toLp 1|| *
    SchwartzMap.seminorm C 0 0 geometry.correction.test
```

and explicit geometric power contraction:

```text
rawFactorSeminorm geometry <=
  2 * ((2 * seminorm(base))^n * seminorm(base)) * seminorm(correction)
```

Connecting this contraction with the canonical harmonic budget:

```text
harmonicBudgetSeminorm geometry delta =
  sqrt(delta / (2 * exp(L) * (visibleHarmonicChebyshevSum + 1)))
```

produces the unified master exits:

```text
riemannHypothesis_of_iteratedBase_decay_and_harmonicBudget :
  (For each off-line zero rho, 1/2 < Re(rho), exists g, geometry, delta with:
     1. delta <= -archimedeanTerm g.convolutionSquare
     2. ||base^{*(n+1)}||_{L1} * seminorm(correction) <= harmonicBudgetSeminorm geometry delta)
  ==> _root_.RiemannHypothesis

riemannHypothesis_of_geometric_contraction_and_harmonicBudget :
  (For each off-line zero rho, 1/2 < Re(rho), exists g, geometry, delta with:
     1. delta <= -archimedeanTerm g.convolutionSquare
     2. 2 * ((2 * S_base)^n * S_base) * S_corr <= harmonicBudgetSeminorm geometry delta)
  ==> _root_.RiemannHypothesis
```

---

## 2. Structural Status of Option A

```text
+------------------------------------------------------------------------+
| Component                                            | Status          |
+------------------------------------------------------------------------+
| 1. Natural 2L Kernel Truncation                      | Formal (Closed) |
| 2. Pointwise cancellation (1/n inside prime sum)     | Formal (Closed) |
| 3. Harmonic Chebyshev Mertens reduction (2L)         | Formal (Closed) |
| 4. Unconditional prime sum dominance (all geom)     | Formal (Closed) |
| 5. Canonical harmonic budget spec (unconditional)    | Formal (Closed) |
| 6. L^1 to L^infty convolution seminorm contraction   | Formal (Closed) |
| 7. Geometric power decay bound (2*S_base)^n          | Formal (Closed) |
| 8. Iterated base decay master exit for RH            | Formal (Closed) |
| 9. Geometric contraction master exit for RH          | Formal (Closed) |
+------------------------------------------------------------------------+
```

## 3. Producer-side reduction (record 1840)

The new theorem `exists_nat_geometric_budget_of_base_contraction` formally
reduces the orbit-index part of the budget obligation: if the selected base
satisfies `2 * seminorm(base) < 1`, then its geometric upper bound eventually
falls below every positive budget after multiplication by a fixed nonnegative
correction seminorm. This is a FORMAL conditional reduction, not a producer
existence theorem. The actual geometry constructor still has to realize the
chosen index and its interpolation, tail, square-zero, support, and
Archimedean-margin fields. The strict base contraction inequality remains
open for the constructor-selected owner.

## 4. Orbit-index quantifier boundary (record 1841)

The eventual-budget lemma is not yet directly consumable by the existing
geometry producer. `exists_orbitG8Geometry_of_sourceNontrivialZero_right`
constructs `OrbitG8Geometry rho g` with an existentially selected
`geometry.orbitIndex`; it does not accept a prescribed index from the caller.
Therefore the implication

```text
2 * seminorm(base) < 1
  -> choose a large index
  -> satisfy the harmonic budget
```

is not valid for the current owner without an additional theorem. The live
producer obligation is now one of:

1. strengthen the constructor to realize a caller-supplied orbit index while
   preserving interpolation, tail, square-zero, and margin fields; or
2. prove that a constructed owner can be lifted to larger orbit index with all
   those fields preserved.

This is a FORMAL quantifier/interface finding, not a no-go theorem and not an
RH result.

## 5. Fixed-correction all-index assembly (record 1850)

The source theorem
`exists_nearbyZero_unscaled_targetValues_assembly_with_fixedCorrection` now
chooses the residual correction and its nonnegative quadratic constant before
the convolution count, then exposes the assembled support, interpolation,
zero constraints, and explicit quadratic tail bound for every `n`. This closes
the immediate quantifier mismatch at the assembly layer: a later producer may
choose `n` after reading `C` from the correction. The theorem is FORMAL
interface progress only. The orbit geometry constructor still must consume it,
and the strict contraction and same-owner positivity obligations remain open.

## 6. All-index healthy orbit assembly (record 1851)

The theorem
`exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets_all_indices`
now lifts the fixed-correction interface through the healthy selected-owner
transport. After choosing the correction and its constant, every orbit count
`n` satisfying the explicit quadratic-tail condition gets the same support,
raw targets, minimal interpolation, centered orbit sum, square-zero control,
and both tail certificates. This is FORMAL producer-interface progress; strict
base contraction and the detector-specific signed budget remain open.

## 7. Common budget/tail index (record 1852)

The theorem `exists_nat_geometric_budget_and_quadratic_tail` intersects the
geometric budget and quadratic-tail convergence conditions and produces one
shared orbit index. This closes the remaining pure quantifier-combination
step between the all-index healthy assembly and the harmonic budget. The
strict contraction and detector-specific signed positivity are still open.

## 8. Indexed OrbitG8 packaging (record 1853)

The theorem `orbitG8Geometry_of_indexed_raw_construction` now accepts the
orbit index explicitly when packaging same-owner raw construction data into
`OrbitG8Geometry`. Support-derived visible-prime cutoff is reconstructed on
that exact owner. This closes the geometry packaging boundary; the raw
construction still has to supply the indexed data, and strict contraction and
semi-local positivity remain open.

## 9. Indexed packaging consumer wiring (record 1854)

The existing raw OrbitG8 producer now routes its final package construction
through the explicit-index theorem from record 1853. This confirms the
indexed interface is live in the producer path; it does not yet replace the
internal existential choice of n or prove the strict contraction and signed
positivity obligations.

## 10. Indexed OrbitG8 producer (record 1855)

The theorem `exists_indexed_orbitG8Geometry_of_sourceNontrivialZero_right`
now lifts the all-index healthy assembly all the way to complete
`OrbitG8Geometry` objects. After base, correction, and C are fixed, every n
meeting the explicit quadratic tail condition is realized on the same owner.
The remaining live obligations are strict base contraction and the
detector-specific signed semi-local positivity.

## 11. Base seminorm quantitative boundary (record 1856)

The current finite-window/surjectivity APIs provide support, interpolation, and
the quadratic vertical tail constant C, but no quantitative
`SchwartzMap.seminorm` upper bound for the selected base. C is not a seminorm
bound and must not be substituted for one. The next quantitative brick is an
explicit seminorm witness for the base construction; this is an interface
boundary, not a no-go result.

## 12. Finite coefficient budget interface (record 1857)

The new leaf `C1P2BaseSeminormBound.lean` formally bounds the zero-order
seminorm of a compact-log window pullback by the coefficient-weighted sum of
the source basis seminorms. Its consumer theorem reduces the required strict
contraction to the explicit finite inequality

```text
2 * sum_(p in coeff.support) ||coeff p|| * seminorm(basis_p) <= 1.
```

This is formal interface progress, not a proof that the right-inverse
coefficients satisfy the budget. The remaining quantitative task is to
certify that finite coefficient/basis sum for the selected Mellin targets.

## 13. Preserve the base window width (record 1858)

The geometric raw-factor estimate now accepts the actual base support window
`[a,b]` and uses `(b-a) * seminorm(base)` as the power-contraction factor. The
former length-2 estimate remains available for compatibility. This is formal
route progress; the selected finite-window coefficient budget and the
detector-specific semi-local positivity are still open.

## 14. Windowed common-index theorem (record 1859)

The producer-side common-index reduction now accepts an arbitrary contraction
factor `q < 1`, while retaining the independent quadratic tail condition. The
planned instantiation is the actual base-window factor from record 1858. This
closes only the quantifier algebra; the finite coefficient budget remains the
next quantitative obligation.

## 15. Right-inverse budget socket (record 1860)

The actual `affineResidualCorrection` now has a formal seminorm bound in
terms of the finite support and coefficients of `windowedMellinRightInverse`.
The remaining quantitative obligation is exactly the bound on that finite
coefficient/basis sum; no hidden seminorm or tail constant is substituted.
