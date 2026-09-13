/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1PsiLinearity

/-!
# C1PsiSectorSplit - psi factors through the reflection-even sector

Campaign brick 3 (record 1413 plan). Bricks 1-2 machine-checked that
`psi` annihilates negation-odd tests (`C1PsiBlindness`) and splits
pointwise sums (`C1PsiLinearity`). This leaf completes kill (a) of
record 1406 in its full form: `psi` is INVARIANT under reflection in
the additive log coordinate, `psi f.reflection = psi f`,
unconditionally - because every readout is built from reflection-symmetric
inputs: the pole pair `laplaceAt (±1/2)` (swapped by
`laplaceAt_reflection`), the prime kernel `F(log n) + F(-log n)`
(fixed pointwise), and the archimedean numerator
`e^{y/2}(F(y) + F(-y)) - 2F(0)` (fixed pointwise). No `IntegrableOn`
hypothesis is needed anywhere in the invariance bundle.

The doubled sector projections `evenSym2` / `oddDiff2` (no scalar
layer, so only 2-times forms) give the corollary form: the doubled odd
part has `psi = 0` (via brick 1), and `psi` of the doubled even part
splits as `psi f + psi f` under the archimedean-summability
hypotheses carried by `psi_testAdd`.

No sign theorem, no positivity statement, no RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1PsiSectorSplit

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.CompactLogConvolution.CompactLogTest
open C1SameOwnerWeil
open C1PsiBlindness
open C1PsiLinearity
open scoped BigOperators

/-! ### Reflection invariance of the readouts -/

/-- `laplaceAt` of the reflection is `laplaceAt` at the negated point:
the change of variables `x ↦ -x` flips the Laplace parameter. -/
theorem laplaceAt_reflection (f : CompactLogTest) (s : ℂ) :
    laplaceAt f.reflection s = laplaceAt f (-s) := by
  unfold laplaceAt
  simp only [exponentialWeight_apply, reflection_apply]
  let paired : ℝ → ℂ := fun x => Complex.exp (-s * (x : ℂ)) * f.test x
  have hrewrite : (fun x : ℝ => Complex.exp (s * (x : ℂ)) * f.test (-x)) =
      fun x => paired (-x) := by
    funext x
    dsimp [paired]
    have harg : (s : ℂ) * Complex.ofReal x =
        (-s) * Complex.ofReal (-x) := by
      push_cast
      ring
    rw [harg]
  rw [hrewrite, integral_neg_eq_self]

/-- The pole functional is reflection-invariant: reflection swaps the
`±1/2` pair. -/
theorem poleTerm_reflection (f : CompactLogTest) :
    poleTerm f.reflection = poleTerm f := by
  unfold poleTerm
  simp only [laplaceAt_reflection, neg_div, neg_neg]
  rw [add_comm]

/-- The complex prime-power term is reflection-invariant pointwise:
its kernel is already the symmetrized `F(log n) + F(-log n)`. -/
theorem finitePrimeTermComplex_reflection (f : CompactLogTest) (n : Nat) :
    finitePrimeTermComplex f.reflection n =
      finitePrimeTermComplex f n := by
  unfold finitePrimeTermComplex
  simp only [reflection_apply, neg_neg]
  rw [add_comm]

/-- The real prime-power term is reflection-invariant. -/
theorem finitePrimeTerm_reflection (f : CompactLogTest) (n : Nat) :
    finitePrimeTerm f.reflection n = finitePrimeTerm f n :=
  congr_arg Complex.re (finitePrimeTermComplex_reflection f n)

/-- Visibility of a prime-power index is reflection-invariant. -/
theorem mem_globalPrimeIndexSet_reflection_iff (f : CompactLogTest)
    (n : Nat) :
    n ∈ globalPrimeIndexSet f.reflection ↔ n ∈ globalPrimeIndexSet f := by
  rw [mem_globalPrimeIndexSet_iff, mem_globalPrimeIndexSet_iff,
    finitePrimeTermComplex_reflection]

/-- The visible index set itself is reflection-invariant. -/
theorem globalPrimeIndexSet_reflection_eq (f : CompactLogTest) :
    globalPrimeIndexSet f.reflection = globalPrimeIndexSet f :=
  Finset.ext fun n => mem_globalPrimeIndexSet_reflection_iff f n

/-- The complete prime-power sum is reflection-invariant. -/
theorem finitePrimeSum_reflection (f : CompactLogTest) :
    finitePrimeSum f.reflection = finitePrimeSum f := by
  unfold finitePrimeSum
  rw [globalPrimeIndexSet_reflection_eq]
  exact Finset.sum_congr rfl fun n _ => finitePrimeTerm_reflection f n

/-- The archimedean numerator is reflection-invariant pointwise. -/
theorem archimedeanNumerator_reflection (f : CompactLogTest) (y : ℝ) :
    archimedeanNumerator f.reflection y = archimedeanNumerator f y := by
  unfold archimedeanNumerator
  simp only [reflection_apply, neg_neg, neg_zero]
  rw [add_comm]

/-- The direct archimedean integrand is reflection-invariant pointwise. -/
theorem archimedeanIntegrand_reflection (f : CompactLogTest) (y : ℝ) :
    archimedeanIntegrand f.reflection y = archimedeanIntegrand f y := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_reflection]

/-- The archimedean functional is reflection-invariant: pointwise
integrand equality makes the Bochner integral equal by
`integral_congr_ae`, with no integrability bookkeeping. -/
theorem archimedeanTerm_reflection (f : CompactLogTest) :
    archimedeanTerm f.reflection = archimedeanTerm f := by
  have hint : (∫ y in Set.Ioi (0 : Real),
        archimedeanIntegrand f.reflection y) =
      ∫ y in Set.Ioi (0 : Real), archimedeanIntegrand f y := by
    apply integral_congr_ae
    filter_upwards with y
    rw [archimedeanIntegrand_reflection]
  unfold archimedeanTerm
  simp only [reflection_apply, neg_zero, hint]

/-! ### The completed kill (a): psi cannot see the odd sector -/

/-- **TOP (brick 3)**: `psi` is invariant under reflection in the
additive log coordinate, unconditionally. Together with brick 1 this is
the full machine form of 1406 kill (a): `psi` reads exactly the
reflection-even sector of its test argument; the odd sector (and hence
the imaginary-odd Chuk cross term `F_d = 2i · odd`) contributes
nothing to `psi` for ANY owner. -/
theorem psi_reflection (f : CompactLogTest) :
    psi f.reflection = psi f := by
  unfold psi
  rw [poleTerm_reflection, archimedeanTerm_reflection,
    finitePrimeSum_reflection]

/-! ### Doubled sector projections -/

/-- Twice the reflection-even part of a test (no scalar layer, so the
form is doubled). -/
noncomputable def evenSym2 (f : CompactLogTest) : CompactLogTest :=
  testAdd f f.reflection

@[simp] theorem evenSym2_apply (f : CompactLogTest) (x : ℝ) :
    (evenSym2 f).test x = f.test x + f.test (-x) :=
  rfl

/-- Twice the reflection-odd part of a test. -/
noncomputable def oddDiff2 (f : CompactLogTest) : CompactLogTest :=
  testAdd f (testNeg f.reflection)

@[simp] theorem oddDiff2_apply (f : CompactLogTest) (x : ℝ) :
    (oddDiff2 f).test x = f.test x + -f.test (-x) :=
  rfl

/-- The doubled odd part is negation-odd, so it is exactly in the
annihilated sector of brick 1. -/
theorem oddDiff2_odd (f : CompactLogTest) (x : ℝ) :
    (oddDiff2 f).test (-x) = -(oddDiff2 f).test x := by
  simp only [oddDiff2_apply, neg_neg]
  ring

/-- `psi` of the doubled odd part vanishes for every test. -/
theorem psi_oddDiff2_eq_zero (f : CompactLogTest) :
    psi (oddDiff2 f) = 0 :=
  psi_eq_zero_of_odd (oddDiff2 f) (oddDiff2_odd f)

/-- The doubled parts recover the doubled test:
`evenSym2 f + oddDiff2 f = f + f`. -/
theorem testAdd_evenSym2_oddDiff2 (f : CompactLogTest) :
    testAdd (evenSym2 f) (oddDiff2 f) = testAdd f f := by
  refine CompactLogTest.ext ?_
  ext x
  simp only [testAdd_apply, evenSym2_apply, oddDiff2_apply]
  ring

/-- `psi` of the doubled even part is twice `psi`, under the archimedean
summability hypotheses that `psi_testAdd` carries. -/
theorem psi_evenSym2 (f : CompactLogTest)
    (hFI : IntegrableOn (archimedeanIntegrand f) (Set.Ioi (0 : Real)))
    (hFR : IntegrableOn (archimedeanIntegrand f.reflection)
      (Set.Ioi (0 : Real))) :
    psi (evenSym2 f) = psi f + psi f := by
  unfold evenSym2
  rw [psi_testAdd f f.reflection hFI hFR, psi_reflection]

end C1PsiSectorSplit
end Source
end ConnesWeilRH
