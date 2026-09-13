/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1PsiBlindness

/-!
# C1PsiLinearity - the additive structure of the Weil functional

Campaign brick 2 (record 1412 plan). `C1PsiBlindness` machine-checked the
odd-annihilation half of the 1406 kill (a); the MODEL argument it was
embedded in treated `psi` as additive. This leaf supplies that additive
structure: pointwise `testAdd`/`testNeg` on `CompactLogTest` (through the
`TestFunction` component, so all accessors are definitional), additivity
and negation of `laplaceAt`, of the pole readout, of the complex prime
term, the real prime term and the prime sum, and of the archimedean
numerator/integrand. The two functional-level archimedean additivity
statements carry explicit `IntegrableOn` hypotheses; the additive
negation of `archimedeanTerm` is unconditional via `integral_neg`.
The square-class corollary at the end is hypothesis-free.

No sign theorem, no positivity statement, no RH claim.
-/

namespace ConnesWeilRH
namespace Source
namespace C1PsiLinearity

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open scoped BigOperators

/-! ### The additive structure on `CompactLogTest` -/

/-- Pointwise addition of compact log tests: `TestFunction` carries the
algebra, and compact support is preserved because the support of a sum
sits inside the union of the supports. -/
noncomputable def testAdd (f g : CompactLogTest) : CompactLogTest :=
  ⟨f.test + g.test, f.compactSupport.add g.compactSupport⟩

@[simp] theorem testAdd_apply (f g : CompactLogTest) (x : ℝ) :
    (testAdd f g).test x = f.test x + g.test x :=
  rfl

/-- Pointwise negation of a compact log test. -/
noncomputable def testNeg (f : CompactLogTest) : CompactLogTest :=
  ⟨-f.test, f.compactSupport.neg⟩

@[simp] theorem testNeg_apply (f : CompactLogTest) (x : ℝ) :
    (testNeg f).test x = -f.test x :=
  rfl

/-! ### Laplace transform and pole term -/

/-- `laplaceAt` is additive: the exponential weight distributes over the
sum pointwise, and both summands are integrable (rapid decay). -/
theorem laplaceAt_testAdd (f g : CompactLogTest) (s : ℂ) :
    laplaceAt (testAdd f g) s = laplaceAt f s + laplaceAt g s := by
  unfold laplaceAt
  simp only [exponentialWeight_apply, testAdd_apply]
  have hi : Integrable (fun x : ℝ => Complex.exp (s * (x : ℂ)) * f.test x)
      volume := (exponentialWeight f s).test.integrable
  have hg : Integrable (fun x : ℝ => Complex.exp (s * (x : ℂ)) * g.test x)
      volume := (exponentialWeight g s).test.integrable
  have hfn : (fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * (f.test x + g.test x)) =
      fun x : ℝ =>
        Complex.exp (s * (x : ℂ)) * f.test x +
          Complex.exp (s * (x : ℂ)) * g.test x := by
    funext x
    rw [mul_add]
  rw [hfn, integral_add hi hg]

/-- `laplaceAt` commutes with negation. -/
theorem laplaceAt_testNeg (f : CompactLogTest) (s : ℂ) :
    laplaceAt (testNeg f) s = -laplaceAt f s := by
  unfold laplaceAt
  simp only [exponentialWeight_apply, testNeg_apply]
  have hfn : (fun x : ℝ => Complex.exp (s * (x : ℂ)) * -f.test x) =
      fun x : ℝ => -(Complex.exp (s * (x : ℂ)) * f.test x) := by
    funext x
    rw [mul_neg]
  rw [hfn, integral_neg]

/-- The pole functional is additive. -/
theorem poleTerm_testAdd (f g : CompactLogTest) :
    poleTerm (testAdd f g) = poleTerm f + poleTerm g := by
  unfold poleTerm
  rw [laplaceAt_testAdd, laplaceAt_testAdd]
  simp only [Complex.add_re]
  ring

/-- The pole functional is odd. -/
theorem poleTerm_testNeg (f : CompactLogTest) :
    poleTerm (testNeg f) = -poleTerm f := by
  unfold poleTerm
  rw [laplaceAt_testNeg, laplaceAt_testNeg]
  simp only [Complex.neg_re, Complex.add_re]
  ring

/-! ### The prime readouts -/

/-- The complex prime-power term is additive. -/
theorem finitePrimeTermComplex_testAdd (f g : CompactLogTest) (n : Nat) :
    finitePrimeTermComplex (testAdd f g) n =
      finitePrimeTermComplex f n + finitePrimeTermComplex g n := by
  unfold finitePrimeTermComplex
  simp only [testAdd_apply]
  ring

/-- The complex prime-power term is odd. -/
theorem finitePrimeTermComplex_testNeg (f : CompactLogTest) (n : Nat) :
    finitePrimeTermComplex (testNeg f) n = -finitePrimeTermComplex f n := by
  unfold finitePrimeTermComplex
  simp only [testNeg_apply]
  ring

/-- The real prime-power term is additive. -/
theorem finitePrimeTerm_testAdd (f g : CompactLogTest) (n : Nat) :
    finitePrimeTerm (testAdd f g) n =
      finitePrimeTerm f n + finitePrimeTerm g n := by
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_testAdd]
  simp only [Complex.add_re]

/-- The real prime-power term is odd. -/
theorem finitePrimeTerm_testNeg (f : CompactLogTest) (n : Nat) :
    finitePrimeTerm (testNeg f) n = -finitePrimeTerm f n := by
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_testNeg]
  simp only [Complex.neg_re]

/-- A nonzero term of `testAdd f g` forces a nonzero term of `f` or of
`g`: the visible index set is contained in the union. -/
theorem globalPrimeIndexSet_testAdd_subset (f g : CompactLogTest) :
    globalPrimeIndexSet (testAdd f g) ⊆
      globalPrimeIndexSet f ∪ globalPrimeIndexSet g := by
  intro n hn
  obtain ⟨hprime, hterm⟩ := (mem_globalPrimeIndexSet_iff (testAdd f g) n).mp hn
  have hadd : finitePrimeTermComplex (testAdd f g) n =
      finitePrimeTermComplex f n + finitePrimeTermComplex g n :=
    finitePrimeTermComplex_testAdd f g n
  have hnonzero : finitePrimeTermComplex f n ≠ 0 ∨
      finitePrimeTermComplex g n ≠ 0 := by
    by_contra h
    rw [not_or] at h
    rw [hadd, not_ne_iff.mp h.1, not_ne_iff.mp h.2] at hterm
    simp at hterm
  rw [Finset.mem_union, mem_globalPrimeIndexSet_iff,
    mem_globalPrimeIndexSet_iff]
  cases hnonzero with
  | inl hf => exact Or.inl ⟨hprime, hf⟩
  | inr hg => exact Or.inr ⟨hprime, hg⟩

/-- Outside the visible index set the real prime term vanishes. -/
theorem finitePrimeTerm_eq_zero_of_not_mem (F : CompactLogTest) (n : Nat)
    (hn : n ∉ globalPrimeIndexSet F) : finitePrimeTerm F n = 0 := by
  rw [mem_globalPrimeIndexSet_iff] at hn
  unfold finitePrimeTerm
  by_cases hprime : IsPrimePow n
  · have hzero : finitePrimeTermComplex F n = 0 := by
      by_contra hne
      exact hn ⟨hprime, hne⟩
    rw [hzero]
    simp
  · unfold finitePrimeTermComplex
    simp [ArithmeticFunction.vonMangoldt_apply, hprime]

/-- The complete prime-power sum is additive. -/
theorem finitePrimeSum_testAdd (F G : CompactLogTest) :
    finitePrimeSum (testAdd F G) = finitePrimeSum F + finitePrimeSum G := by
  unfold finitePrimeSum
  set D := globalPrimeIndexSet F ∪ globalPrimeIndexSet G
  have hsub : globalPrimeIndexSet (testAdd F G) ⊆ D :=
    globalPrimeIndexSet_testAdd_subset F G
  have h1 : (∑ n ∈ globalPrimeIndexSet (testAdd F G),
        finitePrimeTerm (testAdd F G) n) =
      ∑ n ∈ D, finitePrimeTerm (testAdd F G) n :=
    Finset.sum_subset hsub fun n hn hn' =>
      finitePrimeTerm_eq_zero_of_not_mem (testAdd F G) n hn'
  have h2 : ∑ n ∈ D, finitePrimeTerm (testAdd F G) n =
      ∑ n ∈ D, (finitePrimeTerm F n + finitePrimeTerm G n) :=
    Finset.sum_congr rfl fun n _ => finitePrimeTerm_testAdd F G n
  have h3 : ∑ n ∈ D, (finitePrimeTerm F n + finitePrimeTerm G n) =
      (∑ n ∈ D, finitePrimeTerm F n) + ∑ n ∈ D, finitePrimeTerm G n :=
    Finset.sum_add_distrib
  have h4 : ∑ n ∈ D, finitePrimeTerm F n =
      ∑ n ∈ globalPrimeIndexSet F, finitePrimeTerm F n :=
    (Finset.sum_subset (Finset.subset_union_left) fun n hn hn' =>
      finitePrimeTerm_eq_zero_of_not_mem F n hn').symm
  have h5 : ∑ n ∈ D, finitePrimeTerm G n =
      ∑ n ∈ globalPrimeIndexSet G, finitePrimeTerm G n :=
    (Finset.sum_subset (Finset.subset_union_right) fun n hn hn' =>
      finitePrimeTerm_eq_zero_of_not_mem G n hn').symm
  rw [h1, h2, h3, h4, h5]

/-- The complete prime-power sum is odd. -/
theorem finitePrimeSum_testNeg (F : CompactLogTest) :
    finitePrimeSum (testNeg F) = -finitePrimeSum F := by
  unfold finitePrimeSum
  have heq : globalPrimeIndexSet (testNeg F) = globalPrimeIndexSet F := by
    apply Finset.Subset.antisymm
    · intro n hn
      obtain ⟨hprime, hterm⟩ :=
        (mem_globalPrimeIndexSet_iff (testNeg F) n).mp hn
      rw [mem_globalPrimeIndexSet_iff]
      refine ⟨hprime, ?_⟩
      rw [finitePrimeTermComplex_testNeg] at hterm
      exact neg_ne_zero.mp hterm
    · intro n hn
      obtain ⟨hprime, hterm⟩ := (mem_globalPrimeIndexSet_iff F n).mp hn
      rw [mem_globalPrimeIndexSet_iff]
      refine ⟨hprime, ?_⟩
      rw [finitePrimeTermComplex_testNeg]
      exact neg_ne_zero.mpr hterm
  rw [heq, Finset.sum_congr rfl (fun n _ => finitePrimeTerm_testNeg F n),
    Finset.sum_neg_distrib]

/-! ### The archimedean readouts -/

/-- The archimedean numerator is additive pointwise. -/
theorem archimedeanNumerator_testAdd (F G : CompactLogTest) (y : ℝ) :
    archimedeanNumerator (testAdd F G) y =
      archimedeanNumerator F y + archimedeanNumerator G y := by
  unfold archimedeanNumerator
  simp only [testAdd_apply]
  ring

/-- The archimedean numerator is odd pointwise. -/
theorem archimedeanNumerator_testNeg (F : CompactLogTest) (y : ℝ) :
    archimedeanNumerator (testNeg F) y = -archimedeanNumerator F y := by
  unfold archimedeanNumerator
  simp only [testNeg_apply]
  ring

/-- The direct archimedean integrand is additive pointwise. -/
theorem archimedeanIntegrand_testAdd (F G : CompactLogTest) (y : ℝ) :
    archimedeanIntegrand (testAdd F G) y =
      archimedeanIntegrand F y + archimedeanIntegrand G y := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_testAdd]
  rw [add_div]

/-- The direct archimedean integrand is odd pointwise. -/
theorem archimedeanIntegrand_testNeg (F : CompactLogTest) (y : ℝ) :
    archimedeanIntegrand (testNeg F) y = -archimedeanIntegrand F y := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_testNeg]
  rw [neg_div]

/-- The archimedean functional is additive whenever both integrands are
integrable on the positive half-line. For the square class this
hypothesis is discharged by
`C1SameOwnerWeil.archimedeanIntegrand_square_integrableOn_Ioi`. -/
theorem archimedeanTerm_testAdd (F G : CompactLogTest)
    (hFI : IntegrableOn (archimedeanIntegrand F) (Set.Ioi (0 : Real)))
    (hGI : IntegrableOn (archimedeanIntegrand G) (Set.Ioi (0 : Real))) :
    archimedeanTerm (testAdd F G) =
      archimedeanTerm F + archimedeanTerm G := by
  have hint : (∫ y in Set.Ioi (0 : Real),
        archimedeanIntegrand (testAdd F G) y) =
      (∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y) +
        ∫ y in Set.Ioi (0 : Real), archimedeanIntegrand G y := by
    have hfn : (fun y : ℝ => archimedeanIntegrand (testAdd F G) y) =
        fun y : ℝ => archimedeanIntegrand F y + archimedeanIntegrand G y := by
      funext y
      rw [archimedeanIntegrand_testAdd]
    rw [hfn, integral_add hFI hGI]
  unfold archimedeanTerm
  simp only [testAdd_apply, hint]
  rw [mul_add]
  simp only [Complex.add_re]
  ring

/-- The archimedean functional is odd: no integrability hypothesis is
needed because `integral_neg` is unconditional. -/
theorem archimedeanTerm_testNeg (F : CompactLogTest) :
    archimedeanTerm (testNeg F) = -archimedeanTerm F := by
  have hint : (∫ y in Set.Ioi (0 : Real),
        archimedeanIntegrand (testNeg F) y) =
      -(∫ y in Set.Ioi (0 : Real), archimedeanIntegrand F y) := by
    have hfn : (fun y : ℝ => archimedeanIntegrand (testNeg F) y) =
        fun y : ℝ => -(archimedeanIntegrand F y) := by
      funext y
      rw [archimedeanIntegrand_testNeg]
    rw [hfn, integral_neg]
  unfold archimedeanTerm
  simp only [testNeg_apply, hint]
  rw [mul_neg]
  simp only [Complex.neg_re, Complex.add_re]
  ring

/-! ### The complete functional -/

/-- `psi` is additive whenever both integrands are integrable on the
positive half-line. -/
theorem psi_testAdd (F G : CompactLogTest)
    (hFI : IntegrableOn (archimedeanIntegrand F) (Set.Ioi (0 : Real)))
    (hGI : IntegrableOn (archimedeanIntegrand G) (Set.Ioi (0 : Real))) :
    psi (testAdd F G) = psi F + psi G := by
  unfold psi
  rw [poleTerm_testAdd, archimedeanTerm_testAdd F G hFI hGI,
    finitePrimeSum_testAdd]
  ring

/-- `psi` is odd. -/
theorem psi_testNeg (F : CompactLogTest) : psi (testNeg F) = -psi F := by
  unfold psi
  rw [poleTerm_testNeg, archimedeanTerm_testNeg, finitePrimeSum_testNeg]
  ring

/-- **Square-class additivity of `psi`, hypothesis-free**: two
convolution squares are summable inside `psi`, since each integrand is
integrable by the existing selected-owner lemma. -/
theorem psi_testAdd_convolutionSquare (a b : CompactLogTest) :
    psi (testAdd a.convolutionSquare b.convolutionSquare) =
      psi a.convolutionSquare + psi b.convolutionSquare :=
  psi_testAdd a.convolutionSquare b.convolutionSquare
    (archimedeanIntegrand_square_integrableOn_Ioi a)
    (archimedeanIntegrand_square_integrableOn_Ioi b)

end C1PsiLinearity
end Source
end ConnesWeilRH
