import ConnesWeilRH.Dev.C1XiArithmeticPrimePowerReadback

/-!
# C1XiArithmeticPrimePowerAssembly - finite visible-prime assembly

This module assembles the already-proved single prime-power Fourier readback
over the exact finite support owned by `C1SameOwnerWeil`.  It deliberately
stops at a finite sum: no boundary convergence of the full von Mangoldt
series at `Re(s) = 1` is inferred here.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiArithmeticPrimePowerAssembly

open MeasureTheory
open Complex
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1XiArithmeticIntervalReadback
open C1XiArithmeticPrimePowerReadback
open C1XiVerticalFunctional
open C1SameOwnerWeil
open scoped BigOperators LSeries.notation Topology

noncomputable section

theorem integrable_arithmeticPrimePowerIntegrand_one
    (F : CompactLogTest) (n : Nat) :
    Integrable (fun t : Real => arithmeticPrimePowerIntegrand F 1 t n) := by
  by_cases hn : n = 0
  · subst n
    simp [arithmeticPrimePowerIntegrand]
  let fPlus : TestFunction :=
    (CompactLogTest.exponentialWeight F
      (((1 / 2 : Real) : Complex))).test
  let fMinus : TestFunction :=
    (CompactLogTest.exponentialWeight F
      (((-1 / 2 : Real) : Complex))).test
  have hweight :
      (fun t : Real =>
        symmetrizedLaplaceWeight F (verticalPoint 1 t)) =
      (fun t : Real => fourierLaplace fPlus t +
        fourierLaplace fMinus (-t)) := by
    funext t
    unfold symmetrizedLaplaceWeight
    rw [centeredLaplaceWeight_vertical_eq_fourierLaplace F 1 t]
    have hreflect :
        (1 : Complex) - verticalPoint 1 t = verticalPoint 0 (-t) := by
      simpa using (verticalPoint_reflection 1 t).symm
    rw [hreflect]
    rw [centeredLaplaceWeight_vertical_eq_fourierLaplace F 0 (-t)]
    simp only [fPlus, fMinus]
    norm_num
  have hrepr :
      (fun t : Real => arithmeticPrimePowerIntegrand F 1 t n) =
      (fun t : Real =>
        (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
          (fourierLaplace fPlus t *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I)) +
            fourierLaplace fMinus (-t) *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I))) * Complex.I) := by
    funext t
    rw [arithmeticPrimePowerIntegrand_eq_exp_of_ne_zero F hn]
    rw [congrFun hweight t]
    norm_num [one_mul]
    ring
  have hplusInt :=
    integrable_fourierLaplace_mul_character fPlus (Real.log n)
  have hminusInt :=
    integrable_fourierLaplace_neg_mul_character fMinus (Real.log n)
  have hsumInt :
      Integrable (fun t : Real =>
        fourierLaplace fPlus t *
            Complex.exp (-((t : Complex) *
              (Real.log n : Complex) * Complex.I)) +
          fourierLaplace fMinus (-t) *
            Complex.exp (-((t : Complex) *
              (Real.log n : Complex) * Complex.I))) :=
    hplusInt.add hminusInt
  have hwholeInt :
      Integrable (fun t : Real =>
        (ArithmeticFunction.vonMangoldt n : Complex) *
            Complex.exp (-((1 : Complex) * (Real.log n : Complex))) *
          (fourierLaplace fPlus t *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I)) +
            fourierLaplace fMinus (-t) *
              Complex.exp (-((t : Complex) *
                (Real.log n : Complex) * Complex.I))) * Complex.I) := by
    exact (hsumInt.const_mul
      ((ArithmeticFunction.vonMangoldt n : Complex) *
        Complex.exp (-((1 : Complex) * (Real.log n : Complex))))).mul_const
          Complex.I
  rw [hrepr]
  exact hwholeInt

theorem integrable_globalPrimePowerIntegrandSum (F : CompactLogTest) :
    Integrable (fun t : Real =>
      ∑ n ∈ globalPrimeIndexSet F,
        arithmeticPrimePowerIntegrand F 1 t n) := by
  exact integrable_finsetSum _ (fun n _hn =>
    integrable_arithmeticPrimePowerIntegrand_one F n)

theorem integral_globalPrimePowerIntegrandSum_eq
    (F : CompactLogTest) :
    ∫ t : Real,
        ∑ n ∈ globalPrimeIndexSet F,
          arithmeticPrimePowerIntegrand F 1 t n =
      (2 * (Real.pi : Complex) * Complex.I) *
          ∑ n ∈ globalPrimeIndexSet F,
          finitePrimeTermComplex F n := by
  calc
    (∫ t : Real,
        ∑ n ∈ globalPrimeIndexSet F,
          arithmeticPrimePowerIntegrand F 1 t n) =
        ∑ n ∈ globalPrimeIndexSet F,
          ∫ t : Real, arithmeticPrimePowerIntegrand F 1 t n := by
      rw [integral_finsetSum _ (fun n _hn =>
        integrable_arithmeticPrimePowerIntegrand_one F n)]
    _ = ∑ n ∈ globalPrimeIndexSet F,
          ((2 * (Real.pi : Complex) * Complex.I) *
            finitePrimeTermComplex F n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_arithmeticPrimePowerIntegrand_one_eq_finitePrimeTermComplex
        F n
    _ = (2 * (Real.pi : Complex) * Complex.I) *
          ∑ n ∈ globalPrimeIndexSet F, finitePrimeTermComplex F n := by
      rw [Finset.mul_sum]

theorem finitePrimeTermComplex_eq_zero_of_not_mem_globalPrimeIndexSet
    (F : CompactLogTest) {n : Nat}
    (hn : n ∉ globalPrimeIndexSet F) :
    finitePrimeTermComplex F n = 0 := by
  by_contra hterm
  apply hn
  exact (mem_globalPrimeIndexSet_iff F n).2
    ⟨finitePrimeTermComplex_nonzero_primePower F hterm, hterm⟩

theorem re_sum_globalPrimeTermComplex_eq_finitePrimeSum
    (F : CompactLogTest) :
    (∑ n ∈ globalPrimeIndexSet F, finitePrimeTermComplex F n).re =
      finitePrimeSum F := by
  simp [finitePrimeSum, finitePrimeTerm]

theorem finiteArithmeticPrimePowerIntegrand_eq_finset_sum
    (F : CompactLogTest) (N : Nat) (c t : Real) :
    finiteArithmeticPrimePowerIntegrand F N c t =
      ∑ n ∈ Finset.range (N + 1),
        arithmeticPrimePowerIntegrand F c t n := by
  unfold finiteArithmeticPrimePowerIntegrand arithmeticPrimePowerIntegrand
  rw [Finset.sum_mul, Finset.sum_mul]

theorem integral_finiteArithmeticPrimePowerIntegrand_one_eq_range_sum
    (F : CompactLogTest) (N : Nat) :
    ∫ t : Real, finiteArithmeticPrimePowerIntegrand F N 1 t =
      (2 * (Real.pi : Complex) * Complex.I) *
        ∑ n ∈ Finset.range (N + 1), finitePrimeTermComplex F n := by
  calc
    (∫ t : Real, finiteArithmeticPrimePowerIntegrand F N 1 t) =
        ∫ t : Real,
          ∑ n ∈ Finset.range (N + 1),
            arithmeticPrimePowerIntegrand F 1 t n := by
      apply integral_congr_ae
      filter_upwards with t
      exact finiteArithmeticPrimePowerIntegrand_eq_finset_sum F N 1 t
    _ = ∑ n ∈ Finset.range (N + 1),
          ∫ t : Real, arithmeticPrimePowerIntegrand F 1 t n := by
      rw [integral_finsetSum _ (fun n _hn =>
        integrable_arithmeticPrimePowerIntegrand_one F n)]
    _ = ∑ n ∈ Finset.range (N + 1),
          ((2 * (Real.pi : Complex) * Complex.I) *
            finitePrimeTermComplex F n) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact integral_arithmeticPrimePowerIntegrand_one_eq_finitePrimeTermComplex
        F n
    _ = (2 * (Real.pi : Complex) * Complex.I) *
          ∑ n ∈ Finset.range (N + 1), finitePrimeTermComplex F n := by
      rw [Finset.mul_sum]

theorem sum_range_globalIndexBound_finitePrimeTermComplex_eq
    (F : CompactLogTest) :
    (∑ n ∈ Finset.range (globalIndexBound F), finitePrimeTermComplex F n) =
      ∑ n ∈ globalPrimeIndexSet F, finitePrimeTermComplex F n := by
  classical
  unfold globalPrimeIndexSet
  symm
  apply Finset.sum_subset
    (Finset.filter_subset _ (Finset.range (globalIndexBound F)))
  intro n _hnRange hnNotMem
  by_contra hterm
  apply hnNotMem
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨index_lt_globalIndexBound F
      (finitePrimeTermComplex_nonzero_primePower F hterm) hterm,
    finitePrimeTermComplex_nonzero_primePower F hterm, hterm⟩

theorem integral_finiteArithmeticPrimePowerIntegrand_one_at_globalIndexBound_eq
    (F : CompactLogTest) :
    ∫ t : Real,
        finiteArithmeticPrimePowerIntegrand F (globalIndexBound F - 1) 1 t =
      (2 * (Real.pi : Complex) * Complex.I) *
        ∑ n ∈ globalPrimeIndexSet F, finitePrimeTermComplex F n := by
  have hbound : 0 < globalIndexBound F := by
    simp [globalIndexBound]
  calc
    (∫ t : Real,
        finiteArithmeticPrimePowerIntegrand F (globalIndexBound F - 1) 1 t) =
        (2 * (Real.pi : Complex) * Complex.I) *
          ∑ n ∈ Finset.range ((globalIndexBound F - 1) + 1),
            finitePrimeTermComplex F n :=
      integral_finiteArithmeticPrimePowerIntegrand_one_eq_range_sum
        F (globalIndexBound F - 1)
    _ = (2 * (Real.pi : Complex) * Complex.I) *
          ∑ n ∈ Finset.range (globalIndexBound F),
            finitePrimeTermComplex F n := by
      rw [Nat.sub_add_cancel hbound]
    _ = (2 * (Real.pi : Complex) * Complex.I) *
          ∑ n ∈ globalPrimeIndexSet F, finitePrimeTermComplex F n := by
      rw [sum_range_globalIndexBound_finitePrimeTermComplex_eq F]

end
end C1XiArithmeticPrimePowerAssembly
end Source
end ConnesWeilRH
