import ConnesWeilRH.Dev.C1P2TwoPointPhysicalInterpolation

/-!
# Finite physical combinations and Laplace readback

This leaf packages finite linear combinations of genuine compact-log tests.
It supplies the exact linear map from physical bump coefficients to Mellin
values, which is the matrix interface needed before any constrained profile
producer can be attempted.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2FinitePhysicalCombination

open MeasureTheory
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

noncomputable def finitePhysicalCombination
    {ι : Type*} (S : Finset ι) (coeff : ι → Complex)
    (basis : ι → CompactLogTest) : CompactLogTest :=
  { test := ∑ i ∈ S, coeff i • (basis i).test
    compactSupport := by
      have hcompact :
          HasCompactSupport (∑ i ∈ S, fun x : Real =>
            (coeff i • (basis i).test) x) := by
        exact HasCompactSupport.finset_sum
          (s := S)
          (f := fun i : ι => fun x : Real =>
            (coeff i • (basis i).test) x)
          (fun i _hi => by
            simpa [SchwartzMap.smul_apply] using
              (HasCompactSupport.smul_left
                (f := fun _x : Real => coeff i)
                (f' := fun x : Real => (basis i).test x)
                (basis i).compactSupport))
      have hfun :
          (∑ i ∈ S, coeff i • (basis i).test) =
            (∑ i ∈ S, fun x : Real =>
              (coeff i • (basis i).test) x) := by
        funext x
        simp [Finset.sum_apply, SchwartzMap.smul_apply]
      rw [hfun]
      exact hcompact }

@[simp] theorem finitePhysicalCombination_apply
    {ι : Type*} (S : Finset ι) (coeff : ι → Complex)
    (basis : ι → CompactLogTest) (x : Real) :
    (finitePhysicalCombination S coeff basis).test x =
      ∑ i ∈ S, coeff i * (basis i).test x := by
  simp [finitePhysicalCombination, SchwartzMap.smul_apply]

theorem laplaceAt_finitePhysicalCombination
    {ι : Type*} (S : Finset ι) (coeff : ι → Complex)
    (basis : ι → CompactLogTest) (s : Complex) :
    laplaceAt (finitePhysicalCombination S coeff basis) s =
      ∑ i ∈ S, coeff i * laplaceAt (basis i) s := by
  unfold laplaceAt
  simp only [exponentialWeight_apply, finitePhysicalCombination_apply]
  simp_rw [Finset.mul_sum]
  rw [MeasureTheory.integral_finsetSum S]
  · apply Finset.sum_congr rfl
    intro i hi
    calc
      (∫ a : Real, Complex.exp (s * (a : Complex)) *
          (coeff i * (basis i).test a)) =
          ∫ a : Real, (Complex.exp (s * (a : Complex)) *
            (basis i).test a) * coeff i := by
        apply integral_congr_ae
        filter_upwards with a
        ring
      _ = (∫ a : Real, Complex.exp (s * (a : Complex)) *
            (basis i).test a) * coeff i := by
        exact integral_mul_const (μ := volume) (coeff i)
          (fun a : Real => Complex.exp (s * (a : Complex)) *
            (basis i).test a)
      _ = coeff i * (∫ a : Real, Complex.exp (s * (a : Complex)) *
            (basis i).test a) := by ring
  · intro i hi
    have h :=
      (SchwartzMap.integrable (μ := volume)
        (exponentialWeight (basis i) s).test).mul_const (coeff i)
    simpa [exponentialWeight_apply, mul_assoc, mul_comm, mul_left_comm] using h

end
end C1P2FinitePhysicalCombination
end Source
end ConnesWeilRH
