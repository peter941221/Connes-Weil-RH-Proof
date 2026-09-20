import ConnesWeilRH.Dev.C1G8R0OrbitGeometry
import ConnesWeilRH.Dev.C1OrbitFiniteSignBudget
import ConnesWeilRH.Dev.C1P2BilateralProfileExit

/-!
# P2 signed compensation budget

This leaf names the remaining producer obligation after the pointwise-profile
shortcut has been ruled out.  It is an exact positive-credit minus
negative-deficit decomposition of the same finite visible-prime aggregate;
it does not add a sign assumption or change the owner.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2SignedBudget

open C1G8R0OrbitGeometry
open C1OrbitFiniteSignBudget
open C1OrbitWindowSemiLocalGate
open C1P2BilateralProfile
open C1P2BilateralProfileExit
open C1SameOwnerWeil
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open scoped BigOperators

noncomputable section

def signedProfileTerm (g : CompactLogTest) (n : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
    (bilateralProfile g.convolutionSquare (Real.log n)).re

def signedProfileCredit (g : CompactLogTest) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, max 0 (signedProfileTerm g n)

def signedProfileDeficit (g : CompactLogTest) (S : Finset ℕ) : ℝ :=
  ∑ n ∈ S, max 0 (-signedProfileTerm g n)

theorem sum_signedProfileTerm_eq_credit_sub_deficit
    (g : CompactLogTest) (S : Finset ℕ) :
    (∑ n ∈ S, signedProfileTerm g n) =
      signedProfileCredit g S - signedProfileDeficit g S := by
  unfold signedProfileCredit signedProfileDeficit
  calc
    (∑ n ∈ S, signedProfileTerm g n) =
      ∑ n ∈ S,
          (max 0 (signedProfileTerm g n) -
            max 0 (-signedProfileTerm g n)) := by
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : 0 ≤ signedProfileTerm g n
      · rw [max_eq_right h, max_eq_left (neg_nonpos.mpr h)]
        ring
      · have hn : signedProfileTerm g n ≤ 0 := le_of_not_ge h
        rw [max_eq_left hn, max_eq_right (neg_nonneg.mpr hn)]
        ring
    _ = (∑ n ∈ S, max 0 (signedProfileTerm g n)) -
        ∑ n ∈ S, max 0 (-signedProfileTerm g n) := by
      rw [Finset.sum_sub_distrib]

theorem orbitWindowSemiLocalGate_iff_signedBudget
    {rho : sourceNontrivialZeroSet} {g : CompactLogTest}
    (geometry : OrbitG8Geometry rho g) :
    orbitWindowSemiLocalGate g ↔
      archimedeanTerm g.convolutionSquare +
          signedProfileCredit g
            (Finset.range
              (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)) ≤
        signedProfileDeficit g
          (Finset.range
            (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1)) := by
  rw [orbitWindowSemiLocalGate_iff_finiteRangeBilateralProfile geometry]
  have hsum := sum_signedProfileTerm_eq_credit_sub_deficit g
    (Finset.range
      (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1))
  have hterm :
      (∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          ArithmeticFunction.vonMangoldt n * (1 / Real.sqrt (n : ℝ)) *
            (bilateralProfile g.convolutionSquare (Real.log n)).re) =
        ∑ n ∈ Finset.range
          (Nat.ceil (Real.exp (2 * ((geometry.orbitIndex + 2 : Nat) : Real))) + 1),
          signedProfileTerm g n := by
    rfl
  constructor <;> intro h <;> linarith [hsum, hterm]

end
end C1P2SignedBudget
end Source
end ConnesWeilRH
