import ConnesWeilRH.Dev.C1XiCenterTwoGamma

/-!
# C1XiCenterTwoGammaSummedKernel - finite prefix and tail owner

The Gamma_R profile family is useful for sign estimates only after its
constant term and its infinite tail are kept in the same owner.  This module
exposes that decomposition without adding a sign assumption.  The tail is
the genuine shifted series supplied by the already-proved absolute
sum-integrability theorem.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiCenterTwoGammaSummedKernel

open MeasureTheory
open Set
open Filter
open C1SameOwnerWeil
open C1XiCenterTwoGamma
open CCM25Concrete.CompactLogConvolution
open scoped Interval Topology

noncomputable section

/-- The full positive-variable integral of one paired Gamma_R profile. -/
noncomputable def gammaRArchProfileIntegral
    (F : CompactLogTest) (n : Nat) : Complex :=
  ∫ y : Real in Ioi (0 : Real), gammaRArchProfileTerm F n y

/-- The profile tail beginning at index `N`, with the shift kept explicit. -/
noncomputable def gammaRArchProfileTail
    (F : CompactLogTest) (N : Nat) : Complex :=
  ∑' n : Nat, gammaRArchProfileIntegral F (n + N)

private theorem summable_gammaRArchProfileIntegral
    (F : CompactLogTest) :
    Summable (gammaRArchProfileIntegral F) := by
  have hmajor := summable_integralOn_norm_gammaRArchProfileTerm F
  apply hmajor.of_norm_bounded
  intro n
  exact norm_integral_le_integral_norm _

/-- A norm-valued owner for the shifted profile tail.  Keeping this as a
real-valued series lets later sign estimates bound the tail before taking
real parts, without reopening the sum-integral exchange. -/
noncomputable def gammaRArchProfileTailNorm
    (F : CompactLogTest) (N : Nat) : Real :=
  ∑' n : Nat, ‖gammaRArchProfileIntegral F (n + N)‖

/-- The complex shifted tail is bounded by its absolute profile series. -/
theorem norm_gammaRArchProfileTail_le_tailNorm
    (F : CompactLogTest) (N : Nat) :
    ‖gammaRArchProfileTail F N‖ ≤ gammaRArchProfileTailNorm F N := by
  unfold gammaRArchProfileTail gammaRArchProfileTailNorm
  apply norm_tsum_le_tsum_norm
  exact (summable_nat_add_iff N).2 (summable_gammaRArchProfileIntegral F).norm

/-- The absolute profile tail itself tends to zero. -/
theorem tendsto_gammaRArchProfileTailNorm_zero
    (F : CompactLogTest) :
    Tendsto (fun N : Nat => gammaRArchProfileTailNorm F N)
      atTop (𝓝 (0 : Real)) := by
  have hsum := (summable_gammaRArchProfileIntegral F).norm
  have hpartial := hsum.tendsto_sum_tsum_nat
  have hsplit (N : Nat) :
      gammaRArchProfileTailNorm F N =
        (∑' n : Nat, ‖gammaRArchProfileIntegral F n‖) -
          ∑ n ∈ Finset.range N, ‖gammaRArchProfileIntegral F n‖ := by
    unfold gammaRArchProfileTailNorm
    rw [← hsum.sum_add_tsum_nat_add N]
    ring
  rw [show (fun N : Nat => gammaRArchProfileTailNorm F N) =
      (fun N => (∑' n : Nat, ‖gammaRArchProfileIntegral F n‖) -
        ∑ n ∈ Finset.range N, ‖gammaRArchProfileIntegral F n‖) by
    funext N
    exact hsplit N]
  have hlim :=
    (tendsto_const_nhds.sub hpartial :
      Tendsto
        (fun N : Nat => (∑' n : Nat, ‖gammaRArchProfileIntegral F n‖) -
          ∑ n ∈ Finset.range N, ‖gammaRArchProfileIntegral F n‖)
        atTop (𝓝 ((∑' n : Nat, ‖gammaRArchProfileIntegral F n‖) -
          ∑' n : Nat, ‖gammaRArchProfileIntegral F n‖)))
  simpa using hlim

/-- Exact finite-prefix plus shifted-tail decomposition of the archimedean
integrand integral.  This is the owner used by any later finite-kernel sign
estimate; no profile is dropped or signed termwise. -/
theorem integralOn_archimedeanIntegrand_eq_profilePrefix_add_tail
    (F : CompactLogTest) (N : Nat) :
    (∫ y : Real in Ioi (0 : Real),
      C1SameOwnerWeil.archimedeanIntegrand F y) =
      (∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n) +
        gammaRArchProfileTail F N := by
  have hsum := summable_gammaRArchProfileIntegral F
  rw [integralOn_archimedeanIntegrand_eq_tsum F]
  unfold gammaRArchProfileTail
  simpa only [gammaRArchProfileIntegral] using
    (hsum.sum_add_tsum_nat_add N).symm

/-- The shifted Gamma_R profile tail vanishes at infinity. -/
theorem tendsto_gammaRArchProfileTail_zero
    (F : CompactLogTest) :
    Tendsto (fun N : Nat => gammaRArchProfileTail F N)
      atTop (𝓝 (0 : Complex)) := by
  have hsum := summable_gammaRArchProfileIntegral F
  have hpartial := hsum.tendsto_sum_tsum_nat
  have hsplit (N : Nat) :
      gammaRArchProfileTail F N =
        (∑' n : Nat, gammaRArchProfileIntegral F n) -
          ∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n := by
    unfold gammaRArchProfileTail
    rw [← hsum.sum_add_tsum_nat_add N]
    ring
  rw [show (fun N : Nat => gammaRArchProfileTail F N) =
      (fun N => (∑' n : Nat, gammaRArchProfileIntegral F n) -
        ∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n) by
    funext N
    exact hsplit N]
  have hlim :=
    (tendsto_const_nhds.sub hpartial :
      Tendsto
        (fun N : Nat => (∑' n : Nat, gammaRArchProfileIntegral F n) -
          ∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n)
        atTop (𝓝 ((∑' n : Nat, gammaRArchProfileIntegral F n) -
          ∑' n : Nat, gammaRArchProfileIntegral F n)))
  simpa using hlim

/-- The same prefix/tail decomposition after adding the archimedean
constant term. -/
theorem archimedeanTerm_eq_constant_add_profilePrefix_add_tail_re
    (F : CompactLogTest) (N : Nat) :
    C1SameOwnerWeil.archimedeanTerm F =
      ((((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant : Real) : Complex) *
          F.test 0).re) +
        (∑ n ∈ Finset.range N, gammaRArchProfileIntegral F n).re +
        (gammaRArchProfileTail F N).re := by
  unfold C1SameOwnerWeil.archimedeanTerm
  rw [integralOn_archimedeanIntegrand_eq_profilePrefix_add_tail F N]
  simp only [Complex.add_re]
  ring

end
end C1XiCenterTwoGammaSummedKernel
end Source
end ConnesWeilRH
