import ConnesWeilRH.Dev.C1XiArithmeticPoleRemainder
import ConnesWeilRH.Dev.C1XiArithmeticPrimePowerAssembly

/-!
# C1XiArithmeticFiniteHeightLedger - one finite-height boundary owner

This module assembles the three finite-height arithmetic pieces on one
right-hand sequence `c k -> 1+`: the elementary pole, the Gamma_R factor, and
a finite prime-power truncation.  It does not provide the full von Mangoldt
boundary or the arithmetic/spectral equality.
-/

namespace ConnesWeilRH
namespace Source
namespace C1XiArithmeticFiniteHeightLedger

open MeasureTheory
open Set
open Filter
open Complex
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1XiVerticalFunctional
open C1XiArithmeticIntervalReadback
open C1XiArithmeticPoleBoundary
open C1XiArithmeticPoleRemainder
open C1XiArithmeticPrimePowerAssembly
open scoped BigOperators Interval Topology

noncomputable section

/-- The three arithmetic interval terms evaluated on one boundary sequence. -/
noncomputable def finiteHeightArithmeticBoundaryLedgerTerm
    (F : CompactLogTest) (N : Nat) (T : Real)
    (hcontract : ElementaryPoleSingularRemainderBoundaryContract F T)
    (k : Nat) : Complex :=
  (∫ t : Real in (-T)..T,
      elementaryPoleIntegrand F (hcontract.c k) t) +
    (∫ t : Real in (-T)..T,
      gammaRIntegrand F (hcontract.c k) t) +
    ∫ t : Real in (-T)..T,
      finiteArithmeticPrimePowerIntegrand F N (hcontract.c k) t

/-- The corresponding finite-height boundary ledger value. -/
noncomputable def finiteHeightArithmeticBoundaryLedgerValue
    (F : CompactLogTest) (N : Nat) (T : Real)
    (hcontract : ElementaryPoleSingularRemainderBoundaryContract F T) : Complex :=
  ((∫ t : Real in (-T)..T,
      elementaryPoleRegularIntegrand F 1 t) +
      (-(Real.pi : Complex) * Complex.I) *
        symmetrizedLaplaceWeight F (verticalPoint 1 0) +
      hcontract.remainderBoundaryValue) +
    (∫ t : Real in (-T)..T, gammaRIntegrand F 1 t) +
    ∫ t : Real in (-T)..T,
      finiteArithmeticPrimePowerIntegrand F N 1 t

/-- The pole, Gamma_R, and finite prime-power terms converge together because
they use exactly the same sequence carried by the pole remainder contract. -/
theorem tendsto_finiteHeightArithmeticBoundaryLedgerTerm
    (F : CompactLogTest) (N : Nat) (T : Real) (hT : 0 < T)
    (hcontract : ElementaryPoleSingularRemainderBoundaryContract F T) :
    Tendsto
      (fun k : Nat =>
        finiteHeightArithmeticBoundaryLedgerTerm F N T hcontract k)
      atTop
      (𝓝 (finiteHeightArithmeticBoundaryLedgerValue F N T hcontract)) := by
  have hc_within : Tendsto hcontract.c atTop (𝓝[>] (1 : Real)) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨hcontract.c_tendsto_one,
      Filter.Eventually.of_forall (fun k => hcontract.c_gt_one k)⟩
  have hpole :=
    tendsto_elementaryPoleIntegrand_intervalIntegral_of_remainderBoundaryContract
      F T hT hcontract
  have hgamma :=
    (tendsto_gammaRIntegrand_intervalIntegral_c_to_one F T).comp hc_within
  have hprime :=
    (tendsto_finiteArithmeticPrimePowerIntegrand_intervalIntegral_c_to_one
      F N T hT.le).comp hc_within
  have hsum := (hpole.add hgamma).add hprime
  simpa only [finiteHeightArithmeticBoundaryLedgerTerm,
    finiteHeightArithmeticBoundaryLedgerValue, Function.comp_apply] using hsum

end
end C1XiArithmeticFiniteHeightLedger
end Source
end ConnesWeilRH
