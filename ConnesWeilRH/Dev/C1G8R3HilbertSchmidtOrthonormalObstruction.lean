import ConnesWeilRH.Dev.C1G8R3LeakageOrbitEnergy
import ConnesWeilRH.Source.CC20Concrete.HilbertSchmidtIdeal

namespace ConnesWeilRH
namespace Dev

open Source
open Source.CC20Concrete
open Source.CC20YoshidaConvolution
open Source.CCM25Concrete
open Source.CCM25Concrete.CCM24FiniteSProjectionTrace
open Source.CCM25Concrete.CCM24FiniteSRootCompletedFirstJet
open Source.CCM25Concrete.CCM24UnitScaleProlateAlignment
open C1SameOwnerWeil
open scoped InnerProduct InnerProductSpace Topology

set_option autoImplicit true

local notation "Carrier" => finiteSCarrier

/-- A Hilbert--Schmidt operator has summable squared outputs on every
orthonormal sequence, not only on the basis used to present its certificate. -/
theorem summable_normSq_of_orthonormal
    {H G : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [NormedAddCommGroup G] [InnerProductSpace ℂ G]
    [CompleteSpace G]
    {ι : Type*} (basis : HilbertBasis ι ℂ H)
    (operator : H →L[ℂ] G)
    (hoperator : Summable fun i => ‖operator (basis i)‖ ^ 2)
    {v : ℕ → H} (hv : Orthonormal ℂ v) :
    Summable fun n : ℕ => ‖operator (v n)‖ ^ 2 := by
  obtain ⟨wG, basisG, hbG⟩ := exists_hilbertBasis ℂ G
  have hadjoint : Summable fun j => ‖operator.adjoint (basisG j)‖ ^ 2 :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      basis basisG operator hoperator
  obtain ⟨wH, basisH, hsubset, hbH⟩ :=
    hv.toSubtypeRange.exists_hilbertBasis_extension
  have hback : Summable fun k : wH =>
      ‖(operator.adjoint.adjoint) (basisH k)‖ ^ 2 :=
    PositiveTrace.BasisHilbertSchmidtPairData.summable_adjoint_normSq
      basisG basisH operator.adjoint hadjoint
  have hbasisH : Summable fun k : wH => ‖operator (basisH k)‖ ^ 2 := by
    simpa only [ContinuousLinearMap.adjoint_adjoint] using hback
  let embed : ℕ → wH := fun n =>
    ⟨v n, hsubset ⟨n, rfl⟩⟩
  have hembed : Function.Injective embed := by
    intro m n hmn
    apply hv.linearIndependent.injective
    exact congrArg Subtype.val hmn
  have hsub := hbasisH.comp_injective hembed
  apply hsub.congr
  intro n
  change ‖operator (basisH (embed n))‖ ^ 2 = ‖operator (v n)‖ ^ 2
  rw [hbH]

/-- A Hilbert--Schmidt certificate on any Hilbert basis would force the
ambient leakage columns to have summable squared energy on the separated
orthonormal translation orbit. The established lower bound rules this out. -/
theorem sourceRootCompletedRightCommutatorLeftLeg_not_hilbertSchmidt
    (owner : SelectedWeilSquare.SelectedWeilSquareOwner) (rho : ℂ)
    (hvalue : CompactLogTest.laplaceAt owner.sourceTest rho ≠ 0)
    {ι : Type*} (basis : HilbertBasis ι ℂ Carrier) :
    ¬ Summable (fun i =>
      ‖sourceRootCompletedRightCommutatorLeftLeg owner CCM24UnitScaleProlateAlignment.unitSoninScale
        (basis i)‖ ^ 2) := by
  intro hbasis
  have horbit := summable_normSq_of_orthonormal basis
    (sourceRootCompletedRightCommutatorLeftLeg owner CCM24UnitScaleProlateAlignment.unitSoninScale)
    hbasis (normalizedSelectedSourceTranslationOrbit_orthonormal owner rho hvalue)
  have henergy : Summable (fun n : ℕ =>
      ‖normalizedSelectedSourceTranslationLeakageColumn owner n‖ ^ 2) := by
    apply horbit.congr
    intro n
    rw [normalizedSelectedSourceTranslationLeakageColumn_eq_actual]
  exact normalizedSelectedSourceTranslationLeakageColumn_energy_not_summable
    owner rho hvalue henergy

end Dev
end ConnesWeilRH
