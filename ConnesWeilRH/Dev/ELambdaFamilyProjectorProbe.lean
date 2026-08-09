import ConnesWeilRH.Source.AnalyticCore
import ConnesWeilRH.Source.CC20YoshidaMellin
import ConnesWeilRH.Source.AnalyticCoreBase
import ConnesWeilRH.Dev.SchwartzAmbientOwnerProbe
import ConnesWeilRH.Source.CC20Concrete.CCM24LogRadialSupport
import ConnesWeilRH.Source.CC20Concrete.CCM24HardyTitchmarsh
import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
import ConnesWeilRH.Dev.ELambdaFamilyMonotoneProbe

/-!
# Lambda-monotone projector family: star-projections compose along the antitone order

`ELambdaFamilyMonotoneProbe` (850) proved the closed-subspace FAMILY
`E_λ` is antitone in `λ`.  Task 3's continuation ("the λ-monotone projector
spectral bound") needs the corresponding fact one level up: the *orthogonal
star-projections* of nested subspaces obey the projector inverse-order identity

    `V ⊆ W ⟹  P_W ∘ P_V = P_V`      (range(projector onto smaller) ⊆ the bigger one)

This module proves that identity once for a general complete complex inner
product space (importing only `Submodule.starProjection_eq_self_iff`), then
instantiates it on the concrete `cc20GlobalLogCrossingL2` radial / fourier /
sonin families.  It is the honest algebra backbone of 846's "λ-monotone
projector family": 850 gave the subspace antitone, this gives the
projector-folded identity those inclusions force.

The identity does NOT prove `Summable ‖factor λ‖²` on its own — it is the
order side (a projector family closed under folding).  RH is NOT claimed.
Zero `sorry`; `#print axioms` stays `[propext, Classical.choice, Quot.sound]`.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace ELambdaProjector

open MeasureTheory Set
open ELambdaMonotone
open ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSProjectionTrace
universe u

/-- The projector inverse-order identity: if `W₁ ≤ W₂` as closed subspaces,
then the projection onto the LARGER `W₂` fixes the projection onto the smaller
`W₁`, i.e. `P_W₂ ∘ P_W₁ = P_W₁`.

Meaning: containment `W₁ ⊆ W₂`, so a vector already in `W₁` is unchanged by
further projecting onto `W₂`; hence `P_W₂` acts as the identity on `range P_W₁`. -/
lemma starProjection_comp_of_le
    {E : Type u} {𝕜 : Type*}
    [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [CompleteSpace E]
    (W₁ W₂ : Submodule 𝕜 E)
    [W₁.HasOrthogonalProjection] [W₂.HasOrthogonalProjection]
    (hcast : W₁ ≤ W₂) :
    W₂.starProjection ∘L W₁.starProjection = W₁.starProjection := by
  apply ContinuousLinearMap.ext
  intro n
  rw [ContinuousLinearMap.comp_apply]
  exact
    (Submodule.starProjection_eq_self_iff (K := W₂) (v := W₁.starProjection n)).mpr
      (hcast (Submodule.starProjection_apply_mem W₁ n))

/-- Concrete radial family: `λ_a ≤ λ_b` gives `P_{λ_a} ∘ P_{λ_b} = P_{λ_b}`.
The smaller-`λ` subspace is the LARGER (antitone), so the bigger-`λ`
(smaller-subspace) projector is a fixed point of the smaller-`λ` projector. -/
lemma radialProjector_comp_of_le
    (lambda_a : CCM24SoninScale) {lambda_b : CCM24SoninScale}
    (hle : lambda_a.1 ≤ lambda_b.1) :
    ccm24LogRadialSupportProjection lambda_a ∘L
        ccm24LogRadialSupportProjection lambda_b =
      ccm24LogRadialSupportProjection lambda_b := by
  unfold ccm24LogRadialSupportProjection
  apply starProjection_comp_of_le
  exact logRadialSubspace_antitone lambda_a hle

/-- Sanity instance: at `λ_a = 1 ≤ λ_b = 2` the projector composition
collapses to the bigger-`λ` (smaller-subspace) projector. -/
example :
    ccm24LogRadialSupportProjection (⟨1, by norm_num⟩ : CCM24SoninScale) ∘L
        ccm24LogRadialSupportProjection (⟨2, by norm_num⟩ : CCM24SoninScale) =
      ccm24LogRadialSupportProjection (⟨2, by norm_num⟩ : CCM24SoninScale) := by
  exact radialProjector_comp_of_le (⟨1, by norm_num⟩ : CCM24SoninScale) (by norm_num)

/-- Concrete Fourier-support family: `λ_a ≤ λ_b` gives
`P_λa ∘ P_λb = P_λb` (fourier antitone propagates to the projectors). -/
lemma fourierProjector_comp_of_le
    (lambda_a : CCM24SoninScale) {lambda_b : CCM24SoninScale}
    (hle : lambda_a.1 ≤ lambda_b.1) :
    sourceFourierSupportProjection lambda_a ∘L
        sourceFourierSupportProjection lambda_b =
      sourceFourierSupportProjection lambda_b := by
  unfold sourceFourierSupportProjection
  apply starProjection_comp_of_le
  exact fourierSubspace_antitone lambda_a hle

/-- Concrete Sonin-support family: `λ_a ≤ λ_b` gives
`P_λa ∘ P_λb = P_λb` (sonin antitone preserved). -/
lemma soninProjector_comp_of_le
    (lambda_a : CCM24SoninScale) {lambda_b : CCM24SoninScale}
    (hle : lambda_a.1 ≤ lambda_b.1) :
    sourceSoninProjection lambda_a ∘L
        sourceSoninProjection lambda_b =
      sourceSoninProjection lambda_b := by
  unfold sourceSoninProjection
  apply starProjection_comp_of_le
  exact soninSubspace_antitone lambda_a hle

end ELambdaProjector
end CC20Concrete
end Source
end ConnesWeilRH