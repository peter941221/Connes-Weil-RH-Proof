import ConnesWeilRH.Dev.C1SpectralWeil
import ConnesWeilRH.Dev.C1XiConjugation
import ConnesWeilRH.Dev.C1HealthyYoshidaDetector

/-!
# C1SpectralHermitianPartner - the honest off-line companion transport

The functional-equation map `rho |-> 1 - rho` reverses the centered coordinate,
but it does not conjugate it.  The Hermitian square law needs `w |-> -star w`.
This leaf constructs that partner by first transporting a zero through complex
conjugation and only then applying the functional equation.

No pairing of spectral sums is asserted here.  In particular, multiplicity
preservation and the resulting off-line residual estimate remain separate
obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace C1SpectralHermitianPartner

open CC20YoshidaNearZeros
open CC20ZetaCounting
open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open C1SpectralWeil
open C1XiConjugation
open C1HealthyYoshidaDetector

noncomputable section

/-- Complex conjugation transports a source zero to another source zero. -/
noncomputable def conjugateXiZero
    (rho : sourceNontrivialZeroSet) : sourceNontrivialZeroSet :=
  ⟨star rho.1,
    sourceNontrivialZero_of_completedRiemannXi_eq_zero (by
      rw [completedRiemannXi_conj,
        completedRiemannXi_eq_zero_of_sourceNontrivialZero rho.2]
      simp)⟩

@[simp] theorem conjugateXiZero_coe
    (rho : sourceNontrivialZeroSet) :
    (conjugateXiZero rho : Complex) = star rho.1 :=
  rfl

/-- The centered coordinate commutes with the conjugation transport. -/
theorem centeredXiCoordinate_conjugateXiZero
    (rho : sourceNontrivialZeroSet) :
    centeredXiCoordinate (conjugateXiZero rho) =
      star (centeredXiCoordinate rho) := by
  apply Complex.ext <;>
    simp [centeredXiCoordinate, conjugateXiZero_coe, Complex.star_def] <;>
    ring

/-- The Hermitian companion is the conjugated zero followed by the functional
equation involution.  Its centered coordinate is `-star w`. -/
noncomputable def hermitianPartner
    (rho : sourceNontrivialZeroSet) : sourceNontrivialZeroSet :=
  oneSubXiZero (conjugateXiZero rho)

@[simp] theorem hermitianPartner_coe
    (rho : sourceNontrivialZeroSet) :
    (hermitianPartner rho : Complex) = 1 - star rho.1 := by
  rfl

theorem centeredXiCoordinate_hermitianPartner
    (rho : sourceNontrivialZeroSet) :
    centeredXiCoordinate (hermitianPartner rho) =
      -star (centeredXiCoordinate rho) := by
  apply Complex.ext <;>
    simp [centeredXiCoordinate, hermitianPartner_coe, Complex.star_def] <;>
    ring

/-! ### The partner is an involution, and the square values are conjugate -/

theorem conjugateXiZero_involutive
    (rho : sourceNontrivialZeroSet) :
    conjugateXiZero (conjugateXiZero rho) = rho := by
  apply Subtype.ext
  simp [conjugateXiZero_coe]

theorem hermitianPartner_involutive
    (rho : sourceNontrivialZeroSet) :
    hermitianPartner (hermitianPartner rho) = rho := by
  apply Subtype.ext
  simp [hermitianPartner, conjugateXiZero_coe]

theorem spectralTerm_convolutionSquare_hermitianPartner_star
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (hmul : xiMultiplicity (hermitianPartner rho) = xiMultiplicity rho) :
    spectralTerm g.convolutionSquare (hermitianPartner rho) =
      star (spectralTerm g.convolutionSquare rho) := by
  unfold spectralTerm
  rw [hmul]
  rw [centeredXiCoordinate_hermitianPartner]
  rw [laplaceAt_convolutionSquare]
  rw [laplaceAt_convolutionSquare]
  have hcoord :
      -star (-star (centeredXiCoordinate rho)) =
        centeredXiCoordinate rho := by
    apply Complex.ext <;> simp
  rw [hcoord]
  change _ = (starRingEnd ℂ) (_ * _)
  rw [map_mul]
  rw [map_mul]
  have hmulstar :
      (starRingEnd ℂ) (xiMultiplicity rho : ℂ) =
        (xiMultiplicity rho : ℂ) := by
    simpa using map_natCast (starRingEnd ℂ) (xiMultiplicity rho)
  rw [hmulstar]
  simp only [starRingEnd_apply, star_star]
  ring

theorem spectralTerm_convolutionSquare_hermitianPartner_re_eq
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (hmul : xiMultiplicity (hermitianPartner rho) = xiMultiplicity rho) :
    (spectralTerm g.convolutionSquare (hermitianPartner rho)).re =
      (spectralTerm g.convolutionSquare rho).re := by
  rw [spectralTerm_convolutionSquare_hermitianPartner_star g rho hmul]
  simp

/-! ### Exact pair decomposition before multiplicity transport -/

theorem spectralTerm_convolutionSquare_pair_re_decomposition
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet) :
    (spectralTerm g.convolutionSquare (hermitianPartner rho) +
        spectralTerm g.convolutionSquare rho).re =
      2 * (spectralTerm g.convolutionSquare rho).re +
        ((xiMultiplicity (hermitianPartner rho) : ℝ) -
          (xiMultiplicity rho : ℝ)) *
          (CompactLogTest.laplaceAt g.convolutionSquare
            (centeredXiCoordinate rho)).re := by
  simp [spectralTerm, centeredXiCoordinate_hermitianPartner,
    laplaceAt_convolutionSquare]
  ring

#print axioms conjugateXiZero
#print axioms centeredXiCoordinate_conjugateXiZero
#print axioms hermitianPartner
#print axioms centeredXiCoordinate_hermitianPartner
#print axioms conjugateXiZero_involutive
#print axioms hermitianPartner_involutive
#print axioms spectralTerm_convolutionSquare_hermitianPartner_star
#print axioms spectralTerm_convolutionSquare_hermitianPartner_re_eq
#print axioms spectralTerm_convolutionSquare_pair_re_decomposition

end
end C1SpectralHermitianPartner
end Source
end ConnesWeilRH
