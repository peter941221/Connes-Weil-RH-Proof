import ConnesWeilRH.Dev.C1HealthyTestSpace
import ConnesWeilRH.Dev.C1SameOwnerWeil
import ConnesWeilRH.Source.CC20YoshidaCriticalContraction

/-!
# Translation invariance for the healthy C1 owner

The selected Weil value depends on a root only through its Hermitian
convolution square. Translating the root moves its two convolution factors in
opposite directions, so the square and `qw` are unchanged. Mellin/Laplace
zeros are preserved because translation only multiplies each value by a
nonzero exponential character.
-/

namespace ConnesWeilRH
namespace Source
namespace C1YoshidaTranslation

open CC20YoshidaConvolution
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaCriticalContraction.CompactLogTest

/-- Translation preserves the same-owner Weil quadratic value exactly. -/
theorem qw_translate (g : CompactLogTest) (a : Real) :
    C1SameOwnerWeil.qw
        (CC20YoshidaCriticalContraction.CompactLogTest.translate g a) =
      C1SameOwnerWeil.qw g := by
  unfold C1SameOwnerWeil.qw
  rw [CC20YoshidaCriticalContraction.CompactLogTest.translate_convolutionSquare]

/-- Translation carries a support interval to the interval shifted by the
same amount. -/
theorem translate_support_subset_Icc
    (g : CompactLogTest) {lower upper a : Real}
    (hsupport : Function.support g.test ⊆ Set.Icc lower upper) :
    Function.support
        (CC20YoshidaCriticalContraction.CompactLogTest.translate g a).test ⊆
      Set.Icc (lower + a) (upper + a) := by
  intro x hx
  have hsource : x - a ∈ Function.support g.test := by
    simpa only [CC20YoshidaCriticalContraction.CompactLogTest.translate_apply]
      using hx
  rcases hsupport hsource with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- Every finite healthy Mellin-vanishing condition is invariant under root
translation. -/
theorem vanishesOn_translate_iff
    (F : Finset CriticalVanishingPoint) (g : CompactLogTest) (a : Real) :
    CC20VanishesOn C1.healthyCC20TestSpace F
        (CC20YoshidaCriticalContraction.CompactLogTest.translate g a) ↔
      CC20VanishesOn C1.healthyCC20TestSpace F g := by
  constructor
  · intro h p hp
    have htranslated := h p hp
    rw [C1.healthyMellinReadoff,
      CC20YoshidaCriticalContraction.CompactLogTest.laplaceAt_translate]
      at htranslated
    exact (mul_eq_zero.mp htranslated).resolve_left (Complex.exp_ne_zero _)
  · intro h p hp
    have hzero := h p hp
    rw [C1.healthyMellinReadoff] at hzero
    rw [C1.healthyMellinReadoff,
      CC20YoshidaCriticalContraction.CompactLogTest.laplaceAt_translate,
      hzero, mul_zero]

end C1YoshidaTranslation
end Source
end ConnesWeilRH
