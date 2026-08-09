import ConnesWeilRH.Source.CCM25Concrete.CCM24FiniteSCausalMarkovRawBase

namespace ConnesWeilRH
namespace Dev
namespace Gate3UDichotomy

open ConnesWeilRH.Source.CCM25Concrete
open ConnesWeilRH.Source.CC20Concrete
open CCM24FiniteSCausalMarkovRawBase
open CCM24FiniteSPhysicalLeakage
open CCM24FiniteSProjectionTrace

/-- The degenerate (empty-terms) prime-power family. -/
noncomputable def emptyFamily : FinitePrimePowerFamily where
  terms := ∅
  prime := by
    intro pm hp
    simp at hp
  exponent_ne_zero := by
    intro pm hp
    simp at hp

theorem emptyFamily_visiblePrimes : emptyFamily.visiblePrimes = [] := by
  simp [emptyFamily, FinitePrimePowerFamily.visiblePrimes]

theorem leakage_zero_of_visiblePrimes_nil
    (lambda : CCM24SoninScale) (family : FinitePrimePowerFamily)
    (hvisible : family.visiblePrimes = []) :
    sourcePhysicalCoframeLeakage lambda family = 0 :=
  sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil
    lambda family hvisible

theorem emptyFamily_leakage_zero (lambda : CCM24SoninScale) :
    sourcePhysicalCoframeLeakage lambda emptyFamily = 0 :=
  sourcePhysicalCoframeLeakage_eq_zero_of_visiblePrimes_nil
    lambda emptyFamily emptyFamily_visiblePrimes

def gate3UDichotomyObligation (lambda : CCM24SoninScale) : Prop :=
  ∀ family : FinitePrimePowerFamily,
    sourcePhysicalCoframeLeakage lambda family = 0 →
      family.visiblePrimes = []

end Gate3UDichotomy
end Dev
end ConnesWeilRH
