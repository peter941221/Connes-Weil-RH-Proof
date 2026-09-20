import ConnesWeilRH.Dev.C1P2PhysicalPointBump
import ConnesWeilRH.Dev.C1PsiLinearity

/-!
# Two-point physical interpolation for the P2 profile

This is the first finite-dimensional physical interpolation layer.  Two
disjointly sampled log points can receive arbitrary complex values by adding
two compact-log bumps.  The theorem deliberately makes no Mellin, health, or
sign claim; it is the local physical part of a future constrained correction.
-/

namespace ConnesWeilRH
namespace Source
namespace C1P2TwoPointPhysicalInterpolation

open CCM25Concrete.CompactLogConvolution
open C1P2PhysicalPointBump
open C1PsiLinearity

noncomputable section

noncomputable def testSmul (c : Complex) (f : CompactLogTest) : CompactLogTest :=
  { test := c • f.test
    compactSupport := f.compactSupport.smul_left (f := fun _ : Real => c) }

@[simp] theorem testSmul_apply (c : Complex) (f : CompactLogTest) (x : Real) :
    (testSmul c f).test x = c * f.test x := by
  rfl

noncomputable def twoPointCombination
    (c₁ c₂ : Complex) (f₁ f₂ : CompactLogTest) : CompactLogTest :=
  testAdd (testSmul c₁ f₁) (testSmul c₂ f₂)

theorem twoPointCombination_apply
    (c₁ c₂ : Complex) (f₁ f₂ : CompactLogTest) (x : Real)
    (h₁ : f₁.test x = 1) (h₂ : f₂.test x = 0) :
    (twoPointCombination c₁ c₂ f₁ f₂).test x = c₁ := by
  simp [twoPointCombination, testSmul_apply, h₁, h₂]

theorem exists_twoPointPhysicalInterpolation
    {a₁ b₁ a₂ b₂ x₁ x₂ : Real}
    (h₁a : a₁ < x₁) (h₁b : x₁ < b₁)
    (h₂a : a₂ < x₂) (h₂b : x₂ < b₂)
    (h₁₂ : x₁ ∉ Set.Icc a₂ b₂)
    (h₂₁ : x₂ ∉ Set.Icc a₁ b₁)
    (c₁ c₂ : Complex) :
    ∃ g : CompactLogTest, g.test x₁ = c₁ ∧ g.test x₂ = c₂ := by
  obtain ⟨f₁, hf₁supp, hf₁⟩ :=
    exists_compactLogTest_supported_Icc_eq_one h₁a h₁b
  obtain ⟨f₂, hf₂supp, hf₂⟩ :=
    exists_compactLogTest_supported_Icc_eq_one h₂a h₂b
  have h₂at₁ : f₂.test x₁ = 0 := by
    by_contra hne
    exact h₁₂ (hf₂supp (Function.mem_support.mpr hne))
  have h₁at₂ : f₁.test x₂ = 0 := by
    by_contra hne
    exact h₂₁ (hf₁supp (Function.mem_support.mpr hne))
  refine ⟨twoPointCombination c₁ c₂ f₁ f₂, ?_, ?_⟩
  · exact twoPointCombination_apply c₁ c₂ f₁ f₂ x₁ hf₁ h₂at₁
  · have hleft := twoPointCombination_apply c₂ c₁ f₂ f₁ x₂ hf₂ h₁at₂
    simpa [twoPointCombination, add_comm] using hleft

end
end C1P2TwoPointPhysicalInterpolation
end Source
end ConnesWeilRH
