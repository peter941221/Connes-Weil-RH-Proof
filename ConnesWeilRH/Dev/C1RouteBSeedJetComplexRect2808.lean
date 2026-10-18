import ConnesWeilRH.Dev.C1RouteBRealToComplexRect2806
import ConnesWeilRH.Dev.C1SeedIntervalJet2734

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

open ConnesWeilRH.Dev

noncomputable def seedJetComplexRect2808 (B : RealInterval2429) (n : ℕ) : ComplexRect2427 :=
  { reLo := (seedTransitionJetInterval2734 B n).lo
    reHi := (seedTransitionJetInterval2734 B n).hi
    imLo := 0
    imHi := 0 }

theorem seedJetComplexRect_mem2808 (B : RealInterval2429) (n : ℕ)
    (hlo : 0 < B.lo) (hhi : B.hi < 1) {x : ℝ} (hx : B.Mem x) :
    (seedJetComplexRect2808 B n).Mem
      ((iteratedDeriv n Real.smoothTransition x : ℝ) : ℂ) := by
  apply complexRect_mem_of_real_bounds2806
  · exact (seedTransitionJetInterval_mem2734 B n hlo hhi hx).1
  · exact (seedTransitionJetInterval_mem2734 B n hlo hhi hx).2
  · norm_num [seedJetComplexRect2808]
  · norm_num [seedJetComplexRect2808]

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
