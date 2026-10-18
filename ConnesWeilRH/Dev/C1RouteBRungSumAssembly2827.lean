import ConnesWeilRH.Dev.C1RouteBExteriorFiniteSumEnvelope2826

namespace ConnesWeilRH.Source.C1ExplicitSmoothSeed

theorem routeB_rung_sum_assembly2827
    {ι : Type} (s : Finset ι) (f B M : ι → ℝ)
    (hf : ∀ i ∈ s, |f i| ≤ B i)
    (hBM : ∀ i ∈ s, B i ≤ M i) :
    |Finset.sum s f| ≤ Finset.sum s M := by
  have hfinite := routeB_exterior_finite_sum_envelope2826 s f B hf
  exact hfinite.trans (Finset.sum_le_sum (fun i hi => hBM i hi))

end ConnesWeilRH.Source.C1ExplicitSmoothSeed
