import ConnesWeilRH.Dev.C1RouteAOwnerIndexedPanel2465

/-  2466: one universal indexed owner-panel dispatcher.

The three geometric proofs 2463--2465 are exposed through one rectangle
family and one sum theorem.  This is the intended interface for the next
weighted-node/quadrature attachment. -/

namespace ConnesWeilRH.Dev

set_option linter.style.longLine false

noncomputable def ownerPanelRect_2466 (x0 x1 : ℝ) (i : Fin 30) :
    ComplexRect2427 :=
  if 0 ≤ x0 then ownerPanelRect_2463 x0 x1 i
  else if x1 ≤ 0 then ownerPanelRectLeft_2464 x0 x1 i
  else ownerPanelRectCross_2465 x0 x1 i

theorem ownerFamilyPanelMem_2466 {x0 x1 : ℝ}
    (h01 : x0 ≤ x1) (i : Fin 30) (x : ℝ)
    (hx : x ∈ Set.Icc x0 x1) :
    (ownerPanelRect_2466 x0 x1 i).Mem
      (externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
        (ownerRad_2463 i) x) := by
  by_cases hx0 : 0 ≤ x0
  · simp only [ownerPanelRect_2466, if_pos hx0]
    exact ownerFamilyPanelMem_2463 h01 hx0 i x hx
  · have hx0' : x0 ≤ 0 := le_of_not_ge hx0
    by_cases hx1 : x1 ≤ 0
    · simp only [ownerPanelRect_2466, if_neg hx0, if_pos hx1]
      exact ownerFamilyPanelMemLeft_2464 h01 hx1 i x hx
    · have hx1' : 0 ≤ x1 := le_of_not_ge hx1
      simp only [ownerPanelRect_2466, if_neg hx0, if_neg hx1]
      exact ownerFamilyPanelMemCross_2465 h01 hx0' hx1' i x hx

theorem ownerPanelMem_2466 {x0 x1 : ℝ}
    (h01 : x0 ≤ x1) (x : ℝ) (hx : x ∈ Set.Icc x0 x1) :
    (ComplexRect2427.sumFinset (ownerPanelRect_2466 x0 x1) Finset.univ).Mem
      (∑ i : Fin 30,
        externalFamilyValue2344 (ownerCoef_2463 i) (ownerMod_2463 i)
          (ownerRad_2463 i) x) := by
  exact sumPanelMem_2459 (ownerPanelRect_2466 x0 x1)
    (fun i x hx => ownerFamilyPanelMem_2466 h01 i x hx) x hx

end ConnesWeilRH.Dev
