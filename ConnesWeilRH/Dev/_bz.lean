import ConnesWeilRH.Dev.Wall14PlateauFDeriv

namespace ConnesWeilRH.Source.Dev.Wall14Plateau

open MeasureTheory Filter Set
open scoped Topology

noncomputable def bd (u : ℝ) : ℝ := deriv (fun w : ℝ => bumpReal w) u

-- derivative is 0 on the open plateau |u| < 9/10
theorem bd_plateau_zero (u : ℝ) (hu : |u| < (9 / 10 : ℝ)) : bd u = 0 := by
  have h_ev : (fun x : ℝ => bumpReal x) =ᶠ[𝓝 u] (fun _ : ℝ => (1 : ℝ)) := by
    rw [Filter.EventuallyEq]
    have hset : Set.Ioo (-(9 / 10 : ℝ)) (9 / 10 : ℝ) ∈ 𝓝 u := by
      exact isOpen_Ioo.mem_nhds (abs_lt.mp hu)
    filter_upwards [hset] with x hx
    have hxa : |x| < (9/10 : ℝ) := abs_lt.mpr hx
    exact bumpReal_eq_one_of_abs_le x (le_of_lt hxa)
  have hder : HasDerivAt (fun x : ℝ => bumpReal x) (0 : ℝ) u := by
    simpa using ((hasDerivAt_const u (1 : ℝ)).congr_of_eventuallyEq h_ev)
  unfold bd
  exact hder.deriv

-- derivative is 0 on the outer region |u| > 1
theorem bd_outer_zero (u : ℝ) (hu : (1:ℝ) < |u|) : bd u = 0 := by
  have h_ev : (fun x : ℝ => bumpReal x) =ᶠ[𝓝 u] (fun _ : ℝ => (0 : ℝ)) := by
    rw [Filter.EventuallyEq]
    have hset : {x : ℝ | (1:ℝ) < |x|} ∈ 𝓝 u := by
      exact (isOpen_lt continuous_const continuous_abs).mem_nhds hu
    filter_upwards [hset] with x hx
    exact bumpReal_eq_zero_of_abs_ge x (le_of_lt hx)
  have hder : HasDerivAt (fun x : ℝ => bumpReal x) (0 : ℝ) u := by
    simpa using ((hasDerivAt_const u (0 : ℝ)).congr_of_eventuallyEq h_ev)
  unfold bd
  exact hder.deriv

-- bd is odd
theorem bd_neg (u : ℝ) : bd (-u) = -bd u := by
  unfold bd
  exact deriv_bumpReal_neg u

-- expansion: bumpFderiv x = ∫_R bumpReal t * bd(x - t) dt
theorem bumpFderiv_eq_integral (x : ℝ) :
    bumpFderiv x = ∫ t : ℝ, bumpReal t * bd (x - t) := by
  unfold bumpFderiv
  rw [convolution_def]
  simp [Lmul, bd]

end ConnesWeilRH.Source.Dev.Wall14Plateau
