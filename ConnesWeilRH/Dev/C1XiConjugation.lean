import ConnesWeilRH.Source.CC20ZetaCounting
import Mathlib.Analysis.Analytic.Order
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.Deriv.Star

namespace ConnesWeilRH
namespace Source
namespace C1XiConjugation

open Complex
open MeasureTheory
open CC20ZetaCounting
open HurwitzZeta
open scoped ComplexConjugate

noncomputable section

private theorem hurwitzEvenFEPair_zero_f_modif_real (x : ℝ) :
    star ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
  simp only [WeakFEPair.f_modif, HurwitzZeta.hurwitzEvenFEPair]
  simp only [Pi.add_apply]
  change (starRingEnd ℂ) (_ + _) = _
  rw [map_add (starRingEnd ℂ)]
  congr 1
  · by_cases h : x ∈ Set.Ioi (1 : ℝ) <;>
      simp [Set.indicator, h]
  · by_cases h : x ∈ Set.Ioo (0 : ℝ) 1 <;>
      simp [Set.indicator, h]

theorem completedRiemannZeta0_conj (z : ℂ) :
    completedRiemannZeta₀ (star z) = star (completedRiemannZeta₀ z) := by
  unfold completedRiemannZeta₀ completedHurwitzZetaEven₀
  unfold WeakFEPair.Λ₀
  unfold mellin
  rw [star_div₀]
  norm_num
  rw [← integral_conj]
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x hx
  simp only [starRingEnd_apply]
  change _ = (starRingEnd ℂ) (_ * _)
  rw [map_mul (starRingEnd ℂ)]
  change _ = conj ((x : ℂ) ^ (z / 2 - 1)) * conj _
  have hcpow : conj ((x : ℂ) ^ (z / 2 - 1)) =
      (x : ℂ) ^ (star z / 2 - 1) := by
    have hcpow' := Complex.cpow_conj (x : ℂ) (z / 2 - 1) (by
      rw [Complex.arg_ofReal_of_nonneg (le_of_lt hx)]
      exact ne_of_lt Real.pi_pos)
    have htwo : (starRingEnd ℂ) (2 : ℂ) = 2 := by
      exact Complex.conj_ofNat 2
    convert hcpow'.symm using 1 <;> simp [Complex.conj_ofReal, htwo]
  have hreal : (starRingEnd ℂ) ((HurwitzZeta.hurwitzEvenFEPair 0).f_modif x) =
      (HurwitzZeta.hurwitzEvenFEPair 0).f_modif x := by
    simpa only [starRingEnd_apply] using hurwitzEvenFEPair_zero_f_modif_real x
  rw [hcpow, hreal]

theorem completedRiemannXi_conj (z : ℂ) :
    completedRiemannXi (star z) = star (completedRiemannXi z) := by
  unfold completedRiemannXi
  rw [completedRiemannZeta0_conj]
  simp

/-! ### Conjugation-reflection and the vanishing order -/

/-- A single conjugate-companion leg commutes with one derivative: differentiating
`z \mapsto conj (f (conj z))` is the conjugate-companion of `deriv f`.  This is
the anti-holomorphic analogue of the chain rule; a single conjugation is
anti-conformal, so two of them cancel. -/
private theorem deriv_conjConj_commutes {f : ℂ → ℂ} :
    deriv ((fun z => conj (f (conj z)))) = fun z => conj ((deriv f) (conj z)) := by
  have hlhs : (fun z => conj (f (conj z))) = (conj ∘ f ∘ conj) := by
    ext z; simp only [Function.comp_apply, Function.comp_def]
  rw [hlhs, deriv_conj_conj (f := f)]
  ext z; simp only [Function.comp_apply, Function.comp_def]

/-- Complex conjugation commutes with iterated differentiation through the
conjugate-companion map `z \mapsto conj (f (conj z))`: its `n`-th derivative is
the conjugate-companion of the `n`-th derivative of `f`. -/
theorem iteratedDeriv_conjConj {f : ℂ → ℂ} (n : ℕ) :
    deriv^[n] (fun z => conj (f (conj z))) = fun z => conj (deriv^[n] f (conj z)) := by
  induction n with
  | zero => ext z; simp only [Function.iterate_zero]; rfl
  | succ k hk =>
      ext z
      calc deriv^[Nat.succ k] (fun w => conj (f (conj w))) z
          _ = deriv ((deriv^[k] (fun w => conj (f (conj w))))) z := by
              rw [Function.iterate_succ_apply' (n := k) (x := fun w => conj (f (conj w)))]
          _ = deriv ((fun w => conj ((deriv^[k] f) (conj w)))) z := by rw [hk]
          _ = (fun z0 => conj ((deriv (deriv^[k] f)) (conj z0))) z := by
              rw [deriv_conjConj_commutes (f := deriv^[k] f)]
          _ = conj ((deriv^[Nat.succ k] f) (conj z)) := by
              simp [Function.iterate_succ_apply' (n := k) (f := deriv) (x := f)]

/-- The completed xi function is a fixed point of the conjugate-companion map:
conjugating the input and output returns the same value. -/
theorem completedRiemannXi_conjConj_eq :
    (fun z => star (completedRiemannXi (star z))) = completedRiemannXi := by
  funext z
  have h := completedRiemannXi_conj (star z)
  simpa [star_star] using h.symm

/-- The iterated derivatives of the completed xi function commute with complex
conjugation of the point: evaluating the `n`-th derivative at `\overline{z₀}` is
the conjugate of evaluating it at `z₀`. -/
theorem iteratedDeriv_completedRiemannXi_conj (n : ℕ) (z₀ : ℂ) :
    iteratedDeriv n completedRiemannXi (star z₀) =
      star (iteratedDeriv n completedRiemannXi z₀) := by
  rw [iteratedDeriv_eq_iterate]
  -- xi is a fixed point of the conjugation companion.  Push that form into the
  -- LHS head ONLY: after `rw [iteratedDeriv_eq_iterate]` the LHS's xi is the
  -- first occurrence, so a one-sided rewrite leaves the RHS single-conjugated.
  have hfix : completedRiemannXi = fun w => conj (completedRiemannXi (conj w)) := by
    simpa using completedRiemannXi_conjConj_eq.symm
  nth_rewrite 1 [hfix]
  rw [iteratedDeriv_conjConj (f := completedRiemannXi)]
  simp

/-! ### Vanishing-order invariance -/

private theorem star_zero_iff {x : ℂ} : star x = 0 ↔ x = 0 := by
  constructor
  · intro hx; simpa [star_star, star_zero] using congrArg (fun z => star z) hx
  · intro hx; rw [hx, star_zero]

/-- **W4a core.**  The vanishing order of the completed xi function is invariant
under complex conjugation of the point.  This lifts from `xiMultiplicity_oneSub`'s
functional-equation case: whereas `z \mapsto 1 - z` is holomorphic and preserves
the order by the chain rule, its conjugate partner `z \mapstar z` is only
anti-holomorphic, so the invariance must go through differentiation commutation. -/
theorem analyticOrderAt_completedRiemannXi_conj_symmetric (z₀ : ℂ) :
    analyticOrderAt completedRiemannXi (star z₀) = analyticOrderAt completedRiemannXi z₀ := by
  have hana0 : AnalyticAt ℂ completedRiemannXi z₀ := differentiable_completedRiemannXi.analyticAt z₀
  have hanac : AnalyticAt ℂ completedRiemannXi (star z₀) := differentiable_completedRiemannXi.analyticAt (star z₀)
  apply ENat.eq_of_forall_natCast_le_iff fun n ↦ ?_
  rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hanac,
      natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hana0]
  constructor
  · intro h i hi; have hh := h i hi; rw [iteratedDeriv_completedRiemannXi_conj i z₀] at hh; exact star_zero_iff.1 hh
  · intro h i hi; rw [iteratedDeriv_completedRiemannXi_conj i z₀]; exact star_zero_iff.2 (h i hi)

#print axioms completedRiemannZeta0_conj
#print axioms completedRiemannXi_conj
#print axioms iteratedDeriv_conjConj
#print axioms completedRiemannXi_conjConj_eq
#print axioms iteratedDeriv_completedRiemannXi_conj
#print axioms analyticOrderAt_completedRiemannXi_conj_symmetric

end
end C1XiConjugation
end Source
end ConnesWeilRH
