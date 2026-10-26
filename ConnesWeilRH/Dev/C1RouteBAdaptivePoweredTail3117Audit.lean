import ConnesWeilRH.Dev.C1RouteBAdaptivePoweredTail3117

namespace ConnesWeilRH.Source.C1RouteBAdaptivePoweredTail3117

open CC20YoshidaNearZeros C1FourPointSpectralPrefixTransport
open C1FourPointContradictionAssembly C1OrbitWindowSemiLocalGate

/-- Under the hypothetical off-line-zero premise, an actual negative span
cannot also satisfy the positive gate on that very same span. -/
theorem negative_powered_span_rejects_gate3117
    (rho : sourceNontrivialZeroSet) (hright : (1 / 2 : ℝ) < rho.1.re)
    (N : ℕ) (routeNodes : Finset ℂ) (n : ℕ) (lambda : ℝ)
    (hneg : C1SameOwnerWeil.qw (poweredFamilySpan3117 rho.1 N routeNodes n lambda) < 0) :
    ¬ orbitWindowSemiLocalGate (poweredFamilySpan3117 rho.1 N routeNodes n lambda) := by
  intro hgate
  have hg := poweredFamily_cc20_vanishes3117 rho hright N routeNodes n
  exact false_of_annihilatorDetectorSpanVector_gate_and_spectral_neg
    _ _ lambda (fullFunctionalEquationOrbitAnnihilator_vanishesOn_cc20Triple _ rho.1 hg)
    hg hgate hneg

/-- Scalar scope guard only: with lambda_n=q_n^2, geometric q_n does not
force q_n^2*(1+1/lambda_n)^2 to be small. This is not a gate counterexample. -/
theorem shrinking_coefficient_blocks_relative_decay3117 (n : ℕ) :
    4 ≤ (((1 / 2 : ℝ) ^ n) ^ 2) *
      (1 + 1 / (((1 / 2 : ℝ) ^ n) ^ 2)) ^ 2 := by
  let x : ℝ := ((1 / 2 : ℝ) ^ n) ^ 2
  have hx : 0 < x := by dsimp [x]; positivity
  change 4 ≤ x * (1 + 1 / x) ^ 2
  have hid : x * (1 + 1 / x) ^ 2 = 4 + (x - 1) ^ 2 / x := by
    field_simp
    ring
  rw [hid]
  exact le_add_of_nonneg_right (div_nonneg (sq_nonneg _) hx.le)

theorem nonpositive_floor_cannot_supply_relative_budget3117
    (ell : ℝ) (hell : ell ≤ 0) :
    ¬ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → ∀ lambda : ℝ, ell ≤ lambda →
      ((1 / 2 : ℝ) ^ n) ^ 2 < lambda ^ 2 := by
  rintro ⟨n0, h⟩
  have hf := h n0 le_rfl 0 hell
  have hp : 0 < ((1 / 2 : ℝ) ^ n0) ^ 2 := by positivity
  norm_num at hf
  exact (not_lt_of_ge hp.le) hf

theorem unit_factor_does_not_contract3117 :
    ¬ ∃ n0 : ℕ, ∀ n : ℕ, n0 ≤ n → (1 : ℝ) ^ n < 1 := by
  rintro ⟨n0, h⟩
  simpa using h n0 le_rfl

end ConnesWeilRH.Source.C1RouteBAdaptivePoweredTail3117

open ConnesWeilRH.Source.C1RouteBAdaptivePoweredTail3117

#check exists_eventual_powered_span_qw_neg3117
#print axioms poweredFamily_target3117
#print axioms poweredFamily_raw_targets3117
#print axioms poweredFamily_raw_kills3117
#print axioms poweredFamily_prefix_square_zero3117
#print axioms poweredFamily_span_prefix3117
#print axioms poweredFamily_cc20_vanishes3117
#print axioms exists_eventual_relative_tail_budget3117
#print axioms exists_eventual_powered_span_qw_neg3117
#print axioms negative_powered_span_rejects_gate3117
#print axioms shrinking_coefficient_blocks_relative_decay3117
#print axioms nonpositive_floor_cannot_supply_relative_budget3117
#print axioms unit_factor_does_not_contract3117
