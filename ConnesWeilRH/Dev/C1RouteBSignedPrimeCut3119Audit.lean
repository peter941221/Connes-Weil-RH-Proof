import ConnesWeilRH.Dev.C1RouteBSignedPrimeCut3119

namespace ConnesWeilRH.Source.C1RouteBSignedPrimeCut3119

open CCM25Concrete.CompactLogConvolution C1SameOwnerWeil

theorem primeCut_zero3119 (F : CompactLogTest) : primeCut3119 F 0 = 0 := by
  simp [primeCut3119, finitePrimeTerm, finitePrimeTermComplex]

theorem remainder_at_zero3119 (F : CompactLogTest) :
    primeRemainder3119 F 0 = finitePrimeSum F := by
  rw [finitePrimeSum_eq_cut_add_remainder3119, primeCut_zero3119, zero_add]

/-- The cutoff includes its endpoint. -/
theorem primeCut_succ3119 (F : CompactLogTest) (M : ℕ) :
    primeCut3119 F (M + 1) = primeCut3119 F M + finitePrimeTerm F (M + 1) := by
  simp only [primeCut3119, Finset.sum_range_succ]

/-- Scalar guard only: nonzero omitted summands can cancel. -/
theorem nonzero_terms_can_cancel3119 :
    (1 : ℝ) ≠ 0 ∧ (-1 : ℝ) ≠ 0 ∧ (1 : ℝ) + (-1) = 0 := by norm_num

/-- Scalar guard only: a negative cut gives no sign without its remainder. -/
theorem negative_cut_does_not_determine_full_sign3119 :
    (-1 : ℝ) ≤ 0 ∧ (0 : ℝ) < (-1 + 2) := by norm_num

end ConnesWeilRH.Source.C1RouteBSignedPrimeCut3119

open ConnesWeilRH.Source.C1RouteBSignedPrimeCut3119

#check poweredFamily_full_gate3119
#check storedSpan_complete_prime_cut3119
#print axioms primeCut_eq_visible_filter3119
#print axioms finitePrimeSum_eq_cut_add_remainder3119
#print axioms full_gate_eq_cut_add_remainder3119
#print axioms gate_iff_signed_remainder_budget3119
#print axioms poweredFamily_full_gate3119
#print axioms storedSpan_support3119
#print axioms storedSpan_visible_prime_bound3119
#print axioms storedSpan_remainder_at_complete_bound3119
#print axioms storedSpan_complete_prime_cut3119
#print axioms storedSpan_full_gate3119
#print axioms primeCut_zero3119
#print axioms remainder_at_zero3119
#print axioms primeCut_succ3119
#print axioms nonzero_terms_can_cancel3119
#print axioms negative_cut_does_not_determine_full_sign3119
