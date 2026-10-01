import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace ConnesWeilRH.Dev

open scoped BigOperators

/-
The numerical replay accumulates directed upper terms in spans.  These lemmas
separate the order-theoretic finite-sum step from the still-open certificate
that the stored directed terms dominate the mathematical terms.
-/
theorem finite_sum_le_of_termwise_upper2391
    (term upper : ℕ → ℝ) (cells : ℕ) (scalar : ℝ)
    (hterm : ∀ index < cells, term index ≤ upper index)
    (hupper : ∑ index ∈ Finset.range cells, upper index ≤ scalar) :
    ∑ index ∈ Finset.range cells, term index ≤ scalar := by
  exact (Finset.sum_le_sum fun index hindex =>
    hterm index (Finset.mem_range.mp hindex)).trans hupper

theorem finite_span_sum_le_of_termwise_upper2391
    (term upper spanUpper : ℕ → ℕ → ℝ)
    (spans cells : ℕ) (scalar : ℝ)
    (hterm : ∀ span < spans, ∀ index < cells,
      term span index ≤ upper span index)
    (hspan : ∀ span < spans,
      (∑ index ∈ Finset.range cells, upper span index) ≤ spanUpper span)
    (hglobal : ∑ span ∈ Finset.range spans, spanUpper span ≤ scalar) :
    ∑ span ∈ Finset.range spans,
      ∑ index ∈ Finset.range cells, term span index ≤ scalar := by
  calc
    (∑ span ∈ Finset.range spans,
        ∑ index ∈ Finset.range cells, term span index) ≤
        ∑ span ∈ Finset.range spans,
          ∑ index ∈ Finset.range cells, upper span index := by
      apply Finset.sum_le_sum
      intro span hspan'
      apply Finset.sum_le_sum
      intro index hindex
      exact hterm span (Finset.mem_range.mp hspan') index
        (Finset.mem_range.mp hindex)
    _ ≤ ∑ span ∈ Finset.range spans, spanUpper span := by
      apply Finset.sum_le_sum
      intro span hspan'
      exact hspan span (Finset.mem_range.mp hspan')
    _ ≤ scalar := hglobal

end ConnesWeilRH.Dev
