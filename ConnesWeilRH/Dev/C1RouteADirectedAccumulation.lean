import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic

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
    (term upper : ℕ → ℕ → ℝ) (spanUpper : ℕ → ℝ)
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

theorem finite_span_partition_le_of_termwise_upper2393
    (term upper : ℕ → ℝ) (spanUpper : ℕ → ℝ)
    (spanStart spanLength : ℕ → ℕ)
    (spans cells : ℕ) (scalar : ℝ)
    (hterm : ∀ span < spans, ∀ index < spanLength span,
      term (spanStart span + index) ≤ upper (spanStart span + index))
    (hspan : ∀ span < spans,
      (∑ index ∈ Finset.range (spanLength span),
        upper (spanStart span + index)) ≤ spanUpper span)
    (hpartition :
      (∑ index ∈ Finset.range cells, term index) =
        ∑ span ∈ Finset.range spans,
          ∑ index ∈ Finset.range (spanLength span),
            term (spanStart span + index))
    (hglobal : ∑ span ∈ Finset.range spans, spanUpper span ≤ scalar) :
    ∑ index ∈ Finset.range cells, term index ≤ scalar := by
  calc
    (∑ index ∈ Finset.range cells, term index) =
        ∑ span ∈ Finset.range spans,
          ∑ index ∈ Finset.range (spanLength span),
            term (spanStart span + index) := hpartition
    _ ≤ ∑ span ∈ Finset.range spans,
          ∑ index ∈ Finset.range (spanLength span),
            upper (spanStart span + index) := by
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

/-
The replay's spans are contiguous slices.  This lemma proves the exact
partition equality from that index invariant, leaving only the numerical
term/upper inequalities to the certificate layer.
-/
theorem finite_sum_eq_contiguous_partition2394
    (term : ℕ → ℝ) (spanStart spanLength : ℕ → ℕ)
    (spans cells : ℕ)
    (hstart : spanStart 0 = 0)
    (hstep : ∀ span < spans,
      spanStart (span + 1) = spanStart span + spanLength span)
    (hend : spanStart spans = cells) :
    ∑ index ∈ Finset.range cells, term index =
      ∑ span ∈ Finset.range spans,
        ∑ index ∈ Finset.range (spanLength span),
          term (spanStart span + index) := by
  have hprefix : ∀ n ≤ spans,
      (∑ index ∈ Finset.range (spanStart n), term index) =
        ∑ span ∈ Finset.range n,
          ∑ index ∈ Finset.range (spanLength span),
            term (spanStart span + index) := by
    intro n hn
    induction n with
    | zero => simp [hstart]
    | succ n ih =>
        have hnlt : n < spans := Nat.lt_of_succ_le hn
        rw [hstep n hnlt, Finset.sum_range_add,
          ih (Nat.le_of_lt hnlt)]
        rw [Finset.sum_range_succ]
  rw [← hend]
  exact hprefix spans le_rfl

def repairedSpanStart2410 (span : ℕ) : ℕ :=
  if span ≤ 38 then span * 20001 else 776611

def repairedSpanLength2410 (span : ℕ) : ℕ :=
  if span < 38 then 20001 else 16573

theorem repaired_fullgrid_partition_eq2410 (term : ℕ → ℝ) :
    ∑ index ∈ Finset.range 776611, term index =
      ∑ span ∈ Finset.range 39,
        ∑ index ∈ Finset.range (repairedSpanLength2410 span),
          term (repairedSpanStart2410 span + index) := by
  apply finite_sum_eq_contiguous_partition2394 term
    repairedSpanStart2410 repairedSpanLength2410 39 776611
  · simp [repairedSpanStart2410]
  · intro span hspan
    by_cases hlt : span < 37
    · have hlt38 : span < 38 := by omega
      have hnextlt38 : span + 1 < 38 := by omega
      have hle37 : span ≤ 37 := by omega
      have hle38 : span ≤ 38 := by omega
      simp [repairedSpanStart2410, repairedSpanLength2410, hle37, hle38,
        hlt38, hnextlt38]
      omega
    · have hcases : span = 37 ∨ span = 38 := by omega
      rcases hcases with rfl | rfl <;>
        simp [repairedSpanStart2410, repairedSpanLength2410] <;> norm_num
  · simp [repairedSpanStart2410]

end ConnesWeilRH.Dev
