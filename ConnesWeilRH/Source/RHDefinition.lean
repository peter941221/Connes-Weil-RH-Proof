/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic

/-!
# RH definition bridge

This module makes the final definition bridge Lean-visible.  It does not prove
the CC20 source RH statement.  Instead it records the exact data needed to
transport a source RH conclusion to Mathlib's canonical `RiemannHypothesis`.
-/

namespace ConnesWeilRH
namespace Source

/-- Data tying a source RH predicate to Mathlib's zeta-zero formulation. -/
structure RHDefinitionBridge where
  sourceZeta : ℂ → ℂ
  sourceNontrivialZero : ℂ → Prop
  sourceCriticalLine : ℂ → Prop
  sourceZeta_eq_mathlib :
    ∀ s : ℂ, sourceZeta s = riemannZeta s
  sourceNontrivialZero_to_sourceZetaZero :
    ∀ s : ℂ, sourceNontrivialZero s → sourceZeta s = 0
  sourceNontrivialZero_no_negative_even :
    ∀ s : ℂ, sourceNontrivialZero s → ¬∃ n : ℕ, s = -2 * (n + 1)
  sourceNontrivialZero_no_pole :
    ∀ s : ℂ, sourceNontrivialZero s → s ≠ 1
  mathlibNontrivialZero_to_source :
    ∀ s : ℂ,
      riemannZeta s = 0 →
        (¬∃ n : ℕ, s = -2 * (n + 1)) →
          s ≠ 1 →
            sourceNontrivialZero s
  sourceCriticalLine_to_mathlib :
    ∀ s : ℂ, sourceCriticalLine s → s.re = 1 / 2
  mathlibCriticalLine_to_source :
    ∀ s : ℂ, s.re = 1 / 2 → sourceCriticalLine s

namespace RHDefinitionBridge

def MathlibNontrivialZero (s : ℂ) : Prop :=
  riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1

def MathlibCriticalLine (s : ℂ) : Prop :=
  s.re = 1 / 2

/-- The source-side RH statement represented by a bridge. -/
def SourceRH (B : RHDefinitionBridge) : Prop :=
  ∀ s : ℂ, B.sourceNontrivialZero s → B.sourceCriticalLine s

theorem source_nontrivial_zero_to_mathlib
    (B : RHDefinitionBridge) (s : ℂ)
    (h : B.sourceNontrivialZero s) :
    MathlibNontrivialZero s := by
  refine ⟨?_, B.sourceNontrivialZero_no_negative_even s h,
    B.sourceNontrivialZero_no_pole s h⟩
  rw [← B.sourceZeta_eq_mathlib s]
  exact B.sourceNontrivialZero_to_sourceZetaZero s h

theorem mathlib_nontrivial_zero_to_source
    (B : RHDefinitionBridge) (s : ℂ)
    (h : MathlibNontrivialZero s) :
    B.sourceNontrivialZero s :=
  B.mathlibNontrivialZero_to_source s h.1 h.2.1 h.2.2

theorem source_nontrivial_zero_iff_mathlib
    (B : RHDefinitionBridge) (s : ℂ) :
    B.sourceNontrivialZero s ↔ MathlibNontrivialZero s :=
  ⟨source_nontrivial_zero_to_mathlib B s,
    mathlib_nontrivial_zero_to_source B s⟩

theorem source_critical_line_iff_mathlib
    (B : RHDefinitionBridge) (s : ℂ) :
    B.sourceCriticalLine s ↔ MathlibCriticalLine s :=
  ⟨B.sourceCriticalLine_to_mathlib s, B.mathlibCriticalLine_to_source s⟩

theorem source_rh_to_mathlib_rh
    (B : RHDefinitionBridge) (hRH : B.SourceRH) :
    _root_.RiemannHypothesis := by
  intro s hzero hnotNegEven hpole
  exact B.sourceCriticalLine_to_mathlib s
    (hRH s (B.mathlibNontrivialZero_to_source s hzero hnotNegEven hpole))

theorem mathlib_rh_to_source_rh
    (B : RHDefinitionBridge) (hRH : _root_.RiemannHypothesis) :
    B.SourceRH := by
  intro s hsource
  apply B.mathlibCriticalLine_to_source
  apply hRH s
  · rw [← B.sourceZeta_eq_mathlib s]
    exact B.sourceNontrivialZero_to_sourceZetaZero s hsource
  · exact B.sourceNontrivialZero_no_negative_even s hsource
  · exact B.sourceNontrivialZero_no_pole s hsource

theorem source_rh_iff_mathlib
    (B : RHDefinitionBridge) :
    B.SourceRH ↔ _root_.RiemannHypothesis :=
  ⟨source_rh_to_mathlib_rh B, mathlib_rh_to_source_rh B⟩

/-- The canonical bridge where the source predicates are definitionally Mathlib's. -/
noncomputable def standard : RHDefinitionBridge where
  sourceZeta := riemannZeta
  sourceNontrivialZero :=
    fun s => riemannZeta s = 0 ∧ (¬∃ n : ℕ, s = -2 * (n + 1)) ∧ s ≠ 1
  sourceCriticalLine := fun s => s.re = 1 / 2
  sourceZeta_eq_mathlib := by
    intro s
    rfl
  sourceNontrivialZero_to_sourceZetaZero := by
    intro s hs
    exact hs.1
  sourceNontrivialZero_no_negative_even := by
    intro s hs
    exact hs.2.1
  sourceNontrivialZero_no_pole := by
    intro s hs
    exact hs.2.2
  mathlibNontrivialZero_to_source := by
    intro s hzero hnotNegEven hpole
    exact ⟨hzero, hnotNegEven, hpole⟩
  sourceCriticalLine_to_mathlib := by
    intro s hs
    exact hs
  mathlibCriticalLine_to_source := by
    intro s hs
    exact hs

theorem standard_source_rh_iff_mathlib :
    standard.SourceRH ↔ _root_.RiemannHypothesis :=
  source_rh_iff_mathlib standard

theorem standard_source_nontrivial_zero_iff_mathlib
    (s : ℂ) :
    standard.sourceNontrivialZero s ↔ MathlibNontrivialZero s :=
  source_nontrivial_zero_iff_mathlib standard s

theorem standard_source_critical_line_iff_mathlib
    (s : ℂ) :
    standard.sourceCriticalLine s ↔ MathlibCriticalLine s :=
  source_critical_line_iff_mathlib standard s

end RHDefinitionBridge
end Source
end ConnesWeilRH
