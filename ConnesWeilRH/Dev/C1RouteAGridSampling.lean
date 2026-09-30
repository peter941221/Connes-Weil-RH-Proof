/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1RouteAStripTransfer

/-!
# Grid sampling for the centered strip (record 2313)

Record 2312 left the grid-existence arithmetic of the record 2303 strip
envelope as a named hypothesis: every centered `sigma` had to be within
the half-step of one of the 101 certified sigma-nodes.  This module
discharges that arithmetic.

* `gridSample2303` — nearest-node arithmetic, machine-checked: every
  `sigma` in the centered window `[-1/2, 1/2]` lies within the pinned
  half-step `stripHalfStep2303` of a grid node `j / 100` with
  `j : ℤ`, `-50 <= j <= 50` — the record 2303 grid
  `-0.5, -0.49, ..., 0.5` (101 nodes, spacing `1/100`, covering radius
  `1/200`).  The proof is the `Int.floor` round-to-nearest argument:
  `j = floor (sigma * 100 + 1/2)`;
* `frozenStripHypothesis_of_certified_nodes` — the 101-node consumer:
  node values are required only at the record 2303 grid nodes `j / 100`
  (the shape of the committed `grid_rows`), and together with the
  support-radius bound they yield `FrozenStripHypothesis` through the
  record 2312 certified grid consumer at the pins.

The residual strip-lane inputs are now exactly the node-value
arithmetic over the 101 nodes (the grid maximum over the captured owner)
and the support-radius bound — both owner-bridge obligations.

The record 2312 module is untouched, so its committed pin artifact keeps
its recorded file hashes; this record narrows the 2312 "no grid
sampling" non-claim.  No owner bridge, no producer GO, no gate sign
change, no RH claim.
-/

namespace ConnesWeilRH
namespace Dev

open ConnesWeilRH.Source.C1RouteAItem5Arithmetic
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

/-- **Nearest-node sampling of the record 2303 sigma grid (record 2313).**
Every `sigma` in the centered window `[-1/2, 1/2]` lies within the pinned
half-step `stripHalfStep2303 = 1/200` of a grid node `j / 100` with
`-50 <= j <= 50`. -/
theorem gridSample2303 (σ : ℝ) (hσ : σ ∈ Set.Icc (-(1 / 2) : ℝ) (1 / 2)) :
    ∃ j : ℤ, -(50 : ℤ) ≤ j ∧ j ≤ 50 ∧
      |σ - (j : ℝ) / 100| ≤ stripHalfStep2303 := by
  have hlo : -(1 / 2 : ℝ) ≤ σ := hσ.1
  have hhi : σ ≤ (1 / 2 : ℝ) := hσ.2
  refine ⟨⌊σ * 100 + 1 / 2⌋, ?_, ?_, ?_⟩
  · rw [Int.le_floor]
    push_cast
    linarith
  · rw [Int.floor_le_iff]
    push_cast
    linarith
  · have h1 : ((⌊σ * 100 + 1 / 2⌋ : ℤ) : ℝ) ≤ σ * 100 + 1 / 2 :=
      Int.floor_le _
    have h2 : σ * 100 + 1 / 2 < ((⌊σ * 100 + 1 / 2⌋ : ℤ) : ℝ) + 1 :=
      Int.lt_floor_add_one _
    have hd : |σ * 100 - ((⌊σ * 100 + 1 / 2⌋ : ℤ) : ℝ)| ≤ 1 / 2 :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hrw : σ - ((⌊σ * 100 + 1 / 2⌋ : ℤ) : ℝ) / 100
        = (σ * 100 - ((⌊σ * 100 + 1 / 2⌋ : ℤ) : ℝ)) / 100 := by ring
    rw [hrw, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 100)]
    have hpin : stripHalfStep2303 = 1 / 200 := by norm_num [stripHalfStep2303]
    rw [hpin]
    linarith

/-- **101-node grid consumer (record 2313).**  The record 2312 certified
grid consumer at the pins with the grid-existence hypothesis discharged
by `gridSample2303`: node min-product values are needed only at the
record 2303 grid nodes `j / 100` with `-50 <= j <= 50` — the shape of
the committed `grid_rows` — plus the support-radius bound. -/
theorem frozenStripHypothesis_of_certified_nodes (b c : CompactLogTest)
    (htsupp_b : tsupport (b.test : ℝ → ℂ) ⊆
      Set.Icc (-stripRadius2303) stripRadius2303)
    (htsupp_c : tsupport (c.test : ℝ → ℂ) ⊆
      Set.Icc (-stripRadius2303) stripRadius2303)
    (hnode : ∀ j : ℤ, -(50 : ℤ) ≤ j → j ≤ 50 →
      min (stripSecondNorm ((j : ℝ) / 100) (b.test : ℝ → ℂ) *
            stripNorm ((j : ℝ) / 100) (c.test : ℝ → ℂ))
          (stripSecondNorm ((j : ℝ) / 100) (c.test : ℝ → ℂ) *
            stripNorm ((j : ℝ) / 100) (b.test : ℝ → ℂ))
        ≤ stripGridMax2303) :
    FrozenStripHypothesis b c := by
  refine frozenStripHypothesis_of_certified_grid_rmax b c htsupp_b htsupp_c ?_
  intro σ hσ
  obtain ⟨j, hjlo, hjhi, hnear⟩ := gridSample2303 σ hσ
  refine ⟨(j : ℝ) / 100, ?_, hnear, hnode j hjlo hjhi⟩
  constructor
  · have hj : ((-(50 : ℤ) : ℤ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hjlo
    push_cast at hj
    linarith
  · have hj : (j : ℝ) ≤ (50 : ℝ) := by exact_mod_cast hjhi
    linarith

end Dev
end ConnesWeilRH
