/-
Probe for record 1118 tactic shapes (scratch; delete after the idiom is
pinned).  Tests, with tiny literals:
  A  univ-sum over a variable binder against a literal matrix (the hKV idiom)
  B  the sdiff rewrite via the kernel's sumUnivSplit
  C  the full hslack shape (per-class falsifier check) end to end
  D  the mu-positivity norm_num pattern over a def unfold
  E  the Tier-1 ratio headline against the REAL committed Q28 data
-/

import ConnesWeilRH.Dev.C1GateLevelTransfer
import ConnesWeilRH.Dev.C1LocalConfigurationDomination
import ConnesWeilRH.Dev.C1WindowRationalIngestQ28

set_option linter.style.longLine false

namespace Probe1118

open Matrix
open ConnesWeilRH.Source.C1GateLevelTransfer (sumUnivSplit)
open ConnesWeilRH.Source.C1LocalConfigurationDomination (ICgate)
open ConnesWeilRH.Source.C1WindowRationalIngest
open ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution

private theorem sdiff_sum_eq {k : ℕ} (g : Fin k → ℝ) (j : Fin k) :
    (Finset.univ \ {j}).sum g = Finset.univ.sum g - g j := by
  have h := sumUnivSplit (k := k) (g := g) j
  linarith

noncomputable def Lm : Matrix (Fin 5) (Fin 5) ℝ :=
  !![(1 : ℝ), (2 : ℝ), (3 : ℝ), (4 : ℝ), (5 : ℝ);
     (6 : ℝ), (7 : ℝ), (8 : ℝ), (9 : ℝ), (10 : ℝ);
     (1 : ℝ), (1 : ℝ), (2 : ℝ), (2 : ℝ), (3 : ℝ);
     (0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ);
     (2 : ℝ), (0 : ℝ), (1 : ℝ), (0 : ℝ), (1 : ℝ)]

noncomputable def dv : Fin 5 → ℝ := ![(100 : ℝ), (200 : ℝ), (300 : ℝ), (400 : ℝ), (500 : ℝ)]

/-- A: the hKV idiom - plain simp evaluates a univ-sum with a variable binder
over a literal matrix. -/
example : Finset.univ.sum (fun k => Lm 0 k + Lm k 0) = 25 := by
  simp [Lm, Fin.sum_univ_succ] <;> norm_num

/-- C: the full hslack shape end to end. -/
example : ∀ i : Fin 5,
    Lm i i + ((Finset.univ \ {i}).sum fun k => (Lm i k + Lm k i) / 2) < dv i := by
  intro i
  rw [sdiff_sum_eq (fun k => (Lm i k + Lm k i) / 2) i]
  fin_cases i <;> simp [Lm, dv, Fin.sum_univ_succ] <;> norm_num

/-- D: mu positivity over a def unfold. -/
noncomputable def u : ℝ := (-3 / 7 : ℝ)

example : 0 < -u := by simp only [u]; norm_num

/-- E: Tier-1 ratio headline against the REAL committed Q28 data - the exact
statement shape the classes module will ship. -/
theorem rt {w : CompactLogTest} {c : Fin 8 → ℝ}
    (hrep : ICgate w.convolutionSquare = c ⬝ᵥ (Q28.M *ᵥ c))
    (hker : Q28.R.mulVec c = 0) :
    ICgate w.convolutionSquare ≤ Q28.U * c ⬝ᵥ (Q28.G *ᵥ c) := by
  rw [hrep]
  exact Q28.top c hker

end Probe1118
