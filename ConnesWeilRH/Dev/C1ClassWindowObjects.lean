/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import Mathlib.Analysis.Calculus.ContDiff.Polynomial
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Record 1124: the class window-test family as Lean objects (bridge phase 1)

The certified-class window tests of the 1112/1113 pipeline,

    phi_i(u) = P_i(u/a) * exp(-1/(1-(u/a)^2)),   |u| < a;  0 otherwise
    (i = 0..7, P_i the standard Legendre polynomial),

exist so far only Python-side, which blocks every true-data instance of the
certificate chain (`Hbox`, `hrep`, C2).  This record lands the OBJECTS in
Lean.  The point that makes it cheap: Mathlib's `expNegInvGlue` is literally
`exp (-x⁻¹)` for `x > 0`, zero for `x <= 0`, and `ContDiff ℝ n` for every
order, so the class bump

    classBump x = expNegInvGlue (1 - x ^ 2)

agrees pointwise everywhere with the Python bump and is smooth by one
composition.  The Legendre factor is defined by the standard recurrence (no
literal tables); the Python probe asserts its tables satisfy the same
recurrence, so both sides are standard Legendre by construction.

No number is certified, no box is installed, no sign is asserted.  This is
bridge phase 1; phases 2+ (Gram enclosures, gate-matrix enclosures, C2
drift) consume these objects.  RH NOT claimed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1ClassWindowObjects

open MeasureTheory Set Filter
open CCM25Concrete.CompactLogConvolution
open Polynomial
open scoped ContDiff Topology Filter

noncomputable section

/-! ## The class bump -/

/-- The class bump: literally `exp (-1/(1-x^2))` on `|x| < 1`, zero outside.
Matches the 1112 pipeline bump pointwise everywhere. -/
noncomputable def classBump (x : ℝ) : ℝ := expNegInvGlue (1 - x ^ 2)

/-- Pointwise identity of the class bump with the pipeline formula. -/
theorem classBump_eq_exp {x : ℝ} (hx : |x| < 1) :
    classBump x = Real.exp (-(1 / (1 - x ^ 2))) := by
  have hsq : x ^ 2 < 1 := by
    rcases abs_lt.mp hx with ⟨h1, h2⟩
    nlinarith
  have hle : ¬(1 - x ^ 2 ≤ 0) := by linarith
  rw [classBump, expNegInvGlue, if_neg hle, one_div]

/-- The class bump vanishes at and beyond the boundary. -/
theorem classBump_eq_zero {x : ℝ} (hx : 1 ≤ |x|) : classBump x = 0 := by
  have hsq_abs : 1 ≤ |x| ^ 2 := by
    have hprod : 0 ≤ (|x| - 1) * (|x| + 1) := by
      exact mul_nonneg (sub_nonneg.mpr hx) (by linarith [abs_nonneg x])
    nlinarith
  have hsq : 1 ≤ x ^ 2 := by
    simpa only [sq_abs] using hsq_abs
  exact expNegInvGlue.zero_of_nonpos (by linarith)

/-- Smoothness of the class bump: one composition over Mathlib's flat
exp branch. -/
theorem classBump_contDiff : ContDiff ℝ ∞ classBump := by
  rw [contDiff_infty]
  intro n
  exact (expNegInvGlue.contDiff (n := n)).comp
    (contDiff_const.sub (contDiff_id.pow (2 : ℕ)))

/-- Positivity inside the window. -/
theorem classBump_pos {x : ℝ} (hx : |x| < 1) : 0 < classBump x := by
  rw [classBump_eq_exp hx]
  positivity

/-! ## Legendre polynomials (standard, by recurrence) -/

/-- Standard Legendre polynomials over ℝ, by the classical recurrence
`P0 = 1`, `P1 = X`, `(n+2) P_{n+2} = (2n+3) X P_{n+1} - (n+1) P_n`. -/
noncomputable def legendrePoly : ℕ → ℝ[X]
  | 0 => 1
  | 1 => X
  | n + 2 =>
      ((n + 2 : ℕ) : ℝ)⁻¹ •
        ((2 * (n + 1) + 1) • (X * legendrePoly (n + 1))
          - (n + 1) • legendrePoly n)

/-- Polynomial evaluation is smooth. -/
theorem contDiff_legendreEval (p : ℝ[X]) {n : WithTop ℕ∞} :
    ContDiff ℝ n (fun x : ℝ => eval x p) := by
  have h : ContDiff ℝ n (fun x : ℝ => aeval x p) := Polynomial.contDiff_aeval p n
  have hfe : (fun x : ℝ => eval x p) = (fun x : ℝ => aeval x p) := by
    funext x
    simp [aeval_def]
  rw [hfe]
  exact h

/-! ## The window-test objects -/

/-- The real-valued core of `phi_i`: Legendre times the class bump at the
scaled argument, matching `1112 phi_iv(u_iv, i, A_R)` with 0-based `i`. -/
noncomputable def classWindowFun (a : ℝ) (i : ℕ) (u : ℝ) : ℝ :=
  eval (u / a) (legendrePoly i) * classBump (u / a)

/-- The support of the (complexified) window core lies in the open window. -/
theorem support_subset_Ioo (a : ℝ) (ha : 0 < a) (i : ℕ) :
    Function.support (fun u : ℝ => ((classWindowFun a i u : ℝ) : ℂ)) ⊆
      Ioo (-a) a := by
  intro u hu
  rw [Function.mem_support] at hu
  by_contra hout
  apply hu
  have hout' : u ≤ -a ∨ a ≤ u := by
    by_cases hleft : u ≤ -a
    · exact Or.inl hleft
    · right
      by_contra hright
      apply hout
      exact ⟨lt_of_not_ge hleft, lt_of_not_ge hright⟩
  rcases hout' with h | h
  · have h1 : u / a ≤ -1 := by
      rw [div_le_iff₀ ha]
      linarith
    have h2 : u / a ≤ 0 := by linarith
    have hz : classBump (u / a) = 0 := classBump_eq_zero (by rw [abs_of_nonpos h2]; linarith)
    simp [classWindowFun, hz]
  · have h1 : 1 ≤ u / a := by
      rw [le_div_iff₀ ha]
      linarith
    have h2 : 0 ≤ u / a := by linarith
    have hz : classBump (u / a) = 0 := classBump_eq_zero (by rw [abs_of_nonneg h2]; exact h1)
    simp [classWindowFun, hz]

/-- Closed-window twin for downstream consumers. -/
theorem support_subset_Icc (a : ℝ) (ha : 0 < a) (i : ℕ) :
    Function.support (fun u : ℝ => ((classWindowFun a i u : ℝ) : ℂ)) ⊆
      Icc (-a) a :=
  (support_subset_Ioo a ha i).trans Set.Ioo_subset_Icc_self

/-- The class window test as a compact-log test (house packaging). -/
noncomputable def classWindowTest (a : ℝ) (ha : 0 < a) (i : ℕ) : CompactLogTest := by
  have hsub := support_subset_Icc a ha i
  have hcompact : HasCompactSupport
      (fun u : ℝ => ((classWindowFun a i u : ℝ) : ℂ)) :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hsub
  have hdiv : ContDiff ℝ ∞ (fun u : ℝ => u / a) := by fun_prop
  have hpoly : ContDiff ℝ ∞
      (fun u : ℝ => eval (u / a) (legendrePoly i)) :=
    (contDiff_legendreEval (legendrePoly i)).comp hdiv
  have hbump : ContDiff ℝ ∞ (fun u : ℝ => classBump (u / a)) :=
    classBump_contDiff.comp hdiv
  have hreal : ContDiff ℝ ∞ (fun u : ℝ => classWindowFun a i u) := hpoly.mul hbump
  have hsmooth : ContDiff ℝ ∞ (fun u : ℝ => ((classWindowFun a i u : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp hreal
  exact
    { test := hcompact.toSchwartzMap hsmooth
      compactSupport := by simpa using hcompact }

/-- The support of the packaged test lies in the open window. -/
theorem classWindowTest_support (a : ℝ) (ha : 0 < a) (i : ℕ) :
    Function.support (classWindowTest a ha i).test ⊆ Ioo (-a) a :=
  support_subset_Ioo a ha i

/-- Closed twin. -/
theorem classWindowTest_support_Icc (a : ℝ) (ha : 0 < a) (i : ℕ) :
    Function.support (classWindowTest a ha i).test ⊆ Icc (-a) a :=
  support_subset_Icc a ha i

/-! ## The family object -/

/-- The (a, 8) class family: the object the certified-class chain consumes.
The pipeline classes q28/q38/q48 use a = 2, 3, 4. -/
noncomputable def classTestFamily (a : ℝ) (ha : 0 < a) : Fin 8 → CompactLogTest :=
  fun i => classWindowTest a ha i

end
end C1ClassWindowObjects
end Source
end ConnesWeilRH
