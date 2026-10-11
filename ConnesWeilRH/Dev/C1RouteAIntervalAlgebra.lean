import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Group.Pointwise.Interval
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Data.Complex.BigOperators
import Mathlib.Data.Real.Basic

namespace ConnesWeilRH.Dev

open scoped BigOperators
open scoped Complex.SMul
open Set

structure RealInterval2429 where
  lo : ℝ
  hi : ℝ

def RealInterval2429.Mem (x : ℝ) (r : RealInterval2429) : Prop :=
  r.lo ≤ x ∧ x ≤ r.hi

def RealInterval2429.point (x : ℝ) : RealInterval2429 :=
  { lo := x, hi := x }

theorem RealInterval2429.point_mem (x : ℝ) :
    (RealInterval2429.point x).Mem x := by
  simp [RealInterval2429.point, RealInterval2429.Mem]

def RealInterval2429.add (a b : RealInterval2429) : RealInterval2429 :=
  { lo := a.lo + b.lo, hi := a.hi + b.hi }

theorem RealInterval2429.mem_add {a b : RealInterval2429} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (a.add b).Mem (x + y) := by
  constructor
  · exact add_le_add ha.1 hb.1
  · exact add_le_add ha.2 hb.2

def RealInterval2429.mul (a b : RealInterval2429) : RealInterval2429 :=
  { lo := min (min (a.lo * b.lo) (a.lo * b.hi))
      (min (a.hi * b.lo) (a.hi * b.hi))
    hi := max (max (a.lo * b.lo) (a.lo * b.hi))
      (max (a.hi * b.lo) (a.hi * b.hi)) }

def RealInterval2429.sub (a b : RealInterval2429) : RealInterval2429 :=
  { lo := a.lo - b.hi, hi := a.hi - b.lo }

theorem RealInterval2429.mem_sub {a b : RealInterval2429} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (a.sub b).Mem (x - y) := by
  constructor
  · exact sub_le_sub ha.1 hb.2
  · exact sub_le_sub ha.2 hb.1

theorem RealInterval2429.mem_mul {a b : RealInterval2429} {x y : ℝ}
    (ha : a.Mem x) (hb : b.Mem y) : (a.mul b).Mem (x * y) := by
  rcases ha with ⟨hax, hxb⟩
  rcases hb with ⟨hby, hyb⟩
  have hyu : y ∈ uIcc b.lo b.hi := by
    rw [uIcc_of_le (hby.trans hyb)]
    exact ⟨hby, hyb⟩
  have hay : a.lo * y ∈ uIcc (a.lo * b.lo) (a.lo * b.hi) := by
    have h := image_mul_const_uIcc a.lo b.lo b.hi
    have hm : y * a.lo ∈ (fun t : ℝ => t * a.lo) '' uIcc b.lo b.hi :=
      ⟨y, hyu, rfl⟩
    rw [h] at hm
    simpa [mul_comm] using hm
  have hby' : a.hi * y ∈ uIcc (a.hi * b.lo) (a.hi * b.hi) := by
    have h := image_mul_const_uIcc a.hi b.lo b.hi
    have hm : y * a.hi ∈ (fun t : ℝ => t * a.hi) '' uIcc b.lo b.hi :=
      ⟨y, hyu, rfl⟩
    rw [h] at hm
    simpa [mul_comm] using hm
  by_cases hy0 : 0 ≤ y
  · have hlow : a.lo * y ≤ x * y :=
      mul_le_mul_of_nonneg_right hax hy0
    have hhigh : x * y ≤ a.hi * y :=
      mul_le_mul_of_nonneg_right hxb hy0
    constructor
    · exact (min_le_left _ _).trans (hay.1.trans hlow)
    · exact hhigh.trans (hby'.2.trans (le_max_right _ _))
  · have hy0' : y ≤ 0 := le_of_not_ge hy0
    have hlow : a.hi * y ≤ x * y :=
      mul_le_mul_of_nonpos_right hxb hy0'
    have hhigh : x * y ≤ a.lo * y :=
      mul_le_mul_of_nonpos_right hax hy0'
    constructor
    · exact (min_le_right _ _).trans (hby'.1.trans hlow)
    · exact hhigh.trans (hay.2.trans (le_max_left _ _))

noncomputable def RealInterval2429.invPositive (a : RealInterval2429) : RealInterval2429 :=
  { lo := a.hi⁻¹, hi := a.lo⁻¹ }

theorem RealInterval2429.mem_invPositive {a : RealInterval2429} {x : ℝ}
    (hlo : 0 < a.lo) (hx : a.Mem x) :
    (a.invPositive).Mem x⁻¹ := by
  constructor
  · simpa only [RealInterval2429.invPositive, inv_eq_one_div] using
      (one_div_le_one_div_of_le (lt_of_lt_of_le hlo hx.1) hx.2)
  · simpa only [RealInterval2429.invPositive, inv_eq_one_div] using
      (one_div_le_one_div_of_le hlo hx.1)

noncomputable def RealInterval2429.exp (a : RealInterval2429) : RealInterval2429 :=
  { lo := Real.exp a.lo, hi := Real.exp a.hi }

theorem RealInterval2429.mem_exp {a : RealInterval2429} {x : ℝ}
    (hx : a.Mem x) : (a.exp).Mem (Real.exp x) := by
  constructor
  · exact Real.exp_le_exp.mpr hx.1
  · exact Real.exp_le_exp.mpr hx.2

/-- Interval enclosure for the bump factor used by the 2242 evaluator on a
positive `q` interval. -/
noncomputable def RealInterval2429.expNegThirtyDiv (a : RealInterval2429) :
    RealInterval2429 :=
  ((RealInterval2429.point (-30)).mul a.invPositive).exp

theorem RealInterval2429.mem_expNegThirtyDiv {a : RealInterval2429}
    {q : ℝ} (hlo : 0 < a.lo) (hq : a.Mem q) :
    (a.expNegThirtyDiv).Mem (Real.exp (-30 / q)) := by
  have hinv : (a.invPositive).Mem q⁻¹ :=
    RealInterval2429.mem_invPositive hlo hq
  have hmul : ((RealInterval2429.point (-30)).mul a.invPositive).Mem
      ((-30 : ℝ) * q⁻¹) :=
    RealInterval2429.mem_mul (RealInterval2429.point_mem (-30)) hinv
  simpa [RealInterval2429.expNegThirtyDiv, div_eq_mul_inv] using
    RealInterval2429.mem_exp hmul

/-- A twice differentiable function with second derivative bounded by one
stays within `(x-a) * (b-x) / 2` of its endpoint chord. -/
theorem RealInterval2429.abs_sub_chord_le_of_secondDeriv_bound
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f))
    (hsecond : ∀ y, -1 ≤ (deriv^[2] f) y ∧ (deriv^[2] f) y ≤ 1)
    {a x b : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    |f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)| ≤
      ((x - a) * (b - x)) / 2 := by
  let q : ℝ → ℝ := fun y => y ^ 2 / 2
  let t : ℝ := (x - a) / (b - a)
  have hden : 0 < b - a := sub_pos.mpr hab
  have ht0 : 0 ≤ t := div_nonneg (sub_nonneg.mpr hax) hden.le
  have ht1 : t ≤ 1 := by
    dsimp [t]
    rw [div_le_one hden]
    linarith
  have hcomb : x = (1 - t) * a + t * b := by
    dsimp [t]
    field_simp
    ring
  have hq1 : deriv q = fun y => y := by
    ext y
    simp [q]
  have hplus1 : deriv (fun y => f y + q y) = fun y => deriv f y + y := by
    ext y
    change deriv (f + q) y = deriv f y + y
    rw [deriv_add (hf y) (by fun_prop), hq1]
  have hplus2 : deriv (deriv (fun y => f y + q y)) =
      fun y => deriv (deriv f) y + 1 := by
    rw [hplus1]
    ext y
    change deriv (deriv f + fun y => y) y = deriv (deriv f) y + 1
    rw [deriv_add (hf' y) (by fun_prop)]
    simp
  have hminus1 : deriv (fun y => f y - q y) = fun y => deriv f y - y := by
    ext y
    change deriv (f - q) y = deriv f y - y
    rw [deriv_sub (hf y) (by fun_prop), hq1]
  have hminus2 : deriv (deriv (fun y => f y - q y)) =
      fun y => deriv (deriv f) y - 1 := by
    rw [hminus1]
    ext y
    change deriv (deriv f - fun y => y) y = deriv (deriv f) y - 1
    rw [deriv_sub (hf' y) (by fun_prop)]
    simp
  have hplusDiff : Differentiable ℝ (fun y => f y + q y) := hf.add (by fun_prop)
  have hplusDerivDiff : Differentiable ℝ (deriv (fun y => f y + q y)) := by
    rw [hplus1]
    exact hf'.add (by fun_prop)
  have hminusDiff : Differentiable ℝ (fun y => f y - q y) := hf.sub (by fun_prop)
  have hminusDerivDiff : Differentiable ℝ (deriv (fun y => f y - q y)) := by
    rw [hminus1]
    exact hf'.sub (by fun_prop)
  have hplusConvex : ConvexOn ℝ univ (fun y => f y + q y) :=
    convexOn_univ_of_deriv2_nonneg hplusDiff hplusDerivDiff (by
      intro y
      change 0 ≤ deriv (deriv (fun y => f y + q y)) y
      rw [hplus2]
      have hy := hsecond y
      change -1 ≤ deriv (deriv f) y ∧ deriv (deriv f) y ≤ 1 at hy
      linarith [hy.1])
  have hminusConcave : ConcaveOn ℝ univ (fun y => f y - q y) :=
    concaveOn_univ_of_deriv2_nonpos hminusDiff hminusDerivDiff (by
      intro y
      change deriv (deriv (fun y => f y - q y)) y ≤ 0
      rw [hminus2]
      have hy := hsecond y
      change -1 ≤ deriv (deriv f) y ∧ deriv (deriv f) y ≤ 1 at hy
      linarith [hy.2])
  have hplusChord := hplusConvex.2 (Set.mem_univ a) (Set.mem_univ b)
    (show 0 ≤ 1 - t by linarith) ht0 (by ring : (1 - t) + t = 1)
  have hminusChord := hminusConcave.2 (Set.mem_univ a) (Set.mem_univ b)
    (show 0 ≤ 1 - t by linarith) ht0 (by ring : (1 - t) + t = 1)
  have hplusBound : f x + q x ≤
      (1 - t) * (f a + q a) + t * (f b + q b) := by
    simpa [hcomb, q, smul_eq_mul] using hplusChord
  have hminusBound :
      (1 - t) * (f a - q a) + t * (f b - q b) ≤ f x - q x := by
    simpa [hcomb, q, smul_eq_mul] using hminusChord
  have hchord :
      (b - x) / (b - a) * f a + (x - a) / (b - a) * f b =
        (1 - t) * f a + t * f b := by
    dsimp [t]
    have hweights : (b - x) / (b - a) = 1 - (x - a) / (b - a) := by
      field_simp
      ring
    rw [hweights]
  have hgap : ((1 - t) * q a + t * q b) - q x =
      ((x - a) * (b - x)) / 2 := by
    dsimp [t, q]
    field_simp
    rw [hcomb]
    ring
  rw [abs_le]
  constructor
  · rw [hchord]
    linarith [hminusBound, hgap]
  · rw [hchord]
    linarith [hplusBound, hgap]

theorem RealInterval2429.abs_sub_chord_le_widthSq_eighth
    {f : ℝ → ℝ} (hf : Differentiable ℝ f)
    (hf' : Differentiable ℝ (deriv f))
    (hsecond : ∀ y, -1 ≤ (deriv^[2] f) y ∧ (deriv^[2] f) y ≤ 1)
    {a x b : ℝ} (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    |f x - ((b - x) / (b - a) * f a + (x - a) / (b - a) * f b)| ≤
      (b - a) ^ 2 / 8 := by
  have hchord := abs_sub_chord_le_of_secondDeriv_bound hf hf' hsecond hab hax hxb
  have hproduct : (x - a) * (b - x) ≤ (b - a) ^ 2 / 4 := by
    nlinarith [sq_nonneg (2 * x - a - b)]
  nlinarith

theorem RealInterval2429.sin_chord_error {a x b : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.sin x - ((b - x) / (b - a) * Real.sin a +
      (x - a) / (b - a) * Real.sin b)| ≤ (b - a) ^ 2 / 8 := by
  apply abs_sub_chord_le_widthSq_eighth (f := Real.sin) (by fun_prop)
    (by simpa only [Real.deriv_sin] using (Real.differentiable_cos : Differentiable ℝ Real.cos))
    (fun y => by
      have h := Real.abs_iteratedDeriv_sin_le_one 2 y
      have h' : |(deriv^[2] Real.sin) y| ≤ 1 := by simpa using h
      exact abs_le.mp h') hab hax hxb

theorem RealInterval2429.cos_chord_error {a x b : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    |Real.cos x - ((b - x) / (b - a) * Real.cos a +
      (x - a) / (b - a) * Real.cos b)| ≤ (b - a) ^ 2 / 8 := by
  apply abs_sub_chord_le_widthSq_eighth (f := Real.cos) (by fun_prop)
    (by simpa only [Real.deriv_cos'] using
      (Real.differentiable_sin.neg : Differentiable ℝ (fun y => -Real.sin y)))
    (fun y => by
      have h := Real.abs_iteratedDeriv_cos_le_one 2 y
      have h' : |(deriv^[2] Real.cos) y| ≤ 1 := by simpa using h
      exact abs_le.mp h') hab hax hxb

def RealInterval2429.endpointHull (left right radius : ℝ) : RealInterval2429 :=
  { lo := min left right - radius, hi := max left right + radius }

theorem RealInterval2429.mem_endpointHull_of_chord_error
    {value left right u v radius : ℝ}
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hsum : u + v = 1)
    (herror : |value - (u * left + v * right)| ≤ radius) :
    (RealInterval2429.endpointHull left right radius).Mem value := by
  have hmin : min left right ≤ u * left + v * right := by
    by_cases h : left ≤ right
    · rw [min_eq_left h]
      have hsumL : u * left + v * left = left := by
        nlinarith [congrArg (fun z : ℝ => z * left) hsum]
      nlinarith [mul_nonneg hv (sub_nonneg.mpr h)]
    · have h' : right ≤ left := le_of_not_ge h
      rw [min_eq_right h']
      have hsumR : u * right + v * right = right := by
        nlinarith [congrArg (fun z : ℝ => z * right) hsum]
      nlinarith [mul_nonneg hu (sub_nonneg.mpr h')]
  have hmax : u * left + v * right ≤ max left right := by
    by_cases h : left ≤ right
    · rw [max_eq_right h]
      have hsumR : u * right + v * right = right := by
        nlinarith [congrArg (fun z : ℝ => z * right) hsum]
      nlinarith [mul_nonneg hu (sub_nonneg.mpr h)]
    · have h' : right ≤ left := le_of_not_ge h
      rw [max_eq_left h']
      have hsumL : u * left + v * left = left := by
        nlinarith [congrArg (fun z : ℝ => z * left) hsum]
      nlinarith [mul_nonneg hv (sub_nonneg.mpr h')]
  rcases abs_le.mp herror with ⟨hlo, hhi⟩
  constructor
  · dsimp [RealInterval2429.endpointHull, RealInterval2429.Mem]
    linarith
  · dsimp [RealInterval2429.endpointHull, RealInterval2429.Mem]
    linarith

theorem RealInterval2429.mem_sinEndpointHull {a x b : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    (RealInterval2429.endpointHull (Real.sin a) (Real.sin b)
      ((b - a) ^ 2 / 8)).Mem (Real.sin x) := by
  apply mem_endpointHull_of_chord_error (value := Real.sin x)
    (left := Real.sin a) (right := Real.sin b)
    (u := (b - x) / (b - a)) (v := (x - a) / (b - a))
  · exact div_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hab.le)
  · exact div_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hab.le)
  · field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  · exact RealInterval2429.sin_chord_error hab hax hxb

theorem RealInterval2429.mem_cosEndpointHull {a x b : ℝ}
    (hab : a < b) (hax : a ≤ x) (hxb : x ≤ b) :
    (RealInterval2429.endpointHull (Real.cos a) (Real.cos b)
      ((b - a) ^ 2 / 8)).Mem (Real.cos x) := by
  apply mem_endpointHull_of_chord_error (value := Real.cos x)
    (left := Real.cos a) (right := Real.cos b)
    (u := (b - x) / (b - a)) (v := (x - a) / (b - a))
  · exact div_nonneg (sub_nonneg.mpr hxb) (sub_nonneg.mpr hab.le)
  · exact div_nonneg (sub_nonneg.mpr hax) (sub_nonneg.mpr hab.le)
  · field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  · exact RealInterval2429.cos_chord_error hab hax hxb

/-- A closed axis-aligned rectangle in `ℂ`, used only as the logical target of
the directed interval evaluator.  The numerical construction of its endpoints
is deliberately outside this file. -/
structure ComplexRect2427 where
  reLo : ℝ
  reHi : ℝ
  imLo : ℝ
  imHi : ℝ

def ComplexRect2427.Mem (z : ℂ) (r : ComplexRect2427) : Prop :=
  r.reLo ≤ z.re ∧ z.re ≤ r.reHi ∧
  r.imLo ≤ z.im ∧ z.im ≤ r.imHi

def ComplexRect2427.point (z : ℂ) : ComplexRect2427 :=
  { reLo := z.re, reHi := z.re, imLo := z.im, imHi := z.im }

theorem ComplexRect2427.point_mem (z : ℂ) :
    (ComplexRect2427.point z).Mem z := by
  simp [ComplexRect2427.point, ComplexRect2427.Mem]

def ComplexRect2427.add (a b : ComplexRect2427) : ComplexRect2427 :=
  { reLo := a.reLo + b.reLo
    reHi := a.reHi + b.reHi
    imLo := a.imLo + b.imLo
    imHi := a.imHi + b.imHi }

def ComplexRect2427.sub (a b : ComplexRect2427) : ComplexRect2427 :=
  { reLo := a.reLo - b.reHi
    reHi := a.reHi - b.reLo
    imLo := a.imLo - b.imHi
    imHi := a.imHi - b.imLo }

def ComplexRect2427.mul (a b : ComplexRect2427) : ComplexRect2427 :=
  let ar : RealInterval2429 := ⟨a.reLo, a.reHi⟩
  let ai : RealInterval2429 := ⟨a.imLo, a.imHi⟩
  let br : RealInterval2429 := ⟨b.reLo, b.reHi⟩
  let bi : RealInterval2429 := ⟨b.imLo, b.imHi⟩
  let rr := (ar.mul br).sub (ai.mul bi)
  let ii := (ar.mul bi).add (ai.mul br)
  { reLo := rr.lo, reHi := rr.hi, imLo := ii.lo, imHi := ii.hi }

theorem ComplexRect2427.mem_add {z w : ℂ} {a b : ComplexRect2427}
    (hz : a.Mem z) (hw : b.Mem w) : (a.add b).Mem (z + w) := by
  rcases hz with ⟨hzrl, hzrh, hzil, hzir⟩
  rcases hw with ⟨hwrl, hwrh, hwil, hwir⟩
  constructor
  · simpa [ComplexRect2427.add] using add_le_add hzrl hwrl
  constructor
  · simpa [ComplexRect2427.add] using add_le_add hzrh hwrh
  constructor
  · simpa [ComplexRect2427.add] using add_le_add hzil hwil
  · simpa [ComplexRect2427.add] using add_le_add hzir hwir

theorem ComplexRect2427.mem_sub {z w : ℂ} {a b : ComplexRect2427}
    (hz : a.Mem z) (hw : b.Mem w) : (a.sub b).Mem (z - w) := by
  rcases hz with ⟨hzrl, hzrh, hzil, hzir⟩
  rcases hw with ⟨hwrl, hwrh, hwil, hwir⟩
  constructor
  · simpa [ComplexRect2427.sub] using sub_le_sub hzrl hwrh
  constructor
  · simpa [ComplexRect2427.sub] using sub_le_sub hzrh hwrl
  constructor
  · simpa [ComplexRect2427.sub] using sub_le_sub hzil hwir
  · simpa [ComplexRect2427.sub] using sub_le_sub hzir hwil

theorem ComplexRect2427.mem_mul {z w : ℂ} {a b : ComplexRect2427}
    (hz : a.Mem z) (hw : b.Mem w) : (a.mul b).Mem (z * w) := by
  let ar : RealInterval2429 := ⟨a.reLo, a.reHi⟩
  let ai : RealInterval2429 := ⟨a.imLo, a.imHi⟩
  let br : RealInterval2429 := ⟨b.reLo, b.reHi⟩
  let bi : RealInterval2429 := ⟨b.imLo, b.imHi⟩
  have har : ar.Mem z.re := ⟨hz.1, hz.2.1⟩
  have hai : ai.Mem z.im := ⟨hz.2.2.1, hz.2.2.2⟩
  have hbr : br.Mem w.re := ⟨hw.1, hw.2.1⟩
  have hbi : bi.Mem w.im := ⟨hw.2.2.1, hw.2.2.2⟩
  have hrr : (ar.mul br).Mem (z.re * w.re) :=
    RealInterval2429.mem_mul har hbr
  have hii : (ai.mul bi).Mem (z.im * w.im) :=
    RealInterval2429.mem_mul hai hbi
  have hri : (ar.mul bi).Mem (z.re * w.im) :=
    RealInterval2429.mem_mul har hbi
  have hir : (ai.mul br).Mem (z.im * w.re) :=
    RealInterval2429.mem_mul hai hbr
  have hre : ((ar.mul br).sub (ai.mul bi)).Mem
      (z.re * w.re - z.im * w.im) :=
    RealInterval2429.mem_sub hrr hii
  have him : ((ar.mul bi).add (ai.mul br)).Mem
      (z.re * w.im + z.im * w.re) :=
    RealInterval2429.mem_add hri hir
  constructor
  · simpa [ComplexRect2427.mul, ar, ai, br, bi, Complex.mul_re] using hre.1
  constructor
  · simpa [ComplexRect2427.mul, ar, ai, br, bi, Complex.mul_re] using hre.2
  constructor
  · simpa [ComplexRect2427.mul, ar, ai, br, bi, Complex.mul_im] using him.1
  · simpa [ComplexRect2427.mul, ar, ai, br, bi, Complex.mul_im] using him.2

def ComplexRect2427.scale (r : ℝ) (a : ComplexRect2427) : ComplexRect2427 :=
  { reLo := r * a.reLo
    reHi := r * a.reHi
    imLo := r * a.imLo
    imHi := r * a.imHi }

theorem ComplexRect2427.mem_scale {r : ℝ} {z : ℂ} {a : ComplexRect2427}
    (hr : 0 ≤ r) (hz : a.Mem z) : (a.scale r).Mem (r • z) := by
  rcases hz with ⟨hzrl, hzrh, hzil, hzir⟩
  constructor
  · simpa [ComplexRect2427.scale, Complex.smul_re] using
      mul_le_mul_of_nonneg_left hzrl hr
  constructor
  · simpa [ComplexRect2427.scale, Complex.smul_re] using
      mul_le_mul_of_nonneg_left hzrh hr
  constructor
  · simpa [ComplexRect2427.scale, Complex.smul_im] using
      mul_le_mul_of_nonneg_left hzil hr
  · simpa [ComplexRect2427.scale, Complex.smul_im] using
      mul_le_mul_of_nonneg_left hzir hr

def ComplexRect2427.zero : ComplexRect2427 :=
  { reLo := 0, reHi := 0, imLo := 0, imHi := 0 }

def ComplexRect2427.sum (rect : ℕ → ComplexRect2427) (n : ℕ) : ComplexRect2427 :=
  { reLo := ∑ i ∈ Finset.range n, (rect i).reLo
    reHi := ∑ i ∈ Finset.range n, (rect i).reHi
    imLo := ∑ i ∈ Finset.range n, (rect i).imLo
    imHi := ∑ i ∈ Finset.range n, (rect i).imHi }

def ComplexRect2427.sumFinset {α : Type*}
    (rect : α → ComplexRect2427) (s : Finset α) : ComplexRect2427 :=
  { reLo := ∑ i ∈ s, (rect i).reLo
    reHi := ∑ i ∈ s, (rect i).reHi
    imLo := ∑ i ∈ s, (rect i).imLo
    imHi := ∑ i ∈ s, (rect i).imHi }

theorem ComplexRect2427.mem_sum {term : ℕ → ℂ}
    {rect : ℕ → ComplexRect2427} {n : ℕ}
    (hterm : ∀ i < n, (rect i).Mem (term i)) :
    (ComplexRect2427.sum rect n).Mem (∑ i ∈ Finset.range n, term i) := by
  constructor
  · simpa [ComplexRect2427.sum] using
      (Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => (hterm i (Finset.mem_range.mp hi)).1))
  constructor
  · simpa [ComplexRect2427.sum] using
      (Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => (hterm i (Finset.mem_range.mp hi)).2.1))
  constructor
  · simpa [ComplexRect2427.sum] using
      (Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => (hterm i (Finset.mem_range.mp hi)).2.2.1))
  · simpa [ComplexRect2427.sum] using
      (Finset.sum_le_sum (s := Finset.range n)
        (fun i hi => (hterm i (Finset.mem_range.mp hi)).2.2.2))

theorem ComplexRect2427.mem_sumFinset {α : Type*} {term : α → ℂ}
    {rect : α → ComplexRect2427} {s : Finset α}
    (hterm : ∀ i ∈ s, (rect i).Mem (term i)) :
    (ComplexRect2427.sumFinset rect s).Mem (∑ i ∈ s, term i) := by
  constructor
  · simpa [ComplexRect2427.sumFinset] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => (hterm i hi).1))
  constructor
  · simpa [ComplexRect2427.sumFinset] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => (hterm i hi).2.1))
  constructor
  · simpa [ComplexRect2427.sumFinset] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => (hterm i hi).2.2.1))
  · simpa [ComplexRect2427.sumFinset] using
      (Finset.sum_le_sum (s := s)
        (fun i hi => (hterm i hi).2.2.2))

/-! The natural interval evaluator prices a complex rectangle by taking the
largest absolute endpoint in each coordinate, then applying square/add/sqrt.
The following bridge is the logical soundness statement for that operation. -/

def ComplexRect2427.cornerNormSq (r : ComplexRect2427) : ℝ :=
  max |r.reLo| |r.reHi| ^ 2 + max |r.imLo| |r.imHi| ^ 2

noncomputable def ComplexRect2427.cornerNorm (r : ComplexRect2427) : ℝ :=
  Real.sqrt r.cornerNormSq

theorem ComplexRect2427.normSq_le_cornerNormSq {z : ℂ}
    {r : ComplexRect2427} (hz : r.Mem z) :
    Complex.normSq z ≤ r.cornerNormSq := by
  have hre : |z.re| ≤ max |r.reLo| |r.reHi| :=
    abs_le_max_abs_abs hz.1 hz.2.1
  have him : |z.im| ≤ max |r.imLo| |r.imHi| :=
    abs_le_max_abs_abs hz.2.2.1 hz.2.2.2
  have hre_sq : z.re ^ 2 ≤ (max |r.reLo| |r.reHi|) ^ 2 :=
    sq_le_sq' (abs_le.mp hre).1 (abs_le.mp hre).2
  have him_sq : z.im ^ 2 ≤ (max |r.imLo| |r.imHi|) ^ 2 :=
    sq_le_sq' (abs_le.mp him).1 (abs_le.mp him).2
  rw [Complex.normSq_apply, ComplexRect2427.cornerNormSq]
  exact add_le_add (by simpa [pow_two] using hre_sq)
    (by simpa [pow_two] using him_sq)

theorem ComplexRect2427.norm_le_cornerNorm {z : ℂ}
    {r : ComplexRect2427} (hz : r.Mem z) :
    ‖z‖ ≤ r.cornerNorm := by
  rw [Complex.norm_def, ComplexRect2427.cornerNorm]
  exact Real.sqrt_le_sqrt (ComplexRect2427.normSq_le_cornerNormSq hz)

end ConnesWeilRH.Dev
