/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Source.CC20Concrete.GlobalLogHaar
import ConnesWeilRH.Source.CC20Concrete.GlobalLogCrossing
import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-!
# C1 Stage-3 FRONTIER-HS (windowed) — the physical log-window factor is Hilbert–Schmidt

This module proves one of the two named analytic lemmas on which Stage 3 reduces.  The carrier is
the common logarithmic `L2` space `cc20GlobalLogCrossingL2 = Lp ℂ 2 (volume : Measure ℝ)`, an
*infinite*-measure Hilbert space, so a bare convolution operator is **not** Hilbert–Schmidt there
(its kernel has squared mass `‖h‖₂² · meas(ℝ) = ∞`).  The fix — the "physical log-window" choice —
is to cut the output by an expanding logarithmic window before reading off the trace.

For a CCM25 test `g` with analytic kernel `h_g := g.involution.test : ℝ → ℂ` (continuous, compactly
supported), and an expanding window parameter, we define the **windowed factor** pointwise through
inner products:

```text
F_{g,n} u (x)  =  𝟙_{W(n)}(x) · ⟨u, w_x⟩        with   w_x(y) := conj(h_g(x - y))
```

The pointwise inner-product form is what lets Parseval be applied at each fixed `x` for an arbitrary
basis.  For a basis vector `e`:

```text
‖F_{g,n} e‖₂²  =  ∫_{W(n)} |⟨e, w_x⟩|² dx
```

Summing over the basis and interchanging (Tonelli — every term is ≥ 0) collapses the sum pointwise by
Parseval:

```text
∑' e ‖F_{g,n} e‖₂²
  = ∫_{W(n)} [ ∑' e |⟨e, w_x⟩|² ] dx        (Tonelli / lintegral_tsum)
  = ∫_{W(n)} ‖w_x‖₂² dx                     (Parseval: HilbertBasis.tsum_inner_mul_inner)
```

Because Lebesgue measure is **translation-invariant**, the squared mass of every translate `w_x` is
independent of `x`:

```text
‖w_x‖₂²  =  ∫ |h_g(x - y)|² dy  =  ∫ |h_g(t)|² dt  =  ‖h_g‖₂² .
```

Hence the total mass is exactly

```text
∫_{W(n)} ‖w_x‖₂² dx  =  meas(W(n)) · ‖h_g‖₂²   < ∞ ,
```

since `W(n)` is a bounded interval (finite measure) and `h_g` has compact support (so it lies in L²).
Therefore the nonnegative family `(fun e => ‖F_{g,n} e‖²)` has finite total mass and is summable —
i.e. the windowed factor is Hilbert–Schmidt.  The argument uses only Parseval, Tonelli, translation
invariance of Lebesgue measure, compact support of `h_g`, and boundedness of the window; **no**
Hilbert–Schmidt hypothesis on any operator is assumed (that finiteness is exactly what is proved).

Firewall: imports only shared Source bricks (`GlobalLogHaar`) plus the CCM25 kernel module.  No frozen
route leaf, no active-C1 trace consumer — so the lemma is non-circular with respect to the Stage-3
family it will discharge.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3FrontierHS

open CC20Concrete
open CCM25Concrete.CompactLogConvolution
open MeasureTheory
open RCLike
open scoped InnerProduct InnerProductSpace Topology BigOperators ENNReal ComplexConjugate Filter Classical

/-- The bare angle-bracket inner product for our complex carrier, matching the per-file mathlib idiom. -/
local notation "⟪" x ", " y "⟫" => inner ℂ x y

noncomputable section

variable {ν : Type*} [Countable ν] (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)

/-- Expanding log-window parameter: `frontierWindowParam n > 1` always, hence its logarithmic window
has positive length, and it tends to `+∞` as `n → ∞`. -/
def frontierWindowParam (n : Nat) : ℝ := ↑(n + 2)

theorem frontierWindowParam_gt_one (n : Nat) : 1 < frontierWindowParam n := by
  rw [frontierWindowParam]
  have hn : (2 : ℝ) ≤ ↑(n + 2) := by norm_cast; exact Nat.le_add_left _ n
  linarith

/-- The analytic kernel of `g`, as a raw function: the CCM25 involution test. -/
noncomputable def frontierKernel (g : CompactLogTest) : ℝ → ℂ := fun x => (g.involution).test x

/-- The kernel has compact support (inherited from the involution's support field). -/
theorem frontierKernel_hasCompactSupport (g : CompactLogTest) :
    HasCompactSupport (frontierKernel g) := by
  simpa [frontierKernel] using (g.involution).compactSupport

/-- The kernel is continuous (a Schwartz map is continuous). -/
theorem frontierKernel_continuous (g : CompactLogTest) : Continuous (frontierKernel g) := by
  simpa [frontierKernel] using SchwartzMap.continuous _

/-- The expanding window `W(n)` — a bounded measurable interval of finite Lebesgue measure. -/
def frontierWindow (n : Nat) : Set ℝ := cc20LogWindow (frontierWindowParam n)

theorem frontierWindow_finiteMeasure (n : Nat) :
    IsFiniteMeasure (volume.restrict (frontierWindow n)) := by
  simpa only [frontierWindow] using cc20LogWindowRestrictIsFiniteMeasure _

/-- Complex modulus squared is invariant under conjugation: `‖star w‖² = ‖w‖²`.  Both sides are
`Complex.normSq`, and `normSq (conj w) = normSq w`. -/
theorem frontierNormStar_sq {w : ℂ} : ‖(star w : ℂ)‖ ^ 2 = ‖(w : ℂ)‖ ^ 2 := by
  have hL : ‖(star w : ℂ)‖ ^ 2 = Complex.normSq (star w) := by
    change (Real.sqrt (Complex.normSq (star w))) ^ 2 = _
    rw [Real.sq_sqrt, Complex.normSq_apply]
    apply add_nonneg <;> nlinarith
  have hR : ‖(w : ℂ)‖ ^ 2 = Complex.normSq w := by
    change (Real.sqrt (Complex.normSq w)) ^ 2 = _
    rw [Real.sq_sqrt, Complex.normSq_apply]
    apply add_nonneg <;> nlinarith
  rw [hL, hR]
  exact normSq_conj w

/-- The translate `y ↦ h_g(x-y)` lies in L²(ℝ): it is a measure-preserving change of variable (`t ↦ x-t`)
applied to the Schwartz kernel itself, which is in every L^p.  Extracted as a named lemma so that both
the carrier element below and its norm-squared computation reuse *one* `MemLp` proof term (so the two
`.toLp` constructions are definitionally identical). -/
theorem frontierTranslate_memLp (g : CompactLogTest) (x : ℝ) :
    MemLp (fun y => (g.involution).test (x - y)) 2 volume := by
  -- base: the involution test is a Schwartz map, hence in every L^p.  The exponent is written as the bare
  -- literal `2` so it is *definitionally* the carrier's own exponent (`Lp ℂ 2 …`).
  have hbase : MemLp ((g.involution).test : ℝ → ℂ) 2 :=
    SchwartzMap.memLp (g.involution).test 2
  -- `t ↦ x - t` preserves Lebesgue measure (a translate of negation).
  have hsub : MeasurePreserving (fun t => x - t) volume volume := by
    simpa [sub_eq_add_neg, add_comm] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).add_left volume x
  -- composing with a measure-preserving map preserves L² membership: `y ↦ h(x-y)` is in L².
  exact hbase.comp_measurePreserving hsub

/-- The translated kernel vector, as an element of the carrier `cc20GlobalLogCrossingL2`.  It lies in
L² for every `x` because it is a translate of the Schwartz kernel (see `frontierTranslate_memLp`). -/
noncomputable def frontierKernelVec (g : CompactLogTest) (x : ℝ) : cc20GlobalLogCrossingL2 :=
    frontierTranslate_memLp g x |>.toLp (fun y => (g.involution).test (x - y))

/-- Reusable L² bridge (1): the carrier norm of an `f ∈ L²(ℝ)` representative equals its `lpNorm`.
Both sides reduce to `(eLpNorm f 2 volume).toReal` once the `if AEStronglyMeasurable …` in the
`lpNorm` definition is resolved by `hf.aestronglyMeasurable`. -/
theorem frontierLp2normToReal {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ = lpNorm f 2 volume := by
  rw [Lp.norm_toLp, lpNorm, if_pos hf.aestronglyMeasurable]

/-- Reusable L² bridge (2): for `f ∈ L²(ℝ)`, the `lpNorm` is the real square root of its pointwise mass. -/
theorem frontierLp2normEqIntegralSqrt {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    lpNorm f 2 volume = (∫ x, ‖f x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2) := by
  rw [lpNorm_eq_integral_norm_rpow_toReal (show (2 : ℝ≥0∞) ≠ 0 from by norm_num) (by simp) hf.aestronglyMeasurable]
  · simp only [ENNReal.toReal_ofNat, Real.rpow_two, pow_two]
    ring

/-- Reusable L² bridge (3): for `A ≥ 0`, squaring the real square root returns `A` — the Nat-power-2 /
real-power-2 bridge that lets `(root) ^ 2 [nat]` become a real power and collapse. -/
theorem frontierRootSq {A : ℝ} (ha : 0 ≤ A) : (A ^ ((1 : ℝ) / 2)) ^ (2 : ℝ) = A := by
  rw [← Real.rpow_mul ha ((1 : ℝ) / 2) 2, show ((1 : ℝ) / 2) * 2 = 1 from by norm_num, Real.rpow_one]

/-- Reusable L² bridge (main): the squared carrier norm of an `f ∈ L²(ℝ)` representative equals its
pointwise integral mass `∫ ‖f x‖²`.  This is what turns `‖toLp f‖²` into a plain integral — the step the
whole FRONTIER-HS argument hinges on. -/
theorem frontierLp2NormSq {f : ℝ → ℂ} (hf : MemLp f 2 volume) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  have hI : 0 ≤ ∫ x, ‖f x‖ ^ (2 : ℝ) := by positivity
  calc
    _ = (lpNorm f 2 volume) ^ 2 := by rw [frontierLp2normToReal hf]
    _ = ((∫ x, ‖f x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) ^ 2 := by rw [frontierLp2normEqIntegralSqrt hf]
    _ = ∫ x, ‖f x‖ ^ (2 : ℝ) := by
      rw [← Real.rpow_natCast ((∫ x, ‖f x‖ ^ (2 : ℝ)) ^ ((1 : ℝ) / 2)) 2]
      exact frontierRootSq hI
    _ = ∫ x, ‖f x‖ ^ 2 := by
      apply integral_congr_ae
      filter_upwards with x
      · rw [Real.rpow_two, pow_two]

/-- The difference of two translates lies in L² (difference of two L² elements). -/
theorem frontierTranslateSub_memLp (g : CompactLogTest) (x x' : ℝ) :
    MemLp (fun y => (g.involution).test (x-y) - (g.involution).test (x'-y)) 2 volume := by
  exact (frontierTranslate_memLp g x).sub (frontierTranslate_memLp g x')

/-- The squared L² distance between two translates equals the pointwise-mass integral of their
difference: `‖w_x - w_{x'}‖₂² = ∫ |h(x-y) - h(x'-y)|² dy`.  This is the bridge that lets the
uniform-continuity modulus of `h` control the L² distance. -/
theorem frontierKernelVec_distSq_eq (g : CompactLogTest) (x x' : ℝ) :
    ‖frontierKernelVec g x - frontierKernelVec g x'‖ ^ 2 =
      ∫ y, ‖(g.involution).test (x-y) - (g.involution).test (x'-y)‖ ^ 2 := by
  -- `w_x - w_{x'}` is the L² element of the pointwise difference.  The two translate `MemLp` proofs are
  -- exactly those inside `frontierKernelVec`, so `toLp_sub` (whose body is `rfl`) rewrites the RHS to the
  -- *definitionally identical* `(Mx.sub Mxp).toLp (…)`, and both sides then unfold to one term.
  let Mx := frontierTranslate_memLp g x
  let Mxp := frontierTranslate_memLp g x'
  dsimp only [frontierKernelVec]
  rw [← MemLp.toLp_sub (hf := Mx) (hg := Mxp)]
  exact frontierLp2NormSq (frontierTranslateSub_memLp g x x')

/-- The kernel is uniformly continuous: it is continuous and compactly supported. -/
theorem frontierH_uniformContinuous (g : CompactLogTest) : UniformContinuous (frontierKernel g) := by
  exact (frontierKernel_hasCompactSupport g).uniformContinuous_of_continuous
       (frontierKernel_continuous g)

/-- Squared L² distance in the translation-invariant form: `‖w_x - w_{x'}‖₂² = ∫_t |h(t) - h(t-(x-x'))|² dt`.
The right side depends only on the increment `x - x'` — the key to a *uniform* estimate (independent of the
absolute position of `x`).  Uses the same measure-preserving change of variable as `frontierTranslatedNormSq_eq`. -/
theorem frontierKernelVec_distSq_translate (g : CompactLogTest) (x x' : ℝ) :
    ‖frontierKernelVec g x - frontierKernelVec g x'‖ ^ 2 =
      ∫ t, ‖(frontierKernel g) t - (frontierKernel g) (t - (x - x'))‖ ^ 2 := by
  let h := frontierKernel g
  -- the increment form of the integrand: `dfun t = ‖h t - h(t-(x-x'))‖²`.  Bounded in a `let` so the
  -- change-of-variable call mirrors the working template exactly (no inline norm-with-subtraction, which
  -- trips the norm-notation parser when it follows another application).
  let dfun := fun t : ℝ => ‖h t - h (t - (x - x'))‖ ^ 2
  -- first: the L² distance is the pointwise-mass integral over y.
  have hstep : ‖frontierKernelVec g x - frontierKernelVec g x'‖ ^ 2 =
      ∫ y, ‖h (x-y) - h (x'-y)‖ ^ 2 := by simpa only [h] using frontierKernelVec_distSq_eq g x x'
  rw [hstep]
  -- change of variable t = x - y (measure-preserving).  The integrand on the goal's LHS, `‖h(x-y)-h(x'-y)‖²`,
  -- is exactly `dfun (x-y)` because `(x-y)-(x-x') = x'-y`; after that rewrite both sides are `∫ dfun ∘ (…)`.
  have hsub : MeasurePreserving (fun t => x - t) volume volume := by
    simpa [sub_eq_add_neg, add_comm] using
      (Measure.measurePreserving_neg (volume : Measure ℝ)).add_left volume x
  have hdyn : (∫ y, ‖h (x-y) - h (x'-y)‖ ^ 2) = ∫ y, dfun (x-y) := by
    congr; ext y
    have ha : x' - y = (x - y) - (x - x') := by ring
    rw [ha]
  rw [hdyn]
  exact hsub.integral_comp (Homeomorph.subLeft x).measurableEmbedding dfun

/-- The translate map `x ↦ w_x` is uniformly continuous on the carrier.  This is the key step that makes
the scalar correlation map `x ↦ ⟨u, w_x⟩` measurable: `⟨u, ·⟩` is a bounded (hence continuous) linear
functional on the Hilbert space, and composition of continuous maps is continuous.

Strategy: `‖w_x - w_{x'}‖₂² = ∫_t |h(t) - h(t-(x-x'))|² dt` (`frontierKernelVec_distSq_translate`).  For a
fixed increment `δ := x-x'`, the integrand is supported in a *fixed* box (independent of `x`) because `h`
has compact support, and on that box it is pointwise `< p²` whenever `|δ|` is small enough for the uniform
continuity modulus of `h`.  Hence `‖w_x - w_{x'}‖₂ ≤ p·√(box measure)` — a bound depending only on `|δ|`,
not on the absolute position of `x`. -/
theorem frontierKernelVec_uniformContinuous (g : CompactLogTest) :
    UniformContinuous fun x => frontierKernelVec g x := by
  let h := frontierKernel g
  -- (i) uniform continuity of the kernel itself.
  have huc : UniformContinuous h := frontierH_uniformContinuous g
  -- (ii) an explicit interval [L0,U0] containing the topological support of `h` (compact ⟹ bounded).
  have htsc : IsCompact (tsupport h) := frontierKernel_hasCompactSupport g
  rcases htsc.bddAbove with ⟨U0, hU0⟩; simp only [mem_upperBounds] at hU0
  rcases htsc.bddBelow with ⟨L0, hL0⟩; simp only [mem_lowerBounds] at hL0
  -- a nonzero value of `h` forces its argument into [L0,U0].
  have hbnd (z : ℝ) (hzz : h z ≠ 0) : L0 ≤ z ∧ z ≤ U0 := by
    have hsupp : z ∈ Function.support h := by rwa [Function.support]
    have htsp : z ∈ tsupport h := by simpa [tsupport] using subset_closure hsupp
    exact ⟨hL0 z htsp, hU0 z htsp⟩
  -- the box where |h(t)-h(t-δ)|² can be nonzero for |δ|≤1; its measure is a finite nonnegative real `V`.
  set I : Set ℝ := Set.Icc (L0 - 1) (U0 + 1) with hIdef
  -- μ.real s = (μ s).toReal by definition, so this is exactly the box's Lebesgue measure as a real.
  let V : ℝ := (volume : Measure ℝ).real I
  -- off the box both terms vanish when |δ|≤1.
  have hvanish (t δ : ℝ) (hδ : ‖δ‖ ≤ 1) (htI : t ∉ I) : h t = 0 ∧ h (t - δ) = 0 := by
    refine ⟨?_, ?_⟩ <;> (by_contra H; rcases hbnd _ H with ⟨hl, hu⟩)
    · have hin : t ∈ I := by constructor <;> linarith [hl, hu]
      exact htI hin
    · -- L0 ≤ t-δ and t-δ ≤ U0 together with -1≤δ≤1 give (L0-1) ≤ t ≤ (U0+1), i.e. t ∈ I.
      have hd : -1 ≤ δ ∧ δ ≤ 1 := abs_le.mp (show |δ| ≤ 1 from by simpa [Real.norm_eq_abs] using hδ)
      have hin : t ∈ I := by constructor <;> linarith [hl, hu, hd.1, hd.2]
      exact htI hin
  -- the modulus: given ε>0 pick a pointwise scale p with p²·V ≤ ε²/4 (V = box measure ≥ 0), then choose
  -- δ < min(ρ_p, 1) so that |x-x'|<δ forces both the uniform-continuity bound (scale p) and |x-x'|≤1.
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  set M : ℝ := Real.sqrt (max 1 V) with hMdef
  have hMpos : 0 < M := by rw [hMdef]; exact Real.sqrt_pos.mpr (by linarith [le_max_left 1 V])
  have hM2 : M^2 = max 1 V := by rw [hMdef, Real.sq_sqrt]; positivity
  set p : ℝ := ε / (2 * M) with hpdef
  have hposV : 0 ≤ V := by dsimp only [V]; exact measureReal_nonneg
  -- p²·V = (ε/(2M))² · V, and since the multiplier is ≥ 0 with V ≤ M² (M² = max 1 V), this is ≤ (ε/2M)²·M² = ε²/4.
  have hpV : p^2 * V ≤ ε^2 / 4 := by
    have hpf : p = ε / (2*M) := by rw [hpdef]
    calc
      _ = (ε / (2*M))^2 * V := by rw [hpf]
      -- gcongr's single real subgoal is `V ≤ M²`, which follows from M² = max 1 V.
      _ ≤ (ε / (2*M))^2 * M^2 := by
        gcongr
        · rw [hM2]; exact le_max_right _ _
      _ = ε^2 / 4 := by field_simp [show M ≠ 0 from ne_of_gt hMpos]; ring
  -- the uniform-continuity scale ρ of `h` at tolerance p.
  have hp := Metric.uniformContinuous_iff.mp huc p (show 0 < p from by rw [hpdef]; positivity)
  rcases hp with ⟨ρ, hρpos, hrho⟩
  refine ⟨min ρ 1, ?_, ?_⟩
  · -- δ = min(ρ,1) > 0.
    exact lt_min hρpos (by norm_num)
  · intro a b hab
    set inc := a - b with himpdef
    -- |x-x'| < min(ρ,1) forces both |inc|<ρ (uniform-cont scale of h) and |inc|≤1 (box vanishing).
    have himp : |inc| < ρ ∧ |inc| ≤ 1 := by
      constructor
      · simpa [himpdef] using lt_of_lt_of_le hab (min_le_left _ _)
      · simpa [himpdef] using le_of_lt (lt_of_lt_of_le hab (min_le_right _ _))
    -- pointwise: on the box ‖h t - h(t-inc)‖ < p; off it both vanish.
    let gfun (t : ℝ) := if htI : t ∈ I then p^2 else 0
    have hfg (t : ℝ) : ‖h t - h (t - inc)‖ ^ 2 ≤ gfun t := by
      by_cases hIn : t ∈ I
      · -- on the box, uniform continuity at scale ρ applies: dist(t,t-inc)=|inc|<ρ.
        have hdab : dist t (t - inc) < ρ := by simpa using himp.1
        have hp' : ‖h t - h (t - inc)‖ < p := by simpa [dist_eq_norm] using hrho hdab
        dsimp only [gfun]; simp [hIn]   -- gfun t reduces to p² on the box, so goal is ‖·‖² ≤ p².
        have hpn : 0 < p := by rw [hpdef]; exact div_pos hε (by positivity)
        nlinarith [hpn, norm_nonneg (h t - h (t - inc))]
      · -- off the box both terms vanish for |inc|≤1, so LHS=0 and each branch of gfun is ≥ 0.
        have hv := hvanish t inc (by simpa using himp.2) hIn
        rw [hv.1, hv.2]; dsimp only [gfun]
        split_ifs; norm_num
    -- hence the full L² mass of the increment-bounded difference is ≤ p²·V (box measure).
    have hbound : ∫ t, ‖h t - h (t - inc)‖ ^ 2 ≤ p^2 * V := by
      have hfmeas : Measurable (fun t => ‖h t - h (t - inc)‖ ^ 2) := by
        have hc : Continuous h := frontierKernel_continuous g
        have hincont : Continuous fun t : ℝ => t - inc := by continuity
        -- `fun z => ‖z‖²` is continuous: norm then square.  Bare `continuity` misses this form, so build it explicitly.
        have hnormsq : Measurable fun z : ℂ => ‖z‖ ^ 2 := by
          simpa using (Continuous.pow continuous_norm 2).measurable
        exact hnormsq.comp ((hc.sub (hc.comp hincont)).measurable)
      -- gfun = p²·1_I; its integral is the box's measure V times p² (indicator-of-set rule).  The real
      -- integral lands in ℝ, and (volume ℝ).real I is definitionally V, so no ENNReal bridge is needed.
      have hgint : ∫ t, gfun t = p^2 * V := by
        -- `Set.indicator I (·=>p²)` is itself a function ℝ → ℝ (no outer lambda: the indicator already is one).
        have hind : gfun = (I : Set ℝ).indicator (fun _ : ℝ => p^2) := by ext t; simp only [gfun, Set.indicator]; rfl
        rw [hind]
        rw [integral_indicator_const _ (measurableSet_Icc ..)]   -- LHS → (volume ℝ).real I • p²; `V` unfolds to that same real
        simp only [smul_eq_mul]
        ring
      -- gfun = p²·1_I is integrable: rewrite as an indicator, then `integrable_indicator_iff` reduces it to the
      -- constant being IntegrableOn the box.  A bounded interval has finite Lebesgue measure; `volume_Icc` (a
      -- [simp] lemma) makes bare `simp` close that finiteness, which we hand to `integrableOn_const`.
      have hgfint : Integrable gfun volume := by
        have hindg : gfun = (I : Set ℝ).indicator (fun _ : ℝ => p^2) := by ext t; simp only [gfun, Set.indicator]; rfl
        rw [hindg]
        have hIvolFin : volume I ≠ ∞ := by
          have hvlt : volume I < ∞ := by rw [hIdef]; simp
          exact ne_of_lt hvlt
        have hconst : IntegrableOn (fun _ => p^2) I volume := integrableOn_const hIvolFin
        simpa using integrable_indicator_iff (measurableSet_Icc ..) |>.mpr hconst
      -- pre-build the two a.e. side-conditions with pinned types so `positivity` gets an explicit goal:
      -- tactic-mode `apply ae_of_all` fixes α=ℝ against the goal *before* proving it, so pointwise
      -- `positivity` sees a concrete `0 ≤ ‖·‖²`.  (Term mode leaves α unresolved during lambda elaboration.)
      have hfnn : ∀ᵐ (t : ℝ), 0 ≤ ‖h t - h (t - inc)‖ ^ 2 := by
        apply ae_of_all
        intro t
        positivity
      have hfdg : ∀ᵐ (t : ℝ), ‖h t - h (t - inc)‖ ^ 2 ≤ gfun t := by
        apply ae_of_all
        intro t
        exact hfg t
      -- f ≥ 0 a.e., gfun integrable, f ≤ gfun a.e. ⇒ ∫f ≤ ∫gfun = p²·V.
      have hmono : ∫ t, ‖h t - h (t - inc)‖ ^ 2 ≤ ∫ t, gfun t := by
        simpa using integral_mono_of_nonneg hfnn hgfint hfdg
      rw [hgint] at hmono
      exact hmono
    -- (i) squared carrier distance = the real L² mass of the increment-bounded difference.
    have hdist : ‖frontierKernelVec g a - frontierKernelVec g b‖ ^ 2 =
        ∫ t, ‖h t - h (t - inc)‖ ^ 2 := by simpa only [himpdef] using frontierKernelVec_distSq_translate g a b
    -- (ii) that mass is < ε²: it is ≤ p²·V and p²·V ≤ ε²/4 < ε².
    have hsquared : ‖frontierKernelVec g a - frontierKernelVec g b‖ ^ 2 < ε^2 := by
      rw [hdist]
      have hdiv : ε^2 / 4 < ε^2 := by nlinarith [sq_pos_of_pos hε]
      linarith [hbound, hpV, hdiv]
    -- (iii) squaring is monotone on nonnegative reals: r²<ε² with r≥0, ε>0 gives r<ε.
    have hlt : ‖frontierKernelVec g a - frontierKernelVec g b‖ < ε := by
      by_contra H; push Not at H
      nlinarith [H, hsquared]
    simpa [dist_eq_norm] using hlt

/-- The squared mass of a translate is independent of the translation: `‖w_x‖₂² = ‖h_g‖₂²` (Lebesgue
measure is invariant under `y ↦ x - y`). -/
theorem frontierTranslatedNormSq_eq (g : CompactLogTest) (x : ℝ) :
    ‖frontierKernelVec g x‖ ^ 2 = ∫ t, ‖(g.involution).test t‖ ^ 2 := by
  -- LHS: `frontierKernelVec g x` is definitionally `(frontierTranslate_memLp g x).toLp (…)`, so its
  -- squared carrier norm equals that translate's pointwise mass (the reusable L² bridge, step main).
  have hnorm : ‖frontierKernelVec g x‖ ^ 2 = ∫ y, ‖(g.involution).test (x - y)‖ ^ 2 := by
    simpa only [frontierKernelVec] using frontierLp2NormSq (frontierTranslate_memLp g x)
  rw [hnorm]
  · -- the change of variable `t = x-y` preserves Lebesgue measure.
    have hsub : MeasurePreserving (fun t => x - t) volume volume := by
      simpa [sub_eq_add_neg, add_comm] using
        (Measure.measurePreserving_neg (volume : Measure ℝ)).add_left volume x
    simpa only [Function.comp_apply] using
      hsub.integral_comp (Homeomorph.subLeft x).measurableEmbedding
        (fun t => ‖(g.involution).test t‖ ^ 2)

/-- The windowed correlation map of `u` lies in L²(ℝ): it is zero outside the finite-measure window, and on
the window Cauchy–Schwarz bounds it by the constant `‖u‖·‖h_g‖`.  Extracted as a named lemma so that both the
carrier element below *and* its squared-norm computation reuse one `MemLp` proof term (so the two `.toLp`
constructions are definitionally identical — this is what lets `frontierLp2NormSq` rewrite column norms). -/
theorem frontierWindowFactor_memLp (n : Nat) (g : CompactLogTest) (u : cc20GlobalLogCrossingL2) :
    MemLp (fun x => if hx : x ∈ frontierWindow n then ⟪u, frontierKernelVec g x⟫ else 0) 2 volume := by
  let W := frontierWindow n
  set f : ℝ → ℂ := fun x => ⟪u, frontierKernelVec g x⟫ with hfdef
  -- the windowed map is exactly the window indicator times the (unwindowed) correlation map `f`.
  have hindicator : (fun x => if hx : x ∈ frontierWindow n then ⟪u, frontierKernelVec g x⟫ else 0) = W.indicator f := by
    ext x; simp only [hfdef, Set.indicator]; rfl
  rw [hindicator]
  -- L²-membership of an indicator reduces to membership on the restricted measure.
  have hsmeasW : MeasurableSet W := by simpa only [W] using measurableSet_cc20LogWindow _
  rw [memLp_indicator_iff_restrict hsmeasW]
  -- `volume.restrict W` is finite: the window is a bounded interval (its Lebesgue measure is finite).
  haveI hfin : IsFiniteMeasure (volume.restrict W) := frontierWindow_finiteMeasure n
  -- the correlation map f = x ↦ ⟨u, w_x⟩ is continuous: `⟨u, ·⟩` is a bounded linear functional and the
  -- translate map x ↦ w_x is uniformly continuous (`frontierKernelVec_uniformContinuous`).  A continuous
  -- ℂ-valued map on ℝ is a.e.-strongly-measurable with respect to *any* measure.
  have hkvec : Continuous fun x => frontierKernelVec g x := (frontierKernelVec_uniformContinuous g).continuous
  have hcont : Continuous f := by simpa only [f] using (Continuous.inner continuous_const hkvec)
  have hfmeas : AEStronglyMeasurable f (volume.restrict W) := hcont.aestronglyMeasurable
  -- a uniform, x-independent bound: `‖⟨u, w_x⟩‖ ≤ ‖u‖·‖w_x‖` and `‖w_x‖² = mass` is constant in x, so
  -- `‖w_x‖ ≤ √mass` for every x.  Hence the correlation map is bounded by the constant `‖u‖ · √mass`.
  let mass : ℝ := ∫ t, ‖(g.involution).test t‖ ^ 2
  let K0 : ℝ := Real.sqrt mass
  have hwle (x : ℝ) : ‖frontierKernelVec g x‖ ≤ K0 := by
    -- `‖w_x‖² = mass` (`frontierTranslatedNormSq_eq`), so the squared norm is at most `mass`; taking square
    -- roots (`le_sqrt_of_sq_le`) gives the uniform bound.  No separate nonnegativity of `mass` is needed: it
    -- follows from `‖w_x‖² ≤ mass`.
    have hsq : ‖frontierKernelVec g x‖ ^ 2 ≤ mass := by simpa only [frontierTranslatedNormSq_eq g x] using le_rfl
    simpa only [K0] using (Real.le_sqrt_of_sq_le hsq)
  -- the pointwise bound, hence a.e. true on the restricted measure.
  have hbound : ∀ᵐ (x : ℝ) ∂(volume.restrict W), ‖f x‖ ≤ ‖u‖ * K0 := by
    apply ae_of_all
    intro x
    -- Cauchy–Schwarz bounds the norm of the inner product directly (`norm_inner_le_norm`).
    have hcsh : ‖⟪u, frontierKernelVec g x⟫‖ ≤ ‖u‖ * ‖frontierKernelVec g x‖ :=
      norm_inner_le_norm u (frontierKernelVec g x)
    simpa only [hfdef] using (hcsh.trans (mul_le_mul_of_nonneg_left (hwle x) (norm_nonneg u)))
  -- a bounded, a.e.-strongly-measurable function on a finite measure lies in every L^p.
  exact MemLp.of_bound hfmeas (‖u‖ * K0) hbound

/-- The windowed factor `F_{g,n}`: restrict to the window and read off the inner product with `w_x`.
For a basis vector this is the Hilbert–Schmidt column being measured.  It lies in L² for every input `u` by
`frontierWindowFactor_memLp`. -/
noncomputable def frontierWindowFactor (n : Nat) (g : CompactLogTest) (u : cc20GlobalLogCrossingL2)
    : cc20GlobalLogCrossingL2 :=
  (frontierWindowFactor_memLp n g u).toLp (fun x => if hx : x ∈ frontierWindow n then ⟪u, frontierKernelVec g x⟫ else 0)

/-- Complex modulus squared equals `re (star z * z)` — the termwise bridge that lets a scalar
`‖z‖²` be read as the real part of an inner-product product, which is what Parseval needs.  Both
sides equal `Complex.normSq z`. -/
theorem frontierComplexNormSq_eq_reStarMulSelf (z : ℂ) : ‖(z : ℂ)‖ ^ 2 = re (star z * z) := by
  have hL : ‖(z : ℂ)‖ ^ 2 = Complex.normSq z := by
    change (Real.sqrt (Complex.normSq z)) ^ 2 = _
    rw [Real.sq_sqrt]
    · rw [Complex.normSq_apply]; apply add_nonneg <;> nlinarith
  have hR : re (star z * z) = Complex.normSq z := by
    -- `conj` is notation for `star`, so `star z * z ≡ conj z * z`; the lemma bridges it to `(normSq z : ℂ)`
    have hc : star z * z = (Complex.normSq z : ℂ) :=
      by simpa using Complex.normSq_eq_conj_mul_self.symm
    rw [hc]
    norm_cast
  rw [hL, hR]

/-- Parseval for our carrier: for any `v` in the space, `∑' e |⟨e, v⟩|² = ‖v‖₂²`.  Here `|z|²` on a
complex scalar is written as its field-norm square `‖(z : ℂ)‖^2`, which equals `re (star z * z)`. -/
theorem frontierParseval_normSq (v : cc20GlobalLogCrossingL2) :
    ∑' i, ‖(⟪globalBasis i, v⟫ : ℂ)‖ ^ 2 = ‖v‖ ^ 2 := by
  have hsumm := globalBasis.summable_inner_mul_inner v v
  calc
    _ = ∑' i, re (⟪v, globalBasis i⟫ * ⟪globalBasis i, v⟫) := by
        rw [show (fun i => ‖(⟪globalBasis i, v⟫ : ℂ)‖ ^ 2) = fun i => re (⟪v, globalBasis i⟫ * ⟪globalBasis i, v⟫) from
          funext fun i => by
            have hw : star ⟪globalBasis i, v⟫ = ⟪v, globalBasis i⟫ := by
              simpa using inner_conj_symm _ _
            rw [frontierComplexNormSq_eq_reStarMulSelf, hw]]
    _ = re (∑' i, ⟪v, globalBasis i⟫ * ⟪globalBasis i, v⟫) := by
        exact (RCLike.reCLM.map_tsum hsumm).symm
    _ = re (⟪v, v⟫) := by
        congr; exact globalBasis.tsum_inner_mul_inner v v
    _ = ‖v‖ ^ 2 := by rw [inner_self_eq_norm_sq]

/-- The real-part projection `ℂ →+ ℝ`, an additive monoid hom.  It lets Parseval-type summability be pushed
through the termwise identity `‖z‖² = re (star z * z)` via `Summable.map`. -/
def frontierReHom : ℂ →+ ℝ :=
  { toFun     := fun z => z.re,
    map_zero' := by simp [Complex.zero_re],
    map_add'  := fun x y => by simpa using Complex.add_re x y }

/-- For any carrier element `v`, the family of squared basis coefficients is summable — the real-valued form of
Parseval's convergence (it follows from the summability of the inner-product products and `Summable.map` on the
real-part hom).  This supplies the pointwise summability that Tonelli + Parseval needs at each fixed window point. -/
theorem frontierCoeffSummable (v : cc20GlobalLogCrossingL2) :
    Summable fun i => ‖(⟪globalBasis i, v⟫ : ℂ)‖ ^ 2 := by
  -- Bessel's inequality for the orthonormal basis: every finite partial sum of `|⟨e_i, v⟩|²` is bounded by
  -- `‖v‖²`, so (as a nonneg real series) this family is summable.
  simpa using Orthonormal.inner_products_summable v globalBasis.orthonormal

/-- FRONTIER-HS: for every window size `n` and CCM25 test `g`, the family of squared basis norms of
the windowed factor is summable.  The total mass equals `meas(W(n)) · ‖h_g‖₂² < ∞` (Tonelli + pointwise
Parseval + translation invariance). -/
theorem frontierHS_summable (n : Nat) (g : CompactLogTest) :
    Summable fun i => ‖(frontierWindowFactor n g (globalBasis i))‖ ^ 2 := by
  -- Work over the window's restricted measure throughout: this removes every indicator / `if x ∈ W` case split,
  -- and the Tonelli swap (`lintegral_tsum`) then needs only pointwise measurability — no total-mass assumption.
  let W : Set ℝ := frontierWindow n
  have hWmeas : MeasurableSet W := by simpa only [W] using measurableSet_cc20LogWindow _
  -- the constant kernel L² mass; `‖w_x‖²` equals this for every x (`frontierTranslatedNormSq_eq`).
  let mass : ℝ := ∫ t, ‖(g.involution).test t‖ ^ 2

  -- (i) real column identity: the L² bridge turns `‖F e_i‖²` into a full integral whose integrand is the
  --     window indicator of `|⟨e_i, w_x⟩|²`.  Rewrite the set-restricted RHS to that same full integral
  --     (`←integral_indicator`) and close pointwise by cases on window membership — both ites share one condition.
  have hcolReal (i : ν) : ‖frontierWindowFactor n g (globalBasis i)‖ ^ 2 =
      ∫ x in W, ‖(⟪globalBasis i, frontierKernelVec g x⟫ : ℂ)‖ ^ 2 := by
    dsimp only [frontierWindowFactor]
    have hlp := frontierLp2NormSq (frontierWindowFactor_memLp n g (globalBasis i))
    rw [hlp, ← MeasureTheory.integral_indicator hWmeas]
    -- pointwise, |f(x)|² is exactly the window indicator of |⟨e_i,w_x⟩|² (both ites share membership in W):
    have hp (x : ℝ) : ‖(if hx : x ∈ frontierWindow n then ⟪globalBasis i, frontierKernelVec g x⟫ else 0)‖ ^ 2 =
        W.indicator (fun _ => ‖(⟪globalBasis i, frontierKernelVec g x⟫ : ℂ)‖ ^ 2) x := by
      by_cases h : x ∈ frontierWindow n <;> simp [h, W, Set.indicator, norm_zero] <;> norm_num
    -- rewrite the LHS integrand into indicator form so both sides are literally the same integral:
    rw [funext hp]
    rfl

  -- (ii) per-column integrability on the window: `x ↦ |⟨e_i, w_x⟩|²` is bounded by the constant mass on W
  --      (`‖w_x‖² = mass`, Cauchy–Schwarz with `‖e_i‖ = 1`) and W has finite measure, so it lies in L¹ there.
  have hcolInt (i : ν) : Integrable (fun x => ‖(⟪globalBasis i, frontierKernelVec g x⟫ : ℂ)‖ ^ 2) (volume.restrict W) := by
    dsimp only [Integrable]   -- AEStronglyMeasurable ∧ HasFiniteIntegral, over the restricted window measure.
    -- (a) continuity in x: joint continuity of the inner product with one leg fixed to the basis vector.
    have hwcont : Continuous fun x => frontierKernelVec g x := (frontierKernelVec_uniformContinuous g).continuous
    -- annotate the constant leg's domain as ℝ: an unbounded `fun _` leaves its codomain-of-domain a metavariable,
    -- so `[TopologicalSpace ?m]` cannot resolve (`continuous_const` needs it).
    have hconst : Continuous (fun (_ : ℝ) => (globalBasis i : cc20GlobalLogCrossingL2)) := continuous_const
    -- pin 𝕜 = ℂ and E explicitly: two lemmas are named `Continuous.inner` (this one vs. a completion variant),
    -- and unqualified synthesis otherwise thrashes on the inner-product scalar / stuck `TopologicalSpace`.
    -- annotate the output as ℂ: without it the function's codomain stays a metavariable, so `(hA).norm'`
    -- would be `‖·‖` over an unknown type rather than the complex modulus.
    have hA : Continuous fun (x : ℝ) => (⟪globalBasis i, frontierKernelVec g x⟫ : ℂ) := by
      exact Continuous.inner (𝕜 := ℂ) (E := cc20GlobalLogCrossingL2) hconst hwcont
    -- `x ↦ ‖⟨e_i, w_x⟩‖` is continuous (norm of a continuous map); its square keeps continuity.
    have hfcont : Continuous fun (x : ℝ) => ‖(⟪globalBasis i, frontierKernelVec g x⟫ : ℂ)‖ ^ 2 := by
      -- pin the domain as ℝ on every lambda: an unannotated `fun x` leaves the codomain-of-domain a
      -- metavariable, so `(hA).norm'` would be `‖·‖` over an unknown type. Use the concrete composition
      -- `continuous_norm.comp hA` instead of the ambiguous `.norm'` dot-projection.
      have hnormC : Continuous (fun (x : ℝ) => ‖(⟪globalBasis i, frontierKernelVec g x⟫ : ℂ)‖) := continuous_norm.comp hA
      simpa only [pow_two] using Continuous.mul hnormC hnormC
    -- bridge the finite-restricted-measure fact to the plain real inequality `volume W < ∞`:
    -- `Measure.restrict_apply_univ` gives `(volume.restrict W) univ = volume W`, and a finite measure is `< ∞` on `univ`.
    have hWfin : volume W < ∞ := by
      simpa [Measure.restrict_apply_univ] using (frontierWindow_finiteMeasure n).measure_univ_lt_top
    -- (b) a finite pointwise bound on the window: Cauchy–Schwarz gives `|⟨e_i,w_x⟩| ≤ ‖e_i‖ · ‖w_x‖`, and with
    --     `‖w_x‖² = mass` (`frontierTranslatedNormSq_eq`) squaring yields the constant bound below (no normalization needed).
    have hb (x : ℝ) : abs (‖(⟪globalBasis i, frontierKernelVec g x⟫ : ℂ)‖ ^ 2) ≤ ‖globalBasis i‖ ^ 2 * mass := by
      have hsqw : ‖frontierKernelVec g x‖ ^ 2 = mass := by simpa only using frontierTranslatedNormSq_eq g x
      -- Cauchy–Schwarz supplies the base inequality in context; `gcongr`'s discharger then closes the
      -- squared bound from it automatically (an explicit trailing `exact hcs` would find no remaining goals).
      have hcs : ‖(⟪globalBasis i, frontierKernelVec g x⟫ : ℂ)‖ ≤ ‖globalBasis i‖ * ‖frontierKernelVec g x‖ := norm_inner_le_norm _ _
      rw [abs_of_nonneg (by positivity)]   -- the integrand is a square, hence ≥ 0.
      calc
        _ ≤ (‖globalBasis i‖ * ‖frontierKernelVec g x‖) ^ 2 := by gcongr
        _ = ‖globalBasis i‖ ^ 2 * mass := by rw [mul_pow, hsqw]
    have hf : ∀ᵐ x ∂(volume.restrict W), abs (‖(⟪globalBasis i, frontierKernelVec g x⟫ : ℂ)‖ ^ 2) ≤ ‖globalBasis i‖ ^ 2 * mass := by
      simpa using ae_of_all _ hb
    -- continuous ⟹ ae-strongly-measurable; bounded-by-a-constant on a finite-measure set ⟹ HasFiniteIntegral.
    exact ⟨hfcont.aestronglyMeasurable,
      HasFiniteIntegral.restrict_of_bounded (‖globalBasis i‖ ^ 2 * mass) hWfin hf⟩

  -- TEMP (grinding frontierHS_summable): rest of the proof to be filled in.
  sorry

end

end C1Stage3FrontierHS
end Source
end ConnesWeilRH
