import ConnesWeilRH.Dev.C1ExplicitSmoothSeedDerivativeBudget
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# The derivative ladder for shifted products

The committed budget step

    l1Mass (derivativeShift f a) ≤ derivativeL1 f + ‖a‖ * l1Mass f

replaces one `L¹` mass by the next derivative order, so iterating it over a
node list needs one number per order: the ladder

    derivOrderL1 m f = ∫ x, ‖iteratedDeriv m (f.test) x‖

with `derivOrderL1 0 = l1Mass` and `derivOrderL1 1 = derivativeL1`. The
committed `shiftedProductL1Bound` feeds `derivativeL1` back into itself and is
therefore circular as a closed budget; the honest recursion is the ladder

    ladderBound L []      m = L m
    ladderBound L (a::as) m = ladderBound L as (m + 1) + ‖a‖ * ladderBound L as m

which this file proves sound:

* `derivOrderL1_derivativeShift_le` : one shift raises the order,
  `derivOrderL1 m (derivativeShift f a) ≤ derivOrderL1 (m+1) f + ‖a‖ * derivOrderL1 m f`;
* `derivOrderL1_shiftedProduct_le` : for every node list,
  `derivOrderL1 m (shiftedProduct nodes f) ≤ ladderBound (derivOrderL1 · f) nodes m`,
  by induction on the list;
* `l1Mass_shiftedProduct_le_ladder` and `l1Mass_shiftedProduct_le_of_ladder` :
  the `m = 0` case, and the same bound obtained through the committed consumer
  `l1Mass_shiftedProduct_le_of_budget`, whose step condition holds with
  equality by the recursion;
* `derivOrderL1_le_of_support_of_norm_le` : the order-`m` form of the
  committed support-times-sup budget, which converts each ladder value into
  the pair `(2 * B) * M` of a support radius and a sup norm.

So the shifted-product recurrence constants are exactly the numbers
`derivOrderL1 j f`, `j ≤ |nodes| + 1`, for the chosen seed; nothing else is
missing at this step. No numerical value is chosen for them here.
-/

namespace ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection

open MeasureTheory
open CCM25Concrete.CompactLogConvolution
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaCriticalContraction
open CC20YoshidaCriticalContraction.CompactLogTest
open C1LaneRD3Root

noncomputable section

/-! ## 1. The ladder of derivative L1 masses -/

/-- The `L¹` mass of the `m`-th iterated derivative of a compact log test. -/
def derivOrderL1 (m : ℕ) (f : CompactLogTest) : ℝ :=
  ∫ x : ℝ, ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖

/-- The ladder starts at the mass (`m = 0`). -/
theorem derivOrderL1_zero (f : CompactLogTest) : derivOrderL1 0 f = l1Mass f := by
  unfold derivOrderL1 l1Mass
  simp [iteratedDeriv_zero]

/-- The ladder meets the committed derivative budget at `m = 1`. -/
theorem derivOrderL1_one (f : CompactLogTest) : derivOrderL1 1 f = derivativeL1 f := by
  unfold derivOrderL1 derivativeL1
  simp [iteratedDeriv_one]

theorem derivOrderL1_nonneg (m : ℕ) (f : CompactLogTest) : 0 ≤ derivOrderL1 m f :=
  integral_nonneg fun _ => norm_nonneg _

theorem contDiff_iteratedDeriv (m : ℕ) (f : CompactLogTest) :
    ContDiff ℝ (⊤ : ℕ∞) (iteratedDeriv m (f.test : ℝ → ℂ)) := by
  rw [iteratedDeriv_eq_iterate]
  exact ContDiff.iterate_deriv m (f.test.smooth ⊤)

theorem hasCompactSupport_iteratedDeriv (m : ℕ) (f : CompactLogTest) :
    HasCompactSupport (iteratedDeriv m (f.test : ℝ → ℂ)) := by
  rw [iteratedDeriv_eq_iterate]
  induction m with
  | zero => simpa using f.compactSupport
  | succ m ih =>
      rw [Function.iterate_succ']
      exact ih.deriv

theorem iteratedDeriv_integrable (m : ℕ) (f : CompactLogTest) :
    Integrable (fun x : ℝ => ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖) :=
  ((contDiff_iteratedDeriv m f).continuous.integrable_of_hasCompactSupport
    (hasCompactSupport_iteratedDeriv m f)).norm

/-! ## 2. One shift raises the order -/

theorem iteratedDeriv_derivativeShift_apply (m : ℕ) (f : CompactLogTest) (a : ℂ) (x : ℝ) :
    iteratedDeriv m ((derivativeShift f a).test : ℝ → ℂ) x =
      iteratedDeriv (m + 1) (f.test : ℝ → ℂ) x +
        a * iteratedDeriv m (f.test : ℝ → ℂ) x := by
  have hfun : ((derivativeShift f a).test : ℝ → ℂ) =
      (deriv (f.test : ℝ → ℂ)) + (fun y : ℝ => a * f.test y) := by
    funext y
    simp [derivativeShift_apply]
  have hg : ContDiffAt ℝ m (deriv (f.test : ℝ → ℂ)) x :=
    ((ContDiff.iterate_deriv 1 (f.test.smooth ⊤)).contDiffAt).of_le
      (WithTop.coe_le_coe.mpr le_top)
  have hc : ContDiffAt ℝ m (fun y : ℝ => a * f.test y) x :=
    (contDiff_const.mul (f.test.smooth ⊤)).contDiffAt.of_le
      (WithTop.coe_le_coe.mpr le_top)
  rw [hfun, iteratedDeriv_add hg hc, iteratedDeriv_const_mul_field, ← iteratedDeriv_succ']

/-- One shifted factor raises the derivative order by one. -/
theorem derivOrderL1_derivativeShift_le (m : ℕ) (f : CompactLogTest) (a : ℂ) :
    derivOrderL1 m (derivativeShift f a) ≤
      derivOrderL1 (m + 1) f + ‖a‖ * derivOrderL1 m f := by
  have hleft : Integrable (fun x : ℝ =>
      ‖iteratedDeriv m ((derivativeShift f a).test : ℝ → ℂ) x‖) :=
    iteratedDeriv_integrable m (derivativeShift f a)
  have hright : Integrable (fun x : ℝ =>
      ‖iteratedDeriv (m + 1) (f.test : ℝ → ℂ) x‖ +
        ‖a‖ * ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖) :=
    (iteratedDeriv_integrable (m + 1) f).add
      ((iteratedDeriv_integrable m f).const_mul ‖a‖)
  have hpoint (x : ℝ) :
      ‖iteratedDeriv m ((derivativeShift f a).test : ℝ → ℂ) x‖ ≤
        ‖iteratedDeriv (m + 1) (f.test : ℝ → ℂ) x‖ +
          ‖a‖ * ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖ := by
    calc ‖iteratedDeriv m ((derivativeShift f a).test : ℝ → ℂ) x‖
        = ‖iteratedDeriv (m + 1) (f.test : ℝ → ℂ) x +
            a * iteratedDeriv m (f.test : ℝ → ℂ) x‖ := by
          rw [iteratedDeriv_derivativeShift_apply]
      _ ≤ ‖iteratedDeriv (m + 1) (f.test : ℝ → ℂ) x‖ +
            ‖a * iteratedDeriv m (f.test : ℝ → ℂ) x‖ := norm_add_le _ _
      _ = ‖iteratedDeriv (m + 1) (f.test : ℝ → ℂ) x‖ +
            ‖a‖ * ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖ := by rw [norm_mul]
  calc derivOrderL1 m (derivativeShift f a)
      = ∫ x : ℝ, ‖iteratedDeriv m ((derivativeShift f a).test : ℝ → ℂ) x‖ := rfl
    _ ≤ ∫ x : ℝ, ‖iteratedDeriv (m + 1) (f.test : ℝ → ℂ) x‖ +
          ‖a‖ * ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖ :=
        integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = derivOrderL1 (m + 1) f + ‖a‖ * derivOrderL1 m f := by
        rw [integral_add (iteratedDeriv_integrable (m + 1) f)
          ((iteratedDeriv_integrable m f).const_mul ‖a‖), integral_const_mul]
        rfl

/-! ## 3. The ladder bound for a shifted product -/

/-- The ladder budget: `L` is the ladder of the seed, the recursion is the
budget step of `l1Mass_derivativeShift_le` applied one order up. -/
def ladderBound (L : ℕ → ℝ) : List ℂ → ℕ → ℝ
  | [], m => L m
  | a :: as, m => ladderBound L as (m + 1) + ‖a‖ * ladderBound L as m

@[simp] theorem ladderBound_nil (L : ℕ → ℝ) (m : ℕ) : ladderBound L [] m = L m := rfl

@[simp] theorem ladderBound_cons (L : ℕ → ℝ) (a : ℂ) (as : List ℂ) (m : ℕ) :
    ladderBound L (a :: as) m = ladderBound L as (m + 1) + ‖a‖ * ladderBound L as m :=
  rfl

theorem ladderBound_nonneg (L : ℕ → ℝ) (hL : ∀ j, 0 ≤ L j) (nodes : List ℂ) (m : ℕ) :
    0 ≤ ladderBound L nodes m := by
  induction nodes generalizing m with
  | nil => simpa using hL m
  | cons a as ih =>
      rw [ladderBound_cons]
      exact add_nonneg (ih (m + 1)) (mul_nonneg (norm_nonneg a) (ih m))

/-- The ladder theorem: the `m`-th derivative `L¹` mass of a shifted product
is bounded by the ladder budget of the seed. -/
theorem derivOrderL1_shiftedProduct_le (m : ℕ) (nodes : List ℂ) (f : CompactLogTest) :
    derivOrderL1 m (shiftedProduct nodes f) ≤
      ladderBound (fun j => derivOrderL1 j f) nodes m := by
  induction nodes generalizing m with
  | nil => simp [shiftedProduct]
  | cons a as ih =>
      rw [show shiftedProduct (a :: as) f = derivativeShift (shiftedProduct as f) a from rfl,
        ladderBound_cons]
      calc derivOrderL1 m (derivativeShift (shiftedProduct as f) a)
          ≤ derivOrderL1 (m + 1) (shiftedProduct as f) +
              ‖a‖ * derivOrderL1 m (shiftedProduct as f) :=
            derivOrderL1_derivativeShift_le m (shiftedProduct as f) a
        _ ≤ ladderBound (fun j => derivOrderL1 j f) as (m + 1) +
              ‖a‖ * ladderBound (fun j => derivOrderL1 j f) as m :=
            add_le_add (ih (m + 1)) (mul_le_mul_of_nonneg_left (ih m) (norm_nonneg a))

/-! ## 4. The seed-level budget and the committed consumer -/

theorem l1Mass_shiftedProduct_le_ladder (nodes : List ℂ) (f : CompactLogTest) :
    l1Mass (shiftedProduct nodes f) ≤
      ladderBound (fun j => derivOrderL1 j f) nodes 0 := by
  rw [← derivOrderL1_zero (shiftedProduct nodes f)]
  exact derivOrderL1_shiftedProduct_le 0 nodes f

/-- The committed consumer `l1Mass_shiftedProduct_le_of_budget` accepts the
ladder budget: its step condition is the recursion itself. -/
theorem l1Mass_shiftedProduct_le_of_ladder (nodes : List ℂ) (f : CompactLogTest) :
    l1Mass (shiftedProduct nodes f) ≤
      ladderBound (fun j => derivOrderL1 j f) nodes 0 :=
  l1Mass_shiftedProduct_le_of_budget nodes f
    (fun as => ladderBound (fun j => derivOrderL1 j f) as 0)
    (by simp [derivOrderL1_zero])
    (fun a as => by
      have h := derivOrderL1_shiftedProduct_le 1 as f
      rw [derivOrderL1_one] at h
      simp only [ladderBound_cons, Nat.zero_add]
      linarith)

/-! ## 5. The order-`m` support-times-sup budget -/

/-- The order-`m` form of `derivativeL1_le_of_support_of_norm_le`: a support
radius and a sup norm for the `m`-th derivative bound the ladder value. The
committed order-one form carries `0 ≤ M` as a hypothesis; here it would be
redundant, since `hbound` at a point outside `[-B, B]` already forces it. -/
theorem derivOrderL1_le_of_support_of_norm_le
    (m : ℕ) (f : CompactLogTest) (B M : ℝ)
    (hB : 0 ≤ B)
    (hsupport : Function.support (iteratedDeriv m (f.test : ℝ → ℂ)) ⊆ Set.Icc (-B) B)
    (hbound : ∀ x : ℝ, ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖ ≤ M) :
    derivOrderL1 m f ≤ (2 * B) * M := by
  have hleft : Integrable (fun x : ℝ => ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖) :=
    iteratedDeriv_integrable m f
  let bound : ℝ → ℝ := Set.indicator (Set.Icc (-B) B) (fun _ => M)
  have hright : Integrable bound := by
    exact (integrableOn_const (μ := volume) (C := M) (hs := by
      rw [Real.volume_Icc]
      exact ENNReal.ofReal_ne_top)).integrable_indicator measurableSet_Icc
  have hpoint : ∀ x : ℝ, ‖iteratedDeriv m (f.test : ℝ → ℂ) x‖ ≤ bound x := by
    intro x
    by_cases hx : x ∈ Set.Icc (-B) B
    · simp only [bound, Set.indicator_of_mem hx]
      exact hbound x
    · simp only [bound, Set.indicator, hx, ↓reduceIte]
      have hzero : iteratedDeriv m (f.test : ℝ → ℂ) x = 0 := by
        by_contra hne
        exact hx (hsupport (Function.mem_support.mpr hne))
      simp [hzero]
  calc
    derivOrderL1 m f ≤ ∫ x : ℝ, bound x :=
      integral_mono_ae hleft hright (Filter.Eventually.of_forall hpoint)
    _ = (2 * B) * M := by
      rw [show bound = Set.indicator (Set.Icc (-B) B) (fun _ => M) by rfl,
        integral_indicator_const M measurableSet_Icc,
        Real.volume_real_Icc_of_le (by linarith : -B ≤ B)]
      simp only [smul_eq_mul]
      ring

end

end ConnesWeilRH.Source.C1ExplicitFiniteNodeCorrection
