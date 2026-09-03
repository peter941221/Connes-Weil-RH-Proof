/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1OrbitWindowSemiLocalGate

/-!
# C1 record 1117: the Stage-B contract - local-configuration domination, made
# machine-checkable

1114 §2 states the owed lemma (LOCAL-ZERO-CONFIGURATION DOMINANCE) as

    GATE(detector) <= sup { GATE(w) : window family } + error < 0.

This module formalizes EVERY mechanical layer of that schematic and leaves
exactly one open type.  The anatomy that makes this possible (verified from
`C1SameOwnerWeil.lean:55-63,161-162`): both gate summands are LINEAR
functionals of the test function, so a decomposition of the detector square
into a nonnegative combination of window squares plus a defect turns the sign
obligation into additive bookkeeping of gate values.  No fresh integrability
theory is needed: the defect integrand is a finite difference of integrableOn
integrands of actual convolution squares (record-1089's
`archimedeanIntegrand_square_integrableOn_Ioi`), so its integrability follows
from `Integrable.sub` plus a locally proved finset lemma.

Contents:

* `ICgate`: the gate functional; `orbitWindowSemiLocalGate_iff` re-verifies
  (by `Iff.rfl`) that this is the literal 1089 gate of record.
* The linearity layer: numerator/integrand/prime-term pointwise additivity,
  the prime sum rewritten over a common `Finset.range` ceiling controlled by
  the support bound, and the master identity `ICgate_ICdefect`.
* `ICStageBContraction g`: the contraction structure (window family `w`,
  weights `lam`, root-support radii, per-window certified gate margins `mu`,
  defect bound `epsilon`) and the bridge theorem
  `orbitWindowSemiLocalGate_of_contraction`.
* `ICStageBContraction_of_below_floor`: the k=1 toy localization - a
  Platt-Trudgian-shaped floor hypothesis discharges the contraction for every
  test below the floor, so the whole plumbing (floor ==> contraction ==>
  gate ==> `qw_nonneg` of record 1089) typechecks end-to-end on one cell.

Open obligations named in record 1117 (this module proves no sign and claims
no instance of the contraction for an above-floor detector):

* (T1) gate-level class bounds: the 1115 matrix-level `isTopBound` instances
  consumed as the `hcert` fields, class by class, through the registered
  transcendental half.
* (T2) the bone: an `ICStageBContraction g` instance for the D1-pinned
  detector at above-floor configurations.  Record 1116 F1 (model gate +0.457
  at the on-line 13-node shape) is consistent with the contract: that shape
  is excluded by the floor/favorable-branch geometry, and law 65 bars the
  positive-delta surrogate from any contract.

RH unclaimed; no map change keyed.
-/

namespace ConnesWeilRH
namespace Source
namespace C1LocalConfigurationDomination

open MeasureTheory Set Filter
open CCM25Concrete.CompactLogConvolution
open C1SameOwnerWeil
open scoped BigOperators

noncomputable section

/-! ### The gate functional and its 1089 fidelity -/

/-- The gate functional: archimedean term plus finite visible prime sum, as
consumed by `orbitWindowSemiLocalGate` of record 1089. -/
def ICgate (F : CompactLogTest) : Real :=
  archimedeanTerm F + finitePrimeSum F

theorem orbitWindowSemiLocalGate_iff (g : CompactLogTest) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g ↔
      ICgate g.convolutionSquare ≤ 0 :=
  Iff.rfl

/-- The gate respects pointwise equality of tests. -/
theorem ICgate_congr {F G : CompactLogTest} (h : F.test = G.test) :
    ICgate F = ICgate G := by
  have h2 : F = G := CompactLogTest.ext h
  subst h2
  rfl

/-! ### Packaging and coercion plumbing -/

/-- Packaging a compactly supported Schwartz function as a test. -/
def packTest (f : TestFunction) (hf : HasCompactSupport f) : CompactLogTest :=
  ⟨f, hf⟩

@[simp] theorem packTest_apply (f : TestFunction) (hf : HasCompactSupport f)
    (x : ℝ) : (packTest f hf).test x = f x :=
  rfl

theorem coe_sub (f h : TestFunction) :
    ⇑(f - h) = fun x : ℝ => f x - h x := by
  ext x
  simp

theorem coe_smul (c : ℂ) (f : TestFunction) :
    ⇑(c • f) = fun x : ℝ => c • f x := by
  ext x
  simp

theorem coe_add (f g : TestFunction) :
    ⇑(f + g) = fun x : ℝ => f x + g x := by
  ext x
  simp

/-- A finite sum of compactly supported functions has compact support,
by induction through the binary `HasCompactSupport.add`. -/
theorem hasCompactSupport_finset_sum {ι : Type} (s : Finset ι)
    (f : ι → ℝ → ℂ) (hf : ∀ i ∈ s, HasCompactSupport (f i)) :
    HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine HasCompactSupport.of_support_subset_isCompact isCompact_empty ?_
      rintro x hx
      simp at hx
  | @insert a s hat ih =>
      convert (ih fun i hi => hf i (Finset.mem_insert_of_mem hi)).add
        (hf a (Finset.mem_insert_self a s)) using 1
      ext x
      simp [hat]
      abel

/-- A finite sum of integrable functions is integrable. -/
theorem ICintegrable_sum {ι : Type} {μ : Measure ℝ} (s : Finset ι)
    (f : ι → ℝ → ℂ) (h : ∀ i ∈ s, Integrable (f i) μ) :
    Integrable (fun x => ∑ i ∈ s, f i x) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s hat ih =>
      convert (h a (Finset.mem_insert_self a s)).add
        (ih fun b hb => h b (Finset.mem_insert_of_mem hb)) using 1
      ext x
      simp [hat]

/-! ### The defect test of a window combination -/

/-- The defect of a window combination: the head test minus the weighted
sum of the window tests, as one packed test. -/
def ICdefect (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → ℝ) : CompactLogTest where
  test := g.test - ∑ i ∈ s, (lam i : ℂ) • (w i).test
  compactSupport := by
    refine HasCompactSupport.sub g.compactSupport ?_
    convert hasCompactSupport_finset_sum s
      (fun i x => (lam i : ℂ) • (w i).test x)
      fun i _ => (w i).compactSupport.smul_left (f := fun _ => (lam i : ℂ))
      using 1
    ext x
    simp

@[simp] theorem ICdefect_test (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → ℝ) (x : ℝ) :
    (ICdefect g s w lam).test x =
      g.test x - ∑ i ∈ s, (lam i : ℂ) • (w i).test x := by
  show (g.test - ∑ i ∈ s, (lam i : ℂ) • (w i).test) x =
      g.test x - ∑ i ∈ s, (lam i : ℂ) • (w i).test x
  simp only [SchwartzMap.sub_apply, SchwartzMap.sum_apply,
    SchwartzMap.smul_apply]

/-- The defect's support is covered by the ingredients' support bound. -/
theorem support_ICdefect_subset {g : CompactLogTest} {ι : Type} {s : Finset ι}
    {w : ι → CompactLogTest} {lam : ι → ℝ} {B : ℝ}
    (hg : Function.support g.test ⊆ Ioo (-B) B)
    (hw : ∀ i ∈ s, Function.support (w i).test ⊆ Ioo (-B) B) :
    Function.support (ICdefect g s w lam).test ⊆ Ioo (-B) B := by
  intro x hx
  rw [Function.mem_support] at hx
  rw [ICdefect_test] at hx
  by_cases h : x ∈ Ioo (-B) B
  · exact h
  · apply absurd hx
    have hg0 : g.test x = 0 := by
      by_contra hne
      exact h (hg (Function.mem_support.mpr hne))
    have hs : ∑ i ∈ s, (lam i : ℂ) • (w i).test x = 0 := by
      refine Finset.sum_eq_zero fun i hi => ?_
      have hzero : (w i).test x = 0 := by
        by_contra hne
        exact h (hw i hi (Function.mem_support.mpr hne))
      simp [hzero]
    rw [hg0, hs, sub_self]
    exact fun hne => hne rfl

/-- Scalar multiples are support-controlled. -/
theorem support_smul_subset {f : ℝ → ℂ} {c : ℂ} {B : ℝ}
    (h : Function.support f ⊆ Ioo (-B) B) :
    Function.support (fun x => c • f x) ⊆ Ioo (-B) B := by
  intro x hx
  rw [Function.mem_support] at hx
  by_cases h0 : f x = 0
  · rw [h0, smul_zero] at hx
    exact absurd rfl hx
  · exact h h0

/-- Differences are support-controlled. -/
theorem support_sub_subset {f g : ℝ → ℂ} {B : ℝ}
    (hf : Function.support f ⊆ Ioo (-B) B)
    (hg : Function.support g ⊆ Ioo (-B) B) :
    Function.support (fun x => f x - g x) ⊆ Ioo (-B) B := by
  intro x hx
  rw [Function.mem_support] at hx
  by_cases h : f x = 0
  · have h2 : g x ≠ 0 := by
      intro h3; rw [h, h3, sub_self] at hx; exact hx rfl
    exact hg h2
  · exact hf h

/-! ### Pointwise linearity: the archimedean numerator -/

theorem archimedeanNumerator_packTest_add (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (y : ℝ) :
    archimedeanNumerator (packTest (f + g) (hf.add hg)) y =
      archimedeanNumerator (packTest f hf) y +
        archimedeanNumerator (packTest g hg) y := by
  unfold archimedeanNumerator
  simp only [packTest_apply, SchwartzMap.add_apply]
  ring

theorem archimedeanNumerator_packTest_sub (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (y : ℝ) :
    archimedeanNumerator (packTest (f - g) (hf.sub hg)) y =
      archimedeanNumerator (packTest f hf) y -
        archimedeanNumerator (packTest g hg) y := by
  unfold archimedeanNumerator
  simp only [packTest_apply, SchwartzMap.sub_apply]
  ring

/-- Real homogeneity of the numerator.  The compact-support proof of the
scaled function is abstracted (`∀ hc`) so the `packTest` pattern rewrites
against ANY proof term: bundling the proof inside the statement blocked
higher-order matching in the first build. -/
theorem archimedeanNumerator_packTest_smul (c : ℝ) (f : TestFunction)
    (hf : HasCompactSupport f) (y : ℝ) :
    ∀ (hc : HasCompactSupport ((c : ℂ) • f)),
      archimedeanNumerator (packTest ((c : ℂ) • f) hc) y =
        (c : ℂ) • archimedeanNumerator (packTest f hf) y := by
  intro hc
  unfold archimedeanNumerator
  simp only [packTest_apply, SchwartzMap.smul_apply, smul_eq_mul]
  ring

/-- The numerator is linear along the whole defect combination: fixed-`y`
computation packaged by induction over the window set. -/
theorem archimedeanNumerator_ICdefect (g : CompactLogTest) {ι : Type}
    (s : Finset ι) (w : ι → CompactLogTest) (lam : ι → ℝ) (y : ℝ) :
    archimedeanNumerator (ICdefect g s w lam) y =
      archimedeanNumerator g y -
        ∑ i ∈ s, (lam i : ℂ) • archimedeanNumerator (w i) y := by
  classical
  set N : (ℝ → ℂ) → ℂ := fun F =>
    Complex.ofRealCLM (Real.exp (y / 2)) * (F y + F (-y)) - 2 * F 0 with hNdef
  have hNsub (F H : ℝ → ℂ) : N (fun x => F x - H x) = N F - N H := by
    unfold N
    simp only [Complex.ofRealCLM_apply]
    ring
  have hNsmul (c : ℂ) (F : ℝ → ℂ) : N (fun x => c • F x) = c • N F := by
    unfold N
    simp only [Complex.ofRealCLM_apply, smul_eq_mul]
    ring
  have hget : ∀ (G : CompactLogTest), archimedeanNumerator G y = N G.test := by
    intro G
    show archimedeanNumerator (packTest G.test G.compactSupport) y = N G.test
    rfl
  simp_rw [hget]
  induction s using Finset.induction_on with
  | empty =>
      have he0 : (ICdefect g (∅ : Finset ι) w lam).test = g.test := by
        ext x
        simp [ICdefect_test]
      rw [he0, Finset.sum_empty, sub_zero]
  | @insert a s hat ih =>
      have he1 : (ICdefect g (insert a s) w lam).test =
          (ICdefect g s w lam).test - (lam a : ℂ) • (w a).test := by
        ext x
        rw [← ICdefect_test, SchwartzMap.sub_apply,
          SchwartzMap.smul_apply, ICdefect_test, ICdefect_test,
          Finset.sum_insert hat]
        ring
      rw [he1, coe_sub, hNsub, coe_smul, hNsmul, ih,
        Finset.sum_insert hat]
      simp only [sub_eq_add_neg]
      abel

/-! ### Pointwise linearity: the archimedean integrand -/

theorem archimedeanIntegrand_packTest_add (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (y : ℝ) :
    archimedeanIntegrand (packTest (f + g) (hf.add hg)) y =
      archimedeanIntegrand (packTest f hf) y +
        archimedeanIntegrand (packTest g hg) y := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_packTest_add]
  exact add_div _ _ _

theorem archimedeanIntegrand_packTest_sub (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (y : ℝ) :
    archimedeanIntegrand (packTest (f - g) (hf.sub hg)) y =
      archimedeanIntegrand (packTest f hf) y -
        archimedeanIntegrand (packTest g hg) y := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_packTest_sub]
  exact sub_div _ _ _

theorem archimedeanIntegrand_packTest_smul (c : ℝ) (f : TestFunction)
    (hf : HasCompactSupport f) (y : ℝ) :
    ∀ (hc : HasCompactSupport ((c : ℂ) • f)),
      archimedeanIntegrand (packTest ((c : ℂ) • f) hc) y =
        (c : ℂ) • archimedeanIntegrand (packTest f hf) y := by
  intro hc
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_packTest_smul c f hf y hc]
  simp only [div_eq_mul_inv, smul_eq_mul]
  ring

/-- The defect integrand is the linear combination of the ingredient
integrands, pointwise; the identity holds at every `y` including denominator
zeros, where the field division-by-zero convention collapses both sides. -/
theorem archimedeanIntegrand_ICdefect (g : CompactLogTest) {ι : Type}
    (s : Finset ι) (w : ι → CompactLogTest) (lam : ι → ℝ) (y : ℝ) :
    archimedeanIntegrand (ICdefect g s w lam) y =
      archimedeanIntegrand g y -
        ∑ i ∈ s, (lam i : ℂ) • archimedeanIntegrand (w i) y := by
  unfold archimedeanIntegrand
  rw [archimedeanNumerator_ICdefect, sub_div]
  simp only [div_eq_mul_inv, smul_eq_mul, Finset.sum_mul, mul_assoc]

/-- Partial defects are integrable, given integrability of the head and of
every window ingredient on the superset. -/
theorem ICdefect_integrand_integrable (g : CompactLogTest) {ι : Type}
    (t : Finset ι) {s : Finset ι} (w : ι → CompactLogTest) (lam : ι → ℝ)
    (ht : t ⊆ s)
    (hIg : IntegrableOn (archimedeanIntegrand g) (Ioi (0 : ℝ)))
    (hIw : ∀ i ∈ s, IntegrableOn (archimedeanIntegrand (w i)) (Ioi (0 : ℝ))) :
    Integrable (fun y : ℝ => archimedeanIntegrand (ICdefect g t w lam) y)
      (volume.restrict (Ioi (0 : ℝ))) := by
  have hcong : (fun y : ℝ => archimedeanIntegrand (ICdefect g t w lam) y) =
      fun y : ℝ => archimedeanIntegrand g y -
        ∑ i ∈ t, (lam i : ℂ) * archimedeanIntegrand (w i) y := by
    funext y
    rw [archimedeanIntegrand_ICdefect]
    simp only [smul_eq_mul, sub_eq_add_neg]
  rw [hcong]
  refine (hIg : Integrable (fun y => archimedeanIntegrand g y)
      (volume.restrict (Ioi (0 : ℝ)))).sub ?_
  refine ICintegrable_sum t (fun i y =>
    (lam i : ℂ) * archimedeanIntegrand (w i) y) ?_
  intro i hi
  have hI : Integrable (fun y => archimedeanIntegrand (w i) y)
      (volume.restrict (Ioi (0 : ℝ))) := hIw i (ht hi)
  exact hI.const_mul' _

/-! ### Archimedean term linearity -/

theorem archimedeanTerm_packTest_add (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hIf : IntegrableOn (archimedeanIntegrand (packTest f hf)) (Ioi (0 : ℝ)))
    (hIg : IntegrableOn (archimedeanIntegrand (packTest g hg)) (Ioi (0 : ℝ))) :
    archimedeanTerm (packTest (f + g) (hf.add hg)) =
      archimedeanTerm (packTest f hf) + archimedeanTerm (packTest g hg) := by
  unfold archimedeanTerm
  have heval : (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant :
        Real) : Complex)) * (packTest (f + g) (hf.add hg)).test 0 =
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant :
          Real) : Complex)) * (packTest f hf).test 0 +
        (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant :
          Real) : Complex)) * (packTest g hg).test 0 := by
    rw [packTest_apply, packTest_apply, packTest_apply, coe_add]
    simp
    ring
  rw [heval]
  have hcong : ∫ y in Set.Ioi (0 : ℝ),
      archimedeanIntegrand (packTest (f + g) (hf.add hg)) y =
      ∫ y in Set.Ioi (0 : ℝ),
        (archimedeanIntegrand (packTest f hf) y +
          archimedeanIntegrand (packTest g hg) y) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [archimedeanIntegrand_packTest_add f g hf hg y]
  rw [hcong, integral_add (hIf : Integrable _ _) (hIg : Integrable _ _)]
  simp only [Complex.add_re]
  ring

theorem archimedeanTerm_packTest_sub (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g)
    (hIf : IntegrableOn (archimedeanIntegrand (packTest f hf)) (Ioi (0 : ℝ)))
    (hIg : IntegrableOn (archimedeanIntegrand (packTest g hg)) (Ioi (0 : ℝ))) :
    archimedeanTerm (packTest (f - g) (hf.sub hg)) =
      archimedeanTerm (packTest f hf) - archimedeanTerm (packTest g hg) := by
  unfold archimedeanTerm
  have heval : (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant :
        Real) : Complex)) * (packTest (f - g) (hf.sub hg)).test 0 =
      (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant :
          Real) : Complex)) * (packTest f hf).test 0 -
        (((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant :
          Real) : Complex)) * (packTest g hg).test 0 := by
    rw [packTest_apply, packTest_apply, packTest_apply, coe_sub]
    simp
    ring
  rw [heval]
  have hcong : ∫ y in Set.Ioi (0 : ℝ),
      archimedeanIntegrand (packTest (f - g) (hf.sub hg)) y =
      ∫ y in Set.Ioi (0 : ℝ),
        (archimedeanIntegrand (packTest f hf) y -
          archimedeanIntegrand (packTest g hg) y) := by
    apply integral_congr_ae
    filter_upwards with y
    rw [archimedeanIntegrand_packTest_sub f g hf hg y]
  rw [hcong, integral_sub (hIf : Integrable _ _) (hIg : Integrable _ _)]
  simp only [Complex.sub_re, Complex.add_re]
  ring

theorem archimedeanTerm_packTest_smul (c : ℝ) (f : TestFunction)
    (hf : HasCompactSupport f)
    (hIf : IntegrableOn (archimedeanIntegrand (packTest f hf))
      (Ioi (0 : ℝ))) :
    ∀ (hc : HasCompactSupport ((c : ℂ) • f)),
      archimedeanTerm (packTest ((c : ℂ) • f) hc) =
        c * archimedeanTerm (packTest f hf) := by
  intro hc
  set C0 : ℂ := ((Real.log (4 * Real.pi) + Real.eulerMascheroniConstant :
      Real) : ℂ) with hC0
  have heval : C0 * (packTest ((c : ℂ) • f) hc).test 0 =
      (c : ℂ) • (C0 * (packTest f hf).test 0) := by
    rw [packTest_apply, packTest_apply]
    rw [coe_smul]
    simp
    ring
  unfold archimedeanTerm
  rw [heval]
  have hcong : ∫ y in Set.Ioi (0 : ℝ),
      archimedeanIntegrand (packTest ((c : ℂ) • f) hc) y =
      ∫ y in Set.Ioi (0 : ℝ),
        (c : ℂ) • archimedeanIntegrand (packTest f hf) y := by
    apply integral_congr_ae
    filter_upwards with y
    rw [archimedeanIntegrand_packTest_smul c f hf y hc]
  rw [hcong, integral_smul]
  rw [← smul_add]
  have hre : ∀ (Z : ℂ), ((c : ℂ) • Z).re = c * Z.re := by
    intro Z
    simp
  rw [hre]

/-! ### Pointwise linearity: the prime ingredients -/

theorem finitePrimeTermComplex_packTest_add (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (n : ℕ) :
    finitePrimeTermComplex (packTest (f + g) (hf.add hg)) n =
      finitePrimeTermComplex (packTest f hf) n +
        finitePrimeTermComplex (packTest g hg) n := by
  unfold finitePrimeTermComplex
  simp only [packTest_apply, SchwartzMap.add_apply]
  ring

theorem finitePrimeTermComplex_packTest_smul (c : ℝ) (f : TestFunction)
    (hf : HasCompactSupport f) (n : ℕ) :
    ∀ (hc : HasCompactSupport ((c : ℂ) • f)),
      finitePrimeTermComplex (packTest ((c : ℂ) • f) hc) n =
        (c : ℂ) • finitePrimeTermComplex (packTest f hf) n := by
  intro hc
  unfold finitePrimeTermComplex
  simp only [packTest_apply, SchwartzMap.smul_apply, smul_eq_mul]
  ring

theorem finitePrimeTerm_packTest_add (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (n : ℕ) :
    finitePrimeTerm (packTest (f + g) (hf.add hg)) n =
      finitePrimeTerm (packTest f hf) n +
        finitePrimeTerm (packTest g hg) n := by
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_packTest_add]
  exact Complex.add_re _ _

theorem finitePrimeTerm_packTest_smul (c : ℝ) (f : TestFunction)
    (hf : HasCompactSupport f) (n : ℕ) :
    ∀ (hc : HasCompactSupport ((c : ℂ) • f)),
      finitePrimeTerm (packTest ((c : ℂ) • f) hc) n =
        c * finitePrimeTerm (packTest f hf) n := by
  intro hc
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_packTest_smul c f hf n hc]
  have hre : ((c : ℂ) • finitePrimeTermComplex (packTest f hf) n).re =
      c * (finitePrimeTermComplex (packTest f hf) n).re := by
    simp
  rw [hre]

/-- Prime sums are support-controlled: a test supported in `Ioo (-B) B` has
all its visible prime terms inside the common ceiling
`Nat.ceil (exp B) + 1`. -/
theorem finitePrimeSum_packTest_eq_sum_range (f : TestFunction)
    (hf : HasCompactSupport f) {B : ℝ}
    (h : Function.support ⇑f ⊆ Ioo (-B) B) :
    finitePrimeSum (packTest f hf) =
      ∑ n ∈ Finset.range (Nat.ceil (Real.exp B) + 1),
        finitePrimeTerm (packTest f hf) n := by
  set F := packTest f hf
  set N := Nat.ceil (Real.exp B) + 1 with hNdef
  have hzB : ∀ n : ℕ, (Real.exp B : ℝ) < (n : ℝ) →
      finitePrimeTerm F n = 0 := by
    intro n hn
    have hlog : Real.log (n : ℝ) ≥ B := by
      have hpos : (0 : ℝ) < Real.exp B := Real.exp_pos B
      have h' := Real.log_lt_log hpos hn
      rw [Real.log_exp] at h'
      exact le_of_lt h'
    have heq : F.test = f := rfl
    have hp : F.test (Real.log (n : ℝ)) = 0 := by
      rw [heq]
      by_contra hne
      exact not_lt_of_ge hlog ((h (Function.mem_support.mpr hne)).2)
    have hm : F.test (-Real.log (n : ℝ)) = 0 := by
      rw [heq]
      by_contra hne
      have hm1 := (h (Function.mem_support.mpr hne)).1
      have hlt : Real.log (n : ℝ) < B := by linarith
      exact not_lt_of_ge hlog hlt
    unfold finitePrimeTerm finitePrimeTermComplex
    rw [hp, hm]
    simp
  have hzb : ∀ n : ℕ, globalIndexBound F ≤ n → finitePrimeTerm F n = 0 := by
    intro n hn
    by_contra hne
    have hc : finitePrimeTermComplex F n ≠ 0 := by
      intro h; simp [finitePrimeTerm, h] at hne
    have hlt := index_lt_globalIndexBound F
      (finitePrimeTermComplex_nonzero_primePower F hc) hc
    omega
  have hrange : finitePrimeSum F =
      ∑ n ∈ Finset.range (globalIndexBound F), finitePrimeTerm F n := by
    unfold finitePrimeSum globalPrimeIndexSet
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => by
      by_cases hh : IsPrimePow n ∧ finitePrimeTermComplex F n ≠ 0
      · simp [hh]
      · rw [if_neg hh]
        by_cases hnp : IsPrimePow n
        · have hzero : finitePrimeTermComplex F n = 0 := by
            by_contra hc
            exact hh ⟨hnp, hc⟩
          simp [finitePrimeTerm, hzero]
        · have hzero : finitePrimeTermComplex F n = 0 := by
            by_contra hc
            exact hnp (finitePrimeTermComplex_nonzero_primePower F hc)
          simp [finitePrimeTerm, hzero]
  have hgrowL : ∑ n ∈ Finset.range (globalIndexBound F), finitePrimeTerm F n =
      ∑ n ∈ Finset.range (max (globalIndexBound F) N), finitePrimeTerm F n := by
    have hIco : ∑ n ∈ Finset.Ico (globalIndexBound F)
        (max (globalIndexBound F) N), finitePrimeTerm F n = 0 :=
      Finset.sum_eq_zero fun n hn => hzb n (Finset.mem_Ico.mp hn).1
    calc ∑ n ∈ Finset.range (globalIndexBound F), finitePrimeTerm F n
        = ∑ n ∈ Finset.range (globalIndexBound F), finitePrimeTerm F n + 0 :=
          (add_zero _).symm
      _ = (∑ n ∈ Finset.range (globalIndexBound F), finitePrimeTerm F n) +
          ∑ n ∈ Finset.Ico (globalIndexBound F)
            (max (globalIndexBound F) N), finitePrimeTerm F n := by rw [hIco]
      _ = ∑ n ∈ Finset.range (max (globalIndexBound F) N),
            finitePrimeTerm F n :=
          Finset.sum_range_add_sum_Ico _ (Nat.le_max_left _ _)
  have hgrowR : ∑ n ∈ Finset.range N, finitePrimeTerm F n =
      ∑ n ∈ Finset.range (max (globalIndexBound F) N), finitePrimeTerm F n := by
    have hIco : ∑ n ∈ Finset.Ico N (max (globalIndexBound F) N),
        finitePrimeTerm F n = 0 := by
      refine Finset.sum_eq_zero fun n hn => ?_
      have h1 := Finset.mem_Ico.mp hn
      have hceil : (Real.exp B : ℝ) ≤ (Nat.ceil (Real.exp B) : ℝ) :=
        by exact_mod_cast Nat.le_ceil _
      have hN : (N : ℝ) = (Nat.ceil (Real.exp B) : ℝ) + 1 := by
        rw [hNdef]
        norm_num [Nat.cast_add, Nat.cast_one]
      have hexp : (Real.exp B : ℝ) < (n : ℝ) := by
        have hnN : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast h1.1
        linarith
      exact hzB n hexp
    calc ∑ n ∈ Finset.range N, finitePrimeTerm F n
        = ∑ n ∈ Finset.range N, finitePrimeTerm F n + 0 := (add_zero _).symm
      _ = (∑ n ∈ Finset.range N, finitePrimeTerm F n) +
          ∑ n ∈ Finset.Ico N (max (globalIndexBound F) N),
            finitePrimeTerm F n := by rw [hIco]
      _ = ∑ n ∈ Finset.range (max (globalIndexBound F) N),
            finitePrimeTerm F n :=
          Finset.sum_range_add_sum_Ico _ (Nat.le_max_right _ _)
  rw [hrange, hgrowL, ← hgrowR]

/-- The prime sum is additive on tests supported in a common window. -/
theorem finitePrimeSum_packTest_add (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) {B : ℝ}
    (hF : Function.support ⇑f ⊆ Ioo (-B) B)
    (hG : Function.support ⇑g ⊆ Ioo (-B) B) :
    finitePrimeSum (packTest (f + g) (hf.add hg)) =
      finitePrimeSum (packTest f hf) + finitePrimeSum (packTest g hg) := by
  have hFG : Function.support ⇑(f + g) ⊆ Ioo (-B) B := by
    rw [coe_add]
    intro x hx
    by_contra hxB
    have h1 : ⇑f x = 0 := by
      by_contra hne
      exact hxB (hF (Function.mem_support.mpr hne))
    have h2 : ⇑g x = 0 := by
      by_contra hne
      exact hxB (hG (Function.mem_support.mpr hne))
    apply hx
    simp [h1, h2]
  have e1 := finitePrimeSum_packTest_eq_sum_range (f + g) (hf.add hg) hFG
  have e2 := finitePrimeSum_packTest_eq_sum_range f hf hF
  have e3 := finitePrimeSum_packTest_eq_sum_range g hg hG
  rw [e1, e2, e3,
    Finset.sum_congr rfl (fun n _ => finitePrimeTerm_packTest_add f g hf hg n),
    Finset.sum_add_distrib]

/-- The prime sum is real-homogeneous. -/
theorem finitePrimeSum_packTest_smul (c : ℝ) (f : TestFunction)
    (hf : HasCompactSupport f) {B : ℝ}
    (h : Function.support ⇑f ⊆ Ioo (-B) B) :
    ∀ (hc : HasCompactSupport ((c : ℂ) • f)),
      finitePrimeSum (packTest ((c : ℂ) • f) hc) =
        c * finitePrimeSum (packTest f hf) := by
  intro hc
  have hc' : Function.support ⇑((c : ℂ) • f) ⊆ Ioo (-B) B := by
    rw [coe_smul]
    intro x hx
    by_contra hxB
    have h1 : ⇑f x = 0 := by
      by_contra hne
      exact hxB (h (Function.mem_support.mpr hne))
    apply hx
    simp [h1]
  have e1 := finitePrimeSum_packTest_eq_sum_range ((c : ℂ) • f) hc hc'
  have e2 := finitePrimeSum_packTest_eq_sum_range f hf h
  rw [e1, e2, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  exact finitePrimeTerm_packTest_smul c f hf n hc

theorem finitePrimeTermComplex_packTest_sub (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (n : ℕ) :
    finitePrimeTermComplex (packTest (f - g) (hf.sub hg)) n =
      finitePrimeTermComplex (packTest f hf) n -
        finitePrimeTermComplex (packTest g hg) n := by
  unfold finitePrimeTermComplex
  simp only [packTest_apply, SchwartzMap.sub_apply]
  ring

theorem finitePrimeTerm_packTest_sub (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) (n : ℕ) :
    finitePrimeTerm (packTest (f - g) (hf.sub hg)) n =
      finitePrimeTerm (packTest f hf) n -
        finitePrimeTerm (packTest g hg) n := by
  unfold finitePrimeTerm
  rw [finitePrimeTermComplex_packTest_sub]
  exact Complex.sub_re _ _

/-- The prime sum is additive under subtraction on tests supported in a
common window. -/
theorem finitePrimeSum_packTest_sub (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) {B : ℝ}
    (hF : Function.support ⇑f ⊆ Ioo (-B) B)
    (hG : Function.support ⇑g ⊆ Ioo (-B) B) :
    finitePrimeSum (packTest (f - g) (hf.sub hg)) =
      finitePrimeSum (packTest f hf) - finitePrimeSum (packTest g hg) := by
  have hFG : Function.support ⇑(f - g) ⊆ Ioo (-B) B := by
    rw [coe_sub]
    intro x hx
    by_contra hxB
    have h1 : ⇑f x = 0 := by
      by_contra hne
      exact hxB (hF (Function.mem_support.mpr hne))
    have h2 : ⇑g x = 0 := by
      by_contra hne
      exact hxB (hG (Function.mem_support.mpr hne))
    apply hx
    simp [h1, h2]
  have e1 := finitePrimeSum_packTest_eq_sum_range (f - g) (hf.sub hg) hFG
  have e2 := finitePrimeSum_packTest_eq_sum_range f hf hF
  have e3 := finitePrimeSum_packTest_eq_sum_range g hg hG
  rw [e1, e2, e3,
    Finset.sum_congr rfl (fun n _ => finitePrimeTerm_packTest_sub f g hf hg n),
    Finset.sum_sub_distrib]

/-! ### Gate additivity, homogeneity, subtraction -/

/-- Gate subtraction on a common support window: the insert-step workhorse. -/
theorem ICgate_packTest_sub (f h : TestFunction)
    (hf : HasCompactSupport f) (hh : HasCompactSupport h) {B : ℝ}
    (hF : Function.support ⇑f ⊆ Ioo (-B) B)
    (hH : Function.support ⇑h ⊆ Ioo (-B) B)
    (hIf : IntegrableOn (archimedeanIntegrand (packTest f hf)) (Ioi (0 : ℝ)))
    (hIh : IntegrableOn (archimedeanIntegrand (packTest h hh)) (Ioi (0 : ℝ))) :
    ICgate (packTest (f - h) (hf.sub hh)) =
      ICgate (packTest f hf) - ICgate (packTest h hh) := by
  unfold ICgate
  rw [archimedeanTerm_packTest_sub f h hf hh hIf hIh,
    finitePrimeSum_packTest_sub f h hf hh hF hH]
  ring

theorem ICgate_packTest_add (f g : TestFunction)
    (hf : HasCompactSupport f) (hg : HasCompactSupport g) {B : ℝ}
    (hF : Function.support ⇑f ⊆ Ioo (-B) B)
    (hG : Function.support ⇑g ⊆ Ioo (-B) B)
    (hIf : IntegrableOn (archimedeanIntegrand (packTest f hf)) (Ioi (0 : ℝ)))
    (hIg : IntegrableOn (archimedeanIntegrand (packTest g hg)) (Ioi (0 : ℝ))) :
    ICgate (packTest (f + g) (hf.add hg)) =
      ICgate (packTest f hf) + ICgate (packTest g hg) := by
  unfold ICgate
  rw [archimedeanTerm_packTest_add f g hf hg hIf hIg,
    finitePrimeSum_packTest_add f g hf hg hF hG]
  ring

theorem ICgate_packTest_smul (c : ℝ) (f : TestFunction)
    (hf : HasCompactSupport f) {B : ℝ}
    (h : Function.support ⇑f ⊆ Ioo (-B) B)
    (hIf : IntegrableOn (archimedeanIntegrand (packTest f hf)) (Ioi (0 : ℝ))) :
    ∀ (hc : HasCompactSupport ((c : ℂ) • f)),
      ICgate (packTest ((c : ℂ) • f) hc) = c * ICgate (packTest f hf) := by
  intro hc
  unfold ICgate
  rw [archimedeanTerm_packTest_smul c f hf hIf hc,
    finitePrimeSum_packTest_smul c f hf h hc]
  ring

/-! ### The master identity -/

/-- The gate of the defect equals the head gate minus the weighted sum of the
window gates: the algebraic spine of every Stage-B certificate.  The
integrability hypotheses are free at use sites, since both the head and every
window ingredient can be an actual convolution square
(`archimedeanIntegrand_square_integrableOn_Ioi`). -/
theorem ICgate_ICdefect (g : CompactLogTest) {ι : Type} (s : Finset ι)
    (w : ι → CompactLogTest) (lam : ι → ℝ) {B : ℝ}
    (hg : Function.support g.test ⊆ Ioo (-B) B)
    (hw : ∀ i ∈ s, Function.support (w i).test ⊆ Ioo (-B) B)
    (hIg : IntegrableOn (archimedeanIntegrand g) (Ioi (0 : ℝ)))
    (hIw : ∀ i ∈ s, IntegrableOn (archimedeanIntegrand (w i)) (Ioi (0 : ℝ))) :
    ICgate (ICdefect g s w lam) =
      ICgate g - ∑ i ∈ s, lam i * ICgate (w i) := by
  classical
  revert hw hIw
  induction s using Finset.induction_on with
  | empty =>
      intro hw hIw
      have heta0 : ICdefect g (∅ : Finset ι) w lam =
          packTest g.test g.compactSupport := by
        refine CompactLogTest.ext ?_
        ext x
        simp [ICdefect_test]
      rw [heta0, Finset.sum_empty, sub_zero]
      rfl
  | @insert a s hat ih =>
      intro hw hIw
      have hres := ih (fun i hi => hw i (Finset.mem_insert_of_mem hi))
        (fun i hi => hIw i (Finset.mem_insert_of_mem hi))
      have hwa : Function.support (w a).test ⊆ Ioo (-B) B :=
        hw a (Finset.mem_insert_self a s)
      have hIwa : IntegrableOn (archimedeanIntegrand (w a)) (Ioi (0 : ℝ)) :=
        hIw a (Finset.mem_insert_self a s)
      have hpartial : IntegrableOn (archimedeanIntegrand
          (ICdefect g s w lam)) (Ioi (0 : ℝ)) :=
        ICdefect_integrand_integrable g s w lam
          (fun b hb => Finset.mem_insert_of_mem hb) hIg
          hIw
      have hte : (ICdefect g (insert a s) w lam).test =
          (ICdefect g s w lam).test -
            (lam a : ℂ) • (w a).test := by
        ext x
        rw [← ICdefect_test, SchwartzMap.sub_apply,
          SchwartzMap.smul_apply, ICdefect_test, ICdefect_test,
          Finset.sum_insert hat]
        ring
      have hcsS : HasCompactSupport
          ((ICdefect g s w lam).test - (lam a : ℂ) • (w a).test) :=
        HasCompactSupport.sub (ICdefect g s w lam).compactSupport
          ((w a).compactSupport.smul_left (f := fun _ => (lam a : ℂ)))
      have hsuppS : Function.support
          ⇑((lam a : ℂ) • (w a).test) ⊆ Ioo (-B) B := by
        rw [coe_smul]
        intro x hx
        by_contra hxB
        have h1 : ⇑(w a).test x = 0 := by
          by_contra hne
          exact hxB (hwa (Function.mem_support.mpr hne))
        apply hx
        simp [h1]
      have hIsmul : IntegrableOn (archimedeanIntegrand
          (packTest ((lam a : ℂ) • (w a).test)
            ((w a).compactSupport.smul_left (f := fun _ => (lam a : ℂ)))))
          (Ioi (0 : ℝ)) := by
        have hcong : (fun y : ℝ => archimedeanIntegrand
            (packTest ((lam a : ℂ) • (w a).test)
              ((w a).compactSupport.smul_left
                (f := fun _ => (lam a : ℂ)))) y =
            fun y : ℝ => (lam a : ℂ) • archimedeanIntegrand (w a) y := by
          funext y
          rw [archimedeanIntegrand_packTest_smul (lam a) (w a).test
              (w a).compactSupport y]
          have hpacka : packTest ((w a).test) ((w a).compactSupport) = w a := by
            refine CompactLogTest.ext ?_
            ext x
            simp [packTest_apply]
          rw [hpacka]
        rw [hcong]
        have hsmul : (fun y : ℝ => (lam a : ℂ) •
            archimedeanIntegrand (w a) y) =
            fun y : ℝ => (lam a : ℂ) * archimedeanIntegrand (w a) y := by
          funext y
          simp
        rw [hsmul]
        have hI : Integrable (fun y : ℝ => archimedeanIntegrand (w a) y)
            (volume.restrict (Ioi (0 : ℝ))) := hIwa
        exact hI.const_mul' _
      have hstep : ICgate (ICdefect g (insert a s) w lam) =
          ICgate (ICdefect g s w lam) - lam a * ICgate (w a) := by
        rw [show ICdefect g (insert a s) w lam = packTest
            ((ICdefect g s w lam).test - (lam a : ℂ) • (w a).test) hcsS from
          CompactLogTest.ext hte]
        have hfS := (ICdefect g s w lam).compactSupport
        rw [ICgate_packTest_sub ((ICdefect g s w lam).test)
            ((lam a : ℂ) • (w a).test) hfS
            ((w a).compactSupport.smul_left (f := fun _ => (lam a : ℂ)))
            (support_ICdefect_subset hg
              fun i hi => hw i (Finset.mem_insert_of_mem hi))
            hsuppS hpartial hIsmul,
          ICgate_packTest_smul (lam a) (w a).test (w a).compactSupport
            hwa hIwa ((w a).compactSupport.smul_left
              (f := fun _ => (lam a : ℂ)))]
        have hpackS : packTest ((ICdefect g s w lam).test) hfS =
            ICdefect g s w lam := by
          refine CompactLogTest.ext ?_
          ext x
          simp [packTest_apply]
        have hpacka2 : packTest ((w a).test) ((w a).compactSupport) = w a := by
          refine CompactLogTest.ext ?_
          ext x
          simp [packTest_apply]
        rw [hpackS, hpacka2]
      rw [hstep, hres, Finset.sum_insert hat]
      ring

/-! ### The Stage-B contraction structure -/

/-- The Stage-B local-configuration contraction of `g`: a finite window
family `w` with nonnegative weights `lam`, root supports in `Ioo (-b) b` for
the head and `Ioo (-a i) (a i)` for the windows, per-window certified gate
margins `-mu i`, and a defect gate bound `epsilon`.  Satisfying the budget
inequality `epsilon <= sum_i lam i * mu i` contracts the gate: the bridge
theorem below discharges the 1089 gate obligation from such data. -/
structure ICStageBContraction (g : CompactLogTest) where
  ι : Type
  s : Finset ι
  w : ι → CompactLogTest
  lam : ι → ℝ
  hlam : ∀ i ∈ s, 0 ≤ lam i
  mu : ι → ℝ
  epsilon : ℝ
  b : ℝ
  hgsupp : Function.support g.test ⊆ Ioo (-b) b
  a : ι → ℝ
  hwsupp : ∀ i ∈ s, Function.support (w i).test ⊆ Ioo (-a i) (a i)
  hD : ICgate (ICdefect g.convolutionSquare s (fun i =>
      (w i).convolutionSquare) lam) ≤ epsilon
  hcert : ∀ i ∈ s, ICgate ((w i).convolutionSquare) ≤ -mu i

/-- The bridge: contraction data plus the budget inequality give the record
1089 orbit-window semi-local gate of `g`.  All analytic input sits in
`hD`/`hcert` (the two T-obligations of record 1117); everything else is the
linearity layer above. -/
theorem orbitWindowSemiLocalGate_of_contraction (g : CompactLogTest)
    (c : ICStageBContraction g)
    (hbudget : c.epsilon ≤ ∑ i ∈ c.s, c.lam i * c.mu i) :
    C1OrbitWindowSemiLocalGate.orbitWindowSemiLocalGate g := by
  rw [orbitWindowSemiLocalGate_iff]
  -- A common window `Ioo (-B) B` for the head square and every window
  -- square, sized from the root supports through
  -- `convolutionSquare_support_subset_two_mul_Ioo`.  The radius over the
  -- windows is taken as the sum of absolute values (a `sup` over `Finset`
  -- in `ℝ` would need an `OrderBot`, which `ℝ` does not carry).
  set M := ∑ i ∈ c.s, |c.a i| with hMdef
  set B := (2 : ℝ) * max c.b M with hBdef
  have hgs : Function.support g.convolutionSquare.test ⊆ Ioo (-B) B := by
    have h1 : Function.support g.convolutionSquare.test ⊆
        Ioo (-(2 * c.b)) (2 * c.b) :=
      CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo g
        (c.hgsupp.trans Set.Ioo_subset_Icc_self)
    refine Set.Subset.trans h1 ?_
    intro x hx
    simp only [Set.mem_Ioo] at hx ⊢
    have hbnd : (2 : ℝ) * c.b ≤ B := by
      have : c.b ≤ max c.b M := le_max_left _ _
      rw [hBdef]; linarith
    have hnb : -B ≤ -(2 * c.b) := by rw [hBdef]; linarith
    obtain ⟨hL, hR⟩ := hx
    exact ⟨by linarith, by linarith⟩
  have hws : ∀ i ∈ c.s,
      Function.support ((c.w i).convolutionSquare).test ⊆ Ioo (-B) B := by
    intro i hi
    have h1 : Function.support ((c.w i).convolutionSquare).test ⊆
        Ioo (-(2 * c.a i)) (2 * c.a i) :=
      CompactLogTest.convolutionSquare_support_subset_two_mul_Ioo (c.w i)
        ((c.hwsupp i hi).trans Set.Ioo_subset_Icc_self)
    refine Set.Subset.trans h1 ?_
    intro x hx
    simp only [Set.mem_Ioo] at hx ⊢
    have hM : |c.a i| ≤ M :=
      Finset.single_le_sum (fun j _ => abs_nonneg (c.a j)) hi
    have hle : c.a i ≤ M := by
      have : c.a i ≤ |c.a i| := le_abs_self _
      linarith
    have hmaxM : M ≤ max c.b M := le_max_right _ _
    have hbnd : (2 : ℝ) * c.a i ≤ B := by rw [hBdef]; linarith
    have hnb : -B ≤ -(2 * c.a i) := by rw [hBdef]; linarith
    obtain ⟨hL, hR⟩ := hx
    exact ⟨by linarith, by linarith⟩
  have hmain : ICgate (ICdefect g.convolutionSquare c.s
      (fun i => (c.w i).convolutionSquare) c.lam) =
      ICgate g.convolutionSquare -
        ∑ i ∈ c.s, c.lam i * ICgate (c.w i).convolutionSquare :=
    ICgate_ICdefect g.convolutionSquare c.s
      (fun i => (c.w i).convolutionSquare) c.lam hgs
      (fun i hi => hws i hi)
      (archimedeanIntegrand_square_integrableOn_Ioi g)
      (fun i hi => archimedeanIntegrand_square_integrableOn_Ioi (c.w i))
  have hb : ∑ i ∈ c.s, c.lam i * ICgate (c.w i).convolutionSquare ≤
      ∑ i ∈ c.s, c.lam i * (-c.mu i) :=
    Finset.sum_le_sum fun i hi =>
      mul_le_mul_of_nonneg_left (c.hcert i hi) (c.hlam i hi)
  have hneg : ∑ i ∈ c.s, c.lam i * (-c.mu i) =
      -∑ i ∈ c.s, c.lam i * c.mu i := by
    rw [← Finset.sum_neg_distrib]
    congr
    ext
    ring
  have hdefect : ICgate (ICdefect g.convolutionSquare c.s
      (fun i => (c.w i).convolutionSquare) c.lam) ≤ c.epsilon := c.hD
  linarith [hdefect]

/-- The k=1 toy localization: a Platt-Trudgian-shaped verified-zero floor
below `H` makes every `|rho.im| <= H` off-line `rho` hypothesis absurd, so the
contraction type is inhabited for every test by the vacuous cell.  This
proves the floor ==> contraction ==> gate plumbing typechecks end-to-end on
one configuration-space cell, with the floor hypothesis exactly the shape
1114 §2 Stage A produces.  (A `def`, not a `theorem`: its type is the
structure `ICStageBContraction`, which is not a proposition.) -/
noncomputable def ICStageBContraction_of_below_floor (rho : ℂ) (H : ℝ)
    (g : CompactLogTest)
    (hz : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hheight : |rho.im| ≤ H)
    (hfloor : ∀ z : ℂ, RHDefinitionBridge.standard.sourceNontrivialZero z →
      |z.im| ≤ H → z.re = 1 / 2)
    (hoff : rho.re ≠ 1 / 2) : ICStageBContraction g :=
  absurd (hfloor rho hz hheight) hoff

end
end C1LocalConfigurationDomination
end Source
end ConnesWeilRH
