/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Basic
import ConnesWeilRH.Source.CC20Concrete.TraceScale
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

/-!
# Shared source analytic base

This module contains the common source-facing carriers used by the CCM24,
CCM25, and CC20 source-model discharges.  Heavier theorem rows and peeling
records live in downstream modules so the support-window interface can be
refined without forcing every source object into one file.
-/

namespace ConnesWeilRH
namespace Source
namespace AnalyticCore

open scoped ArithmeticFunction FourierTransform

/-- Bridge between the new source test object and the legacy `TestFunction`. -/
structure LegacyTestEquiv (Test : Type) where
  encode : Test → TestFunction
  decode : TestFunction → Test
  encode_decode : ∀ F : TestFunction, encode (decode F) = F
  decode_encode : ∀ f : Test, decode (encode f) = f

namespace LegacyTestEquiv

@[simp]
theorem encode_decode_apply {Test : Type} (e : LegacyTestEquiv Test)
    (F : TestFunction) :
    e.encode (e.decode F) = F :=
  e.encode_decode F

@[simp]
theorem decode_encode_apply {Test : Type} (e : LegacyTestEquiv Test)
    (f : Test) :
    e.decode (e.encode f) = f :=
  e.decode_encode f

theorem encode_leftInverse_decode {Test : Type} (e : LegacyTestEquiv Test) :
    Function.LeftInverse e.encode e.decode :=
  e.encode_decode

theorem decode_leftInverse_encode {Test : Type} (e : LegacyTestEquiv Test) :
    Function.LeftInverse e.decode e.encode :=
  e.decode_encode

theorem encode_injective {Test : Type} (e : LegacyTestEquiv Test) :
    Function.Injective e.encode := by
  intro f g h
  calc
    f = e.decode (e.encode f) := (e.decode_encode f).symm
    _ = e.decode (e.encode g) := by rw [h]
    _ = g := e.decode_encode g

theorem decode_injective {Test : Type} (e : LegacyTestEquiv Test) :
    Function.Injective e.decode := by
  intro F G h
  calc
    F = e.encode (e.decode F) := (e.encode_decode F).symm
    _ = e.encode (e.decode G) := by rw [h]
    _ = G := e.encode_decode G

theorem encode_eq_iff {Test : Type} (e : LegacyTestEquiv Test)
    {f g : Test} :
    e.encode f = e.encode g ↔ f = g :=
  e.encode_injective.eq_iff

theorem decode_eq_iff {Test : Type} (e : LegacyTestEquiv Test)
    {F G : TestFunction} :
    e.decode F = e.decode G ↔ F = G :=
  e.decode_injective.eq_iff

theorem encode_surjective {Test : Type} (e : LegacyTestEquiv Test) :
    Function.Surjective e.encode := by
  intro F
  exact ⟨e.decode F, e.encode_decode F⟩

theorem decode_surjective {Test : Type} (e : LegacyTestEquiv Test) :
    Function.Surjective e.decode := by
  intro f
  exact ⟨e.encode f, e.decode_encode f⟩

theorem encode_bijective {Test : Type} (e : LegacyTestEquiv Test) :
    Function.Bijective e.encode :=
  ⟨e.encode_injective, e.encode_surjective⟩

theorem decode_bijective {Test : Type} (e : LegacyTestEquiv Test) :
    Function.Bijective e.decode :=
  ⟨e.decode_injective, e.decode_surjective⟩

end LegacyTestEquiv

/--
The shared source test algebra.

`convolutionStar` is the CCM25 half-density square product.  The same object is
also the test whose support is controlled by CCM24 and whose trace amplitude is
read by CC20.
-/
structure SourceTestAlgebra where
  Test : Type
  legacy : LegacyTestEquiv Test
  convolutionStar : Test → Test → Test
  involution : Test → Test
  convolutionSquare : Test → Test := fun g => convolutionStar g g
  convolutionSquare_eq : ∀ g : Test, convolutionSquare g = convolutionStar g g

namespace SourceTestAlgebra

def legacyConvolutionStar (A : SourceTestAlgebra) :
    TestFunction → TestFunction → TestFunction :=
  fun f g => A.legacy.encode
    (A.convolutionStar (A.legacy.decode f) (A.legacy.decode g))

def legacyInvolution (A : SourceTestAlgebra) :
    TestFunction → TestFunction :=
  fun f => A.legacy.encode (A.involution (A.legacy.decode f))

def legacyConvolutionSquare (A : SourceTestAlgebra) :
    TestFunction → TestFunction :=
  fun f => A.legacy.encode (A.convolutionSquare (A.legacy.decode f))

@[simp] theorem legacyConvolutionStar_apply
    (A : SourceTestAlgebra) (f g : TestFunction) :
    A.legacyConvolutionStar f g =
      A.legacy.encode
        (A.convolutionStar (A.legacy.decode f) (A.legacy.decode g)) :=
  rfl

@[simp] theorem legacyInvolution_apply
    (A : SourceTestAlgebra) (f : TestFunction) :
    A.legacyInvolution f =
      A.legacy.encode (A.involution (A.legacy.decode f)) :=
  rfl

@[simp] theorem legacyConvolutionSquare_apply
    (A : SourceTestAlgebra) (f : TestFunction) :
    A.legacyConvolutionSquare f =
      A.legacy.encode (A.convolutionSquare (A.legacy.decode f)) :=
  rfl

@[simp] theorem legacy_decode_legacyConvolutionStar
    (A : SourceTestAlgebra) (f g : TestFunction) :
    A.legacy.decode (A.legacyConvolutionStar f g) =
      A.convolutionStar (A.legacy.decode f) (A.legacy.decode g) := by
  simp [legacyConvolutionStar]

@[simp] theorem legacy_decode_legacyInvolution
    (A : SourceTestAlgebra) (f : TestFunction) :
    A.legacy.decode (A.legacyInvolution f) =
      A.involution (A.legacy.decode f) := by
  simp [legacyInvolution]

@[simp] theorem legacy_decode_legacyConvolutionSquare
    (A : SourceTestAlgebra) (f : TestFunction) :
    A.legacy.decode (A.legacyConvolutionSquare f) =
      A.convolutionSquare (A.legacy.decode f) := by
  simp [legacyConvolutionSquare]

@[simp] theorem legacyConvolutionStar_encode_left
    (A : SourceTestAlgebra) (f : A.Test) (g : TestFunction) :
    A.legacyConvolutionStar (A.legacy.encode f) g =
      A.legacy.encode (A.convolutionStar f (A.legacy.decode g)) := by
  simp [legacyConvolutionStar]

@[simp] theorem legacyConvolutionStar_encode_right
    (A : SourceTestAlgebra) (f : TestFunction) (g : A.Test) :
    A.legacyConvolutionStar f (A.legacy.encode g) =
      A.legacy.encode (A.convolutionStar (A.legacy.decode f) g) := by
  simp [legacyConvolutionStar]

@[simp] theorem legacyConvolutionStar_encode_encode
    (A : SourceTestAlgebra) (f g : A.Test) :
    A.legacyConvolutionStar (A.legacy.encode f) (A.legacy.encode g) =
      A.legacy.encode (A.convolutionStar f g) := by
  simp [legacyConvolutionStar]

@[simp] theorem legacyInvolution_encode
    (A : SourceTestAlgebra) (f : A.Test) :
    A.legacyInvolution (A.legacy.encode f) =
      A.legacy.encode (A.involution f) := by
  simp [legacyInvolution]

@[simp] theorem legacyConvolutionSquare_encode
    (A : SourceTestAlgebra) (g : A.Test) :
    A.legacyConvolutionSquare (A.legacy.encode g) =
      A.legacy.encode (A.convolutionSquare g) := by
  simp [legacyConvolutionSquare]

@[simp] theorem legacy_decode_legacyConvolutionStar_encode_encode
    (A : SourceTestAlgebra) (f g : A.Test) :
    A.legacy.decode
        (A.legacyConvolutionStar (A.legacy.encode f) (A.legacy.encode g)) =
      A.convolutionStar f g := by
  simp

@[simp] theorem legacy_decode_legacyInvolution_encode
    (A : SourceTestAlgebra) (f : A.Test) :
    A.legacy.decode (A.legacyInvolution (A.legacy.encode f)) =
      A.involution f := by
  simp

@[simp] theorem legacy_decode_legacyConvolutionSquare_encode
    (A : SourceTestAlgebra) (g : A.Test) :
    A.legacy.decode (A.legacyConvolutionSquare (A.legacy.encode g)) =
      A.convolutionSquare g := by
  simp

theorem legacyConvolutionSquare_eq_legacyConvolutionStar_self
    (A : SourceTestAlgebra) (f : TestFunction) :
    A.legacyConvolutionSquare f = A.legacyConvolutionStar f f := by
  simp [legacyConvolutionSquare, legacyConvolutionStar,
    A.convolutionSquare_eq (A.legacy.decode f)]

theorem legacyConvolutionStar_self_eq_legacyConvolutionSquare
    (A : SourceTestAlgebra) (f : TestFunction) :
    A.legacyConvolutionStar f f = A.legacyConvolutionSquare f :=
  (A.legacyConvolutionSquare_eq_legacyConvolutionStar_self f).symm

theorem legacy_convolution_star_square
    (A : SourceTestAlgebra) (g : A.Test) :
    A.legacyConvolutionStar (A.legacy.encode g) (A.legacy.encode g) =
      A.legacy.encode (A.convolutionSquare g) := by
  simp [legacyConvolutionStar, A.convolutionSquare_eq g]

theorem legacy_convolution_square_star
    (A : SourceTestAlgebra) (g : A.Test) :
    A.legacyConvolutionSquare (A.legacy.encode g) =
      A.legacy.encode (A.convolutionStar g g) := by
  simp [legacyConvolutionSquare, A.convolutionSquare_eq g]

theorem legacy_decode_legacyConvolutionStar_square
    (A : SourceTestAlgebra) (f : TestFunction) :
    A.legacy.decode (A.legacyConvolutionStar f f) =
      A.convolutionSquare (A.legacy.decode f) := by
  calc
    A.legacy.decode (A.legacyConvolutionStar f f) =
        A.convolutionStar (A.legacy.decode f) (A.legacy.decode f) :=
      legacy_decode_legacyConvolutionStar A f f
    _ = A.convolutionSquare (A.legacy.decode f) :=
      (A.convolutionSquare_eq (A.legacy.decode f)).symm

@[simp] theorem legacy_decode_legacyConvolutionStar_encode_square
    (A : SourceTestAlgebra) (g : A.Test) :
    A.legacy.decode
        (A.legacyConvolutionStar (A.legacy.encode g) (A.legacy.encode g)) =
      A.convolutionSquare g := by
  simp [A.convolutionSquare_eq g]

end SourceTestAlgebra

/-- Source evaluation data for the shared test object. -/
structure SourceEvaluationData (A : SourceTestAlgebra) where

namespace SourceEvaluationData

noncomputable def valueAt {A : SourceTestAlgebra}
    (_E : SourceEvaluationData A) (F : A.Test) (x : ℝ) : ℝ :=
  ‖A.legacy.encode F x‖

noncomputable def mellinAt {A : SourceTestAlgebra}
    (_E : SourceEvaluationData A) (F : A.Test) (s : ℂ) : ℂ :=
  mellin (fun x : ℝ => A.legacy.encode F x) s

noncomputable def poleFunctional {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : A.Test) : ℝ :=
  (E.mellinAt F (Complex.I / 2)).re +
    (E.mellinAt F (-Complex.I / 2)).re

noncomputable def polePairing {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (g : A.Test) : ℝ :=
  E.poleFunctional (A.convolutionSquare g)

@[simp] theorem valueAt_eq_norm {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : A.Test) (x : ℝ) :
    E.valueAt F x = ‖A.legacy.encode F x‖ :=
  rfl

@[simp] theorem mellinAt_eq_mellin {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : A.Test) (s : ℂ) :
    E.mellinAt F s = mellin (fun x : ℝ => A.legacy.encode F x) s :=
  rfl

noncomputable def legacyValueAt {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) : TestFunction → ℝ → ℝ :=
  fun F x => E.valueAt (A.legacy.decode F) x

noncomputable def sourcePrimePowerPairing {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (n : ℕ) (f g : A.Test) : ℝ :=
  (1 / Real.sqrt (n : ℝ)) *
    (E.valueAt (A.convolutionStar f g) (n : ℝ) +
      E.valueAt (A.convolutionStar f g) ((n : ℝ)⁻¹))

noncomputable def sourceFinitePrimeTerm {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (n : ℕ) (F : A.Test) : ℝ :=
  ArithmeticFunction.vonMangoldt n *
    ((1 / Real.sqrt (n : ℝ)) *
      (E.valueAt F (n : ℝ) + E.valueAt F ((n : ℝ)⁻¹)))

noncomputable def legacySourcePrimePowerPairing {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) : ℕ → TestFunction → TestFunction → ℝ :=
  fun n f g =>
    E.sourcePrimePowerPairing n (A.legacy.decode f) (A.legacy.decode g)

@[simp] theorem legacyValueAt_apply {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : TestFunction) (x : ℝ) :
    E.legacyValueAt F x = E.valueAt (A.legacy.decode F) x :=
  rfl

@[simp] theorem sourcePrimePowerPairing_eq_valueAt
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (n : ℕ) (f g : A.Test) :
    E.sourcePrimePowerPairing n f g =
      (1 / Real.sqrt (n : ℝ)) *
        (E.valueAt (A.convolutionStar f g) (n : ℝ) +
          E.valueAt (A.convolutionStar f g) ((n : ℝ)⁻¹)) :=
  rfl

@[simp] theorem sourceFinitePrimeTerm_eq_valueAt
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (n : ℕ) (F : A.Test) :
    E.sourceFinitePrimeTerm n F =
      ArithmeticFunction.vonMangoldt n *
        ((1 / Real.sqrt (n : ℝ)) *
          (E.valueAt F (n : ℝ) + E.valueAt F ((n : ℝ)⁻¹))) :=
  rfl

@[simp] theorem sourceFinitePrimeTerm_convolutionStar
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (n : ℕ) (f g : A.Test) :
    E.sourceFinitePrimeTerm n (A.convolutionStar f g) =
      ArithmeticFunction.vonMangoldt n *
        E.sourcePrimePowerPairing n f g :=
  rfl

theorem sourceFinitePrimeTerm_nonzero_primePower
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) {n : ℕ} {F : A.Test}
    (h : E.sourceFinitePrimeTerm n F ≠ 0) :
    IsPrimePow n := by
  by_contra hn
  apply h
  simp [sourceFinitePrimeTerm, ArithmeticFunction.vonMangoldt_apply, hn]

@[simp] theorem legacySourcePrimePowerPairing_apply
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (n : ℕ) (f g : TestFunction) :
    E.legacySourcePrimePowerPairing n f g =
      E.sourcePrimePowerPairing n (A.legacy.decode f) (A.legacy.decode g) :=
  rfl

@[simp] theorem legacyValueAt_eq_norm {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : TestFunction) (x : ℝ) :
    E.legacyValueAt F x = ‖F x‖ := by
  simp [legacyValueAt, valueAt]

@[simp] theorem legacyValueAt_encode {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : A.Test) (x : ℝ) :
    E.legacyValueAt (A.legacy.encode F) x = E.valueAt F x := by
  simp [legacyValueAt]

@[simp] theorem legacyValueAt_encode_eq_norm {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : A.Test) (x : ℝ) :
    E.legacyValueAt (A.legacy.encode F) x = ‖A.legacy.encode F x‖ := by
  simp [legacyValueAt]

@[simp] theorem legacyValueAt_legacyConvolutionStar_eq_norm
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F G : TestFunction) (x : ℝ) :
    E.legacyValueAt (A.legacyConvolutionStar F G) x =
      ‖A.legacyConvolutionStar F G x‖ := by
  simp [legacyValueAt, valueAt]

@[simp] theorem legacyValueAt_legacyInvolution_eq_norm
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : TestFunction) (x : ℝ) :
    E.legacyValueAt (A.legacyInvolution F) x =
      ‖A.legacyInvolution F x‖ := by
  simp [legacyValueAt, valueAt]

@[simp] theorem legacyValueAt_legacyConvolutionSquare_eq_norm
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : TestFunction) (x : ℝ) :
    E.legacyValueAt (A.legacyConvolutionSquare F) x =
      ‖A.legacyConvolutionSquare F x‖ := by
  simp [legacyValueAt, valueAt]

@[simp] theorem legacyValueAt_legacyConvolutionStar {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F G : TestFunction) (x : ℝ) :
    E.legacyValueAt (A.legacyConvolutionStar F G) x =
      E.valueAt (A.convolutionStar (A.legacy.decode F) (A.legacy.decode G)) x :=
  by simp [legacyValueAt, SourceTestAlgebra.legacyConvolutionStar]

@[simp] theorem legacyValueAt_legacyInvolution {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : TestFunction) (x : ℝ) :
    E.legacyValueAt (A.legacyInvolution F) x =
      E.valueAt (A.involution (A.legacy.decode F)) x :=
  by simp [legacyValueAt, SourceTestAlgebra.legacyInvolution]

@[simp] theorem legacyValueAt_legacyConvolutionSquare {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : TestFunction) (x : ℝ) :
    E.legacyValueAt (A.legacyConvolutionSquare F) x =
      E.valueAt (A.convolutionSquare (A.legacy.decode F)) x :=
  by simp [legacyValueAt, SourceTestAlgebra.legacyConvolutionSquare]

@[simp] theorem legacyValueAt_legacyConvolutionStar_encode_left
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : A.Test) (G : TestFunction) (x : ℝ) :
    E.legacyValueAt (A.legacyConvolutionStar (A.legacy.encode F) G) x =
      E.valueAt (A.convolutionStar F (A.legacy.decode G)) x := by
  simp [legacyValueAt]

@[simp] theorem legacyValueAt_legacyConvolutionStar_encode_right
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : TestFunction) (G : A.Test) (x : ℝ) :
    E.legacyValueAt (A.legacyConvolutionStar F (A.legacy.encode G)) x =
      E.valueAt (A.convolutionStar (A.legacy.decode F) G) x := by
  simp [legacyValueAt]

@[simp] theorem legacyValueAt_legacyConvolutionStar_encode_encode
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F G : A.Test) (x : ℝ) :
    E.legacyValueAt
        (A.legacyConvolutionStar (A.legacy.encode F) (A.legacy.encode G)) x =
      E.valueAt (A.convolutionStar F G) x := by
  simp [legacyValueAt]

@[simp] theorem legacyValueAt_legacyConvolutionStar_self
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : TestFunction) (x : ℝ) :
    E.legacyValueAt (A.legacyConvolutionStar F F) x =
      E.valueAt (A.convolutionSquare (A.legacy.decode F)) x := by
  rw [legacyValueAt_legacyConvolutionStar, A.convolutionSquare_eq]

@[simp] theorem legacyValueAt_legacyConvolutionStar_encode_square
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : A.Test) (x : ℝ) :
    E.legacyValueAt
        (A.legacyConvolutionStar (A.legacy.encode F) (A.legacy.encode F)) x =
      E.valueAt (A.convolutionSquare F) x := by
  simp [legacyValueAt, A.convolutionSquare_eq F]

@[simp] theorem legacyValueAt_legacyConvolutionSquare_encode
    {A : SourceTestAlgebra}
    (E : SourceEvaluationData A) (F : A.Test) (x : ℝ) :
    E.legacyValueAt (A.legacyConvolutionSquare (A.legacy.encode F)) x =
      E.valueAt (A.convolutionSquare F) x := by
  simp [legacyValueAt]

theorem poleFunctional_eq_mellin_half_sum
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (F : A.Test) :
    E.poleFunctional F =
      (E.mellinAt F (Complex.I / 2)).re +
        (E.mellinAt F (-Complex.I / 2)).re :=
  rfl

theorem mellin_half_sum_eq_poleFunctional
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (F : A.Test) :
    (E.mellinAt F (Complex.I / 2)).re +
        (E.mellinAt F (-Complex.I / 2)).re =
      E.poleFunctional F :=
  rfl

theorem polePairing_eq_poleFunctional_convolutionSquare
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (g : A.Test) :
    E.polePairing g = E.poleFunctional (A.convolutionSquare g) :=
  rfl

theorem poleFunctional_convolutionSquare_eq_polePairing
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (g : A.Test) :
    E.poleFunctional (A.convolutionSquare g) = E.polePairing g :=
  rfl

theorem polePairing_eq_mellin_convolutionSquare_half_sum
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (g : A.Test) :
    E.polePairing g =
      (E.mellinAt (A.convolutionSquare g) (Complex.I / 2)).re +
        (E.mellinAt (A.convolutionSquare g) (-Complex.I / 2)).re := by
  rfl

theorem mellin_convolutionSquare_half_sum_eq_polePairing
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (g : A.Test) :
    (E.mellinAt (A.convolutionSquare g) (Complex.I / 2)).re +
        (E.mellinAt (A.convolutionSquare g) (-Complex.I / 2)).re =
      E.polePairing g :=
  (E.polePairing_eq_mellin_convolutionSquare_half_sum g).symm

theorem polePairing_eq_poleFunctional_convolutionStar_self
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (g : A.Test) :
    E.polePairing g = E.poleFunctional (A.convolutionStar g g) := by
  rw [polePairing_eq_poleFunctional_convolutionSquare, A.convolutionSquare_eq g]

theorem poleFunctional_convolutionStar_self_eq_polePairing
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (g : A.Test) :
    E.poleFunctional (A.convolutionStar g g) = E.polePairing g :=
  (E.polePairing_eq_poleFunctional_convolutionStar_self g).symm

theorem polePairing_eq_mellin_convolutionStar_self_half_sum
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (g : A.Test) :
    E.polePairing g =
      (E.mellinAt (A.convolutionStar g g) (Complex.I / 2)).re +
        (E.mellinAt (A.convolutionStar g g) (-Complex.I / 2)).re := by
  rw [E.polePairing_eq_poleFunctional_convolutionStar_self g,
    E.poleFunctional_eq_mellin_half_sum (A.convolutionStar g g)]

theorem mellin_convolutionStar_self_half_sum_eq_polePairing
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (g : A.Test) :
    (E.mellinAt (A.convolutionStar g g) (Complex.I / 2)).re +
        (E.mellinAt (A.convolutionStar g g) (-Complex.I / 2)).re =
      E.polePairing g :=
  (E.polePairing_eq_mellin_convolutionStar_self_half_sum g).symm

theorem polePairing_decode_eq_poleFunctional_decode_legacyConvolutionStar_self
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (f : TestFunction) :
    E.polePairing (A.legacy.decode f) =
      E.poleFunctional (A.legacy.decode (A.legacyConvolutionStar f f)) := by
  rw [E.polePairing_eq_poleFunctional_convolutionSquare (A.legacy.decode f),
    SourceTestAlgebra.legacy_decode_legacyConvolutionStar_square]

theorem poleFunctional_decode_legacyConvolutionStar_self_eq_polePairing_decode
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (f : TestFunction) :
    E.poleFunctional (A.legacy.decode (A.legacyConvolutionStar f f)) =
      E.polePairing (A.legacy.decode f) :=
  (E.polePairing_decode_eq_poleFunctional_decode_legacyConvolutionStar_self f).symm

theorem polePairing_decode_eq_mellin_decode_legacyConvolutionStar_self_half_sum
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (f : TestFunction) :
    E.polePairing (A.legacy.decode f) =
      (E.mellinAt
          (A.legacy.decode (A.legacyConvolutionStar f f))
          (Complex.I / 2)).re +
        (E.mellinAt
          (A.legacy.decode (A.legacyConvolutionStar f f))
          (-Complex.I / 2)).re := by
  rw [E.polePairing_decode_eq_poleFunctional_decode_legacyConvolutionStar_self f,
    E.poleFunctional_eq_mellin_half_sum
      (A.legacy.decode (A.legacyConvolutionStar f f))]

theorem mellin_decode_legacyConvolutionStar_self_half_sum_eq_polePairing_decode
    {A : SourceTestAlgebra} (E : SourceEvaluationData A)
    (f : TestFunction) :
    (E.mellinAt
        (A.legacy.decode (A.legacyConvolutionStar f f))
        (Complex.I / 2)).re +
      (E.mellinAt
        (A.legacy.decode (A.legacyConvolutionStar f f))
        (-Complex.I / 2)).re =
      E.polePairing (A.legacy.decode f) :=
  (E.polePairing_decode_eq_mellin_decode_legacyConvolutionStar_self_half_sum f).symm

end SourceEvaluationData

/-- Point/window incidence coordinate for the CCM24 source-window carrier. -/
structure SourceWindowMembershipCoordinate (SupportPoint Window : Type) where
  pointCoordinate : SupportPoint → Window → ℝ
  lowerEndpoint : Window → ℝ
  upperEndpoint : Window → ℝ

namespace SourceWindowMembershipCoordinate

/-- The lower closed-window incidence relation behind the base carrier. -/
def pointInClosedWindow
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) : Prop :=
  C.lowerEndpoint I ≤ C.pointCoordinate x I ∧
    C.pointCoordinate x I ≤ C.upperEndpoint I

def pointInBaseWindow
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) : Prop :=
  C.pointInClosedWindow x I

theorem pointInClosedWindow_lower
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hx : C.pointInClosedWindow x I) :
    C.lowerEndpoint I ≤ C.pointCoordinate x I :=
  hx.1

theorem pointInClosedWindow_upper
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hx : C.pointInClosedWindow x I) :
    C.pointCoordinate x I ≤ C.upperEndpoint I :=
  hx.2

theorem pointInClosedWindow_iff
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    C.pointInClosedWindow x I ↔
      C.lowerEndpoint I ≤ C.pointCoordinate x I ∧
        C.pointCoordinate x I ≤ C.upperEndpoint I :=
  Iff.rfl

theorem pointInClosedWindow_of_bounds
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hLower : C.lowerEndpoint I ≤ C.pointCoordinate x I)
    (hUpper : C.pointCoordinate x I ≤ C.upperEndpoint I) :
    C.pointInClosedWindow x I :=
  ⟨hLower, hUpper⟩

theorem pointInBaseWindow_iff
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    C.pointInBaseWindow x I ↔
      C.lowerEndpoint I ≤ C.pointCoordinate x I ∧
        C.pointCoordinate x I ≤ C.upperEndpoint I :=
  Iff.rfl

theorem pointInBaseWindow_iff_closedWindow
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    C.pointInBaseWindow x I ↔ C.pointInClosedWindow x I :=
  Iff.rfl

theorem pointInBaseWindow_lower
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hx : C.pointInBaseWindow x I) :
    C.lowerEndpoint I ≤ C.pointCoordinate x I :=
  pointInClosedWindow_lower hx

theorem pointInBaseWindow_upper
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hx : C.pointInBaseWindow x I) :
    C.pointCoordinate x I ≤ C.upperEndpoint I :=
  pointInClosedWindow_upper hx

def baseCarrier
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (I : Window) : Set SupportPoint :=
  {x | C.pointInBaseWindow x I}

theorem mem_baseCarrier_iff
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    x ∈ C.baseCarrier I ↔ C.pointInBaseWindow x I :=
  Iff.rfl

theorem mem_baseCarrier_iff_closedWindow
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    x ∈ C.baseCarrier I ↔ C.pointInClosedWindow x I :=
  Iff.rfl

theorem mem_baseCarrier_iff_bounds
    {SupportPoint Window : Type}
    (C : SourceWindowMembershipCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    x ∈ C.baseCarrier I ↔
      C.lowerEndpoint I ≤ C.pointCoordinate x I ∧
        C.pointCoordinate x I ≤ C.upperEndpoint I :=
  Iff.rfl

theorem mem_baseCarrier_lower
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hx : x ∈ C.baseCarrier I) :
    C.lowerEndpoint I ≤ C.pointCoordinate x I :=
  pointInBaseWindow_lower hx

theorem mem_baseCarrier_upper
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hx : x ∈ C.baseCarrier I) :
    C.pointCoordinate x I ≤ C.upperEndpoint I :=
  pointInBaseWindow_upper hx

theorem pointInBaseWindow_of_bounds
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hLower : C.lowerEndpoint I ≤ C.pointCoordinate x I)
    (hUpper : C.pointCoordinate x I ≤ C.upperEndpoint I) :
    C.pointInBaseWindow x I :=
  pointInClosedWindow_of_bounds hLower hUpper

theorem mem_baseCarrier_of_bounds
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hLower : C.lowerEndpoint I ≤ C.pointCoordinate x I)
    (hUpper : C.pointCoordinate x I ≤ C.upperEndpoint I) :
    x ∈ C.baseCarrier I :=
  pointInBaseWindow_of_bounds hLower hUpper

theorem carrier_subset_baseCarrier_of_bounds
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {I : Window} {carrier : Set SupportPoint}
    (hLower : ∀ x : SupportPoint, x ∈ carrier →
      C.lowerEndpoint I ≤ C.pointCoordinate x I)
    (hUpper : ∀ x : SupportPoint, x ∈ carrier →
      C.pointCoordinate x I ≤ C.upperEndpoint I) :
    carrier ⊆ C.baseCarrier I := by
  intro x hx
  exact mem_baseCarrier_of_bounds (hLower x hx) (hUpper x hx)

theorem carrier_subset_baseCarrier_iff_bounds
    {SupportPoint Window : Type}
    {C : SourceWindowMembershipCoordinate SupportPoint Window}
    {I : Window} {carrier : Set SupportPoint} :
    carrier ⊆ C.baseCarrier I ↔
      ∀ x : SupportPoint, x ∈ carrier →
        C.lowerEndpoint I ≤ C.pointCoordinate x I ∧
          C.pointCoordinate x I ≤ C.upperEndpoint I := by
  constructor
  · intro hSubset x hx
    exact (mem_baseCarrier_iff_bounds C x I).mp (hSubset hx)
  · intro hBounds
    exact carrier_subset_baseCarrier_of_bounds
      (fun x hx => (hBounds x hx).1)
      (fun x hx => (hBounds x hx).2)

end SourceWindowMembershipCoordinate

/-- Logarithmic scale coordinate for CCM24 source support points. -/
structure SourceSupportLogScaleCoordinate (SupportPoint : Type) where
  logScale : SupportPoint → ℝ

namespace SourceSupportLogScaleCoordinate

noncomputable def scale
    {SupportPoint : Type}
    (C : SourceSupportLogScaleCoordinate SupportPoint)
    (x : SupportPoint) : ℝ :=
  Real.exp (C.logScale x)

theorem scale_eq_one_of_logScale_eq_zero
    {SupportPoint : Type}
    {C : SourceSupportLogScaleCoordinate SupportPoint}
    {x : SupportPoint} (hLog : C.logScale x = 0) :
    C.scale x = 1 := by
  simp [scale, hLog]

theorem logScale_eq_zero_of_scale_eq_one
    {SupportPoint : Type}
    {C : SourceSupportLogScaleCoordinate SupportPoint}
    {x : SupportPoint} (hScale : C.scale x = 1) :
    C.logScale x = 0 := by
  exact (Real.exp_eq_one_iff _).mp (by
    simpa [scale] using hScale)

end SourceSupportLogScaleCoordinate

/-- CCM24 source-window coordinate object for support points. -/
structure SourceWindowCoordinate (SupportPoint Window : Type) where
  windowMembershipCoordinate :
    SourceWindowMembershipCoordinate SupportPoint Window
  supportLogScaleCoordinate :
    SourceSupportLogScaleCoordinate SupportPoint

namespace SourceWindowCoordinate

def baseCarrier
    {SupportPoint Window : Type}
    (C : SourceWindowCoordinate SupportPoint Window)
    (I : Window) : Set SupportPoint :=
  C.windowMembershipCoordinate.baseCarrier I

theorem mem_baseCarrier_iff
    {SupportPoint Window : Type}
    (C : SourceWindowCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    x ∈ C.baseCarrier I ↔
      x ∈ C.windowMembershipCoordinate.baseCarrier I :=
  Iff.rfl

theorem mem_baseCarrier_iff_bounds
    {SupportPoint Window : Type}
    (C : SourceWindowCoordinate SupportPoint Window)
    (x : SupportPoint) (I : Window) :
    x ∈ C.baseCarrier I ↔
      C.windowMembershipCoordinate.lowerEndpoint I ≤
          C.windowMembershipCoordinate.pointCoordinate x I ∧
        C.windowMembershipCoordinate.pointCoordinate x I ≤
          C.windowMembershipCoordinate.upperEndpoint I :=
  SourceWindowMembershipCoordinate.mem_baseCarrier_iff_bounds
    C.windowMembershipCoordinate x I

theorem mem_baseCarrier_lower
    {SupportPoint Window : Type}
    {C : SourceWindowCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hx : x ∈ C.baseCarrier I) :
    C.windowMembershipCoordinate.lowerEndpoint I ≤
      C.windowMembershipCoordinate.pointCoordinate x I :=
  SourceWindowMembershipCoordinate.mem_baseCarrier_lower hx

theorem mem_baseCarrier_upper
    {SupportPoint Window : Type}
    {C : SourceWindowCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hx : x ∈ C.baseCarrier I) :
    C.windowMembershipCoordinate.pointCoordinate x I ≤
      C.windowMembershipCoordinate.upperEndpoint I :=
  SourceWindowMembershipCoordinate.mem_baseCarrier_upper hx

theorem mem_baseCarrier_of_bounds
    {SupportPoint Window : Type}
    {C : SourceWindowCoordinate SupportPoint Window}
    {x : SupportPoint} {I : Window}
    (hLower :
      C.windowMembershipCoordinate.lowerEndpoint I ≤
        C.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper :
      C.windowMembershipCoordinate.pointCoordinate x I ≤
        C.windowMembershipCoordinate.upperEndpoint I) :
    x ∈ C.baseCarrier I :=
  SourceWindowMembershipCoordinate.mem_baseCarrier_of_bounds hLower hUpper

theorem carrier_subset_baseCarrier_of_bounds
    {SupportPoint Window : Type}
    {C : SourceWindowCoordinate SupportPoint Window}
    {I : Window} {carrier : Set SupportPoint}
    (hLower : ∀ x : SupportPoint, x ∈ carrier →
      C.windowMembershipCoordinate.lowerEndpoint I ≤
        C.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper : ∀ x : SupportPoint, x ∈ carrier →
      C.windowMembershipCoordinate.pointCoordinate x I ≤
        C.windowMembershipCoordinate.upperEndpoint I) :
    carrier ⊆ C.baseCarrier I :=
  SourceWindowMembershipCoordinate.carrier_subset_baseCarrier_of_bounds
    hLower hUpper

theorem carrier_subset_baseCarrier_iff_bounds
    {SupportPoint Window : Type}
    {C : SourceWindowCoordinate SupportPoint Window}
    {I : Window} {carrier : Set SupportPoint} :
    carrier ⊆ C.baseCarrier I ↔
      ∀ x : SupportPoint, x ∈ carrier →
        C.windowMembershipCoordinate.lowerEndpoint I ≤
            C.windowMembershipCoordinate.pointCoordinate x I ∧
          C.windowMembershipCoordinate.pointCoordinate x I ≤
            C.windowMembershipCoordinate.upperEndpoint I :=
  SourceWindowMembershipCoordinate.carrier_subset_baseCarrier_iff_bounds

noncomputable def scale
    {SupportPoint Window : Type}
    (C : SourceWindowCoordinate SupportPoint Window)
    (x : SupportPoint) : ℝ :=
  C.supportLogScaleCoordinate.scale x

theorem scale_eq_one_of_logScale_eq_zero
    {SupportPoint Window : Type}
    {C : SourceWindowCoordinate SupportPoint Window}
    {x : SupportPoint}
    (hLog : C.supportLogScaleCoordinate.logScale x = 0) :
    C.scale x = 1 :=
  SourceSupportLogScaleCoordinate.scale_eq_one_of_logScale_eq_zero hLog

theorem logScale_eq_zero_of_scale_eq_one
    {SupportPoint Window : Type}
    {C : SourceWindowCoordinate SupportPoint Window}
    {x : SupportPoint}
    (hScale : C.scale x = 1) :
    C.supportLogScaleCoordinate.logScale x = 0 :=
  SourceSupportLogScaleCoordinate.logScale_eq_zero_of_scale_eq_one
    (C := C.supportLogScaleCoordinate) (by
      simpa [scale] using hScale)

end SourceWindowCoordinate

/-- CCM24-facing support/window data for the shared source tests. -/
structure SourceSupportWindowData (A : SourceTestAlgebra) where
  PlaceSet : Type
  Window : Type
  sourcePlaceSet : PlaceSet
  sourceSupportWindow : Window
  sourceTest : A.Test
  SupportPoint : Type
  supportValue : A.Test → SupportPoint → ℝ
  sourceWindowCoordinate : SourceWindowCoordinate SupportPoint Window

namespace SourceSupportWindowData

def supportCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) : Set S.SupportPoint :=
  {x | S.supportValue f x ≠ 0}

def fourierSupportCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) : Set S.SupportPoint :=
  S.supportCarrier (A.involution f)

@[simp] theorem mem_supportCarrier_iff_supportValue_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint} :
    x ∈ S.supportCarrier f ↔ S.supportValue f x ≠ 0 :=
  Iff.rfl

@[simp] theorem fourierSupportCarrier_eq_supportCarrier_involution
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) :
    S.fourierSupportCarrier f = S.supportCarrier (A.involution f) :=
  rfl

theorem supportValue_ne_zero_of_mem_supportCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.supportValue f x ≠ 0 :=
  hx

theorem mem_supportCarrier_of_supportValue_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint}
    (hx : S.supportValue f x ≠ 0) :
    x ∈ S.supportCarrier f :=
  hx

theorem not_mem_supportCarrier_iff_supportValue_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint} :
    x ∉ S.supportCarrier f ↔ S.supportValue f x = 0 :=
  by
    change ¬S.supportValue f x ≠ 0 ↔ S.supportValue f x = 0
    exact not_ne_iff

theorem supportValue_eq_zero_of_not_mem_supportCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint}
    (hx : x ∉ S.supportCarrier f) :
    S.supportValue f x = 0 :=
  not_mem_supportCarrier_iff_supportValue_eq_zero.mp hx

theorem not_mem_supportCarrier_of_supportValue_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint}
    (hx : S.supportValue f x = 0) :
    x ∉ S.supportCarrier f :=
  not_mem_supportCarrier_iff_supportValue_eq_zero.mpr hx

theorem supportValue_eq_zero_iff_not_mem_supportCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint} :
    S.supportValue f x = 0 ↔ x ∉ S.supportCarrier f :=
  not_mem_supportCarrier_iff_supportValue_eq_zero.symm

theorem supportCarrier_subset_iff_supportValue_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {carrier : Set S.SupportPoint} :
    carrier ⊆ S.supportCarrier f ↔
      ∀ x : S.SupportPoint, x ∈ carrier → S.supportValue f x ≠ 0 := by
  constructor
  · intro hSubset x hx
    exact hSubset hx
  · intro hPoint x hx
    exact hPoint x hx

theorem supportCarrier_subset_zero_complement
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} :
    S.supportCarrier f ⊆ {x : S.SupportPoint | S.supportValue f x ≠ 0} := by
  intro x hx
  exact hx

theorem supportCarrier_nonempty_iff_exists_supportValue_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} :
    Set.Nonempty (S.supportCarrier f) ↔
      ∃ x : S.SupportPoint, S.supportValue f x ≠ 0 := by
  constructor
  · intro hNonempty
    rcases hNonempty with ⟨x, hx⟩
    exact ⟨x, hx⟩
  · intro hExists
    rcases hExists with ⟨x, hx⟩
    exact ⟨x, hx⟩

@[simp] theorem mem_fourierSupportCarrier_iff_supportValue_involution_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint} :
    x ∈ S.fourierSupportCarrier f ↔ S.supportValue (A.involution f) x ≠ 0 :=
  Iff.rfl

theorem supportValue_involution_ne_zero_of_mem_fourierSupportCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    S.supportValue (A.involution f) x ≠ 0 :=
  hx

theorem mem_fourierSupportCarrier_of_supportValue_involution_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint}
    (hx : S.supportValue (A.involution f) x ≠ 0) :
    x ∈ S.fourierSupportCarrier f :=
  hx

theorem not_mem_fourierSupportCarrier_iff_supportValue_involution_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint} :
    x ∉ S.fourierSupportCarrier f ↔
      S.supportValue (A.involution f) x = 0 :=
  by
    change ¬S.supportValue (A.involution f) x ≠ 0 ↔
      S.supportValue (A.involution f) x = 0
    exact not_ne_iff

theorem supportValue_involution_eq_zero_of_not_mem_fourierSupportCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint}
    (hx : x ∉ S.fourierSupportCarrier f) :
    S.supportValue (A.involution f) x = 0 :=
  not_mem_fourierSupportCarrier_iff_supportValue_involution_eq_zero.mp hx

theorem not_mem_fourierSupportCarrier_of_supportValue_involution_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint}
    (hx : S.supportValue (A.involution f) x = 0) :
    x ∉ S.fourierSupportCarrier f :=
  not_mem_fourierSupportCarrier_iff_supportValue_involution_eq_zero.mpr hx

theorem supportValue_involution_eq_zero_iff_not_mem_fourierSupportCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {x : S.SupportPoint} :
    S.supportValue (A.involution f) x = 0 ↔
      x ∉ S.fourierSupportCarrier f :=
  not_mem_fourierSupportCarrier_iff_supportValue_involution_eq_zero.symm

theorem fourierSupportCarrier_subset_iff_supportValue_involution_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {carrier : Set S.SupportPoint} :
    carrier ⊆ S.fourierSupportCarrier f ↔
      ∀ x : S.SupportPoint, x ∈ carrier →
        S.supportValue (A.involution f) x ≠ 0 := by
  constructor
  · intro hSubset x hx
    exact hSubset hx
  · intro hPoint x hx
    exact hPoint x hx

theorem fourierSupportCarrier_subset_zero_complement
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} :
    S.fourierSupportCarrier f ⊆
      {x : S.SupportPoint | S.supportValue (A.involution f) x ≠ 0} := by
  intro x hx
  exact hx

theorem fourierSupportCarrier_nonempty_iff_exists_supportValue_involution_ne_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} :
    Set.Nonempty (S.fourierSupportCarrier f) ↔
      ∃ x : S.SupportPoint, S.supportValue (A.involution f) x ≠ 0 := by
  constructor
  · intro hNonempty
    rcases hNonempty with ⟨x, hx⟩
    exact ⟨x, hx⟩
  · intro hExists
    rcases hExists with ⟨x, hx⟩
    exact ⟨x, hx⟩

def windowBaseCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Set S.SupportPoint :=
  S.sourceWindowCoordinate.baseCarrier I

theorem mem_windowBaseCarrier_iff_baseCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint} :
    x ∈ S.windowBaseCarrier I ↔
      x ∈ S.sourceWindowCoordinate.baseCarrier I :=
  Iff.rfl

noncomputable def supportScale
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (x : S.SupportPoint) : ℝ :=
  S.sourceWindowCoordinate.scale x

def windowCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Set S.SupportPoint :=
  {x | x ∈ S.windowBaseCarrier I ∧ S.supportScale x = 1}

def coordinateWindowCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) : Set S.SupportPoint :=
  {x |
    x ∈ S.windowBaseCarrier I ∧
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0}

@[simp] theorem mem_windowCarrier_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint} :
    x ∈ S.windowCarrier I ↔
      x ∈ S.windowBaseCarrier I ∧ S.supportScale x = 1 :=
  Iff.rfl

@[simp] theorem mem_coordinateWindowCarrier_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint} :
    x ∈ S.coordinateWindowCarrier I ↔
      x ∈ S.windowBaseCarrier I ∧
        S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 :=
  Iff.rfl

theorem mem_windowBaseCarrier_of_coordinate_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hLower :
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper :
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I) :
    x ∈ S.windowBaseCarrier I :=
  SourceWindowCoordinate.mem_baseCarrier_of_bounds hLower hUpper

theorem mem_windowBaseCarrier_iff_coordinate_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint} :
    x ∈ S.windowBaseCarrier I ↔
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ∧
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
          S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  SourceWindowCoordinate.mem_baseCarrier_iff_bounds
    S.sourceWindowCoordinate x I

theorem mem_windowBaseCarrier_coordinate_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.windowBaseCarrier I) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I :=
  SourceWindowCoordinate.mem_baseCarrier_lower hx

theorem mem_windowBaseCarrier_coordinate_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.windowBaseCarrier I) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  SourceWindowCoordinate.mem_baseCarrier_upper hx

theorem carrier_subset_windowBaseCarrier_of_coordinate_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {carrier : Set S.SupportPoint}
    (hLower : ∀ x : S.SupportPoint, x ∈ carrier →
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper : ∀ x : S.SupportPoint, x ∈ carrier →
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I) :
    carrier ⊆ S.windowBaseCarrier I :=
  SourceWindowCoordinate.carrier_subset_baseCarrier_of_bounds hLower hUpper

theorem carrier_subset_windowBaseCarrier_iff_coordinate_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {carrier : Set S.SupportPoint} :
    carrier ⊆ S.windowBaseCarrier I ↔
      ∀ x : S.SupportPoint, x ∈ carrier →
        S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
            S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ∧
          S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
            S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  SourceWindowCoordinate.carrier_subset_baseCarrier_iff_bounds

theorem supportScale_eq_one_of_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint}
    (hLog :
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    S.supportScale x = 1 := by
  exact SourceWindowCoordinate.scale_eq_one_of_logScale_eq_zero hLog

theorem logScale_eq_zero_of_supportScale_eq_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint}
    (hScale : S.supportScale x = 1) :
    S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 := by
  exact SourceWindowCoordinate.logScale_eq_zero_of_scale_eq_one
    (C := S.sourceWindowCoordinate) (by
      simpa [supportScale] using hScale)

theorem mem_windowCarrier_windowBase
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    x ∈ S.windowBaseCarrier I :=
  hx.1

theorem mem_windowCarrier_supportScale_eq_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.supportScale x = 1 :=
  hx.2

theorem mem_windowCarrier_coordinate_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I :=
  mem_windowBaseCarrier_coordinate_lower (mem_windowCarrier_windowBase hx)

theorem mem_windowCarrier_coordinate_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  mem_windowBaseCarrier_coordinate_upper (mem_windowCarrier_windowBase hx)

theorem mem_windowCarrier_of_base_and_scale
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hBase : x ∈ S.windowBaseCarrier I)
    (hScale : S.supportScale x = 1) :
    x ∈ S.windowCarrier I :=
  ⟨hBase, hScale⟩

theorem windowCarrier_subset_windowBaseCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} :
    S.windowCarrier I ⊆ S.windowBaseCarrier I := by
  intro x hx
  exact mem_windowCarrier_windowBase hx

theorem mem_coordinateWindowCarrier_windowBase
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    x ∈ S.windowBaseCarrier I :=
  hx.1

theorem mem_coordinateWindowCarrier_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 :=
  hx.2

theorem mem_coordinateWindowCarrier_coordinate_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I :=
  mem_windowBaseCarrier_coordinate_lower
    (mem_coordinateWindowCarrier_windowBase hx)

theorem mem_coordinateWindowCarrier_coordinate_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  mem_windowBaseCarrier_coordinate_upper
    (mem_coordinateWindowCarrier_windowBase hx)

theorem mem_coordinateWindowCarrier_of_base_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hBase : x ∈ S.windowBaseCarrier I)
    (hLog :
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    x ∈ S.coordinateWindowCarrier I :=
  ⟨hBase, hLog⟩

theorem mem_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hLower :
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper :
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog :
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    x ∈ S.coordinateWindowCarrier I :=
  mem_coordinateWindowCarrier_of_base_logScale_eq_zero
    (mem_windowBaseCarrier_of_coordinate_bounds hLower hUpper)
    hLog

theorem mem_coordinateWindowCarrier_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    x ∈ S.windowCarrier I :=
  mem_windowCarrier_of_base_and_scale
    (mem_coordinateWindowCarrier_windowBase hx)
    (supportScale_eq_one_of_logScale_eq_zero
      (mem_coordinateWindowCarrier_logScale_eq_zero hx))

theorem coordinateWindowCarrier_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} :
    S.coordinateWindowCarrier I ⊆ S.windowCarrier I := by
  intro x hx
  exact mem_coordinateWindowCarrier_windowCarrier hx

theorem coordinateWindowCarrier_subset_windowBaseCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} :
    S.coordinateWindowCarrier I ⊆ S.windowBaseCarrier I := by
  intro x hx
  exact mem_coordinateWindowCarrier_windowBase hx

theorem mem_windowCarrier_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    x ∈ S.coordinateWindowCarrier I :=
  mem_coordinateWindowCarrier_of_base_logScale_eq_zero
    (mem_windowCarrier_windowBase hx)
    (logScale_eq_zero_of_supportScale_eq_one
      (mem_windowCarrier_supportScale_eq_one hx))

theorem windowCarrier_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} :
    S.windowCarrier I ⊆ S.coordinateWindowCarrier I := by
  intro x hx
  exact mem_windowCarrier_coordinateWindowCarrier hx

theorem coordinateWindowCarrier_eq_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} :
    S.coordinateWindowCarrier I = S.windowCarrier I :=
  Set.Subset.antisymm coordinateWindowCarrier_subset_windowCarrier
    windowCarrier_subset_coordinateWindowCarrier

theorem windowCarrier_eq_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} :
    S.windowCarrier I = S.coordinateWindowCarrier I :=
  coordinateWindowCarrier_eq_windowCarrier.symm

theorem mem_coordinateWindowCarrier_iff_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint} :
    x ∈ S.coordinateWindowCarrier I ↔ x ∈ S.windowCarrier I := by
  rw [coordinateWindowCarrier_eq_windowCarrier]

theorem carrier_subset_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {carrier : Set S.SupportPoint}
    (hLower : ∀ x : S.SupportPoint, x ∈ carrier →
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper : ∀ x : S.SupportPoint, x ∈ carrier →
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog : ∀ x : S.SupportPoint, x ∈ carrier →
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    carrier ⊆ S.coordinateWindowCarrier I := by
  intro x hx
  exact
    mem_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
      (hLower x hx) (hUpper x hx) (hLog x hx)

theorem mem_windowCarrier_of_coordinate_bounds_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hLower :
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper :
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog :
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    x ∈ S.windowCarrier I :=
  mem_coordinateWindowCarrier_windowCarrier
    (mem_coordinateWindowCarrier_of_coordinate_bounds_logScale_eq_zero
      hLower hUpper hLog)

theorem carrier_subset_windowCarrier_of_coordinate_bounds_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {carrier : Set S.SupportPoint}
    (hLower : ∀ x : S.SupportPoint, x ∈ carrier →
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper : ∀ x : S.SupportPoint, x ∈ carrier →
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog : ∀ x : S.SupportPoint, x ∈ carrier →
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    carrier ⊆ S.windowCarrier I := by
  intro x hx
  exact
    mem_windowCarrier_of_coordinate_bounds_logScale_eq_zero
      (hLower x hx) (hUpper x hx) (hLog x hx)

theorem carrier_subset_windowCarrier_iff_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {carrier : Set S.SupportPoint} :
    carrier ⊆ S.windowCarrier I ↔
      carrier ⊆ S.coordinateWindowCarrier I := by
  constructor
  · intro hSubset x hx
    exact mem_windowCarrier_coordinateWindowCarrier (hSubset hx)
  · intro hSubset x hx
    exact mem_coordinateWindowCarrier_windowCarrier (hSubset hx)

def supportInWindow
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) : Prop :=
  S.supportCarrier f ⊆ S.windowCarrier I

@[simp] theorem supportInWindow_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.supportInWindow f I ↔ S.supportCarrier f ⊆ S.windowCarrier I :=
  Iff.rfl

theorem supportInWindow_iff_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.supportInWindow f I ↔
      S.supportCarrier f ⊆ S.coordinateWindowCarrier I :=
  carrier_subset_windowCarrier_iff_subset_coordinateWindowCarrier

theorem supportInWindow_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) :
    S.supportCarrier f ⊆ S.windowCarrier I :=
  supportInWindow_iff.mp hSupport

theorem supportInWindow_of_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSubset : S.supportCarrier f ⊆ S.windowCarrier I) :
    S.supportInWindow f I :=
  supportInWindow_iff.mpr hSubset

theorem supportInWindow_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) :
    S.supportCarrier f ⊆ S.coordinateWindowCarrier I :=
  supportInWindow_iff_subset_coordinateWindowCarrier.mp hSupport

theorem supportInWindow_of_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSubset : S.supportCarrier f ⊆ S.coordinateWindowCarrier I) :
    S.supportInWindow f I :=
  supportInWindow_iff_subset_coordinateWindowCarrier.mpr hSubset

theorem supportCarrier_mem_coordinateWindowCarrier_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.coordinateWindowCarrier I :=
  supportInWindow_subset_coordinateWindowCarrier hSupport hx

def fourierSupportInWindow
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) : Prop :=
  S.fourierSupportCarrier f ⊆ S.windowCarrier I

@[simp] theorem fourierSupportInWindow_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.fourierSupportInWindow f I ↔
      S.fourierSupportCarrier f ⊆ S.windowCarrier I :=
  Iff.rfl

theorem fourierSupportInWindow_iff_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.fourierSupportInWindow f I ↔
      S.fourierSupportCarrier f ⊆ S.coordinateWindowCarrier I :=
  carrier_subset_windowCarrier_iff_subset_coordinateWindowCarrier

theorem fourierSupportInWindow_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) :
    S.fourierSupportCarrier f ⊆ S.windowCarrier I :=
  fourierSupportInWindow_iff.mp hFourier

theorem fourierSupportInWindow_of_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSubset : S.fourierSupportCarrier f ⊆ S.windowCarrier I) :
    S.fourierSupportInWindow f I :=
  fourierSupportInWindow_iff.mpr hSubset

theorem fourierSupportInWindow_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) :
    S.fourierSupportCarrier f ⊆ S.coordinateWindowCarrier I :=
  fourierSupportInWindow_iff_subset_coordinateWindowCarrier.mp hFourier

theorem fourierSupportInWindow_of_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSubset : S.fourierSupportCarrier f ⊆ S.coordinateWindowCarrier I) :
    S.fourierSupportInWindow f I :=
  fourierSupportInWindow_iff_subset_coordinateWindowCarrier.mpr hSubset

theorem fourierSupportCarrier_mem_coordinateWindowCarrier_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.coordinateWindowCarrier I :=
  fourierSupportInWindow_subset_coordinateWindowCarrier hFourier hx

def supportTransported
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) : Prop :=
  S.supportInWindow f I

@[simp] theorem supportTransported_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.supportTransported f I ↔ S.supportInWindow f I :=
  Iff.rfl

theorem supportTransported_iff_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.supportTransported f I ↔
      S.supportCarrier f ⊆ S.coordinateWindowCarrier I :=
  supportInWindow_iff_subset_coordinateWindowCarrier

theorem supportInWindow_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) :
    S.supportInWindow f I :=
  supportTransported_iff.mp hTransported

theorem supportTransported_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) :
    S.supportCarrier f ⊆ S.coordinateWindowCarrier I :=
  supportTransported_iff_subset_coordinateWindowCarrier.mp hTransported

theorem supportTransported_of_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSubset : S.supportCarrier f ⊆ S.coordinateWindowCarrier I) :
    S.supportTransported f I :=
  supportTransported_iff_subset_coordinateWindowCarrier.mpr hSubset

def convolutionSupportTransported
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (f : A.Test) (I : S.Window) : Prop :=
  S.fourierSupportInWindow f I

@[simp] theorem convolutionSupportTransported_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.convolutionSupportTransported f I ↔ S.fourierSupportInWindow f I :=
  Iff.rfl

theorem convolutionSupportTransported_iff_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.convolutionSupportTransported f I ↔
      S.fourierSupportCarrier f ⊆ S.coordinateWindowCarrier I :=
  fourierSupportInWindow_iff_subset_coordinateWindowCarrier

theorem fourierSupportInWindow_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I) :
    S.fourierSupportInWindow f I :=
  convolutionSupportTransported_iff.mp hTransported

theorem convolutionSupportTransported_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I) :
    S.fourierSupportCarrier f ⊆ S.coordinateWindowCarrier I :=
  convolutionSupportTransported_iff_subset_coordinateWindowCarrier.mp
    hTransported

theorem convolutionSupportTransported_of_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSubset :
      S.fourierSupportCarrier f ⊆ S.coordinateWindowCarrier I) :
    S.convolutionSupportTransported f I :=
  convolutionSupportTransported_iff_subset_coordinateWindowCarrier.mpr
    hSubset

def pointInLambdaCutoff
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (x : S.SupportPoint) (lambda : ℝ) : Prop :=
  lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda

@[simp] theorem pointInLambdaCutoff_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ} :
    S.pointInLambdaCutoff x lambda ↔
      lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda :=
  Iff.rfl

def lambdaCarrier
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (lambda : ℝ) : Set S.SupportPoint :=
  {x | S.pointInLambdaCutoff x lambda}

@[simp] theorem mem_lambdaCarrier_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ} :
    x ∈ S.lambdaCarrier lambda ↔ S.pointInLambdaCutoff x lambda :=
  Iff.rfl

theorem pointInLambdaCutoff_of_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hLower : lambda⁻¹ ≤ S.supportScale x)
    (hUpper : S.supportScale x ≤ lambda) :
    S.pointInLambdaCutoff x lambda :=
  ⟨hLower, hUpper⟩

theorem pointInLambdaCutoff_of_mem_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hx : x ∈ S.lambdaCarrier lambda) :
    S.pointInLambdaCutoff x lambda :=
  hx

theorem mem_lambdaCarrier_of_pointInLambdaCutoff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hx : S.pointInLambdaCutoff x lambda) :
    x ∈ S.lambdaCarrier lambda :=
  hx

theorem lambdaCarrier_eq_setOf_pointInLambdaCutoff
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (lambda : ℝ) :
    S.lambdaCarrier lambda = {x | S.pointInLambdaCutoff x lambda} :=
  rfl

theorem lambdaCarrier_eq_setOf_bounds
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (lambda : ℝ) :
    S.lambdaCarrier lambda =
      {x | lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda} :=
  rfl

def windowContainedInLambda
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) (lambda : ℝ) : Prop :=
  S.windowCarrier I ⊆ S.lambdaCarrier lambda

@[simp] theorem windowContainedInLambda_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.windowContainedInLambda I lambda ↔
      S.windowCarrier I ⊆ S.lambdaCarrier lambda :=
  Iff.rfl

def lambdaCompatible
    {A : SourceTestAlgebra} (S : SourceSupportWindowData A)
    (I : S.Window) (lambda : ℝ) : Prop :=
  S.windowContainedInLambda I lambda

@[simp] theorem lambdaCompatible_iff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.lambdaCompatible I lambda ↔ S.windowContainedInLambda I lambda :=
  Iff.rfl

theorem supportTransported_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.supportInWindow f I → S.supportTransported f I := by
  intro hSupport
  exact hSupport

theorem supportTransported_of_subset
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSubset : S.supportCarrier f ⊆ S.windowCarrier I) :
    S.supportTransported f I :=
  hSubset

theorem supportInWindow_of_coordinate_bounds_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hLower : ∀ x : S.SupportPoint, x ∈ S.supportCarrier f →
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper : ∀ x : S.SupportPoint, x ∈ S.supportCarrier f →
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog : ∀ x : S.SupportPoint, x ∈ S.supportCarrier f →
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    S.supportInWindow f I :=
  carrier_subset_windowCarrier_of_coordinate_bounds_logScale_eq_zero
    hLower hUpper hLog

theorem supportTransported_of_coordinate_bounds_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hLower : ∀ x : S.SupportPoint, x ∈ S.supportCarrier f →
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper : ∀ x : S.SupportPoint, x ∈ S.supportCarrier f →
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog : ∀ x : S.SupportPoint, x ∈ S.supportCarrier f →
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    S.supportTransported f I :=
  supportTransported_of_supportInWindow
    (supportInWindow_of_coordinate_bounds_logScale_eq_zero
      hLower hUpper hLog)

theorem convolutionSupportTransported_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} :
    S.fourierSupportInWindow f I →
      S.convolutionSupportTransported f I := by
  intro hFourier
  exact hFourier

theorem convolutionSupportTransported_of_subset
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSubset : S.fourierSupportCarrier f ⊆ S.windowCarrier I) :
    S.convolutionSupportTransported f I :=
  hSubset

theorem fourierSupportInWindow_of_coordinate_bounds_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hLower : ∀ x : S.SupportPoint, x ∈ S.fourierSupportCarrier f →
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper : ∀ x : S.SupportPoint, x ∈ S.fourierSupportCarrier f →
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog : ∀ x : S.SupportPoint, x ∈ S.fourierSupportCarrier f →
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    S.fourierSupportInWindow f I :=
  carrier_subset_windowCarrier_of_coordinate_bounds_logScale_eq_zero
    hLower hUpper hLog

theorem convolutionSupportTransported_of_coordinate_bounds_logScale_eq_zero
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hLower : ∀ x : S.SupportPoint, x ∈ S.fourierSupportCarrier f →
      S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I)
    (hUpper : ∀ x : S.SupportPoint, x ∈ S.fourierSupportCarrier f →
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
        S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I)
    (hLog : ∀ x : S.SupportPoint, x ∈ S.fourierSupportCarrier f →
      S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0) :
    S.convolutionSupportTransported f I :=
  convolutionSupportTransported_of_fourierSupportInWindow
    (fourierSupportInWindow_of_coordinate_bounds_logScale_eq_zero
      hLower hUpper hLog)

theorem lambdaCompatible_of_windowContainedInLambda
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.windowContainedInLambda I lambda → S.lambdaCompatible I lambda := by
  intro hWindow
  exact hWindow

theorem lambdaCompatible_of_subset
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.windowCarrier I ⊆ S.lambdaCarrier lambda) :
    S.lambdaCompatible I lambda :=
  hSubset

theorem supportCarrier_mem_windowCarrier_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.windowCarrier I :=
  hSupport hx

theorem supportCarrier_mem_windowBaseCarrier_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.windowBaseCarrier I :=
  (supportCarrier_mem_windowCarrier_of_supportInWindow hSupport hx).1

theorem supportCarrier_supportScale_eq_one_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.supportScale x = 1 :=
  (supportCarrier_mem_windowCarrier_of_supportInWindow hSupport hx).2

theorem supportCarrier_mem_coordinateWindowCarrier_of_supportInWindow'
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.coordinateWindowCarrier I :=
  mem_windowCarrier_coordinateWindowCarrier
    (supportCarrier_mem_windowCarrier_of_supportInWindow hSupport hx)

theorem supportCarrier_logScale_eq_zero_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 :=
  logScale_eq_zero_of_supportScale_eq_one
    (supportCarrier_supportScale_eq_one_of_supportInWindow hSupport hx)

theorem supportCarrier_coordinate_lower_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I :=
  mem_windowCarrier_coordinate_lower
    (supportCarrier_mem_windowCarrier_of_supportInWindow hSupport hx)

theorem supportCarrier_coordinate_upper_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  mem_windowCarrier_coordinate_upper
    (supportCarrier_mem_windowCarrier_of_supportInWindow hSupport hx)

theorem fourierSupportCarrier_mem_windowCarrier_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.windowCarrier I :=
  hFourier hx

theorem fourierSupportCarrier_mem_windowBaseCarrier_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.windowBaseCarrier I :=
  (fourierSupportCarrier_mem_windowCarrier_of_fourierSupportInWindow
    hFourier hx).1

theorem fourierSupportCarrier_supportScale_eq_one_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    S.supportScale x = 1 :=
  (fourierSupportCarrier_mem_windowCarrier_of_fourierSupportInWindow
    hFourier hx).2

theorem fourierSupportCarrier_mem_coordinateWindowCarrier_of_fourierSupportInWindow'
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.coordinateWindowCarrier I :=
  mem_windowCarrier_coordinateWindowCarrier
    (fourierSupportCarrier_mem_windowCarrier_of_fourierSupportInWindow
      hFourier hx)

theorem fourierSupportCarrier_logScale_eq_zero_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 :=
  logScale_eq_zero_of_supportScale_eq_one
    (fourierSupportCarrier_supportScale_eq_one_of_fourierSupportInWindow
      hFourier hx)

theorem fourierSupportCarrier_coordinate_lower_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I :=
  mem_windowCarrier_coordinate_lower
    (fourierSupportCarrier_mem_windowCarrier_of_fourierSupportInWindow
      hFourier hx)

theorem fourierSupportCarrier_coordinate_upper_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  mem_windowCarrier_coordinate_upper
    (fourierSupportCarrier_mem_windowCarrier_of_fourierSupportInWindow
      hFourier hx)

theorem pointInLambdaCutoff_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hx : S.pointInLambdaCutoff x lambda) :
    lambda⁻¹ ≤ S.supportScale x :=
  hx.1

theorem pointInLambdaCutoff_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hx : S.pointInLambdaCutoff x lambda) :
    S.supportScale x ≤ lambda :=
  hx.2

theorem mem_lambdaCarrier_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hx : x ∈ S.lambdaCarrier lambda) :
    lambda⁻¹ ≤ S.supportScale x :=
  hx.1

theorem mem_lambdaCarrier_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hx : x ∈ S.lambdaCarrier lambda) :
    S.supportScale x ≤ lambda :=
  hx.2

theorem mem_lambdaCarrier_of_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hLower : lambda⁻¹ ≤ S.supportScale x)
    (hUpper : S.supportScale x ≤ lambda) :
    x ∈ S.lambdaCarrier lambda :=
  ⟨hLower, hUpper⟩

theorem mem_lambdaCarrier_iff_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ} :
    x ∈ S.lambdaCarrier lambda ↔
      lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda :=
  Iff.rfl

theorem pointInLambdaCutoff_of_supportScale_eq_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hScale : S.supportScale x = 1) :
    S.pointInLambdaCutoff x lambda := by
  rw [pointInLambdaCutoff_iff]
  rw [hScale]
  exact ⟨inv_le_one_of_one_le₀ hlambda.le, hlambda.le⟩

theorem mem_lambdaCarrier_of_supportScale_eq_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {x : S.SupportPoint} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hScale : S.supportScale x = 1) :
    x ∈ S.lambdaCarrier lambda :=
  mem_lambdaCarrier_of_bounds
    (by rw [hScale]; exact inv_le_one_of_one_le₀ hlambda.le)
    (by rw [hScale]; exact hlambda.le)

theorem supportCarrier_pointInLambdaCutoff_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.pointInLambdaCutoff x lambda :=
  pointInLambdaCutoff_of_supportScale_eq_one hlambda
    (supportCarrier_supportScale_eq_one_of_supportInWindow hSupport hx)

theorem supportCarrier_mem_lambdaCarrier_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.lambdaCarrier lambda :=
  supportCarrier_pointInLambdaCutoff_of_supportInWindow
    hlambda hSupport hx

theorem supportCarrier_lambda_lower_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (supportCarrier_mem_lambdaCarrier_of_supportInWindow
      hlambda hSupport hx)

theorem supportCarrier_lambda_upper_of_supportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hSupport : S.supportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (supportCarrier_mem_lambdaCarrier_of_supportInWindow
      hlambda hSupport hx)

theorem fourierSupportCarrier_pointInLambdaCutoff_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    S.pointInLambdaCutoff x lambda :=
  pointInLambdaCutoff_of_supportScale_eq_one hlambda
    (fourierSupportCarrier_supportScale_eq_one_of_fourierSupportInWindow
      hFourier hx)

theorem fourierSupportCarrier_mem_lambdaCarrier_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.lambdaCarrier lambda :=
  fourierSupportCarrier_pointInLambdaCutoff_of_fourierSupportInWindow
    hlambda hFourier hx

theorem fourierSupportCarrier_lambda_lower_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (fourierSupportCarrier_mem_lambdaCarrier_of_fourierSupportInWindow
      hlambda hFourier hx)

theorem fourierSupportCarrier_lambda_upper_of_fourierSupportInWindow
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hFourier : S.fourierSupportInWindow f I) {x : S.SupportPoint}
    (hx : x ∈ S.fourierSupportCarrier f) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (fourierSupportCarrier_mem_lambdaCarrier_of_fourierSupportInWindow
      hlambda hFourier hx)

theorem supportCarrier_mem_windowCarrier_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.windowCarrier I :=
  supportCarrier_mem_windowCarrier_of_supportInWindow
    (supportInWindow_of_supportTransported hTransported) hx

theorem supportCarrier_mem_windowBaseCarrier_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.windowBaseCarrier I :=
  mem_windowCarrier_windowBase
    (supportCarrier_mem_windowCarrier_of_supportTransported hTransported hx)

theorem supportCarrier_mem_coordinateWindowCarrier_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.coordinateWindowCarrier I :=
  supportTransported_subset_coordinateWindowCarrier hTransported hx

theorem supportCarrier_supportScale_eq_one_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.supportScale x = 1 :=
  mem_windowCarrier_supportScale_eq_one
    (supportCarrier_mem_windowCarrier_of_supportTransported hTransported hx)

theorem supportCarrier_logScale_eq_zero_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 :=
  mem_coordinateWindowCarrier_logScale_eq_zero
    (supportCarrier_mem_coordinateWindowCarrier_of_supportTransported
      hTransported hx)

theorem supportCarrier_coordinate_lower_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I :=
  mem_coordinateWindowCarrier_coordinate_lower
    (supportCarrier_mem_coordinateWindowCarrier_of_supportTransported
      hTransported hx)

theorem supportCarrier_coordinate_upper_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  mem_coordinateWindowCarrier_coordinate_upper
    (supportCarrier_mem_coordinateWindowCarrier_of_supportTransported
      hTransported hx)

theorem supportCarrier_pointInLambdaCutoff_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    S.pointInLambdaCutoff x lambda :=
  pointInLambdaCutoff_of_supportScale_eq_one hlambda
    (supportCarrier_supportScale_eq_one_of_supportTransported
      hTransported hx)

theorem supportCarrier_mem_lambdaCarrier_of_supportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hTransported : S.supportTransported f I) {x : S.SupportPoint}
    (hx : x ∈ S.supportCarrier f) :
    x ∈ S.lambdaCarrier lambda :=
  supportCarrier_pointInLambdaCutoff_of_supportTransported
    hlambda hTransported hx

theorem fourierSupportCarrier_mem_windowCarrier_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.windowCarrier I :=
  fourierSupportCarrier_mem_windowCarrier_of_fourierSupportInWindow
    (fourierSupportInWindow_of_convolutionSupportTransported hTransported)
    hx

theorem fourierSupportCarrier_mem_windowBaseCarrier_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.windowBaseCarrier I :=
  mem_windowCarrier_windowBase
    (fourierSupportCarrier_mem_windowCarrier_of_convolutionSupportTransported
      hTransported hx)

theorem fourierSupportCarrier_mem_coordinateWindowCarrier_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.coordinateWindowCarrier I :=
  convolutionSupportTransported_subset_coordinateWindowCarrier
    hTransported hx

theorem fourierSupportCarrier_supportScale_eq_one_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    S.supportScale x = 1 :=
  mem_windowCarrier_supportScale_eq_one
    (fourierSupportCarrier_mem_windowCarrier_of_convolutionSupportTransported
      hTransported hx)

theorem fourierSupportCarrier_logScale_eq_zero_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    S.sourceWindowCoordinate.supportLogScaleCoordinate.logScale x = 0 :=
  mem_coordinateWindowCarrier_logScale_eq_zero
    (fourierSupportCarrier_mem_coordinateWindowCarrier_of_convolutionSupportTransported
      hTransported hx)

theorem fourierSupportCarrier_coordinate_lower_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I :=
  mem_coordinateWindowCarrier_coordinate_lower
    (fourierSupportCarrier_mem_coordinateWindowCarrier_of_convolutionSupportTransported
      hTransported hx)

theorem fourierSupportCarrier_coordinate_upper_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window}
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    S.sourceWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I ≤
      S.sourceWindowCoordinate.windowMembershipCoordinate.upperEndpoint I :=
  mem_coordinateWindowCarrier_coordinate_upper
    (fourierSupportCarrier_mem_coordinateWindowCarrier_of_convolutionSupportTransported
      hTransported hx)

theorem fourierSupportCarrier_pointInLambdaCutoff_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    S.pointInLambdaCutoff x lambda :=
  pointInLambdaCutoff_of_supportScale_eq_one hlambda
    (fourierSupportCarrier_supportScale_eq_one_of_convolutionSupportTransported
      hTransported hx)

theorem fourierSupportCarrier_mem_lambdaCarrier_of_convolutionSupportTransported
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hTransported : S.convolutionSupportTransported f I)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.lambdaCarrier lambda :=
  fourierSupportCarrier_pointInLambdaCutoff_of_convolutionSupportTransported
    hlambda hTransported hx

theorem carrier_subset_lambdaCarrier_of_supportScale_eq_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {carrier : Set S.SupportPoint} {lambda : ℝ}
    (hlambda : 1 < lambda)
    (hScale : ∀ x : S.SupportPoint, x ∈ carrier → S.supportScale x = 1) :
    carrier ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact mem_lambdaCarrier_of_supportScale_eq_one hlambda (hScale x hx)

theorem carrier_subset_lambdaCarrier_of_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {carrier : Set S.SupportPoint} {lambda : ℝ}
    (hLower : ∀ x : S.SupportPoint, x ∈ carrier →
      lambda⁻¹ ≤ S.supportScale x)
    (hUpper : ∀ x : S.SupportPoint, x ∈ carrier →
      S.supportScale x ≤ lambda) :
    carrier ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact mem_lambdaCarrier_of_bounds (hLower x hx) (hUpper x hx)

theorem carrier_subset_lambdaCarrier_iff_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {carrier : Set S.SupportPoint} {lambda : ℝ} :
    carrier ⊆ S.lambdaCarrier lambda ↔
      ∀ x : S.SupportPoint, x ∈ carrier →
        lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda := by
  constructor
  · intro hSubset x hx
    exact (mem_lambdaCarrier_iff_bounds).mp (hSubset hx)
  · intro hBounds
    exact carrier_subset_lambdaCarrier_of_bounds
      (fun x hx => (hBounds x hx).1)
      (fun x hx => (hBounds x hx).2)

theorem carrier_subset_lambdaCarrier_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {carrier : Set S.SupportPoint} {lambda : ℝ}
    (hSubset : carrier ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ carrier) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower (hSubset hx)

theorem carrier_subset_lambdaCarrier_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {carrier : Set S.SupportPoint} {lambda : ℝ}
    (hSubset : carrier ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ carrier) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper (hSubset hx)

theorem carrier_subset_lambdaCarrier_pointInCutoff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {carrier : Set S.SupportPoint} {lambda : ℝ}
    (hSubset : carrier ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ carrier) :
    S.pointInLambdaCutoff x lambda :=
  pointInLambdaCutoff_of_mem_lambdaCarrier (hSubset hx)

theorem mem_lambdaCarrier_of_windowContainedInLambda
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hWindow : S.windowContainedInLambda I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    x ∈ S.lambdaCarrier lambda :=
  hWindow hx

theorem windowContainedInLambda_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hWindow : S.windowContainedInLambda I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (mem_lambdaCarrier_of_windowContainedInLambda hWindow hx)

theorem windowContainedInLambda_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hWindow : S.windowContainedInLambda I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (mem_lambdaCarrier_of_windowContainedInLambda hWindow hx)

theorem windowContainedInLambda_of_subset
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.windowCarrier I ⊆ S.lambdaCarrier lambda) :
    S.windowContainedInLambda I lambda :=
  hSubset

theorem windowContainedInLambda_of_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLower : ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
      lambda⁻¹ ≤ S.supportScale x)
    (hUpper : ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
      S.supportScale x ≤ lambda) :
    S.windowContainedInLambda I lambda :=
  carrier_subset_lambdaCarrier_of_bounds hLower hUpper

theorem windowContainedInLambda_iff_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.windowContainedInLambda I lambda ↔
      ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
        lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda :=
  carrier_subset_lambdaCarrier_iff_bounds

theorem windowCarrier_subset_lambdaCarrier_of_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLower : ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
      lambda⁻¹ ≤ S.supportScale x)
    (hUpper : ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
      S.supportScale x ≤ lambda) :
    S.windowCarrier I ⊆ S.lambdaCarrier lambda :=
  carrier_subset_lambdaCarrier_of_bounds hLower hUpper

theorem windowCarrier_subset_lambdaCarrier_iff_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.windowCarrier I ⊆ S.lambdaCarrier lambda ↔
      ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
        lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda :=
  carrier_subset_lambdaCarrier_iff_bounds

theorem windowCarrier_subset_lambdaCarrier_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.windowCarrier I ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x :=
  carrier_subset_lambdaCarrier_lower hSubset hx

theorem windowCarrier_subset_lambdaCarrier_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.windowCarrier I ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    S.supportScale x ≤ lambda :=
  carrier_subset_lambdaCarrier_upper hSubset hx

theorem windowCarrier_subset_lambdaCarrier_pointInCutoff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.windowCarrier I ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    S.pointInLambdaCutoff x lambda :=
  carrier_subset_lambdaCarrier_pointInCutoff hSubset hx

theorem windowContainedInLambda_of_lambdaCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLambda : S.lambdaCompatible I lambda) :
    S.windowContainedInLambda I lambda :=
  lambdaCompatible_iff.mp hLambda

theorem lambdaCompatible_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLambda : S.lambdaCompatible I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x :=
  windowContainedInLambda_lower
    (windowContainedInLambda_of_lambdaCompatible hLambda) hx

theorem lambdaCompatible_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLambda : S.lambdaCompatible I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    S.supportScale x ≤ lambda :=
  windowContainedInLambda_upper
    (windowContainedInLambda_of_lambdaCompatible hLambda) hx

theorem mem_lambdaCarrier_of_lambdaCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLambda : S.lambdaCompatible I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.windowCarrier I) :
    x ∈ S.lambdaCarrier lambda :=
  mem_lambdaCarrier_of_windowContainedInLambda
    (windowContainedInLambda_of_lambdaCompatible hLambda) hx

theorem lambdaCompatible_iff_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.lambdaCompatible I lambda ↔
      ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
        lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda := by
  rw [lambdaCompatible_iff, windowContainedInLambda_iff_bounds]

theorem lambdaCompatible_of_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLower : ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
      lambda⁻¹ ≤ S.supportScale x)
    (hUpper : ∀ x : S.SupportPoint, x ∈ S.windowCarrier I →
      S.supportScale x ≤ lambda) :
    S.lambdaCompatible I lambda :=
  lambdaCompatible_iff_bounds.mpr
    (fun x hx => ⟨hLower x hx, hUpper x hx⟩)

theorem supportInWindow_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hSupport : S.supportInWindow f I)
    (hlambda : 1 < lambda) :
    S.supportCarrier f ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact mem_lambdaCarrier_of_supportScale_eq_one hlambda (hSupport hx).2

theorem supportInWindow_mem_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hSupport : S.supportInWindow f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.supportCarrier f) :
    x ∈ S.lambdaCarrier lambda :=
  supportInWindow_subset_lambdaCarrier hSupport hlambda hx

theorem supportInWindow_lambda_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hSupport : S.supportInWindow f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.supportCarrier f) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (supportInWindow_mem_lambdaCarrier hSupport hlambda hx)

theorem supportInWindow_lambda_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hSupport : S.supportInWindow f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.supportCarrier f) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (supportInWindow_mem_lambdaCarrier hSupport hlambda hx)

theorem fourierSupportInWindow_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hFourier : S.fourierSupportInWindow f I)
    (hlambda : 1 < lambda) :
    S.fourierSupportCarrier f ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact mem_lambdaCarrier_of_supportScale_eq_one hlambda (hFourier hx).2

theorem fourierSupportInWindow_mem_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hFourier : S.fourierSupportInWindow f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.lambdaCarrier lambda :=
  fourierSupportInWindow_subset_lambdaCarrier hFourier hlambda hx

theorem fourierSupportInWindow_lambda_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hFourier : S.fourierSupportInWindow f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (fourierSupportInWindow_mem_lambdaCarrier hFourier hlambda hx)

theorem fourierSupportInWindow_lambda_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hFourier : S.fourierSupportInWindow f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (fourierSupportInWindow_mem_lambdaCarrier hFourier hlambda hx)

theorem supportTransported_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hTransported : S.supportTransported f I)
    (hlambda : 1 < lambda) :
    S.supportCarrier f ⊆ S.lambdaCarrier lambda :=
  supportInWindow_subset_lambdaCarrier
    (supportInWindow_of_supportTransported hTransported) hlambda

theorem supportTransported_mem_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hTransported : S.supportTransported f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.supportCarrier f) :
    x ∈ S.lambdaCarrier lambda :=
  supportTransported_subset_lambdaCarrier hTransported hlambda hx

theorem supportTransported_lambda_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hTransported : S.supportTransported f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.supportCarrier f) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (supportTransported_mem_lambdaCarrier hTransported hlambda hx)

theorem supportTransported_lambda_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hTransported : S.supportTransported f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.supportCarrier f) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (supportTransported_mem_lambdaCarrier hTransported hlambda hx)

theorem convolutionSupportTransported_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hTransported : S.convolutionSupportTransported f I)
    (hlambda : 1 < lambda) :
    S.fourierSupportCarrier f ⊆ S.lambdaCarrier lambda :=
  fourierSupportInWindow_subset_lambdaCarrier
    (fourierSupportInWindow_of_convolutionSupportTransported hTransported)
    hlambda

theorem convolutionSupportTransported_mem_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hTransported : S.convolutionSupportTransported f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    x ∈ S.lambdaCarrier lambda :=
  convolutionSupportTransported_subset_lambdaCarrier hTransported hlambda hx

theorem convolutionSupportTransported_lambda_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hTransported : S.convolutionSupportTransported f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (convolutionSupportTransported_mem_lambdaCarrier hTransported hlambda hx)

theorem convolutionSupportTransported_lambda_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {f : A.Test} {I : S.Window} {lambda : ℝ}
    (hTransported : S.convolutionSupportTransported f I)
    (hlambda : 1 < lambda)
    {x : S.SupportPoint} (hx : x ∈ S.fourierSupportCarrier f) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (convolutionSupportTransported_mem_lambdaCarrier hTransported hlambda hx)

theorem windowPoint_supportScale_eq_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window}
    {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.supportScale x = 1 := by
  exact hx.2

theorem windowPoint_supportScale_lowerBound
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x := by
  rw [windowPoint_supportScale_eq_one hx]
  exact inv_le_one_of_one_le₀ hlambda.le

theorem windowPoint_supportScale_upperBound
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.supportScale x ≤ lambda := by
  rw [windowPoint_supportScale_eq_one hx]
  exact hlambda.le

theorem windowPoint_mem_lambdaCutoff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    S.pointInLambdaCutoff x lambda := by
  exact
    ⟨windowPoint_supportScale_lowerBound hlambda hx,
      windowPoint_supportScale_upperBound hlambda hx⟩

theorem windowPoint_mem_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.windowCarrier I) :
    x ∈ S.lambdaCarrier lambda :=
  windowPoint_mem_lambdaCutoff hlambda hx

theorem coordinateWindowPoint_supportScale_eq_one
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    S.supportScale x = 1 :=
  windowPoint_supportScale_eq_one
    (mem_coordinateWindowCarrier_windowCarrier hx)

theorem coordinateWindowPoint_supportScale_lowerBound
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x :=
  windowPoint_supportScale_lowerBound hlambda
    (mem_coordinateWindowCarrier_windowCarrier hx)

theorem coordinateWindowPoint_supportScale_upperBound
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    S.supportScale x ≤ lambda :=
  windowPoint_supportScale_upperBound hlambda
    (mem_coordinateWindowCarrier_windowCarrier hx)

theorem coordinateWindowPoint_mem_lambdaCutoff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    S.pointInLambdaCutoff x lambda :=
  windowPoint_mem_lambdaCutoff hlambda
    (mem_coordinateWindowCarrier_windowCarrier hx)

theorem windowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.windowCarrier I ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact windowPoint_mem_lambdaCutoff hlambda hx

theorem coordinateWindowPoint_mem_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) {x : S.SupportPoint}
    (hx : x ∈ S.coordinateWindowCarrier I) :
    x ∈ S.lambdaCarrier lambda :=
  coordinateWindowPoint_mem_lambdaCutoff hlambda hx

theorem coordinateWindowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact coordinateWindowPoint_mem_lambdaCarrier hlambda hx

theorem carrier_subset_lambdaCarrier_of_subset_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} {carrier : Set S.SupportPoint}
    (hlambda : 1 < lambda)
    (hSubset : carrier ⊆ S.windowCarrier I) :
    carrier ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact windowPoint_mem_lambdaCarrier hlambda (hSubset hx)

theorem carrier_subset_lambdaCarrier_of_subset_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} {carrier : Set S.SupportPoint}
    (hlambda : 1 < lambda)
    (hSubset : carrier ⊆ S.coordinateWindowCarrier I) :
    carrier ⊆ S.lambdaCarrier lambda := by
  intro x hx
  exact coordinateWindowPoint_mem_lambdaCarrier hlambda (hSubset hx)

theorem windowCarrier_inter_lambdaCarrier_eq_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.windowCarrier I ∩ S.lambdaCarrier lambda = S.windowCarrier I := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx
    exact ⟨hx, windowPoint_mem_lambdaCarrier hlambda hx⟩

theorem lambdaCarrier_inter_windowCarrier_eq_windowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.lambdaCarrier lambda ∩ S.windowCarrier I = S.windowCarrier I := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hx
    exact ⟨windowPoint_mem_lambdaCarrier hlambda hx, hx⟩

theorem coordinateWindowCarrier_inter_lambdaCarrier_eq_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.coordinateWindowCarrier I ∩ S.lambdaCarrier lambda =
      S.coordinateWindowCarrier I := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.1
  · intro x hx
    exact ⟨hx, coordinateWindowPoint_mem_lambdaCarrier hlambda hx⟩

theorem lambdaCarrier_inter_coordinateWindowCarrier_eq_coordinateWindowCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.lambdaCarrier lambda ∩ S.coordinateWindowCarrier I =
      S.coordinateWindowCarrier I := by
  apply Set.Subset.antisymm
  · intro x hx
    exact hx.2
  · intro x hx
    exact ⟨coordinateWindowPoint_mem_lambdaCarrier hlambda hx, hx⟩

theorem windowCarrier_union_lambdaCarrier_eq_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.windowCarrier I ∪ S.lambdaCarrier lambda = S.lambdaCarrier lambda := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | hx
    · exact windowPoint_mem_lambdaCarrier hlambda hx
    · exact hx
  · intro x hx
    exact Or.inr hx

theorem lambdaCarrier_union_windowCarrier_eq_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.lambdaCarrier lambda ∪ S.windowCarrier I = S.lambdaCarrier lambda := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | hx
    · exact hx
    · exact windowPoint_mem_lambdaCarrier hlambda hx
  · intro x hx
    exact Or.inl hx

theorem coordinateWindowCarrier_union_lambdaCarrier_eq_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.coordinateWindowCarrier I ∪ S.lambdaCarrier lambda =
      S.lambdaCarrier lambda := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | hx
    · exact coordinateWindowPoint_mem_lambdaCarrier hlambda hx
    · exact hx
  · intro x hx
    exact Or.inr hx

theorem lambdaCarrier_union_coordinateWindowCarrier_eq_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.lambdaCarrier lambda ∪ S.coordinateWindowCarrier I =
      S.lambdaCarrier lambda := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hx | hx
    · exact hx
    · exact coordinateWindowPoint_mem_lambdaCarrier hlambda hx
  · intro x hx
    exact Or.inl hx

theorem coordinateWindowCarrier_subset_lambdaCarrier_iff_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda ↔
      ∀ x : S.SupportPoint, x ∈ S.coordinateWindowCarrier I →
        lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda :=
  carrier_subset_lambdaCarrier_iff_bounds

theorem coordinateWindowCarrier_subset_lambdaCarrier_of_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLower : ∀ x : S.SupportPoint, x ∈ S.coordinateWindowCarrier I →
      lambda⁻¹ ≤ S.supportScale x)
    (hUpper : ∀ x : S.SupportPoint, x ∈ S.coordinateWindowCarrier I →
      S.supportScale x ≤ lambda) :
    S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda :=
  carrier_subset_lambdaCarrier_of_bounds hLower hUpper

theorem coordinateWindowCarrier_subset_lambdaCarrier_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x :=
  carrier_subset_lambdaCarrier_lower hSubset hx

theorem coordinateWindowCarrier_subset_lambdaCarrier_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    S.supportScale x ≤ lambda :=
  carrier_subset_lambdaCarrier_upper hSubset hx

theorem coordinateWindowCarrier_subset_lambdaCarrier_pointInCutoff
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    S.pointInLambdaCutoff x lambda :=
  carrier_subset_lambdaCarrier_pointInCutoff hSubset hx

theorem windowCarrier_subset_lambdaCarrier_iff_coordinateWindowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.windowCarrier I ⊆ S.lambdaCarrier lambda ↔
      S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda := by
  constructor
  · intro hWindow x hx
    exact hWindow (mem_coordinateWindowCarrier_windowCarrier hx)
  · intro hCoordinate x hx
    exact hCoordinate (mem_windowCarrier_coordinateWindowCarrier hx)

theorem coordinateWindowCarrier_subset_lambdaCarrier_of_windowCarrier_subset
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hWindow : S.windowCarrier I ⊆ S.lambdaCarrier lambda) :
    S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda :=
  windowCarrier_subset_lambdaCarrier_iff_coordinateWindowCarrier_subset_lambdaCarrier.mp
    hWindow

theorem windowCarrier_subset_lambdaCarrier_of_coordinateWindowCarrier_subset
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hCoordinate : S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda) :
    S.windowCarrier I ⊆ S.lambdaCarrier lambda :=
  windowCarrier_subset_lambdaCarrier_iff_coordinateWindowCarrier_subset_lambdaCarrier.mpr
    hCoordinate

theorem windowContainedInLambda_iff_coordinateWindowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.windowContainedInLambda I lambda ↔
      S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda := by
  constructor
  · intro hWindow x hx
    exact hWindow (mem_coordinateWindowCarrier_windowCarrier hx)
  · intro hCoordinate x hx
    exact hCoordinate (mem_windowCarrier_coordinateWindowCarrier hx)

theorem coordinateWindowCarrier_subset_lambdaCarrier_of_windowContainedInLambda
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hWindow : S.windowContainedInLambda I lambda) :
    S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda :=
  windowContainedInLambda_iff_coordinateWindowCarrier_subset_lambdaCarrier.mp
    hWindow

theorem windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda) :
    S.windowContainedInLambda I lambda :=
  windowContainedInLambda_iff_coordinateWindowCarrier_subset_lambdaCarrier.mpr
    hSubset

theorem coordinateWindowPoint_mem_lambdaCarrier_of_windowContainedInLambda
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hWindow : S.windowContainedInLambda I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    x ∈ S.lambdaCarrier lambda :=
  coordinateWindowCarrier_subset_lambdaCarrier_of_windowContainedInLambda
    hWindow hx

theorem coordinateWindowContainedInLambda_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hWindow : S.windowContainedInLambda I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (coordinateWindowPoint_mem_lambdaCarrier_of_windowContainedInLambda
      hWindow hx)

theorem coordinateWindowContainedInLambda_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hWindow : S.windowContainedInLambda I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (coordinateWindowPoint_mem_lambdaCarrier_of_windowContainedInLambda
      hWindow hx)

theorem lambdaCompatible_iff_coordinateWindowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.lambdaCompatible I lambda ↔
      S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda := by
  rw [lambdaCompatible_iff,
    windowContainedInLambda_iff_coordinateWindowCarrier_subset_lambdaCarrier]

theorem windowContainedInLambda_iff_coordinateWindowCarrier_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.windowContainedInLambda I lambda ↔
      ∀ x : S.SupportPoint, x ∈ S.coordinateWindowCarrier I →
        lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda := by
  rw [windowContainedInLambda_iff_coordinateWindowCarrier_subset_lambdaCarrier,
    coordinateWindowCarrier_subset_lambdaCarrier_iff_bounds]

theorem lambdaCompatible_iff_coordinateWindowCarrier_bounds
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ} :
    S.lambdaCompatible I lambda ↔
      ∀ x : S.SupportPoint, x ∈ S.coordinateWindowCarrier I →
        lambda⁻¹ ≤ S.supportScale x ∧ S.supportScale x ≤ lambda := by
  rw [lambdaCompatible_iff_coordinateWindowCarrier_subset_lambdaCarrier,
    coordinateWindowCarrier_subset_lambdaCarrier_iff_bounds]

theorem coordinateWindowCarrier_subset_lambdaCarrier_of_lambdaCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLambda : S.lambdaCompatible I lambda) :
    S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda :=
  lambdaCompatible_iff_coordinateWindowCarrier_subset_lambdaCarrier.mp
    hLambda

theorem lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hSubset : S.coordinateWindowCarrier I ⊆ S.lambdaCarrier lambda) :
    S.lambdaCompatible I lambda :=
  lambdaCompatible_iff_coordinateWindowCarrier_subset_lambdaCarrier.mpr
    hSubset

theorem coordinateWindowPoint_mem_lambdaCarrier_of_lambdaCompatible
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLambda : S.lambdaCompatible I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    x ∈ S.lambdaCarrier lambda :=
  coordinateWindowCarrier_subset_lambdaCarrier_of_lambdaCompatible
    hLambda hx

theorem lambdaCompatible_coordinateWindow_lower
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLambda : S.lambdaCompatible I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    lambda⁻¹ ≤ S.supportScale x :=
  mem_lambdaCarrier_lower
    (coordinateWindowPoint_mem_lambdaCarrier_of_lambdaCompatible
      hLambda hx)

theorem lambdaCompatible_coordinateWindow_upper
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hLambda : S.lambdaCompatible I lambda)
    {x : S.SupportPoint} (hx : x ∈ S.coordinateWindowCarrier I) :
    S.supportScale x ≤ lambda :=
  mem_lambdaCarrier_upper
    (coordinateWindowPoint_mem_lambdaCarrier_of_lambdaCompatible
      hLambda hx)

theorem windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.windowContainedInLambda I lambda :=
  windowContainedInLambda_of_coordinateWindowCarrier_subset_lambdaCarrier
    (coordinateWindowCarrier_subset_lambdaCarrier hlambda)

theorem lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier_of_one_lt
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.lambdaCompatible I lambda :=
  lambdaCompatible_of_coordinateWindowCarrier_subset_lambdaCarrier
    (coordinateWindowCarrier_subset_lambdaCarrier hlambda)

theorem windowContainedInLambda_of_one_lt
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.windowContainedInLambda I lambda :=
  windowCarrier_subset_lambdaCarrier hlambda

theorem lambdaCompatible_of_one_lt
    {A : SourceTestAlgebra} {S : SourceSupportWindowData A}
    {I : S.Window} {lambda : ℝ}
    (hlambda : 1 < lambda) :
    S.lambdaCompatible I lambda :=
  lambdaCompatible_of_windowContainedInLambda
    (windowContainedInLambda_of_one_lt hlambda)

end SourceSupportWindowData

/-
Concrete base-layer source model for the current project boundary.

The public `TestFunction` boundary is Mathlib's Schwartz space on `ℝ` with
complex values.  This model gives the base source fields an honest
Lean/Mathlib-bottom realization: the test involution is the Mathlib Fourier
transform, support points are real coordinate pairs, and support values are the
norm of the Schwartz function on the first coordinate inside the closed
window/log-scale slice.
-/
namespace SourceConcreteBaseLayer

abbrev ConcreteTest : Type := TestFunction

abbrev ConcretePlace : Type := PUnit

abbrev ConcreteWindow : Type := ℝ × ℝ

abbrev ConcreteSupportPoint : Type := ℝ × ℝ

def defaultWindow : ConcreteWindow :=
  (0, 0)

noncomputable def defaultSourceTest : ConcreteTest :=
  0

def concreteLegacyTestEquiv : LegacyTestEquiv ConcreteTest where
  encode := id
  decode := id
  encode_decode := by
    intro F
    rfl
  decode_encode := by
    intro f
    rfl

noncomputable def concreteTestAlgebra : SourceTestAlgebra where
  Test := ConcreteTest
  legacy := concreteLegacyTestEquiv
  convolutionStar := fun f g => f + g
  involution := fun f => 𝓕 f
  convolutionSquare := fun g => g + g
  convolutionSquare_eq := by
    intro g
    rfl

@[simp] theorem concreteTestAlgebra_involution
    (f : ConcreteTest) :
    concreteTestAlgebra.involution f = 𝓕 f :=
  rfl

@[simp] theorem concreteTestAlgebra_convolutionStar
    (f g : ConcreteTest) :
    concreteTestAlgebra.convolutionStar f g = f + g :=
  rfl

@[simp] theorem concreteTestAlgebra_convolutionSquare
    (g : ConcreteTest) :
    concreteTestAlgebra.convolutionSquare g = g + g :=
  rfl

def concreteWindowMembershipCoordinate :
    SourceWindowMembershipCoordinate ConcreteSupportPoint ConcreteWindow where
  pointCoordinate := fun x _I => x.1
  lowerEndpoint := fun I => I.1
  upperEndpoint := fun I => I.2

def concreteLogScaleCoordinate :
    SourceSupportLogScaleCoordinate ConcreteSupportPoint where
  logScale := fun x => x.2

def concreteWindowCoordinate :
    SourceWindowCoordinate ConcreteSupportPoint ConcreteWindow where
  windowMembershipCoordinate := concreteWindowMembershipCoordinate
  supportLogScaleCoordinate := concreteLogScaleCoordinate

@[simp] theorem concreteWindowCoordinate_pointCoordinate
    (x : ConcreteSupportPoint) (I : ConcreteWindow) :
    concreteWindowCoordinate.windowMembershipCoordinate.pointCoordinate x I =
      x.1 :=
  rfl

@[simp] theorem concreteWindowCoordinate_lowerEndpoint
    (I : ConcreteWindow) :
    concreteWindowCoordinate.windowMembershipCoordinate.lowerEndpoint I =
      I.1 :=
  rfl

@[simp] theorem concreteWindowCoordinate_upperEndpoint
    (I : ConcreteWindow) :
    concreteWindowCoordinate.windowMembershipCoordinate.upperEndpoint I =
      I.2 :=
  rfl

@[simp] theorem concreteWindowCoordinate_logScale
    (x : ConcreteSupportPoint) :
    concreteWindowCoordinate.supportLogScaleCoordinate.logScale x =
      x.2 :=
  rfl

def pointInConcreteWindow
    (I : ConcreteWindow) (x : ConcreteSupportPoint) : Prop :=
  I.1 ≤ x.1 ∧ x.1 ≤ I.2 ∧ x.2 = 0

noncomputable def concreteSupportValue
    (I : ConcreteWindow) (f : ConcreteTest)
    (x : ConcreteSupportPoint) : ℝ := by
  classical
  exact if pointInConcreteWindow I x then ‖f x.1‖ else 0

noncomputable def concreteRawSupportKernel
    (f : ConcreteTest) (z : ℝ × ℝ) : ℝ :=
  ‖f z.1‖

theorem concreteRawSupportKernel_eq_norm
    (f : ConcreteTest) (z : ℝ × ℝ) :
    concreteRawSupportKernel f z = ‖f z.1‖ := by
  rfl

theorem concreteRawSupportKernel_ne_zero_iff
    (f : ConcreteTest) (z : ℝ × ℝ) :
    concreteRawSupportKernel f z ≠ 0 ↔ f z.1 ≠ 0 := by
  simp [concreteRawSupportKernel]

theorem concreteSupportValue_eq_norm
    {I : ConcreteWindow} {f : ConcreteTest} {x : ConcreteSupportPoint}
    (hx : pointInConcreteWindow I x) :
    concreteSupportValue I f x = ‖f x.1‖ := by
  classical
  simp [concreteSupportValue, hx]

theorem concreteSupportValue_eq_zero
    {I : ConcreteWindow} {f : ConcreteTest} {x : ConcreteSupportPoint}
    (h : ¬pointInConcreteWindow I x) :
    concreteSupportValue I f x = 0 := by
  classical
  simp [concreteSupportValue, h]

theorem concreteSupportValue_ne_zero_iff
    {I : ConcreteWindow} {f : ConcreteTest} {x : ConcreteSupportPoint} :
    concreteSupportValue I f x ≠ 0 ↔
      pointInConcreteWindow I x ∧ f x.1 ≠ 0 := by
  classical
  by_cases hx : pointInConcreteWindow I x
  · simp [concreteSupportValue, hx]
  · simp [concreteSupportValue, hx]

theorem pointInConcreteWindow_of_concreteSupportValue_ne_zero
    {I : ConcreteWindow} {f : ConcreteTest} {x : ConcreteSupportPoint}
    (hx : concreteSupportValue I f x ≠ 0) :
    pointInConcreteWindow I x :=
  (concreteSupportValue_ne_zero_iff.mp hx).1

theorem concreteSupportValue_ne_zero_coordinateLower
    {I : ConcreteWindow} {f : ConcreteTest} {x : ConcreteSupportPoint}
    (hx : concreteSupportValue I f x ≠ 0) :
    I.1 ≤ x.1 :=
  (pointInConcreteWindow_of_concreteSupportValue_ne_zero hx).1

theorem concreteSupportValue_ne_zero_coordinateUpper
    {I : ConcreteWindow} {f : ConcreteTest} {x : ConcreteSupportPoint}
    (hx : concreteSupportValue I f x ≠ 0) :
    x.1 ≤ I.2 :=
  (pointInConcreteWindow_of_concreteSupportValue_ne_zero hx).2.1

theorem concreteSupportValue_ne_zero_logScale_eq_zero
    {I : ConcreteWindow} {f : ConcreteTest} {x : ConcreteSupportPoint}
    (hx : concreteSupportValue I f x ≠ 0) :
    x.2 = 0 :=
  (pointInConcreteWindow_of_concreteSupportValue_ne_zero hx).2.2

theorem concreteSupportValue_involution_eq_fourier
    (I : ConcreteWindow) (f : ConcreteTest) (x : ConcreteSupportPoint) :
    concreteSupportValue I (concreteTestAlgebra.involution f) x =
      concreteSupportValue I (𝓕 f) x := by
  rfl

noncomputable def concreteSupportWindowData
    (I : ConcreteWindow := defaultWindow)
    (sourceTest : ConcreteTest := defaultSourceTest) :
    SourceSupportWindowData concreteTestAlgebra where
  PlaceSet := ConcretePlace
  Window := ConcreteWindow
  sourcePlaceSet := PUnit.unit
  sourceSupportWindow := I
  sourceTest := sourceTest
  SupportPoint := ConcreteSupportPoint
  supportValue := concreteSupportValue I
  sourceWindowCoordinate := concreteWindowCoordinate

@[simp] theorem concreteSupportWindowData_supportValue
    (I : ConcreteWindow) (sourceTest f : ConcreteTest)
    (x : ConcreteSupportPoint) :
    (concreteSupportWindowData I sourceTest).supportValue f x =
      concreteSupportValue I f x :=
  rfl

@[simp] theorem concreteSupportWindowData_sourceWindowCoordinate
    (I : ConcreteWindow) (sourceTest : ConcreteTest) :
    (concreteSupportWindowData I sourceTest).sourceWindowCoordinate =
      concreteWindowCoordinate :=
  rfl

theorem mem_concreteSupportCarrier_iff
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint} :
    x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f ↔
      pointInConcreteWindow I x ∧ f x.1 ≠ 0 := by
  change concreteSupportValue I f x ≠ 0 ↔
    pointInConcreteWindow I x ∧ f x.1 ≠ 0
  exact concreteSupportValue_ne_zero_iff

theorem pointInConcreteWindow_of_mem_concreteSupportCarrier
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    pointInConcreteWindow I x :=
  (mem_concreteSupportCarrier_iff.mp hx).1

theorem mem_concreteSupportCarrier_coordinateLower
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    I.1 ≤ x.1 :=
  (pointInConcreteWindow_of_mem_concreteSupportCarrier hx).1

theorem mem_concreteSupportCarrier_coordinateUpper
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    x.1 ≤ I.2 :=
  (pointInConcreteWindow_of_mem_concreteSupportCarrier hx).2.1

theorem mem_concreteSupportCarrier_logScale_eq_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    x.2 = 0 :=
  (pointInConcreteWindow_of_mem_concreteSupportCarrier hx).2.2

theorem mem_concreteFourierSupportCarrier_iff
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint} :
    x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f ↔
      pointInConcreteWindow I x ∧ (𝓕 f) x.1 ≠ 0 := by
  change
    concreteSupportValue I (concreteTestAlgebra.involution f) x ≠ 0 ↔
      pointInConcreteWindow I x ∧ (𝓕 f) x.1 ≠ 0
  simpa using (concreteSupportValue_ne_zero_iff
    (I := I) (f := concreteTestAlgebra.involution f) (x := x))

theorem pointInConcreteWindow_of_mem_concreteFourierSupportCarrier
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    pointInConcreteWindow I x :=
  (mem_concreteFourierSupportCarrier_iff.mp hx).1

theorem mem_concreteFourierSupportCarrier_coordinateLower
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    I.1 ≤ x.1 :=
  (pointInConcreteWindow_of_mem_concreteFourierSupportCarrier hx).1

theorem mem_concreteFourierSupportCarrier_coordinateUpper
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    x.1 ≤ I.2 :=
  (pointInConcreteWindow_of_mem_concreteFourierSupportCarrier hx).2.1

theorem mem_concreteFourierSupportCarrier_logScale_eq_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    x.2 = 0 :=
  (pointInConcreteWindow_of_mem_concreteFourierSupportCarrier hx).2.2

theorem pointInConcreteWindow_lower
    {I : ConcreteWindow} {x : ConcreteSupportPoint}
    (hx : pointInConcreteWindow I x) :
    I.1 ≤ x.1 :=
  hx.1

theorem pointInConcreteWindow_upper
    {I : ConcreteWindow} {x : ConcreteSupportPoint}
    (hx : pointInConcreteWindow I x) :
    x.1 ≤ I.2 :=
  hx.2.1

theorem pointInConcreteWindow_logScale_eq_zero
    {I : ConcreteWindow} {x : ConcreteSupportPoint}
    (hx : pointInConcreteWindow I x) :
    x.2 = 0 :=
  hx.2.2

theorem mem_concreteSupportCarrier_pointInWindow
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    pointInConcreteWindow I x :=
  (mem_concreteSupportCarrier_iff.mp hx).1

theorem mem_concreteSupportCarrier_value_ne_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    f x.1 ≠ 0 :=
  (mem_concreteSupportCarrier_iff.mp hx).2

theorem mem_concreteSupportCarrier_of_pointInWindow_value_ne_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hWindow : pointInConcreteWindow I x) (hValue : f x.1 ≠ 0) :
    x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f :=
  mem_concreteSupportCarrier_iff.mpr ⟨hWindow, hValue⟩

theorem not_mem_concreteSupportCarrier_of_not_pointInWindow
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hWindow : ¬pointInConcreteWindow I x) :
    x ∉ (concreteSupportWindowData I sourceTest).supportCarrier f := by
  intro hx
  exact hWindow (mem_concreteSupportCarrier_pointInWindow hx)

theorem not_mem_concreteSupportCarrier_of_value_eq_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hValue : f x.1 = 0) :
    x ∉ (concreteSupportWindowData I sourceTest).supportCarrier f := by
  intro hx
  exact mem_concreteSupportCarrier_value_ne_zero hx hValue

theorem concreteSupportCarrier_subset_pointInConcreteWindow
    {I : ConcreteWindow} {sourceTest f : ConcreteTest} :
    (concreteSupportWindowData I sourceTest).supportCarrier f ⊆
      {x : ConcreteSupportPoint | pointInConcreteWindow I x} := by
  intro x hx
  exact mem_concreteSupportCarrier_pointInWindow hx

theorem concreteSupportCarrier_eq_setOf_pointInWindow_value_ne_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest} :
    (concreteSupportWindowData I sourceTest).supportCarrier f =
      {x : ConcreteSupportPoint | pointInConcreteWindow I x ∧ f x.1 ≠ 0} := by
  ext x
  exact mem_concreteSupportCarrier_iff

theorem mem_concreteFourierSupportCarrier_pointInWindow
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    pointInConcreteWindow I x :=
  (mem_concreteFourierSupportCarrier_iff.mp hx).1

theorem mem_concreteFourierSupportCarrier_fourier_value_ne_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    (𝓕 f) x.1 ≠ 0 :=
  (mem_concreteFourierSupportCarrier_iff.mp hx).2

theorem mem_concreteFourierSupportCarrier_of_pointInWindow_fourier_value_ne_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hWindow : pointInConcreteWindow I x) (hValue : (𝓕 f) x.1 ≠ 0) :
    x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f :=
  mem_concreteFourierSupportCarrier_iff.mpr ⟨hWindow, hValue⟩

theorem not_mem_concreteFourierSupportCarrier_of_not_pointInWindow
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hWindow : ¬pointInConcreteWindow I x) :
    x ∉ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f := by
  intro hx
  exact hWindow (mem_concreteFourierSupportCarrier_pointInWindow hx)

theorem not_mem_concreteFourierSupportCarrier_of_fourier_value_eq_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hValue : (𝓕 f) x.1 = 0) :
    x ∉ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f := by
  intro hx
  exact mem_concreteFourierSupportCarrier_fourier_value_ne_zero hx hValue

theorem concreteFourierSupportCarrier_subset_pointInConcreteWindow
    {I : ConcreteWindow} {sourceTest f : ConcreteTest} :
    (concreteSupportWindowData I sourceTest).fourierSupportCarrier f ⊆
      {x : ConcreteSupportPoint | pointInConcreteWindow I x} := by
  intro x hx
  exact mem_concreteFourierSupportCarrier_pointInWindow hx

theorem concreteFourierSupportCarrier_eq_setOf_pointInWindow_fourier_value_ne_zero
    {I : ConcreteWindow} {sourceTest f : ConcreteTest} :
    (concreteSupportWindowData I sourceTest).fourierSupportCarrier f =
      {x : ConcreteSupportPoint | pointInConcreteWindow I x ∧ (𝓕 f) x.1 ≠ 0} := by
  ext x
  exact mem_concreteFourierSupportCarrier_iff

theorem concreteSupportScale_eq_exp
    (I : ConcreteWindow) (sourceTest : ConcreteTest)
    (x : ConcreteSupportPoint) :
    (concreteSupportWindowData I sourceTest).supportScale x = Real.exp x.2 := by
  rfl

theorem concreteSupportScale_eq_one_of_second_eq_zero
    {I : ConcreteWindow} {sourceTest : ConcreteTest}
    {x : ConcreteSupportPoint} (hx : x.2 = 0) :
    (concreteSupportWindowData I sourceTest).supportScale x = 1 := by
  simpa [concreteSupportScale_eq_exp I sourceTest x, hx]

theorem pointInConcreteWindow_mem_concreteWindowCarrier
    {I : ConcreteWindow} {sourceTest : ConcreteTest}
    {x : ConcreteSupportPoint} (hx : pointInConcreteWindow I x) :
    x ∈ (concreteSupportWindowData I sourceTest).windowCarrier I := by
  exact
    SourceSupportWindowData.mem_windowCarrier_of_coordinate_bounds_logScale_eq_zero
      (S := concreteSupportWindowData I sourceTest)
      (I := I) (x := x)
      (by simpa using hx.1)
      (by simpa using hx.2.1)
      (by simpa using hx.2.2)

theorem mem_concreteWindowCarrier_pointInWindow
    {I : ConcreteWindow} {sourceTest : ConcreteTest}
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).windowCarrier I) :
    pointInConcreteWindow I x := by
  exact
    ⟨by
        simpa using
          SourceSupportWindowData.mem_windowCarrier_coordinate_lower
            (S := concreteSupportWindowData I sourceTest) hx,
      by
        simpa using
          SourceSupportWindowData.mem_windowCarrier_coordinate_upper
            (S := concreteSupportWindowData I sourceTest) hx,
      by
        simpa using
          SourceSupportWindowData.logScale_eq_zero_of_supportScale_eq_one
            (S := concreteSupportWindowData I sourceTest)
            (SourceSupportWindowData.mem_windowCarrier_supportScale_eq_one
              (S := concreteSupportWindowData I sourceTest) hx)⟩

theorem mem_concreteWindowCarrier_iff_pointInConcreteWindow
    {I : ConcreteWindow} {sourceTest : ConcreteTest}
    {x : ConcreteSupportPoint} :
    x ∈ (concreteSupportWindowData I sourceTest).windowCarrier I ↔
      pointInConcreteWindow I x := by
  constructor
  · exact mem_concreteWindowCarrier_pointInWindow
  · exact pointInConcreteWindow_mem_concreteWindowCarrier

theorem concreteWindowCarrier_eq_setOf_pointInConcreteWindow
    {I : ConcreteWindow} {sourceTest : ConcreteTest} :
    (concreteSupportWindowData I sourceTest).windowCarrier I =
      {x : ConcreteSupportPoint | pointInConcreteWindow I x} := by
  ext x
  exact mem_concreteWindowCarrier_iff_pointInConcreteWindow

theorem pointInConcreteWindow_mem_concreteLambdaCarrier_of_one_lt
    {I : ConcreteWindow} {sourceTest : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda)
    {x : ConcreteSupportPoint} (hx : pointInConcreteWindow I x) :
    x ∈ (concreteSupportWindowData I sourceTest).lambdaCarrier lambda := by
  exact
    SourceSupportWindowData.mem_lambdaCarrier_of_supportScale_eq_one
      (S := concreteSupportWindowData I sourceTest)
      (lambda := lambda) hlambda
      (concreteSupportScale_eq_one_of_second_eq_zero
        (I := I) (sourceTest := sourceTest) hx.2.2)

theorem concreteWindowCarrier_subset_lambdaCarrier_of_one_lt
    {I : ConcreteWindow} {sourceTest : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    (concreteSupportWindowData I sourceTest).windowCarrier I ⊆
      (concreteSupportWindowData I sourceTest).lambdaCarrier lambda := by
  intro x hx
  exact pointInConcreteWindow_mem_concreteLambdaCarrier_of_one_lt
    (I := I) (sourceTest := sourceTest) hlambda
    (mem_concreteWindowCarrier_pointInWindow hx)

theorem concreteWindowContainedInLambda_of_one_lt
    {I : ConcreteWindow} {sourceTest : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    (concreteSupportWindowData I sourceTest).windowContainedInLambda I lambda :=
  concreteWindowCarrier_subset_lambdaCarrier_of_one_lt
    (I := I) (sourceTest := sourceTest) hlambda

theorem concreteLambdaCompatible_of_one_lt
    {I : ConcreteWindow} {sourceTest : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    (concreteSupportWindowData I sourceTest).lambdaCompatible I lambda :=
  SourceSupportWindowData.lambdaCompatible_of_windowContainedInLambda
    (concreteWindowContainedInLambda_of_one_lt
      (I := I) (sourceTest := sourceTest) hlambda)

theorem concreteSupportCarrier_subset_lambdaCarrier_of_one_lt
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    (concreteSupportWindowData I sourceTest).supportCarrier f ⊆
      (concreteSupportWindowData I sourceTest).lambdaCarrier lambda := by
  intro x hx
  exact pointInConcreteWindow_mem_concreteLambdaCarrier_of_one_lt
    (I := I) (sourceTest := sourceTest) hlambda
    (mem_concreteSupportCarrier_pointInWindow hx)

theorem concreteFourierSupportCarrier_subset_lambdaCarrier_of_one_lt
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    (concreteSupportWindowData I sourceTest).fourierSupportCarrier f ⊆
      (concreteSupportWindowData I sourceTest).lambdaCarrier lambda := by
  intro x hx
  exact pointInConcreteWindow_mem_concreteLambdaCarrier_of_one_lt
    (I := I) (sourceTest := sourceTest) hlambda
    (mem_concreteFourierSupportCarrier_pointInWindow hx)

theorem concreteSupportCarrier_mem_lambdaCarrier_of_one_lt
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda)
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    x ∈ (concreteSupportWindowData I sourceTest).lambdaCarrier lambda :=
  concreteSupportCarrier_subset_lambdaCarrier_of_one_lt
    (I := I) (sourceTest := sourceTest) (f := f) hlambda hx

theorem concreteFourierSupportCarrier_mem_lambdaCarrier_of_one_lt
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda)
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    x ∈ (concreteSupportWindowData I sourceTest).lambdaCarrier lambda :=
  concreteFourierSupportCarrier_subset_lambdaCarrier_of_one_lt
    (I := I) (sourceTest := sourceTest) (f := f) hlambda hx

theorem concreteSupportCarrier_lambda_lower_of_one_lt
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda)
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    lambda⁻¹ ≤ (concreteSupportWindowData I sourceTest).supportScale x :=
  SourceSupportWindowData.mem_lambdaCarrier_lower
    (concreteSupportCarrier_mem_lambdaCarrier_of_one_lt
      (I := I) (sourceTest := sourceTest) (f := f) hlambda hx)

theorem concreteSupportCarrier_lambda_upper_of_one_lt
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda)
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).supportCarrier f) :
    (concreteSupportWindowData I sourceTest).supportScale x ≤ lambda :=
  SourceSupportWindowData.mem_lambdaCarrier_upper
    (concreteSupportCarrier_mem_lambdaCarrier_of_one_lt
      (I := I) (sourceTest := sourceTest) (f := f) hlambda hx)

theorem concreteFourierSupportCarrier_lambda_lower_of_one_lt
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda)
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    lambda⁻¹ ≤ (concreteSupportWindowData I sourceTest).supportScale x :=
  SourceSupportWindowData.mem_lambdaCarrier_lower
    (concreteFourierSupportCarrier_mem_lambdaCarrier_of_one_lt
      (I := I) (sourceTest := sourceTest) (f := f) hlambda hx)

theorem concreteFourierSupportCarrier_lambda_upper_of_one_lt
    {I : ConcreteWindow} {sourceTest f : ConcreteTest}
    {lambda : ℝ} (hlambda : 1 < lambda)
    {x : ConcreteSupportPoint}
    (hx : x ∈ (concreteSupportWindowData I sourceTest).fourierSupportCarrier f) :
    (concreteSupportWindowData I sourceTest).supportScale x ≤ lambda :=
  SourceSupportWindowData.mem_lambdaCarrier_upper
    (concreteFourierSupportCarrier_mem_lambdaCarrier_of_one_lt
      (I := I) (sourceTest := sourceTest) (f := f) hlambda hx)

end SourceConcreteBaseLayer

end AnalyticCore
end Source
end ConnesWeilRH
