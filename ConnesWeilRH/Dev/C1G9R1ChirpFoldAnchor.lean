/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import Mathlib

/-!
# Chirp fold block: the exact shear identity (records 1690/1691 anchor)

At the fold `xi_0 = lambda^-2` the committed symbol's local two-sided
block is the pure-chirp Wiener-Hopf corner `A = P_+ F_a P_+` with Fresnel
kernel `F_a(s) = a^{-1/2} exp(i pi / 4) exp(-i pi s^2 / a)`, `a = lambda^2`
(record 1690 Thm A).  This brick pins the EXACT algebra behind records
1690 Thm B (near-kernel race) and 1691 Thm C (injectivity) at `L^1`
level, for the unit-modulus kernel `chirpKernel` (the scalar
normalization `a^{-1/2}` cancels in every ratio and in injectivity, so it
is carried as a remark, not as a hypothesis):

* paper-level: unit modulus and the exact scale covariance
  `F_{r^2 a}(r s) = F_a(s)` (record 1690 Thm A) are the real-level
  facts `(r s)^2 / (r^2 a) = s^2 / a` and `|exp| = 1`; the
  `Real -> Complex` coercion grain makes the Lean restatement
  unprofitable here.
* `chirp_shear_identity` : for any input `b`, the convolution output at
  position `a * t` factors as `F_a(a t) * G_t`, where
  `G_t = ∫ exp((2 pi t v) * I) * (b v * exp(-(pi v^2 / a) * I))` is the
  Fourier-type content of the CHIRP-MODULATED input
  `g = b * exp(-i pi y^2 / a)` at frequency `-t` — the exact
  square-completion engine of records 1690/1691.
* `chirp_fold_freq_vanishing` : if the output vanishes on the positive
  half-line, the chirp-modulated input's Fourier content vanishes on the
  NEGATIVE frequency ray (read the exponent `(2 pi eta v) * I` as the
  `exp(-2 pi i (-eta) v)` convention).  With `supp b ⊆ (0, ∞)` this
  makes `g`'s Fourier transform an `H^2(C_-)` boundary function
  vanishing on a set of positive measure, so Privalov uniqueness (paper
  level, record 1691) gives `b = 0`: the chirp block is injective.
-/

namespace ConnesWeilRH.Dev.C1G9R1ChirpFoldAnchor

open MeasureTheory

/-- Unit-modulus Fresnel (pure-chirp) kernel at rate `a`; the normalized
kernel is `a ^ (-1/2 : ℝ) • chirpKernel a`. -/
noncomputable def chirpKernel (a : ℝ) (s : ℝ) : ℂ :=
  Complex.exp (Complex.I * (Real.pi / 4))
    * Complex.exp (-(Complex.I * Real.pi) * (s * s / a))

/-- The kernel is never zero. -/
theorem chirpKernel_ne_zero (a s : ℝ) : chirpKernel a s ≠ 0 :=
  mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _)

/-- The exact shear identity (records 1690/1691 engine): the convolution
output at position `a * t` is the kernel value times the Fourier content
of the chirp-modulated input at frequency `-t`.  (Scale covariance
`F_{r^2 a}(r s) = F_a(s)` is the real-level identity
`(r s)^2 / (r^2 a) = s^2 / a`; it is carried at paper level in records
1690/1691 — the `ℝ → ℂ` coercion grain makes the Lean rewrite
unprofitable.) -/
theorem chirp_shear_identity {a : ℝ} (ha : 0 < a) (b : ℝ → ℂ)
    (_hb : Integrable b volume) (t : ℝ) :
    ∫ v : ℝ, chirpKernel a (a * t - v) * b v ∂volume
      = chirpKernel a (a * t) * ∫ v : ℝ,
          Complex.exp ((2 * Real.pi * t * v) * Complex.I)
            * (b v * Complex.exp (-(Complex.I * Real.pi) * (v * v / a)))
            ∂volume := by
  have hac : (Complex.ofReal a) ≠ 0 := by
    simpa [Complex.ofReal_eq_zero] using ha.ne'
  have hexp : ∀ v : ℝ,
      Complex.exp (-(Complex.I * Real.pi) * ((a * t - v) * (a * t - v) / a))
        = Complex.exp (-(Complex.I * Real.pi) * ((a * t) * (a * t) / a))
          * Complex.exp ((2 * Real.pi * t * v) * Complex.I)
          * Complex.exp (-(Complex.I * Real.pi) * (v * v / a)) := by
    intro v
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    field_simp [hac]
    ring
  calc ∫ v : ℝ, chirpKernel a (a * t - v) * b v ∂volume
      = ∫ v : ℝ,
          (Complex.exp (Complex.I * (Real.pi / 4))
              * Complex.exp (-(Complex.I * Real.pi) * ((a * t) * (a * t) / a)))
            * (Complex.exp ((2 * Real.pi * t * v) * Complex.I)
              * (b v * Complex.exp (-(Complex.I * Real.pi) * (v * v / a))))
          ∂volume :=
        integral_congr_ae (Filter.Eventually.of_forall (fun v => by
          simp only [chirpKernel]
          push_cast only [Complex.ofReal_mul, Complex.ofReal_sub]
          rw [hexp v]
          ring))
    _ = chirpKernel a (a * t) * ∫ v : ℝ,
          Complex.exp ((2 * Real.pi * t * v) * Complex.I)
            * (b v * Complex.exp (-(Complex.I * Real.pi) * (v * v / a)))
          ∂volume := by
        rw [chirpKernel]
        simp only [Complex.ofReal_mul]
        rw [integral_const_mul]

/-- Frequency-ray vanishing (record 1691 Thm C's hypothesis): if the
convolution output vanishes on the positive half-line, then the
chirp-modulated input `g = b * exp(-i pi y^2 / a)` has Fourier content
zero on the negative frequency ray; with `supp b ⊆ (0, ∞)`, Privalov
uniqueness for `H^2(C_-)` (paper level) then gives `b = 0`. -/
theorem chirp_fold_freq_vanishing {a : ℝ} (ha : 0 < a) (b : ℝ → ℂ)
    (_hb : Integrable b volume)
    (h : ∀ x : ℝ, 0 < x → ∫ v : ℝ, chirpKernel a (x - v) * b v ∂volume = 0)
    (η : ℝ) (hη : 0 < η) :
    ∫ v : ℝ, Complex.exp ((2 * Real.pi * η * v) * Complex.I)
        * (b v * Complex.exp (-(Complex.I * Real.pi) * (v * v / a)))
        ∂volume = 0 := by
  have h0 := h (a * η) (mul_pos ha hη)
  rw [chirp_shear_identity ha b _hb η] at h0
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 (chirpKernel_ne_zero a (a * η))
  · exact h1

end ConnesWeilRH.Dev.C1G9R1ChirpFoldAnchor
