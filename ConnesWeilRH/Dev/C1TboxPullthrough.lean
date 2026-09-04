/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under the Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1EntrywiseBound
import ConnesWeilRH.Dev.C1HboxRationalData
import ConnesWeilRH.Dev.C1GateLevelTransferClasses

/-!
# Record 1119: T-box (Gt, Mt)-level pull-through per class

Closes the record-1118 sub-obligation (a) FULL statement (the box theorem)
and composes it with sub-obligation (b)'s data: the whole (a)+(b) chain of
each class certificate now has, as its only analytic named hypothesis,
`Hbox` (the true data lies in the committed outward boxes) plus the
representation/normalization slots - see
docs/proofs/1119_hbox_tbox_pullthrough_preregistration.md section 1c.

Mechanism (generic `tbox_of_identities`): the certificate `D = U • G - M`
is extended to every `Gt/Mt` inside the radius boxes.  The quadratic form
sees only the symmetrization (`qform_sym_half`); the symmetrized
perturbation `Δ + Δᵀ` is entrywise-bounded by `2 (mu radG + radM)` (sym
radii), propagated through `K` by `entrywise_triple` (`= DredRad` via
`hDredRad`), transported to the whitened coordinates `z = Lᵀ x`,
`x = Lamᵀ z` (`hLLam`), propagated through `Lam` (`= radp` via `hRadp`),
halved, and closed by the LANDED record-1118 kernel
`qform_nonneg_whitenedBox` on the committed `radp`/`dd`/slacks.

RH NOT claimed; no gate Prop is discharged here beyond the named slots.
-/

namespace ConnesWeilRH
namespace Source
namespace C1TboxPullthrough

open Matrix
open C1EntrywiseBound
open C1HboxRationalData
open C1GateLevelTransfer
open C1GateLevelTransferClasses
open C1LocalConfigurationDomination
open C1WindowRationalIngest
open CCM25Concrete.CompactLogConvolution

/-- **The generic T-box pull-through** (preregistration section 1c).

Given a class certificate in the record-1115 ingestion shape (closure
witness, symmetrized pencil factorization, whitening inverse `Lam`, and
the record-1118 whitened kernel data `radp`/`dd`/slacks), the top bound
extends from the center to EVERY `Gt/Mt` inside the committed radius
boxes `radG/radM`. -/
theorem tbox_of_identities
    {n m k : ℕ}
    (U : ℝ) (G M : Matrix (Fin n) (Fin n) ℝ)
    (R : Matrix (Fin m) (Fin n) ℝ)
    (K : Matrix (Fin n) (Fin k) ℝ) (V : Matrix (Fin k) (Fin n) ℝ)
    (W : Matrix (Fin n) (Fin m) ℝ)
    (Dc : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin k) (Fin k) ℝ)
    (d : Fin k → ℝ)
    (radG radM : Matrix (Fin n) (Fin n) ℝ)
    (absK : Matrix (Fin n) (Fin k) ℝ)
    (Lam absLam DredRad radp : Matrix (Fin k) (Fin k) ℝ) (dd : Fin k → ℝ)
    (mu : ℝ)
    (hKVW : K * V + W * R = 1)
    (hDtwo : Dc + Dc = (U • G - M) + (U • G - M).transpose)
    (hPencil : K.transpose * Dc * K = L * Matrix.diagonal d * L.transpose)
    (hUabs : |U| = mu)
    (hradGsym : ∀ i j, radG i j = radG j i)
    (hradMsym : ∀ i j, radM i j = radM j i)
    (habsK : ∀ i j, absK i j = |K i j|)
    (habsLam : ∀ i j, absLam i j = |Lam i j|)
    (hLamL : Lam * L = 1) (hLLam : L * Lam = 1)
    (hDredRad : Matrix.transpose absK * (mu • radG + radM) * absK = DredRad)
    (hRadp : absLam * DredRad * Matrix.transpose absLam = radp)
    (hradpos : ∀ i j, 0 ≤ radp i j)
    (hslack : ∀ i, radp i i + ((Finset.univ \ {i}).sum fun j => (radp i j + radp j i) / 2)
      < d i)
    (Gt Mt : Matrix (Fin n) (Fin n) ℝ)
    (hG : ∀ i j, |Gt i j - G i j| ≤ radG i j)
    (hM : ∀ i j, |Mt i j - M i j| ≤ radM i j)
    (c : Fin n → ℝ) (hc : R.mulVec c = 0) :
    c ⬝ᵥ (Mt *ᵥ c) ≤ U * c ⬝ᵥ (Gt *ᵥ c) := by
  -- closure witness: c = K *ᵥ x
  obtain ⟨x, hx⟩ := exists_mulVec_eq_of_closure K V W R hKVW c hc
  set Δ : Matrix (Fin n) (Fin n) ℝ := (U • Gt - Mt) - (U • G - M) with hΔdef
  -- entrywise bound on the perturbation: |Δ| <= mu radG + radM
  have hbΔ : ∀ i j, |Δ i j| ≤ mu * radG i j + radM i j := by
    intro i j
    rw [hΔdef]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    have e1 : (U * Gt i j - Mt i j) - (U * G i j - M i j)
        = U * (Gt i j - G i j) - (Mt i j - M i j) := by ring
    rw [e1]
    have hUd : |U * (Gt i j - G i j)| ≤ mu * radG i j := by
      rw [abs_mul, hUabs]
      nlinarith [hG i j, abs_nonneg U]
    have tri := abs_sub (U * (Gt i j - G i j)) (Mt i j - M i j)
    linarith [tri, hUd, hM i j]
  -- the form sees the symmetrization; symmetrized perturbation by 2(mu radG + radM)
  have hsplit : ((1 : ℝ) / 2) • ((U • Gt - Mt) + (U • Gt - Mt).transpose)
      = Dc + ((1 : ℝ) / 2) • (Δ + Δ.transpose) := by
    ext i j
    simp only [Matrix.smul_apply, smul_add, Matrix.add_apply, Matrix.sub_apply,
      Matrix.transpose_apply, smul_eq_mul]
    have h3 : (Dc + Dc) i j = ((U • G - M) + (U • G - M).transpose) i j := by
      rw [hDtwo]
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.transpose_apply, smul_eq_mul] at h3
    rw [hΔdef]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul]
    linarith
  have F1 : c ⬝ᵥ (((1 : ℝ) / 2) • ((U • Gt - Mt) + (U • Gt - Mt).transpose)).mulVec c
      = c ⬝ᵥ (Dc.mulVec c)
        + ((1 : ℝ) / 2) * c ⬝ᵥ ((Δ + Δ.transpose).mulVec c) := by
    rw [hsplit, Matrix.add_mulVec, dotProduct_add, Matrix.smul_mulVec, dotProduct_smul]
    ring
  -- center piece through closure + pencil
  have stepC : c ⬝ᵥ (Dc.mulVec c)
      = (L.transpose.mulVec x) ⬝ᵥ (Matrix.diagonal d *ᵥ (L.transpose.mulVec x)) := by
    rw [← hx, qform_pull K Dc x, hPencil]
    exact (qform_pull L.transpose (Matrix.diagonal d) x).symm
  -- perturbation piece through K
  have stepD : c ⬝ᵥ ((Δ + Δ.transpose).mulVec c)
      = x ⬝ᵥ ((K.transpose * (Δ + Δ.transpose) * K).mulVec x) := by
    rw [← hx]
    exact qform_pull K (Δ + Δ.transpose) x
  -- entrywise bound on N := Kᵀ (Δ + Δᵀ) K, via the (2 : ℝ)-scaled smul bookkeeping
  have hscaleK : Matrix.transpose absK * ((2 : ℝ) • (mu • radG + radM)) * absK
      = (2 : ℝ) • (Matrix.transpose absK * (mu • radG + radM) * absK) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hbN : ∀ i j, |(K.transpose * (Δ + Δ.transpose) * K) i j| ≤ 2 * DredRad i j := by
    intro i j
    have hbS0 : ∀ i' j', |(Δ + Δ.transpose) i' j'|
        ≤ ((2 : ℝ) • (mu • radG + radM)) i' j' := by
      intro i' j'
      have g1 := hbΔ i' j'
      have g2 := hbΔ j' i'
      have t2 : ((2 : ℝ) • (mu • radG + radM)) i' j'
          = 2 * (mu * radG i' j' + radM i' j') := by
        simp [Matrix.smul_apply, Matrix.add_apply, smul_eq_mul]
      rw [Matrix.add_apply, Matrix.transpose_apply, t2, abs_le]
      constructor <;> linarith [hradGsym i' j', hradMsym i' j']
    have habsK' : ∀ i' j', |K i' j'| ≤ absK i' j' := fun i' j' => by
      rw [habsK i' j']
    have h1 := entrywise_triple K K (Δ + Δ.transpose) absK absK
      ((2 : ℝ) • (mu • radG + radM)) habsK' hbS0 habsK' i j
    rw [hscaleK, hDredRad, Matrix.smul_apply, smul_eq_mul] at h1
    exact h1
  -- transport to whitened coordinates: z = Lᵀ x, x = Lamᵀ z
  have hxz : (Matrix.transpose Lam).mulVec (L.transpose.mulVec x) = x := by
    rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hLLam]
    simp
  have stepE : x ⬝ᵥ ((K.transpose * (Δ + Δ.transpose) * K).mulVec x)
      = (L.transpose.mulVec x) ⬝ᵥ
        ((Lam * (K.transpose * (Δ + Δ.transpose) * K) * Lam.transpose).mulVec
          (L.transpose.mulVec x)) := by
    have h := qform_pull (Matrix.transpose Lam)
      (K.transpose * (Δ + Δ.transpose) * K) (L.transpose.mulVec x)
    rw [hxz] at h
    rw [Matrix.transpose_transpose] at h
    exact h
  -- entrywise bound on E := Lam * N * Lamᵀ
  have hscaleLam : absLam * ((2 : ℝ) • DredRad) * Matrix.transpose absLam
      = (2 : ℝ) • (absLam * DredRad * Matrix.transpose absLam) := by
    rw [Matrix.mul_smul, Matrix.smul_mul]
  have hbE : ∀ i j,
      |(Lam * (K.transpose * (Δ + Δ.transpose) * K) * Lam.transpose) i j|
        ≤ 2 * radp i j := by
    intro i j
    have hbN' : ∀ i' j', |(K.transpose * (Δ + Δ.transpose) * K) i' j'|
        ≤ ((2 : ℝ) • DredRad) i' j' := by
      intro i' j'
      have g := hbN i' j'
      rw [Matrix.smul_apply, smul_eq_mul]
      exact g
    have hxb : ∀ i' j', |(Matrix.transpose Lam) i' j'|
        ≤ (Matrix.transpose absLam) i' j' := by
      intro i' j'
      rw [Matrix.transpose_apply, Matrix.transpose_apply]
      exact le_of_eq (habsLam j' i').symm
    have h1 := entrywise_triple (Matrix.transpose Lam) (Matrix.transpose Lam)
      (K.transpose * (Δ + Δ.transpose) * K) (Matrix.transpose absLam)
      (Matrix.transpose absLam) ((2 : ℝ) • DredRad) hxb hbN' hxb i j
    rw [Matrix.transpose_transpose, hscaleLam, hRadp, Matrix.smul_apply,
      smul_eq_mul] at h1
    exact h1
  -- assemble: F = whitened form of (diagonal d + (1/2) • E)
  have Ffinal : c ⬝ᵥ ((U • Gt - Mt).mulVec c)
      = (L.transpose.mulVec x) ⬝ᵥ (Matrix.diagonal d *ᵥ (L.transpose.mulVec x))
        + (L.transpose.mulVec x) ⬝ᵥ
          ((((1 : ℝ) / 2) • (Lam * (K.transpose * (Δ + Δ.transpose) * K)
            * Lam.transpose)).mulVec (L.transpose.mulVec x)) := by
    rw [qform_sym_half (U • Gt - Mt) c, F1, stepC, stepD, stepE,
      Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  have heb' : ∀ i j,
      |(((1 : ℝ) / 2) • (Lam * (K.transpose * (Δ + Δ.transpose) * K)
        * Lam.transpose)) i j| ≤ radp i j := by
    intro i j
    rw [Matrix.smul_apply, smul_eq_mul, abs_mul]
    norm_num
    nlinarith [hbE i j]
  have hbig : 0 ≤ c ⬝ᵥ ((U • Gt - Mt).mulVec c) := by
    have hpos := qform_nonneg_whitenedBox radp hradpos hslack
      (E := ((1 : ℝ) / 2) • (Lam * (K.transpose * (Δ + Δ.transpose) * K)
        * Lam.transpose)) heb' (L.transpose.mulVec x)
    rw [Matrix.add_mulVec, dotProduct_add] at hpos
    rw [Ffinal]
    exact hpos
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, dotProduct_sub, dotProduct_smul,
    smul_eq_mul] at hbig
  linarith

theorem hUneg_q28 : Q28.U < 0 := by
  simp only [Q28.U]
  norm_num

theorem hUabs_q28 : |Q28.U| = mu_q28 := by
  simp only [mu_q28]
  exact abs_of_neg hUneg_q28

theorem hDtwo_q28 : Q28.Dc + Q28.Dc
    = (Q28.U • Q28.G - Q28.M) + (Q28.U • Q28.G - Q28.M).transpose := by
  rw [← Q28.hD]
  exact Q28.hDc

/-- **T-box (2,8)**: the record-1118 §1a box theorem at radius form - for
EVERY `Gt/Mt` inside the committed radius boxes the top bound holds on
`ker R`. -/
theorem tbox_q28 (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - Q28.G i j| ≤ radG_q28 i j)
    (hM : ∀ i j, |Mt i j - Q28.M i j| ≤ radM_q28 i j)
    (c : Fin 8 → ℝ) (hc : Q28.R.mulVec c = 0) :
    c ⬝ᵥ (Mt *ᵥ c) ≤ Q28.U * c ⬝ᵥ (Gt *ᵥ c) :=
  tbox_of_identities Q28.U Q28.G Q28.M Q28.R Q28.K Q28.V Q28.W Q28.Dc Q28.L Q28.d
    radG_q28 radM_q28 absK_q28 Lam_q28 absLam_q28 DredRad_q28 radp_q28 dd_q28 mu_q28
    Q28.hclosure hDtwo_q28 Q28.hPencil hUabs_q28
    hsymRadG_q28 hsymRadM_q28 habsK_q28 habsLam_q28
    hLamL_q28 hLLam_q28 hDredRad_q28 hRadp_q28
    hradpos_q28 hslack_q28 Gt Mt hG hM c hc

/-- **T-box true (2,8)**: `Hbox` (true data in the committed bundle boxes)
suffices - the bridge is the reverse containment. -/
theorem tbox_true_q28 (G_true M_true : Matrix (Fin 8) (Fin 8) ℝ)
    (hbox : Hbox GLo_q28 GHi_q28 MLo_q28 MHi_q28 G_true M_true)
    (c : Fin 8 → ℝ) (hc : Q28.R.mulVec c = 0) :
    c ⬝ᵥ (M_true *ᵥ c) ≤ Q28.U * c ⬝ᵥ (G_true *ᵥ c) := by
  refine tbox_q28 G_true M_true ?_ ?_ c hc
  · intro i j
    obtain ⟨h1, h2⟩ := hbox.1 i j
    obtain ⟨h3, h4⟩ := hrevG_q28 i j
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hbox.2 i j
    obtain ⟨h3, h4⟩ := hrevM_q28 i j
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **ABSOLUTE headline (2,8) over true data**: with the representation and
L2-normalization slots, `Hbox` alone pins the gate at the named margin. -/
theorem absolute_true_q28 {w : CompactLogTest} {G_true : Matrix (Fin 8) (Fin 8) ℝ}
    {M_true : Matrix (Fin 8) (Fin 8) ℝ} {c : Fin 8 → ℝ}
    (hrep : ICgate w.convolutionSquare = c ⬝ᵥ (M_true *ᵥ c))
    (hker : Q28.R.mulVec c = 0)
    (hnorm : c ⬝ᵥ (G_true *ᵥ c) = 1)
    (hbox : Hbox GLo_q28 GHi_q28 MLo_q28 MHi_q28 G_true M_true) :
    ICgate w.convolutionSquare ≤ -mu_q28 := by
  have h := tbox_true_q28 G_true M_true hbox c hker
  have hmu : Q28.U = -mu_q28 := by
    rw [show mu_q28 = -Q28.U from rfl, neg_neg]
  rw [hmu] at h
  exact absolute_headline hrep h hnorm

theorem hUneg_q38 : Q38.U < 0 := by
  simp only [Q38.U]
  norm_num

theorem hUabs_q38 : |Q38.U| = mu_q38 := by
  simp only [mu_q38]
  exact abs_of_neg hUneg_q38

theorem hDtwo_q38 : Q38.Dc + Q38.Dc
    = (Q38.U • Q38.G - Q38.M) + (Q38.U • Q38.G - Q38.M).transpose := by
  rw [← Q38.hD]
  exact Q38.hDc

/-- **T-box (3,8)**: radius form over the (3,8) certificate data. -/
theorem tbox_q38 (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - Q38.G i j| ≤ radG_q38 i j)
    (hM : ∀ i j, |Mt i j - Q38.M i j| ≤ radM_q38 i j)
    (c : Fin 8 → ℝ) (hc : Q38.R.mulVec c = 0) :
    c ⬝ᵥ (Mt *ᵥ c) ≤ Q38.U * c ⬝ᵥ (Gt *ᵥ c) :=
  tbox_of_identities Q38.U Q38.G Q38.M Q38.R Q38.K Q38.V Q38.W Q38.Dc Q38.L Q38.d
    radG_q38 radM_q38 absK_q38 Lam_q38 absLam_q38 DredRad_q38 radp_q38 dd_q38 mu_q38
    Q38.hclosure hDtwo_q38 Q38.hPencil hUabs_q38
    hsymRadG_q38 hsymRadM_q38 habsK_q38 habsLam_q38
    hLamL_q38 hLLam_q38 hDredRad_q38 hRadp_q38
    hradpos_q38 hslack_q38 Gt Mt hG hM c hc

/-- **T-box true (3,8)**. -/
theorem tbox_true_q38 (G_true M_true : Matrix (Fin 8) (Fin 8) ℝ)
    (hbox : Hbox GLo_q38 GHi_q38 MLo_q38 MHi_q38 G_true M_true)
    (c : Fin 8 → ℝ) (hc : Q38.R.mulVec c = 0) :
    c ⬝ᵥ (M_true *ᵥ c) ≤ Q38.U * c ⬝ᵥ (G_true *ᵥ c) := by
  refine tbox_q38 G_true M_true ?_ ?_ c hc
  · intro i j
    obtain ⟨h1, h2⟩ := hbox.1 i j
    obtain ⟨h3, h4⟩ := hrevG_q38 i j
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hbox.2 i j
    obtain ⟨h3, h4⟩ := hrevM_q38 i j
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **ABSOLUTE headline (3,8) over true data**. -/
theorem absolute_true_q38 {w : CompactLogTest} {G_true : Matrix (Fin 8) (Fin 8) ℝ}
    {M_true : Matrix (Fin 8) (Fin 8) ℝ} {c : Fin 8 → ℝ}
    (hrep : ICgate w.convolutionSquare = c ⬝ᵥ (M_true *ᵥ c))
    (hker : Q38.R.mulVec c = 0)
    (hnorm : c ⬝ᵥ (G_true *ᵥ c) = 1)
    (hbox : Hbox GLo_q38 GHi_q38 MLo_q38 MHi_q38 G_true M_true) :
    ICgate w.convolutionSquare ≤ -mu_q38 := by
  have h := tbox_true_q38 G_true M_true hbox c hker
  have hmu : Q38.U = -mu_q38 := by
    rw [show mu_q38 = -Q38.U from rfl, neg_neg]
  rw [hmu] at h
  exact absolute_headline hrep h hnorm

theorem hUneg_q48 : Q48.U < 0 := by
  simp only [Q48.U]
  norm_num

theorem hUabs_q48 : |Q48.U| = mu_q48 := by
  simp only [mu_q48]
  exact abs_of_neg hUneg_q48

theorem hDtwo_q48 : Q48.Dc + Q48.Dc
    = (Q48.U • Q48.G - Q48.M) + (Q48.U • Q48.G - Q48.M).transpose := by
  rw [← Q48.hD]
  exact Q48.hDc

/-- **T-box (4,8)**: radius form over the (4,8) certificate data. -/
theorem tbox_q48 (Gt Mt : Matrix (Fin 8) (Fin 8) ℝ)
    (hG : ∀ i j, |Gt i j - Q48.G i j| ≤ radG_q48 i j)
    (hM : ∀ i j, |Mt i j - Q48.M i j| ≤ radM_q48 i j)
    (c : Fin 8 → ℝ) (hc : Q48.R.mulVec c = 0) :
    c ⬝ᵥ (Mt *ᵥ c) ≤ Q48.U * c ⬝ᵥ (Gt *ᵥ c) :=
  tbox_of_identities Q48.U Q48.G Q48.M Q48.R Q48.K Q48.V Q48.W Q48.Dc Q48.L Q48.d
    radG_q48 radM_q48 absK_q48 Lam_q48 absLam_q48 DredRad_q48 radp_q48 dd_q48 mu_q48
    Q48.hclosure hDtwo_q48 Q48.hPencil hUabs_q48
    hsymRadG_q48 hsymRadM_q48 habsK_q48 habsLam_q48
    hLamL_q48 hLLam_q48 hDredRad_q48 hRadp_q48
    hradpos_q48 hslack_q48 Gt Mt hG hM c hc

/-- **T-box true (4,8)**. -/
theorem tbox_true_q48 (G_true M_true : Matrix (Fin 8) (Fin 8) ℝ)
    (hbox : Hbox GLo_q48 GHi_q48 MLo_q48 MHi_q48 G_true M_true)
    (c : Fin 8 → ℝ) (hc : Q48.R.mulVec c = 0) :
    c ⬝ᵥ (M_true *ᵥ c) ≤ Q48.U * c ⬝ᵥ (G_true *ᵥ c) := by
  refine tbox_q48 G_true M_true ?_ ?_ c hc
  · intro i j
    obtain ⟨h1, h2⟩ := hbox.1 i j
    obtain ⟨h3, h4⟩ := hrevG_q48 i j
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · intro i j
    obtain ⟨h1, h2⟩ := hbox.2 i j
    obtain ⟨h3, h4⟩ := hrevM_q48 i j
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **ABSOLUTE headline (4,8) over true data**. -/
theorem absolute_true_q48 {w : CompactLogTest} {G_true : Matrix (Fin 8) (Fin 8) ℝ}
    {M_true : Matrix (Fin 8) (Fin 8) ℝ} {c : Fin 8 → ℝ}
    (hrep : ICgate w.convolutionSquare = c ⬝ᵥ (M_true *ᵥ c))
    (hker : Q48.R.mulVec c = 0)
    (hnorm : c ⬝ᵥ (G_true *ᵥ c) = 1)
    (hbox : Hbox GLo_q48 GHi_q48 MLo_q48 MHi_q48 G_true M_true) :
    ICgate w.convolutionSquare ≤ -mu_q48 := by
  have h := tbox_true_q48 G_true M_true hbox c hker
  have hmu : Q48.U = -mu_q48 := by
    rw [show mu_q48 = -Q48.U from rfl, neg_neg]
  rw [hmu] at h
  exact absolute_headline hrep h hnorm

end C1TboxPullthrough
end Source
end ConnesWeilRH
