/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1RowBCardinalCarrier2722D

/-
# Record 2722F: exact capture of the stored row-B witness data

The 2722E screen decided the finite-data legs of the reopen motion on the
stored row-B configuration at model grade; this record makes them Lean
theorems.  The stored binary64 lists (8 healthy targets, the 56-node owner,
the correction values and the formal radius at `gamma_2 = 21.022039638771556`,
`re = 0.55`, `N = 5`) are exact dyadic rationals, so the capture carries no
error radius: every literal below is the exact value of the stored float.

Proved here with zero premises: `storedTripleSubset2722F`
(`{1/2, 1, 3/2} ⊆ storedTargets2722F`), `storedTargetsSubset2722F`
(`storedTargets2722F ⊆ storedNodes2722F`), and `storedYVanishes2722F`
(`storedY2722F = 0` on the shifted triple).  The stored correction function
`storedY2722F` is `1` at the node `rho`, `-1` at `1 - conj rho` and at
`rho + 1/2`, and `0` elsewhere (the record-1980 `target_value` table, tied
by the generator payload `results/2722f_rowB_capture_data.json`).

`fourPointContradictionRowBStored2722F` is the 2722D contradiction
instantiated at this data: the three finite-data hypotheses are discharged,
and the concrete lists, radius and value function are definitions instead
of quantified arguments.  What remains named (seven hypotheses): the rho
caps, the three cardinal-sum pins (artifact-grade support: the 2722E
screen; Lean certification is the next brick), and `hgate24` / `hprefix`
(the RH core under the map-103 freeze).  `rho` stays a named carrier point.

Honesty line: this record does not discharge any pin, the gate or the
prefix; `wired_hypotheses_removed = 3` counts only the finite data legs.
No producer GO, no RH claim; the `DEAD_ON_CURRENT_FAMILY` freeze is
unchanged.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RowBStoredCapture2722F

open Matrix
open CC20YoshidaConvolution
open CC20YoshidaConvolution.CompactLogTest
open CC20YoshidaNearZeros
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.UnscaledYoshidaSelectedOwner
open ConnesWeilRH.Dev.C1C3CarrierTransport
open C1ArchimedeanIntegrabilityGeneric
open C1CenterTwoCriterionBridge
open C1GateMatrixRepresentation
open C1HealthyYoshidaDetector
open C1HealthyYoshidaSpectralNegativity
open C1LocalConfigurationDomination
open C1OrbitWindowSemiLocalGate
open C1SpectralWeil
open C1SpectralTailBound
open C1SpectralSummability
open C1SameOwnerWeil
open C1TwoPointSpectralDecomposition
open C1FourPointSpectralPrefixTransport
open C1FourPointHighShellTail
open C1FourPointSpanGateCertificate
open C1SignedVarianceIdentity
open C1BipartiteMeanGapCertificate
open C1FourPointContradictionAssembly
open C1FourPointRowBWired2721
open C1ExplicitFiniteNodeCorrection
open C1StripTransport2722C
open C1RowBCardinalCarrier2722D
open scoped BigOperators

noncomputable section

/-- Exact dyadic literal of the stored formal radius 87.0719873427753. -/
def storedRadius2722F : ℝ :=
  ((6127146402364553 : ℝ) / 70368744177664)

theorem storedHRadius2722F : 0 < storedRadius2722F := by
  norm_num [storedRadius2722F]

/-- The stored row-B healthy targets (record-1980
`healthy_targets`). -/
def storedTargets2722F : Finset ℂ :=
  {
  ⟨((2476979795053773 : ℝ) / 4503599627370496),
      ((5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((2026619832316723 : ℝ) / 4503599627370496),
      ((5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((2476979795053773 : ℝ) / 4503599627370496),
      ((-5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((2026619832316723 : ℝ) / 4503599627370496),
      ((-5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((4728779608739021 : ℝ) / 4503599627370496),
      ((5917178117733711 : ℝ) / 281474976710656)⟩,
  (1 / 2 : ℂ),
  (1 : ℂ),
  (3 / 2 : ℂ)}

/-- The stored row-B owner (record-1980 `build_owner`: 48
known ball zeros, the orbit, and the targets). -/
def storedNodes2722F : Finset ℂ :=
  {
  ⟨((1 : ℝ) / 2),
      ((3978571430081297 : ℝ) / 281474976710656)⟩,
  ⟨((1 : ℝ) / 2),
      ((-3978571430081297 : ℝ) / 281474976710656)⟩,
  ⟨((1 : ℝ) / 2),
      ((5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((1 : ℝ) / 2),
      ((-5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((1 : ℝ) / 2),
      ((3519965277442521 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((-3519965277442521 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((2140960324737725 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((-2140960324737725 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((4635197846686455 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((-4635197846686455 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((1322446077737253 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((-1322446077737253 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((5758797740487047 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((-5758797740487047 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((3048871735671609 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((-3048871735671609 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((6756124363134027 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((-6756124363134027 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((1751261042181613 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((-1751261042181613 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((1863727500536955 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((-1863727500536955 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((7944103127967419 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((-7944103127967419 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((8352353914239387 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((-8352353914239387 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((8561311721741165 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((-8561311721741165 : ℝ) / 140737488355328)⟩,
  ⟨((1 : ℝ) / 2),
      ((4581887954876333 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((-4581887954876333 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((4720322026636147 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((152934154702833 : ℝ) / 2199023255552)⟩,
  ⟨((1 : ℝ) / 2),
      ((316954711375437 : ℝ) / 4398046511104)⟩,
  ⟨((1 : ℝ) / 2),
      ((665905501606627 : ℝ) / 8796093022208)⟩,
  ⟨((1 : ℝ) / 2),
      ((2714292757716727 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((2791435723263659 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((5834299379993871 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((745341278539281 : ℝ) / 8796093022208)⟩,
  ⟨((1 : ℝ) / 2),
      ((769000847989129 : ℝ) / 8796093022208)⟩,
  ⟨((1 : ℝ) / 2),
      ((3124692813607871 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((3254269399138099 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((3330248107429703 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((210821754192431 : ℝ) / 2199023255552)⟩,
  ⟨((1 : ℝ) / 2),
      ((6954627022713097 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((7129609938052989 : ℝ) / 70368744177664)⟩,
  ⟨((1 : ℝ) / 2),
      ((456189740691311 : ℝ) / 4398046511104)⟩,
  ⟨((1 : ℝ) / 2),
      ((3710073220983851 : ℝ) / 35184372088832)⟩,
  ⟨((1 : ℝ) / 2),
      ((7541320584301887 : ℝ) / 70368744177664)⟩,
  ⟨((2476979795053773 : ℝ) / 4503599627370496),
      ((5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((2026619832316723 : ℝ) / 4503599627370496),
      ((5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((2476979795053773 : ℝ) / 4503599627370496),
      ((-5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((2026619832316723 : ℝ) / 4503599627370496),
      ((-5917178117733711 : ℝ) / 281474976710656)⟩,
  ⟨((4728779608739021 : ℝ) / 4503599627370496),
      ((5917178117733711 : ℝ) / 281474976710656)⟩,
  (1 / 2 : ℂ),
  (1 : ℂ),
  (3 / 2 : ℂ)}

/-- The stored correction value function (record-1980
`target_value`): `1` at `rho`, `-1` at `1 - conj rho` and
`rho + 1/2`, zero elsewhere. -/
def storedY2722F : ℂ → ℂ :=
  fun z =>
    if z =
      (⟨((2476979795053773 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ) then
      (1 : ℂ)
    else if z =
      (⟨((2026619832316723 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ) then
      (-1 : ℂ)
    else if z =
      (⟨((4728779608739021 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ) then
      (-1 : ℂ)
    else 0

/-! ## The captured finite-data legs -/

theorem storedNeHalfRho2722F :
    ¬(((1 / 2 : ℂ) : ℂ) =
      (⟨((2476979795053773 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedNeHalfOmc2722F :
    ¬(((1 / 2 : ℂ) : ℂ) =
      (⟨((2026619832316723 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedNeHalfRph2722F :
    ¬(((1 / 2 : ℂ) : ℂ) =
      (⟨((4728779608739021 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedNeOneRho2722F :
    ¬(((1 : ℂ) : ℂ) =
      (⟨((2476979795053773 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedNeOneOmc2722F :
    ¬(((1 : ℂ) : ℂ) =
      (⟨((2026619832316723 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedNeOneRph2722F :
    ¬(((1 : ℂ) : ℂ) =
      (⟨((4728779608739021 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedNeThreeHalfRho2722F :
    ¬(((3 / 2 : ℂ) : ℂ) =
      (⟨((2476979795053773 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedNeThreeHalfOmc2722F :
    ¬(((3 / 2 : ℂ) : ℂ) =
      (⟨((2026619832316723 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedNeThreeHalfRph2722F :
    ¬(((3 / 2 : ℂ) : ℂ) =
      (⟨((4728779608739021 : ℝ) / 4503599627370496),
        ((5917178117733711 : ℝ) / 281474976710656)⟩ : ℂ)) := by
    intro h
    exact absurd (congrArg Complex.im h) (by norm_num)

theorem storedTripleSubset2722F :
    shiftedCC20Triple2722D ⊆ storedTargets2722F := by
  intro x hx
  simp only [shiftedCC20Triple2722D, storedTargets2722F, Finset.mem_insert,
    Finset.mem_singleton] at hx ⊢
  rcases hx with (rfl|rfl|rfl)
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    exact rfl

theorem storedTargetsSubset2722F :
    storedTargets2722F ⊆ storedNodes2722F := by
  intro x hx
  simp only [storedTargets2722F, storedNodes2722F, Finset.mem_insert,
    Finset.mem_singleton] at hx ⊢
  rcases hx with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl)
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inl
    exact rfl
  · apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    apply Or.inr
    exact rfl

theorem storedYVanishes2722F :
    ∀ s ∈ shiftedCC20Triple2722D, storedY2722F s = 0 := by
  intro s hs
  simp only [shiftedCC20Triple2722D, Finset.mem_insert,
    Finset.mem_singleton] at hs
  rcases hs with (rfl|rfl|rfl)
  · simp only [storedY2722F]
    rw [if_neg storedNeHalfRho2722F,
      if_neg storedNeHalfOmc2722F,
      if_neg storedNeHalfRph2722F]
  · simp only [storedY2722F]
    rw [if_neg storedNeOneRho2722F,
      if_neg storedNeOneOmc2722F,
      if_neg storedNeOneRph2722F]
  · simp only [storedY2722F]
    rw [if_neg storedNeThreeHalfRho2722F,
      if_neg storedNeThreeHalfOmc2722F,
      if_neg storedNeThreeHalfRph2722F]

/-! ## The carrier instance and the captured contradiction -/

def storedCarrierSourceTest2722F : CompactLogTest :=
  carrierSourceTest2722D storedTargets2722F storedNodes2722F
    storedRadius2722F storedHRadius2722F storedY2722F

/-- The 2722D row-B contradiction at the captured stored data.
The finite-data legs `hsub` / `htri` / `hy` are the proved
theorems above; `rho`, the caps, the three pins, the gate and
the prefix stay named hypotheses. -/
theorem fourPointContradictionRowBStored2722F
    (rho : sourceNontrivialZeroSet)
    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (hcontractPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        64 ≤ |t| →
          ‖cardinalSum storedTargets2722F (explicitSeed
            storedRadius2722F storedHRadius2722F) (fun _ => 1)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
            wiredQRowB2721)
    (hquarticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 * ‖cardinalSum storedTargets2722F
          (explicitSeed storedRadius2722F storedHRadius2722F)
          (fun _ => 1) ((sigma : Complex) + (t : Complex) *
            Complex.I)‖ ≤ wiredC4RowB2721)
    (hquadraticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 * ‖cardinalSum storedNodes2722F
          (explicitSeed storedRadius2722F storedHRadius2722F)
          storedY2722F ((sigma : Complex) + (t : Complex) *
            Complex.I)‖ ≤ wiredC2RowB2721)
    (hgate24 : ICgate
        ((fullFunctionalEquationOrbitAnnihilator
          (storedCarrierSourceTest2722F) rho.1).convolutionSquare) -
      24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator
          (storedCarrierSourceTest2722F) rho.1).involution.convolution
            (storedCarrierSourceTest2722F)) +
        ICgate ((storedCarrierSourceTest2722F).involution.convolution
          (fullFunctionalEquationOrbitAnnihilator
            (storedCarrierSourceTest2722F) rho.1))) +
      24 ^ 2 * ICgate
        ((storedCarrierSourceTest2722F).convolutionSquare) ≤ 0)
    (hprefix : (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (storedCarrierSourceTest2722F) rho.1)
            (storedCarrierSourceTest2722F) 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2)) :
    False :=
  fourPointContradictionRowBCarrier2722D storedTargets2722F
    storedNodes2722F storedTargetsSubset2722F
    storedTripleSubset2722F storedRadius2722F
    storedHRadius2722F storedY2722F storedYVanishes2722F
    rho hNorm hIm hcontractPin hquarticPin hquadraticPin
    hgate24 hprefix


end
end C1RowBStoredCapture2722F
end Source
end ConnesWeilRH
