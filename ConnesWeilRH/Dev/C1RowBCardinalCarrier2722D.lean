/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1StripTransport2722C

/-!
# Record 2722D: the row-B contradiction on the explicit cardinal carrier

Record 2722C relocated the three wired strip premises to pins on the
explicit cardinal sum and named the two strip owners by identification
equalities `hbase` / `hcorr`.  This record instantiates the 2722C
variant at the record-1958 carrier family

```text
base       = cardinalOwner targets (explicitSeed r hr) (fun _ => 1)
correction = cardinalOwner nodes   (explicitSeed r hr) y
```

and PROVES the remaining transport-side premises instead of assuming
them:

* `hbase`, `hcorr` — gone: the owners are the carrier terms
  definitionally (`rfl`).
* `hvanish` (CC20 triple vanishing of the source test) — proved by
  interpolation: `healthyCC20TestSpace.mellinAt` is `laplaceAt`, the
  triple values are the absolute points `{0, 1/2, 1}`, and
  `selectedOwner_explicit_base_and_correction_target` reads the source
  test at `s - 1/2` as `y s`; so requiring the shifted triple
  `{1/2, 1, 3/2}` inside `targets ⊆ nodes` with `y = 0` there is a
  FINITE DATA condition, not an analytic premise.
* `hsupport` — proved by the convolution support growth law
  `convolutionIterate_convolution_support_subset_Ioo`: each factor
  lives in `Ioo (-(2 r + 1)) (2 r + 1)`, so the `n = 3` source test
  lives in `Ioo (-(5 * (2 r + 1))) (5 * (2 r + 1))`.

Kept as named hypotheses: the rho caps `hNorm` / `hIm`, the three
cardinal-sum pins (the record-2720 certified inequalities, artifact
`results/2720_p3_certified_strip_constants.json`, still tied by
`scripts/check_strip_transport_2722c.py`), and the gate/prefix lanes
`hgate24` / `hprefix` (P5 sign and P2 — the RH core itself).

Honesty line: this record does not produce the row-B witness.  The
node sets stay quantified; supplying the stored row-B zero data and
discharging pins/gate/prefix on it is the remaining reopen motion.
No producer GO, no RH claim; the map-103 freeze is unchanged.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RowBCardinalCarrier2722D

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
open scoped BigOperators

noncomputable section

/-- The CC20 critical triple `{0, 1/2, 1}` in the centered coordinate
of `selectedOwner_laplaceAt_sourceTest_centered`: the source-test value
at `w` is the correction's `y` at the shifted node `s = w + 1 / 2`. -/
def shiftedCC20Triple2722D : Finset ℂ :=
  {(1 / 2 : ℂ), 1, (3 / 2 : ℂ)}

/-- Triple-vanishing discharged by interpolation: every carrier member
whose target set contains the shifted triple and whose values vanish
there satisfies `CC20VanishesOn C1.healthyCC20TestSpace
cc20TripleFiniteVanishingSet` on its source test. -/
theorem carrier_cc20Vanishes2722D
    (targets nodes : Finset ℂ) (hsub : targets ⊆ nodes)
    (htri : shiftedCC20Triple2722D ⊆ targets)
    (r : ℝ) (hr : 0 < r) (y : ℂ → ℂ)
    (hy : ∀ s ∈ shiftedCC20Triple2722D, y s = 0) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet
      (selectedOwner (cardinalOwner targets (explicitSeed r hr) (fun _ => 1))
        (cardinalOwner nodes (explicitSeed r hr) y) 3).sourceTest := by
  intro p _hp
  change CompactLogTest.laplaceAt
      (selectedOwner (correction targets (explicitSeed r hr) (fun _ => 1))
        (correction nodes (explicitSeed r hr) y) 3).sourceTest
      (criticalVanishingPointValue p) = 0
  cases p
  · have hT := selectedOwner_explicit_base_and_correction_target
      targets nodes hsub r hr y 3
      (htri (by simp [shiftedCC20Triple2722D] : (1 / 2 : ℂ) ∈
        shiftedCC20Triple2722D))
    rw [show ((1 / 2 : ℂ) - 1 / 2) = (0 : ℂ) by ring] at hT
    exact hT.trans (hy _ (by simp [shiftedCC20Triple2722D]))
  · have hT := selectedOwner_explicit_base_and_correction_target
      targets nodes hsub r hr y 3
      (htri (by simp [shiftedCC20Triple2722D] : (1 : ℂ) ∈
        shiftedCC20Triple2722D))
    rw [show ((1 : ℂ) - 1 / 2 : ℂ) = (1 / 2 : ℂ) by ring] at hT
    exact hT.trans (hy _ (by simp [shiftedCC20Triple2722D]))
  · have hT := selectedOwner_explicit_base_and_correction_target
      targets nodes hsub r hr y 3
      (htri (by simp [shiftedCC20Triple2722D] : (3 / 2 : ℂ) ∈
        shiftedCC20Triple2722D))
    rw [show ((3 / 2 : ℂ) - 1 / 2 : ℂ) = (1 : ℂ) by ring] at hT
    exact hT.trans (hy _ (by simp [shiftedCC20Triple2722D]))

/-- Support discharged by the growth law: for every `0 < r` and every
node pair, the `n = 3` source test of the carrier is supported in the
explicit radius `5 * (2 * r + 1)`. -/
theorem carrier_sourceTest_support2722D
    (targets nodes : Finset ℂ) (r : ℝ) (hr : 0 < r) (y : ℂ → ℂ) :
    Function.support
        (selectedOwner (cardinalOwner targets (explicitSeed r hr) (fun _ => 1))
          (cardinalOwner nodes (explicitSeed r hr) y) 3).sourceTest.test ⊆
      Set.Ioo (-(5 * (2 * r + 1))) (5 * (2 * r + 1)) := by
  have hIoo : Set.Icc (-(2 * r)) (2 * r) ⊆
      Set.Ioo (-(2 * r + 1)) (2 * r + 1) := by
    intro x hx
    exact ⟨by linarith [hx.1, hx.2], by linarith [hx.1, hx.2]⟩
  have hbaseS : Function.support
      (cardinalOwner targets (explicitSeed r hr) (fun _ => 1)).test ⊆
      Set.Ioo (-(2 * r + 1)) (2 * r + 1) :=
    Set.Subset.trans (explicitSeed_correction_support targets r hr
      (fun _ => 1)) hIoo
  have hcorrS : Function.support
      (cardinalOwner nodes (explicitSeed r hr) y).test ⊆
      Set.Ioo (-(2 * r + 1)) (2 * r + 1) :=
    Set.Subset.trans (explicitSeed_correction_support nodes r hr y) hIoo
  have hconv := convolutionIterate_convolution_support_subset_Ioo
    (cardinalOwner targets (explicitSeed r hr) (fun _ => 1))
    (cardinalOwner nodes (explicitSeed r hr) y) hbaseS hcorrS 3
  have hcast : ((3 + 1 : ℕ) : ℝ) = (4 : ℝ) := by norm_num
  rw [hcast] at hconv
  have hradius : Function.support
      ((convolutionIterate (cardinalOwner targets (explicitSeed r hr) (fun _ => 1))
          3).convolution (cardinalOwner nodes (explicitSeed r hr) y)).test ⊆
      Set.Ioo (-(5 * (2 * r + 1))) (5 * (2 * r + 1)) := by
    convert hconv using 1
    all_goals ring
  simpa only [selectedOwner_sourceTest] using
    halfDensityShift_support_subset
      ((convolutionIterate (cardinalOwner targets (explicitSeed r hr) (fun _ => 1))
          3).convolution (cardinalOwner nodes (explicitSeed r hr) y))
      hradius

/-- The `n = 3` source test of the 1958 carrier as a single short name,
so the gate/prefix hypotheses below keep the record-2721 line layout
(a multi-line carrier term at each site makes the indentation parser
attach continuation lines to `ICgate` instead of `.convolution`).
Unfolds definitionally to the carrier term the transport theorems
prove about. -/
def carrierSourceTest2722D (targets nodes : Finset ℂ) (r : ℝ) (hr : 0 < r)
    (y : ℂ → ℂ) : CompactLogTest :=
  (selectedOwner (cardinalOwner targets (explicitSeed r hr) (fun _ => 1))
    (cardinalOwner nodes (explicitSeed r hr) y) 3).sourceTest

/-- Record 2722D: the wired row-B contradiction on the explicit
1958 cardinal carrier.  Compared with `fourPointContradictionRowBWired
2722C`, the premises `hvanish`, `hsupport`, `hbase`, `hcorr` are GONE:
vanishing and support are theorems of the carrier family
(`carrier_cc20Vanishes2722D`, `carrier_sourceTest_support2722D`), and
the identification equalities are definitional.  What remains named:
the rho caps, the three cardinal-sum pins (record-2720 certified
inequalities, proxy-tie doctrine), and `hgate24` / `hprefix` (P5 gate
sign and P2 prefix — the RH core).  The data conditions
`hsub` / `htri` / `hy` are finite membership requirements on the node
sets, satisfied by adding the shifted triple to any reopen witness.
No producer GO, no RH claim. -/
theorem fourPointContradictionRowBCarrier2722D
    (targets nodes : Finset ℂ) (hsub : targets ⊆ nodes)
    (htri : shiftedCC20Triple2722D ⊆ targets)
    (r : ℝ) (hr : 0 < r) (y : ℂ → ℂ)
    (hy : ∀ s ∈ shiftedCC20Triple2722D, y s = 0)
    (rho : sourceNontrivialZeroSet)
    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (hcontractPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        64 ≤ |t| →
          ‖cardinalSum targets (explicitSeed r hr) (fun _ => 1)
            ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
            wiredQRowB2721)
    (hquarticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 4 * ‖cardinalSum targets (explicitSeed r hr)
          (fun _ => 1) ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC4RowB2721)
    (hquadraticPin : ∀ sigma ∈ Set.Icc (0 : Real) 1, ∀ t : Real,
        ‖t / (2 * Real.pi)‖ ^ 2 * ‖cardinalSum nodes (explicitSeed r hr) y
          ((sigma : Complex) + (t : Complex) * Complex.I)‖ ≤
          wiredC2RowB2721)
    (hgate24 : ICgate
        ((fullFunctionalEquationOrbitAnnihilator
          (carrierSourceTest2722D targets nodes r hr y) rho.1).convolutionSquare) -
      24 * (ICgate ((fullFunctionalEquationOrbitAnnihilator
          (carrierSourceTest2722D targets nodes r hr y) rho.1).involution.convolution
            (carrierSourceTest2722D targets nodes r hr y)) +
        ICgate ((carrierSourceTest2722D targets nodes r hr y).involution.convolution
          (fullFunctionalEquationOrbitAnnihilator
            (carrierSourceTest2722D targets nodes r hr y) rho.1))) +
      24 ^ 2 * ICgate
        ((carrierSourceTest2722D targets nodes r hr y).convolutionSquare) ≤ 0)
    (hprefix : (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (carrierSourceTest2722D targets nodes r hr y) rho.1)
            (carrierSourceTest2722D targets nodes r hr y) 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2)) :
    False := by
  refine fourPointContradictionRowBWired2722C targets nodes
    (explicitSeed r hr) (fun _ => 1) y
    (cardinalOwner targets (explicitSeed r hr) (fun _ => 1))
    (cardinalOwner nodes (explicitSeed r hr) y) rho
    (B := 5 * (2 * r + 1))
    hNorm hIm
    (carrier_cc20Vanishes2722D targets nodes hsub htri r hr y hy)
    (carrier_sourceTest_support2722D targets nodes r hr y)
    rfl rfl hcontractPin hquarticPin hquadraticPin hgate24 hprefix

end

end C1RowBCardinalCarrier2722D
end Source
end ConnesWeilRH
