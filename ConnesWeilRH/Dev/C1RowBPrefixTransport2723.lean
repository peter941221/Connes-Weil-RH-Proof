/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Dev.C1FourPointSpectralPrefixTransport
import ConnesWeilRH.Dev.C1HealthyYoshidaSpectralNegativity
import ConnesWeilRH.Dev.C1RowBStoredCapture2722F

/-!
# Record 2723: the wired `hprefix` proved from orbit data

The 2708 joint-acceptance contract's P2 duty names one remaining
identification: the finite-set span prefix (`hprefix` in the wired
row-B statements, a bound on the shell-range-six sum) must be derived
from the record-2722C transport theorem's orbit data, not assumed.
This record performs that derivation and rewires the stored row-B
contradiction on it.

Three theorems, in increasing concreteness:

* `dyadicShellIndex_abs_im_lt_six_2723` — the shell-index-six side
  condition from the wired imaginary-part cap `421/20`: the strict
  dyadic bound `2^6 = 64` exceeds `21.05` by `Nat.find_min'`.
* `rowBSpanPrefix_re_le_negXiMult_sq_2723` — the wired
  `hprefix` shape at ANY source test `g`, proved from
  {`hoff`, `h6`, `htarget`, `hzero`} by rewriting the shell-range sum
  to the finite prefix (`sum_spectralHeightShellPrefix_eq_shell_prefix`)
  and applying
  `finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport`.
* `fourPointContradictionRowBStored2723` — the 2722F stored
  contradiction with `hprefix` REPLACED by {`hright`, `htarget`,
  `hzero`}.

Honesty line: `hprefix` was an analytic sign estimate on the actual
owner; the replacements are pointwise facts (a first-order sign fact
and two equality conditions — the orbit interpolation values and the
in-ball non-orbit vanishing).  The entire summation sign argument now
lives inside a proved theorem, so the obligation shrank in kind, not
in count (premises 7 -> 9: `hprefix` removed, `hright` / `htarget` /
`hzero` added).  `htarget` and `hzero` are named residual duties —
their numeric support is the 2719 complete-owner identification and
the orbit-value measurement, and their Lean certification is a
separate brick.  No pin, `hgate24`, or `rho` cap is discharged.  No
producer GO, no RH claim; `DEAD_ON_CURRENT_FAMILY` unchanged.
-/

namespace ConnesWeilRH
namespace Source
namespace C1RowBPrefixTransport2723

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
open C1RowBStoredCapture2722F
open scoped BigOperators

noncomputable section

/-- The strict shell index stays below six under the wired
imaginary-part cap: `421 / 20 = 21.05 < 64 = 2 ^ 6`. -/
theorem dyadicShellIndex_abs_im_lt_six_2723
    (rho : sourceNontrivialZeroSet)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721) :
    dyadicShellIndex |rho.1.im| < 6 := by
  have hcap : |rho.1.im| ≤ 421 / 20 := by
    simpa only [wiredRhoImCapRowB2721] using hIm
  have hpow : |rho.1.im| < (2 : Real) ^ (5 + 1) := by
    norm_num
    linarith
  have hle : dyadicShellIndex |rho.1.im| ≤ 5 :=
    Nat.find_min' (exists_lt_two_pow_succ |rho.1.im|) hpow
  omega

/-- The wired `hprefix` shell-range-six span bound, proved from the
record-2722C transport theorem's orbit data at any source test `g`:
the finite-set to shell-prefix identification plus the full-orbit
transport inequality. -/
theorem rowBSpanPrefix_re_le_negXiMult_sq_2723
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (h6 : dyadicShellIndex |rho.1.im| < 6)
    (htarget :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt g (w.1 - 1 / 2) = negativeSourceOrbitValue rho.1 w)
    (hzero : ∀ z : sourceNontrivialZeroSet, z ∈ spectralHeightShellPrefix 6 →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt g.convolutionSquare (z.1 - 1 / 2) = 0) :
    (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator g rho.1) g 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2) := by
  have hmem : rho ∈ spectralHeightShellPrefix 6 :=
    (mem_spectralHeightShellPrefix_iff 6 rho).mpr h6
  have htransport :=
    finiteSpectralPrefix_re_le_neg_xiMultiplicity_mul_sq_of_fullOrbit_transport
      g rho 24 (spectralHeightShellPrefix 6) hmem hoff htarget hzero
  rw [← sum_spectralHeightShellPrefix_eq_shell_prefix]
  simpa only [neg_mul] using htransport

/-- The same span bound with the wired cap replacing the raw index
premise. -/
theorem rowBSpanPrefix_of_imCap_2723
    (g : CompactLogTest) (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (htarget :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt g (w.1 - 1 / 2) = negativeSourceOrbitValue rho.1 w)
    (hzero : ∀ z : sourceNontrivialZeroSet, z ∈ spectralHeightShellPrefix 6 →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt g.convolutionSquare (z.1 - 1 / 2) = 0) :
    (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator g rho.1) g 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2) :=
  rowBSpanPrefix_re_le_negXiMult_sq_2723 g rho hoff
    (dyadicShellIndex_abs_im_lt_six_2723 rho hIm) htarget hzero

/-- The stored-carrier `hprefix` instance, in exactly the shape the
2722F contradiction consumes. -/
theorem storedRowBPrefix2723
    (rho : sourceNontrivialZeroSet)
    (hright : (1 / 2 : Real) < rho.1.re)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (htarget :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt storedCarrierSourceTest2722F (w.1 - 1 / 2) =
          negativeSourceOrbitValue rho.1 w)
    (hzero : ∀ z : sourceNontrivialZeroSet, z ∈ spectralHeightShellPrefix 6 →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (storedCarrierSourceTest2722F).convolutionSquare
          (z.1 - 1 / 2) = 0) :
    (∑ k ∈ Finset.range 6, ∑' z : spectralHeightShell k,
        spectralTerm
          (annihilatorDetectorSpanVector
            (fullFunctionalEquationOrbitAnnihilator
              (storedCarrierSourceTest2722F) rho.1)
            (storedCarrierSourceTest2722F) 24).convolutionSquare
          z.1).re ≤
      -((xiMultiplicity rho : Real) * 24 ^ 2) :=
  rowBSpanPrefix_of_imCap_2723 storedCarrierSourceTest2722F rho
    (ne_of_gt hright) hIm htarget hzero

/-- The stored row-B contradiction with `hprefix` replaced by its
orbit-data premises.  Against `fourPointContradictionRowBStored2722F`
the analytic estimate is gone; the premise list is the caps, the
three cardinal-sum pins, `hgate24`, and the orbit data
{`hright`, `htarget`, `hzero`}. -/
theorem fourPointContradictionRowBStored2723
    (rho : sourceNontrivialZeroSet)
    (hNorm : ‖rho.1‖ ≤ wiredRhoNormCapRowB2721)
    (hIm : |rho.1.im| ≤ wiredRhoImCapRowB2721)
    (hright : (1 / 2 : Real) < rho.1.re)
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
    (htarget :
      ∀ w : FiniteMellinNode (sourceFunctionalEquationOrbit rho.1),
        laplaceAt storedCarrierSourceTest2722F (w.1 - 1 / 2) =
          negativeSourceOrbitValue rho.1 w)
    (hzero : ∀ z : sourceNontrivialZeroSet, z ∈ spectralHeightShellPrefix 6 →
      z.1 ∉ sourceFunctionalEquationOrbit rho.1 →
        laplaceAt (storedCarrierSourceTest2722F).convolutionSquare
          (z.1 - 1 / 2) = 0) :
    False :=
  fourPointContradictionRowBStored2722F rho hNorm hIm
    hcontractPin hquarticPin hquadraticPin hgate24
    (storedRowBPrefix2723 rho hright hIm htarget hzero)

end

end C1RowBPrefixTransport2723
end Source
end ConnesWeilRH
