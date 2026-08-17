import ConnesWeilRH.Dev.C1HealthyYoshidaDetector
import ConnesWeilRH.Source.CC20YoshidaConstruction
import ConnesWeilRH.Source.CCM25Concrete.SelectedYoshidaBridge

/-!
# C1HealthyYoshidaInterpolation - finite Mellin interpolation on the healthy owner

The existing finite-node interpolation proof constructs a compactly supported
positive-variable function and prescribes its Mellin values on any finite
node set.  Its final normalized-owner detector proof is not portable: it
uses the normalized additive-doubling convolution and its incompatible local
Weil sum.

This module transports only the valid linear interpolation layer through
`compactLogTestOfWindow`.  The bridge has the exact coordinate contract

```text
laplaceAt (compactLogTestOfWindow g) s = mellin (encode g) s.
```

Consequently the healthy compact-log owner has exact six-node interpolation
on the Yoshida nodes.  The transported test is triple-vanishing and detects
the off-line zero, but no positivity for its genuine Hermitian square is
claimed here.  That positivity is the remaining detector-construction step.
-/

namespace ConnesWeilRH
namespace Source
namespace C1HealthyYoshidaInterpolation

open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedYoshidaBridge
open CC20YoshidaConvolution
open CC20YoshidaInterpolationNode
open C1HealthyYoshidaDetector
open C1CenterTwoRHExit

/-- Exact healthy-owner realization of the six finite Yoshida Mellin nodes. -/
def HealthyExpandedLaplaceRealizes (rho : Complex) (g : CompactLogTest) : Prop :=
  forall n : CC20YoshidaExpandedMomentNode,
    CompactLogTest.laplaceAt g (CC20YoshidaExpandedMomentNode.nodeValue rho n) =
      CC20YoshidaExpandedMomentNode.targetValue n

/-- The compact-log bridge transports arbitrary values on the finite image of
the six Yoshida nodes.  The source interpolation uses only linear Mellin
evaluation and compact support; no normalized convolution operation is used. -/
theorem healthy_node_value_image_laplace_surjective_with_support
    {rho : Complex} {a b : Real}
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    forall y : CC20YoshidaExpandedMomentNode.NodeValueImage rho -> Complex,
      exists g : CompactLogTest,
        Function.support g.test ⊆ Set.Ioo (Real.log a) (Real.log b) /\
          forall z : CC20YoshidaExpandedMomentNode.NodeValueImage rho,
            CompactLogTest.laplaceAt g z.1 = y z := by
  intro y
  have hb : 0 < b := lt_trans (by norm_num) hone_b
  rcases CC20YoshidaExpandedMomentNode.fixed_window_node_value_image_mellin_surjective
      (rho := rho) ha ha_one hone_b y with
    ⟨g, _hcompact, hsupport, hvalue⟩
  refine ⟨compactLogTestOfWindow g ha hb hsupport, ?_, ?_⟩
  · exact compactLogTestOfWindow_support_subset g ha hb hsupport
  · intro z
    rw [CompactLogTest.laplaceAt_compactLogTestOfWindow_eq_mellin]
    simpa only [normalizedCC20TestSpace_mellinAt_eq,
      normalizedCC20ConcreteEvaluationData_mellinAt_eq_mellin] using hvalue z

/-- The support-free form of
`healthy_node_value_image_laplace_surjective_with_support`. -/
theorem healthy_node_value_image_laplace_surjective
    {rho : Complex} {a b : Real}
    (ha : 0 < a) (ha_one : a < 1) (hone_b : 1 < b) :
    forall y : CC20YoshidaExpandedMomentNode.NodeValueImage rho -> Complex,
      exists g : CompactLogTest,
        forall z : CC20YoshidaExpandedMomentNode.NodeValueImage rho,
          CompactLogTest.laplaceAt g z.1 = y z := by
  intro y
  rcases healthy_node_value_image_laplace_surjective_with_support
      (rho := rho) ha ha_one hone_b y with
    ⟨g, _hsupport, hvalue⟩
  exact ⟨g, hvalue⟩

/-- For every off-line source zero, the healthy owner has a compact-log test
with the exact Yoshida six-node values in the fixed positive window `(1/2, 2)`.
The half-density values are retained as interpolation data only; they do not
provide a healthy-owner positivity proof. -/
theorem exists_healthyExpandedLaplaceRealizes
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    exists g : CompactLogTest, HealthyExpandedLaplaceRealizes rho g := by
  rcases healthy_node_value_image_laplace_surjective
      (rho := rho) (a := (1 / 2 : Real)) (b := (2 : Real))
      (by norm_num) (by norm_num) (by norm_num)
      (fun z => CC20YoshidaExpandedMomentNode.targetValueOnNodeValue rho z.1) with
    ⟨g, hg⟩
  refine ⟨g, ?_⟩
  intro n
  have hn := hg ⟨CC20YoshidaExpandedMomentNode.nodeValue rho n,
    by simp [CC20YoshidaExpandedMomentNode.expandedNodeValueFinset]⟩
  rw [hn]
  exact CC20YoshidaExpandedMomentNode.targetValueOnNodeValue_eq_targetValue
    hrho hoff n

/-- The same six-node interpolation can be placed in the fixed narrow
positive window `(3/4, 5/4)`. Its Hermitian square is then supported strictly
between `-log 2` and `log 2`, so it has no finite prime-power contribution. -/
theorem exists_healthyExpandedLaplaceRealizes_primeFreeSquare
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    exists g : CompactLogTest,
      HealthyExpandedLaplaceRealizes rho g /\
        Function.support g.convolutionSquare.test ⊆
          Set.Ioo (-Real.log 2) (Real.log 2) := by
  rcases healthy_node_value_image_laplace_surjective_with_support
      (rho := rho)
      CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower_pos
      CCM25Concrete.SelectedYoshidaBridge.fixedWindowLower_lt_one
      CCM25Concrete.SelectedYoshidaBridge.one_lt_fixedWindowUpper
      (fun z => CC20YoshidaExpandedMomentNode.targetValueOnNodeValue rho z.1) with
    ⟨g, hsupport, hvalue⟩
  have hrealizes : HealthyExpandedLaplaceRealizes rho g := by
    intro n
    have hn := hvalue ⟨CC20YoshidaExpandedMomentNode.nodeValue rho n,
      by simp [CC20YoshidaExpandedMomentNode.expandedNodeValueFinset]⟩
    rw [hn]
    exact CC20YoshidaExpandedMomentNode.targetValueOnNodeValue_eq_targetValue
      hrho hoff n
  have hsquare :=
    CCM25Concrete.SelectedYoshidaBridge.convolutionSquare_support_subset_difference
      g hsupport
  have hwidth :=
    CCM25Concrete.SelectedYoshidaBridge.fixedWindow_logWidth_lt_log_two
  refine ⟨g, hrealizes, ?_⟩
  intro x hx
  rcases hsquare hx with ⟨hlower, hupper⟩
  constructor <;> linarith

/-- The exact interpolation data gives the three finite-vanishing equations
on the healthy test space. -/
theorem HealthyExpandedLaplaceRealizes.vanishesOn_cc20Triple
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyExpandedLaplaceRealizes rho g) :
    CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g := by
  intro p _hp
  change CompactLogTest.laplaceAt g (criticalVanishingPointValue p) = 0
  cases p
  · simpa [HealthyExpandedLaplaceRealizes,
      CC20YoshidaExpandedMomentNode.nodeValue,
      CC20YoshidaExpandedMomentNode.targetValue,
      criticalVanishingPointValue] using h CC20YoshidaExpandedMomentNode.zero
  · simpa [HealthyExpandedLaplaceRealizes,
      CC20YoshidaExpandedMomentNode.nodeValue,
      CC20YoshidaExpandedMomentNode.targetValue,
      criticalVanishingPointValue] using h CC20YoshidaExpandedMomentNode.half
  · simpa [HealthyExpandedLaplaceRealizes,
      CC20YoshidaExpandedMomentNode.nodeValue,
      CC20YoshidaExpandedMomentNode.targetValue,
      criticalVanishingPointValue] using h CC20YoshidaExpandedMomentNode.one

/-- The target-node value `-1` makes the interpolated healthy test detect its
off-line source zero. -/
theorem HealthyExpandedLaplaceRealizes.detects_rho
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyExpandedLaplaceRealizes rho g) :
    CompactLogTest.laplaceAt g rho ≠ 0 := by
  have htarget : CompactLogTest.laplaceAt g rho = (-1 : Complex) := by
    simpa [HealthyExpandedLaplaceRealizes,
      CC20YoshidaExpandedMomentNode.nodeValue,
      CC20YoshidaExpandedMomentNode.targetValue] using
      h CC20YoshidaExpandedMomentNode.targetRho
  rw [htarget]
  norm_num

/-- The interpolation layer provides every field of healthy detector data
except the genuine local-Weil positivity field.  Keeping that field explicit
prevents the normalized-owner positivity argument from crossing owners. -/
theorem healthyDetectorData_of_HealthyExpandedLaplaceRealizes
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyExpandedLaplaceRealizes rho g)
    (hpositive :
      0 < C1.healthyCC20TestSpace.weilLocalSum
        (C1.healthyCC20TestSpace.starConvolution g)) :
    HealthyYoshidaDetectorData rho g where
  compactSupportSmooth := C1.healthyCC20CompactSupportSmooth g
  vanishesOnF := h.vanishesOn_cc20Triple
  detectsRho := h.detects_rho
  weilSquareSumPositive := hpositive

/-- On a narrow-window interpolation root, strict positivity of the
archimedean term supplies the only remaining detector-data field. -/
theorem healthyDetectorData_of_HealthyExpandedLaplaceRealizes_of_archimedeanTerm_pos
    {rho : Complex} {g : CompactLogTest}
    (h : HealthyExpandedLaplaceRealizes rho g)
    (hsupport : Function.support g.convolutionSquare.test ⊆
      Set.Ioo (-Real.log 2) (Real.log 2))
    (harch : 0 < C1SameOwnerWeil.archimedeanTerm g.convolutionSquare) :
    HealthyYoshidaDetectorData rho g := by
  apply healthyDetectorData_of_HealthyExpandedLaplaceRealizes h
  apply
    (weilSquareSumPositive_iff_archimedeanTerm_pos_of_vanishesOn_cc20Triple
      g h.vanishesOn_cc20Triple hsupport).mpr
  exact harch

/-- Constructive interpolation endpoint: every off-line source zero has a
healthy compact-log root that is compactly smooth, triple-vanishing, and
detected at the prescribed value `-1`. -/
theorem exists_healthyYoshidaInterpolationRoot
    {rho : Complex}
    (hrho : RHDefinitionBridge.standard.sourceNontrivialZero rho)
    (hoff : rho.re ≠ 1 / 2) :
    exists g : CompactLogTest,
      C1.healthyCC20TestSpace.compactSupportSmooth g /\
      CC20VanishesOn C1.healthyCC20TestSpace cc20TripleFiniteVanishingSet g /\
      CompactLogTest.laplaceAt g rho = (-1 : Complex) := by
  rcases exists_healthyExpandedLaplaceRealizes hrho hoff with ⟨g, hg⟩
  refine ⟨g, C1.healthyCC20CompactSupportSmooth g,
    hg.vanishesOn_cc20Triple, ?_⟩
  simpa [HealthyExpandedLaplaceRealizes,
    CC20YoshidaExpandedMomentNode.nodeValue,
    CC20YoshidaExpandedMomentNode.targetValue] using
    hg CC20YoshidaExpandedMomentNode.targetRho

/-- The healthy detector-existence premise reduces exactly to the still-open
strict negative spectral value of an otherwise fully constructed six-node
interpolant.  The interpolation theorem supplies the compactness, three
vanishings, and off-line detection fields; the strict inequality supplies
only the genuine local-Weil positivity field. -/
theorem healthyCC20YoshidaDetectorExists_of_healthyExpandedLaplaceRealizes_and_spectral_neg
    (h : forall {rho : Complex},
      RHDefinitionBridge.standard.sourceNontrivialZero rho ->
        rho.re ≠ 1 / 2 ->
          exists g : CompactLogTest,
            HealthyExpandedLaplaceRealizes rho g /\
              C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0) :
    CC20YoshidaDetectorExists C1.healthyCC20TestSpace
      cc20TripleFiniteVanishingSet := by
  apply healthyCC20YoshidaDetectorExists_of_healthyDetectorData
  intro rho hrho hoff
  rcases h hrho hoff with ⟨g, hrealizes, hnegative⟩
  refine ⟨g, healthyDetectorData_of_HealthyExpandedLaplaceRealizes hrealizes ?_⟩
  exact (weilSquareSumPositive_iff_spectralWeilValue_neg g).mpr hnegative

/-- The complete healthy-owner exit written at the interpolation boundary.
For every hypothetical off-line source zero, the only detector-side input is
strict negativity of its constructed Hermitian square; the global
nonnegativity premise remains the independently guarded RH-level sign
condition. -/
theorem healthy_sourceRH_of_healthyExpandedLaplaceRealizes_and_spectral_sign
    (hdetector : forall {rho : Complex},
      RHDefinitionBridge.standard.sourceNontrivialZero rho ->
        rho.re ≠ 1 / 2 ->
          exists g : CompactLogTest,
            HealthyExpandedLaplaceRealizes rho g /\
              C1SpectralWeil.spectralWeilValue g.convolutionSquare < 0)
    (hsign : forall g : CompactLogTest,
      CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g ->
        0 <= C1SpectralWeil.spectralWeilValue g.convolutionSquare) :
    RHDefinitionBridge.standard.SourceRH :=
  healthy_spectral_nonneg_sourceRH_of_yoshida_detector
    (healthyCC20YoshidaDetectorExists_of_healthyExpandedLaplaceRealizes_and_spectral_neg
      hdetector)
    hsign

end C1HealthyYoshidaInterpolation
end Source
end ConnesWeilRH
