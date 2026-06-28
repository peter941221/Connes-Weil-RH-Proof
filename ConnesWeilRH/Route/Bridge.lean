/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Exhaustion
import ConnesWeilRH.Source.CCM25Concrete.Package

/-!
# Restricted/full QW and final sign bridge interfaces

This module keeps the final scalar bridge and sign bridge visible as Lean data.
It does not prove the analytic bridge theorems.
-/

namespace ConnesWeilRH
namespace Route

open Source.CCM25Concrete

def PackageBackedCCM25WeilFormReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  WindowLambdaCompatibility inputs g lambda ∧
    W.qw g.weilTest g.weilTest =
      W.psi (W.convolutionStar g.weilTest g.weilTest) ∧
      W.psi (W.convolutionStar g.weilTest g.weilTest) =
        W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
            ∑ n ∈ W.globalPrimeIndexSet,
              W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest) ∧
        W.qwLambda lambda g.weilTest g.weilTest =
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
            W.polePairing g.weilTest -
              ∑ n ∈ W.restrictedPrimeIndexSet lambda,
                W.vonMangoldtWeight n *
                  W.primePowerPairing n g.weilTest g.weilTest ∧
          W.polePairing g.weilTest =
            W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) ∧
            (∑ n ∈ W.globalPrimeIndexSet,
              W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
              Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
                pkg ∧
            (∑ n ∈ W.restrictedPrimeIndexSet lambda,
              W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
              Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
                pkg

theorem package_backed_ccm25_weil_form_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hwindow : WindowLambdaCompatibility inputs g lambda) :
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg :=
  ⟨hwindow,
    ccm25_qw_definition_read_off_of_package pkg,
    ccm25_psi_sign_read_off_of_package pkg,
    ccm25_qw_lambda_formula_read_off_of_package pkg,
    ccm25_pole_normalization_read_off_of_package pkg,
    Source.CCM25Concrete.Package.global_finite_prime_sum_of_package_components
      pkg,
    Source.CCM25Concrete.Package.restricted_finite_prime_sum_of_package_components
      pkg⟩

structure SourceConvolutionSquareCompatibility
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda)
    : Prop where
  squareReadOff :
    F_g =
      inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest

theorem source_convolution_square_compatibility_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hF :
      F_g =
        inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) :
    SourceConvolutionSquareCompatibility inputs g lambda F_g pkg :=
  ⟨hF⟩

theorem source_square_qw_reads_square
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceConvolutionSquareCompatibility inputs g lambda F_g pkg) :
    inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.psi F_g := by
  rw [h.squareReadOff]
  exact Source.CCM25Concrete.Package.qw_definition_of_package_components pkg

theorem source_square_psi_sign_uses_square
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceConvolutionSquareCompatibility inputs g lambda F_g pkg) :
    inputs.ccm25.weilSymbols.psi F_g =
      inputs.ccm25.weilSymbols.poleFunctional F_g -
        inputs.ccm25.weilSymbols.archimedeanTerm F_g -
          ∑ n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet,
            inputs.ccm25.weilSymbols.finitePrimeTerm n F_g := by
  rw [h.squareReadOff]
  exact Source.CCM25Concrete.Package.psi_sign_of_package_components pkg

theorem source_square_finite_prime_visibility_target
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : SourceConvolutionSquareCompatibility inputs g lambda F_g pkg) :
    WeilFormSymbols.FinitePrimeVisibilityStatement
      inputs.ccm25.weilSymbols g.weilTest g.weilTest :=
  Source.CCM25Concrete.Package.finite_prime_normalization_of_package
    pkg g.weilTest g.weilTest

theorem source_square_visible_atoms_use_square
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceConvolutionSquareCompatibility inputs g lambda F_g pkg)
    (n : ℕ) :
    inputs.ccm25.weilSymbols.finitePrimeAtomVisible n F_g ↔
      inputs.ccm25.weilSymbols.finitePrimeAtomVisible n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest) := by
  rw [h.squareReadOff]

def SourceCommonTestTupleContract
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  WindowLambdaCompatibility inputs g lambda ∧
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg ∧
      SourceConvolutionSquareCompatibility inputs g lambda F_g pkg

theorem source_common_test_tuple_contract_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hwindow : WindowLambdaCompatibility inputs g lambda)
    (hF :
      F_g =
        inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) :
    SourceCommonTestTupleContract inputs g lambda F_g pkg :=
  ⟨hwindow, package_backed_ccm25_weil_form_read_off hwindow,
    source_convolution_square_compatibility_of_package hF⟩

theorem source_convolution_square_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    F_g =
      inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest :=
  h.2.2.squareReadOff

def SourceWindowControlsRestrictedRoute
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  WindowLambdaCompatibility inputs g lambda ∧
    WindowSupportContainment inputs g lambda

def SourceFinitePrimeSignOwnedByPackage
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  WindowLambdaCompatibility inputs g lambda ∧
    WeilFormSymbols.FinitePrimeNormalizationStatement W ∧
      (∑ n ∈ W.globalPrimeIndexSet,
        W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
        Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
          pkg ∧
      (∑ n ∈ W.restrictedPrimeIndexSet lambda,
        W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
        Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
          pkg

def PackageFinitePrimeSupportStabilization
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  let sourceTest := Source.CCM25Concrete.Package.source_test_of_package pkg
  (∀ n : ℕ,
    n ∈ W.globalPrimeIndexSet →
      Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex n ∧
        sourceTest.sourceAtomVisible n) ∧
    (∀ n : ℕ,
      n ∈ W.restrictedPrimeIndexSet lambda →
        Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex n ∧
          sourceTest.sourceAtomVisible n ∧
            Source.CCM25Concrete.PrimePowerSupport.SourceLambdaCut lambda n) ∧
      (∀ n : ℕ,
        W.finitePrimeAtomVisible n (W.convolutionStar g.weilTest g.weilTest) →
          Source.CCM25Concrete.PrimePowerSupport.SourceLambdaCut lambda n) ∧
        (∑ n ∈ W.globalPrimeIndexSet,
          W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg ∧
        (∑ n ∈ W.restrictedPrimeIndexSet lambda,
          W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            pkg

def PackageExactFinitePrimeSupportAtLambda
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let _packageWitness := pkg
  Nonempty
    (Source.CCM25Concrete.FinitePrimeExact.ExactSupportAtLambda
      inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda)

noncomputable def package_exact_finite_prime_support_at_lambda
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :
    Source.CCM25Concrete.FinitePrimeExact.ExactSupportAtLambda
      inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda :=
  Source.CCM25Concrete.FinitePrimeCertificate.exact_support_of_arithmetic_certificate
    (Source.CCM25Concrete.Package.formula_components
      pkg).restricted.finitePrimeSumReadOff.certificate

theorem package_exact_finite_prime_support_at_lambda_holds
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda} :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg :=
  ⟨package_exact_finite_prime_support_at_lambda pkg⟩

noncomputable def exact_support_of_package_exact_support
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg) :
    Source.CCM25Concrete.FinitePrimeExact.ExactSupportAtLambda
      inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda :=
  h.some

theorem visibility_at_lambda_of_package_exact_support
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg) :
    Source.CCM25Concrete.FinitePrimeExact.FinitePrimeVisibilityAtLambdaStatement
      inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda :=
  Source.CCM25Concrete.FinitePrimeExact.visibility_at_lambda_of_exact_support
    (exact_support_of_package_exact_support h)

theorem package_finite_prime_support_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda} :
    PackageFinitePrimeSupportStabilization inputs g lambda pkg := by
  dsimp [PackageFinitePrimeSupportStabilization]
  let exactSupport := package_exact_finite_prime_support_at_lambda pkg
  constructor
  · intro n hn
    exact ⟨
      Source.CCM25Concrete.Package.global_index_prime_power_of_package
        pkg hn,
      Source.CCM25Concrete.Package.global_index_visible_of_package
        pkg hn⟩
  constructor
  · intro n hn
    exact ⟨
      Source.CCM25Concrete.Package.restricted_index_prime_power_of_package
        pkg hn,
      Source.CCM25Concrete.Package.restricted_index_visible_of_package
        pkg hn,
      Source.CCM25Concrete.Package.restricted_index_lambda_cut_of_package
        pkg hn⟩
  constructor
  · intro n hn
    exact exactSupport.visibleAtomsInLambdaCut n hn
  constructor
  · exact
      Source.CCM25Concrete.Package.global_finite_prime_sum_of_package_components
        pkg
  · exact
      Source.CCM25Concrete.Package.restricted_finite_prime_sum_of_package_components
        pkg

structure FixedTestSupportCutoffData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) where
  oneLtLambda : 1 < lambda
  supportInWindow :
    inputs.ccm24.semilocalSymbols.supportInWindow
      g.semilocalTest g.window
  fourierSupportInWindow :
    inputs.ccm24.semilocalSymbols.fourierSupportInWindow
      g.semilocalTest g.window
  convolutionSupportTransported :
    inputs.ccm24.semilocalSymbols.convolutionSupportTransported
      g.semilocalTest g.window
  windowContainedInLambda :
    inputs.ccm24.semilocalSymbols.windowContainedInLambda
      g.window lambda
  lambdaCompatible :
    inputs.ccm24.semilocalSymbols.lambdaCompatible g.window lambda
  windowSupportContainment :
    WindowSupportContainment inputs g lambda
  windowLambdaCompatibility :
    WindowLambdaCompatibility inputs g lambda

def FixedTestSupportThresholdAtLarge
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  ∃ _cutoff : FixedTestSupportCutoffData inputs g lambda, True

theorem fixed_test_support_cutoff_data_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    FixedTestSupportCutoffData inputs g lambda where
  oneLtLambda := hlambda
  supportInWindow := g.supportInWindow
  fourierSupportInWindow := g.fourierSupportInWindow
  convolutionSupportTransported :=
    (support_transport_of_source_backed g).2
  windowContainedInLambda := g.windowContainedInLambda lambda hlambda
  lambdaCompatible := lambda_compatible_of_source_backed g hlambda
  windowSupportContainment :=
    window_support_containment_of_source_backed g hlambda
  windowLambdaCompatibility :=
    ⟨hlambda, window_support_containment_of_source_backed g hlambda,
      lambda_compatible_of_source_backed g hlambda⟩

theorem fixed_test_support_threshold_at_large_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    FixedTestSupportThresholdAtLarge inputs g lambda :=
  ⟨fixed_test_support_cutoff_data_of_source_backed hlambda, True.intro⟩

theorem window_support_containment_of_fixed_test_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedTestSupportThresholdAtLarge inputs g lambda) :
    WindowSupportContainment inputs g lambda :=
  h.choose.windowSupportContainment

theorem window_lambda_compatibility_of_fixed_test_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedTestSupportThresholdAtLarge inputs g lambda) :
    WindowLambdaCompatibility inputs g lambda :=
  h.choose.windowLambdaCompatibility

def PrimePowerAtomStabilizationAtLarge
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg ∧
    PackageFinitePrimeSupportStabilization inputs g lambda pkg

def FinitePrimeStabilizationAtLarge
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  FixedTestSupportThresholdAtLarge inputs g lambda ∧
    PrimePowerAtomStabilizationAtLarge inputs g lambda pkg

def SourceRestrictedQWLambdaDefinitionReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  CCM25QWLambdaFormulaReadOff inputs g lambda ∧
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg

def SourceFullQWDefinitionReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  CCM25QWDefinitionReadOff inputs g ∧
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg

def RestrictedFinitePrimeSupportStabilizes
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  FinitePrimeStabilizationAtLarge inputs g lambda pkg

def SourceArchimedeanPoleStabilityForRestriction
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  CCM25PoleNormalizationReadOff inputs g ∧
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg

theorem source_restricted_qw_lambda_definition_read_off_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    SourceRestrictedQWLambdaDefinitionReadOff inputs g lambda pkg :=
  ⟨ccm25_qw_lambda_formula_read_off_of_package pkg, h.2.1⟩

theorem source_full_qw_definition_read_off_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    SourceFullQWDefinitionReadOff inputs g lambda pkg :=
  ⟨ccm25_qw_definition_read_off_of_package pkg, h.2.1⟩

theorem source_archimedean_pole_stability_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg :=
  ⟨ccm25_pole_normalization_read_off_of_package pkg, h.2.1⟩

structure SourceQWLambdaRestrictionRows
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  restrictedDefinition :
    SourceRestrictedQWLambdaDefinitionReadOff inputs g lambda pkg
  fullDefinition :
    SourceFullQWDefinitionReadOff inputs g lambda pkg
  finitePrimeStabilization :
    RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg
  exactFinitePrimeSupport :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg
  archimedeanPoleStability :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg

def SourceQWLambdaIsRestrictionOfQW
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  ∃ _rows : SourceQWLambdaRestrictionRows inputs g lambda pkg, True

theorem source_qw_lambda_restriction_rows_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hstabilization :
      RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg) :
    SourceQWLambdaRestrictionRows inputs g lambda pkg where
  restrictedDefinition :=
    source_restricted_qw_lambda_definition_read_off_of_common_tuple hcommon
  fullDefinition :=
    source_full_qw_definition_read_off_of_common_tuple hcommon
  finitePrimeStabilization := hstabilization
  exactFinitePrimeSupport :=
    package_exact_finite_prime_support_at_lambda_holds
  archimedeanPoleStability :=
    source_archimedean_pole_stability_of_common_tuple hcommon

theorem source_qw_lambda_is_restriction_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hstabilization :
      RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg) :
    SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg :=
  ⟨source_qw_lambda_restriction_rows_of_common_tuple
    hcommon hstabilization, True.intro⟩

theorem restricted_definition_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceRestrictedQWLambdaDefinitionReadOff inputs g lambda pkg :=
  h.choose.restrictedDefinition

theorem full_definition_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceFullQWDefinitionReadOff inputs g lambda pkg :=
  h.choose.fullDefinition

theorem finite_prime_stabilization_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg :=
  h.choose.finitePrimeStabilization

theorem exact_finite_prime_support_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg :=
  h.choose.exactFinitePrimeSupport

theorem archimedean_pole_stability_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg :=
  h.choose.archimedeanPoleStability

theorem package_read_off_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg :=
  h.choose.restrictedDefinition.2

structure RestrictedToFullQWLargeLambdaThreshold
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (F_g : TestFunction) where
  lambda0 : ℝ
  oneLtLambda0 : 1 < lambda0
  thresholdPackage :
    Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      inputs.ccm25.weilSymbols g.weilTest lambda0
  thresholdTuple :
    SourceCommonTestTupleContract inputs g lambda0 F_g thresholdPackage
  supportThresholdAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        FixedTestSupportThresholdAtLarge inputs g lambda
  primePowerAtomStabilizationAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        ∀ pkg :
          Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
            inputs.ccm25.weilSymbols g.weilTest lambda,
          SourceCommonTestTupleContract inputs g lambda F_g pkg →
            PrimePowerAtomStabilizationAtLarge inputs g lambda pkg

def RestrictedToFullQWLambdaThreshold
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (F_g : TestFunction) : Prop :=
  ∃ _threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g, True

def RestrictedToFullQWScalarRestrictionEquality
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg ∧
    SourceCommonTestTupleContract inputs g lambda F_g pkg

theorem restricted_to_full_scalar_restriction_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hstabilization :
      RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg) :
    RestrictedToFullQWScalarRestrictionEquality
      inputs g lambda F_g pkg :=
  ⟨source_qw_lambda_is_restriction_of_common_tuple
    hcommon hstabilization, hcommon⟩

def RestrictedToFullQWLowerBoundEvidence
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceEndpointStripRemainderCdefDomination inputs g lambda L

def RestrictedToFullQWLowerBoundTransfer
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  RestrictedToFullQWScalarRestrictionEquality inputs g lambda F_g pkg ∧
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L

theorem restricted_to_full_lower_bound_transfer_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hscalar :
      RestrictedToFullQWScalarRestrictionEquality inputs g lambda F_g pkg)
    (hevidence :
      RestrictedToFullQWLowerBoundEvidence inputs g lambda L) :
    RestrictedToFullQWLowerBoundTransfer inputs g lambda F_g L pkg :=
  ⟨hscalar, hevidence⟩

theorem restricted_to_full_lower_bound_transfer_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hstabilization :
      RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg)
    (hevidence :
      RestrictedToFullQWLowerBoundEvidence inputs g lambda L) :
    RestrictedToFullQWLowerBoundTransfer inputs g lambda F_g L pkg :=
  restricted_to_full_lower_bound_transfer_of_parts
    (restricted_to_full_scalar_restriction_of_common_tuple
      hcommon hstabilization)
    hevidence

structure RestrictedToFullQWBridgeData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  largeLambdaThreshold :
    RestrictedToFullQWLargeLambdaThreshold inputs g F_g
  currentAboveThreshold :
    largeLambdaThreshold.lambda0 ≤ lambda
  scalarRestrictionEquality :
    RestrictedToFullQWScalarRestrictionEquality inputs g lambda F_g pkg
  exactFinitePrimeSupport :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg
  lowerBoundEvidence :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L

def restricted_to_full_bridge_data_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hevidence :
      RestrictedToFullQWLowerBoundEvidence inputs g lambda L) :
    RestrictedToFullQWBridgeData inputs g lambda F_g L pkg where
  largeLambdaThreshold := threshold
  currentAboveThreshold := habove
  scalarRestrictionEquality :=
    restricted_to_full_scalar_restriction_of_common_tuple hcommon
      ⟨threshold.supportThresholdAtLarge lambda habove,
        threshold.primePowerAtomStabilizationAtLarge
          lambda habove pkg hcommon⟩
  exactFinitePrimeSupport :=
    exact_finite_prime_support_of_qw_lambda_restriction
      (restricted_to_full_scalar_restriction_of_common_tuple hcommon
        ⟨threshold.supportThresholdAtLarge lambda habove,
          threshold.primePowerAtomStabilizationAtLarge
            lambda habove pkg hcommon⟩).1
  lowerBoundEvidence := hevidence

def RestrictedToFullQWBridgeContract
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  ∃ _row : RestrictedToFullQWBridgeData inputs g lambda F_g L pkg, True

theorem restricted_to_full_bridge_contract_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hevidence :
      RestrictedToFullQWLowerBoundEvidence inputs g lambda L) :
    RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg :=
  ⟨restricted_to_full_bridge_data_of_common_tuple
    threshold habove hcommon hevidence, True.intro⟩

def SourceQWUsesCommonTest
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  SourceCommonTestTupleContract inputs g lambda F_g pkg

theorem source_qw_common_tuple_of_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    SourceCommonTestTupleContract inputs g lambda F_g pkg :=
  h

theorem source_qw_square_compatibility_of_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    SourceConvolutionSquareCompatibility inputs g lambda F_g pkg :=
  h.2.2

theorem source_qw_package_read_off_of_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg :=
  h.2.1

theorem source_finite_prime_sign_owned_by_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg := by
  let hread := source_qw_package_read_off_of_common_test h
  exact
    ⟨hread.1,
      Source.CCM25Concrete.Package.finite_prime_normalization_of_package
        pkg,
      hread.2.2.2.2.2.1,
      hread.2.2.2.2.2.2⟩

def SourcePsiSignExpansion
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  SourceQWUsesCommonTest inputs g lambda F_g pkg

def SourceArchimedeanSignBridge
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (_g : SourceBackedFixedSTest inputs) : Prop :=
  CC20TraceLegality inputs a ∧
    CC20PositiveTraceNonnegative inputs a ∧
      (Source.cc20SignsAndNormalizations
        inputs.cc20.archimedeanSymbols).Holds ∧
        (Source.cc20MellinHalfDensityConvention
          inputs.cc20.archimedeanSymbols).Holds

def LegacySourceFinitePrimeSignOwnedByFormula
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  ∃ pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda,
    SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg

def SourcePoleSignInCC20LocalSum
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  SourceQWUsesCommonTest inputs g lambda F_g pkg

theorem source_psi_sign_expansion_of_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    SourcePsiSignExpansion inputs g lambda F_g pkg :=
  h

theorem source_pole_sign_in_cc20_local_sum_of_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    SourcePoleSignInCC20LocalSum inputs g lambda F_g pkg :=
  h

def SourceQWEqualsNegCC20WeilSum
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  SourceQWUsesCommonTest inputs g lambda F_g pkg ∧
    SourcePsiSignExpansion inputs g lambda F_g pkg ∧
      SourceArchimedeanSignBridge inputs a g ∧
        SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg ∧
          SourcePoleSignInCC20LocalSum inputs g lambda F_g pkg

def SourceQWNonnegativeToCC20Nonpositive
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  SourceQWEqualsNegCC20WeilSum inputs a g lambda F_g pkg

theorem source_qw_equals_neg_cc20_weil_sum_of_common_test
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceQWUsesCommonTest inputs g lambda F_g pkg)
    (hsign : SourceArchimedeanSignBridge inputs a g) :
    SourceQWEqualsNegCC20WeilSum inputs a g lambda F_g pkg :=
  ⟨hcommon,
    source_psi_sign_expansion_of_common_test hcommon,
    hsign,
    source_finite_prime_sign_owned_by_common_test hcommon,
    source_pole_sign_in_cc20_local_sum_of_common_test hcommon⟩

theorem source_qw_nonnegative_to_cc20_nonpositive_of_common_test
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceQWUsesCommonTest inputs g lambda F_g pkg)
    (hsign : SourceArchimedeanSignBridge inputs a g) :
    SourceQWNonnegativeToCC20Nonpositive inputs a g lambda F_g pkg :=
  source_qw_equals_neg_cc20_weil_sum_of_common_test hcommon hsign

structure FinalSignBridgeData
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
      inputs.ccm25.weilSymbols g.weilTest lambda) where
  sourceQWUsesCommonTest :
    SourceQWUsesCommonTest inputs g lambda F_g pkg
  sourceArchimedeanSignBridge :
    SourceArchimedeanSignBridge inputs a g

def final_sign_bridge_data_of_common_test
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceQWUsesCommonTest inputs g lambda F_g pkg)
    (hsign : SourceArchimedeanSignBridge inputs a g) :
    FinalSignBridgeData inputs a g lambda F_g pkg where
  sourceQWUsesCommonTest := hcommon
  sourceArchimedeanSignBridge := hsign

def FinalSignBridgeContract
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  ∃ _row : FinalSignBridgeData inputs a g lambda F_g pkg, True

theorem final_sign_bridge_contract_of_common_test
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceQWUsesCommonTest inputs g lambda F_g pkg)
    (hsign : SourceArchimedeanSignBridge inputs a g) :
    FinalSignBridgeContract inputs a g lambda F_g pkg :=
  ⟨final_sign_bridge_data_of_common_test hcommon hsign, True.intro⟩

structure RouteBridgeCertificate
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (L : RouteLedgers) where
  sourceTraceReadOff : SourceTraceReadOffData inputs g
  sourceBackedLedgers : SourceBackedLedgers inputs g L
  restrictedToFullQWBridge :
    RestrictedToFullQWBridgeContract inputs g sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      L sourceTraceReadOff.ccm25ArithmeticPackage
  finalSignBridge :
    FinalSignBridgeContract inputs sourceTraceReadOff.archimedeanTest g
      sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      sourceTraceReadOff.ccm25ArithmeticPackage

def route_bridge_certificate_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (sourceTraceReadOff : SourceTraceReadOffData inputs g)
    (signDefectClassification :
      SourceSignDefectClassification inputs g sourceTraceReadOff.lambda L)
    (restrictedToFullQWBridge :
      RestrictedToFullQWBridgeContract inputs g sourceTraceReadOff.lambda
        (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
        L sourceTraceReadOff.ccm25ArithmeticPackage)
    (finalSignBridge :
      FinalSignBridgeContract inputs sourceTraceReadOff.archimedeanTest g
        sourceTraceReadOff.lambda
        (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
        sourceTraceReadOff.ccm25ArithmeticPackage) :
    RouteBridgeCertificate inputs g L where
  sourceTraceReadOff := sourceTraceReadOff
  sourceBackedLedgers :=
    source_backed_ledgers_of_sign_defect_classification
      signDefectClassification
  restrictedToFullQWBridge := restrictedToFullQWBridge
  finalSignBridge := finalSignBridge

theorem restricted_to_full_qw_lambda_threshold_of_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullQWLambdaThreshold inputs g F_g :=
  ⟨h.choose.largeLambdaThreshold, True.intro⟩

theorem current_above_threshold_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    h.choose.largeLambdaThreshold.lambda0 ≤ lambda :=
  h.choose.currentAboveThreshold

theorem fixed_test_support_threshold_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    FixedTestSupportThresholdAtLarge inputs g lambda :=
  h.choose.largeLambdaThreshold.supportThresholdAtLarge lambda
    h.choose.currentAboveThreshold

theorem prime_power_atom_stabilization_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    PrimePowerAtomStabilizationAtLarge inputs g lambda pkg :=
  h.choose.largeLambdaThreshold.primePowerAtomStabilizationAtLarge lambda
    h.choose.currentAboveThreshold pkg h.choose.scalarRestrictionEquality.2

theorem finite_prime_stabilization_at_large_of_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    FinitePrimeStabilizationAtLarge inputs g lambda pkg :=
  ⟨fixed_test_support_threshold_of_large_lambda_threshold h,
    prime_power_atom_stabilization_of_large_lambda_threshold h⟩

theorem finite_prime_stabilization_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    PackageFinitePrimeSupportStabilization inputs g lambda pkg :=
  (prime_power_atom_stabilization_of_large_lambda_threshold h).2

theorem scalar_restriction_equality_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullQWScalarRestrictionEquality inputs g lambda F_g pkg :=
  h.choose.scalarRestrictionEquality

theorem exact_finite_prime_support_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg :=
  h.choose.exactFinitePrimeSupport

theorem lower_bound_evidence_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L :=
  h.choose.lowerBoundEvidence

theorem lower_bound_transfer_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullQWLowerBoundTransfer inputs g lambda F_g L pkg :=
  restricted_to_full_lower_bound_transfer_of_parts
    (scalar_restriction_equality_of_restricted_to_full_contract h)
    (lower_bound_evidence_of_restricted_to_full_contract h)

theorem final_sign_bridge_of_contract
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : FinalSignBridgeContract inputs a g lambda F_g pkg) :
    SourceQWEqualsNegCC20WeilSum inputs a g lambda F_g pkg :=
  source_qw_equals_neg_cc20_weil_sum_of_common_test
    h.choose.sourceQWUsesCommonTest
    h.choose.sourceArchimedeanSignBridge

theorem final_sign_nonnegative_to_nonpositive_of_contract
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : FinalSignBridgeContract inputs a g lambda F_g pkg) :
    SourceQWNonnegativeToCC20Nonpositive inputs a g lambda F_g pkg :=
  final_sign_bridge_of_contract h

theorem finite_prime_normalization_of_sign_owned_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg) :
    WeilFormSymbols.FinitePrimeNormalizationStatement inputs.ccm25.weilSymbols :=
  h.2.1

theorem finite_prime_normalization_of_legacy_sign_owned_formula
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : LegacySourceFinitePrimeSignOwnedByFormula inputs g lambda) :
    WeilFormSymbols.FinitePrimeNormalizationStatement inputs.ccm25.weilSymbols :=
  finite_prime_normalization_of_sign_owned_package h.choose_spec

theorem restricted_to_full_qw_bridge_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : RouteBridgeCertificate inputs g L) :
    RestrictedToFullQWBridgeContract inputs g h.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      L h.sourceTraceReadOff.ccm25ArithmeticPackage :=
  h.restrictedToFullQWBridge

theorem final_sign_bridge_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : RouteBridgeCertificate inputs g L) :
    FinalSignBridgeContract inputs h.sourceTraceReadOff.archimedeanTest g
      h.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      h.sourceTraceReadOff.ccm25ArithmeticPackage :=
  h.finalSignBridge

def source_backed_full_positivity_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : RouteBridgeCertificate inputs g L) :
    SourceBackedFullPositivity inputs g L :=
  ⟨h.sourceTraceReadOff, h.sourceBackedLedgers⟩

end Route
end ConnesWeilRH
