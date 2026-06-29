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

structure PackageBackedCCM25WeilFormReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop where
  windowLambdaCompatibility : WindowLambdaCompatibility inputs g lambda
  qwDefinitionReadOff :
    let W := inputs.ccm25.weilSymbols
    W.qw g.weilTest g.weilTest =
      W.psi (W.convolutionStar g.weilTest g.weilTest)
  psiSignReadOff :
    let W := inputs.ccm25.weilSymbols
    W.psi (W.convolutionStar g.weilTest g.weilTest) =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          ∑ n ∈ W.globalPrimeIndexSet,
            W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)
  qwLambdaFormulaReadOff :
    let W := inputs.ccm25.weilSymbols
    W.qwLambda lambda g.weilTest g.weilTest =
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
          ∑ n ∈ W.restrictedPrimeIndexSet lambda,
            W.vonMangoldtWeight n *
              W.primePowerPairing n g.weilTest g.weilTest
  poleNormalizationReadOff :
    let W := inputs.ccm25.weilSymbols
    W.polePairing g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest)
  globalFinitePrimeSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg
  restrictedFinitePrimeSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        pkg
  psiSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.psi (W.convolutionStar g.weilTest g.weilTest) =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg
  qwSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.qw g.weilTest g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg
  qwLambdaSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.qwLambda lambda g.weilTest g.weilTest =
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
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
  { windowLambdaCompatibility := hwindow
    qwDefinitionReadOff := ccm25_qw_definition_read_off_of_package pkg
    psiSignReadOff := ccm25_psi_sign_read_off_of_package pkg
    qwLambdaFormulaReadOff := ccm25_qw_lambda_formula_read_off_of_package pkg
    poleNormalizationReadOff := ccm25_pole_normalization_read_off_of_package pkg
    globalFinitePrimeSumReadOff :=
      Source.CCM25Concrete.Package.global_finite_prime_sum_of_package_components
        pkg
    restrictedFinitePrimeSumReadOff :=
      Source.CCM25Concrete.Package.restricted_finite_prime_sum_of_package_components
        pkg
    psiSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.psi_source_evaluator_of_package_components
        pkg
    qwSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.qw_source_evaluator_of_package_components
        pkg
    qwLambdaSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.qw_lambda_formula_source_evaluator_of_package_components
        pkg }

theorem package_backed_global_finite_prime_sum
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg :=
  h.globalFinitePrimeSumReadOff

theorem package_backed_restricted_finite_prime_sum
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        pkg :=
  h.restrictedFinitePrimeSumReadOff

theorem package_backed_restricted_index_set_eq_global
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.restrictedPrimeIndexSet lambda = W.globalPrimeIndexSet :=
  Source.CCM25Concrete.Package.restricted_index_set_eq_global_of_package
    pkg

theorem package_backed_source_restricted_sum_eq_global
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg :=
  Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum_eq_global
    pkg

theorem package_backed_source_global_sum_eq_common_atoms
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg :=
  Source.CCM25Concrete.Package.source_global_sum_eq_common_atoms_of_package
    pkg

theorem package_backed_source_restricted_sum_eq_common_atoms
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
        pkg :=
  Source.CCM25Concrete.Package.source_restricted_sum_eq_common_atoms_of_package
    pkg

theorem package_backed_source_common_restricted_sum_eq_common_global
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg := by
  exact
    Source.CCM25Concrete.Package.source_common_restricted_sum_eq_common_global_of_package
      pkg

theorem package_backed_psi_source_evaluator
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.psi (W.convolutionStar g.weilTest g.weilTest) =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg :=
  h.psiSourceEvaluatorReadOff

theorem package_backed_psi_source_evaluator_common_atoms
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.psi (W.convolutionStar g.weilTest g.weilTest) =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
            pkg :=
  Source.CCM25Concrete.Package.psi_source_evaluator_common_atoms_of_package
    pkg

theorem package_backed_qw_source_evaluator
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.qw g.weilTest g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg :=
  h.qwSourceEvaluatorReadOff

theorem package_backed_qw_source_evaluator_common_atoms
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.qw g.weilTest g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
            pkg :=
  Source.CCM25Concrete.Package.qw_source_evaluator_common_atoms_of_package
    pkg

theorem package_backed_qw_lambda_source_evaluator
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.qwLambda lambda g.weilTest g.weilTest =
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            pkg :=
  h.qwLambdaSourceEvaluatorReadOff

theorem package_backed_qw_lambda_source_evaluator_common_atoms
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.qwLambda lambda g.weilTest g.weilTest =
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
            pkg :=
  Source.CCM25Concrete.Package.qw_lambda_formula_source_evaluator_common_atoms_of_package
    pkg

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

structure SourceCommonTestTupleContract
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop where
  windowLambdaCompatibility : WindowLambdaCompatibility inputs g lambda
  packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg
  squareCompatibility :
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
  { windowLambdaCompatibility := hwindow
    packageReadOff := package_backed_ccm25_weil_form_read_off hwindow
    squareCompatibility := source_convolution_square_compatibility_of_package hF }

theorem source_convolution_square_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    F_g =
      inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest :=
  h.squareCompatibility.squareReadOff

structure SourceWindowControlsRestrictedRoute
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) where
  windowLambdaCompatibility : WindowLambdaCompatibility inputs g lambda
  windowSupportContainment : WindowSupportContainment inputs g lambda

theorem source_window_controls_restricted_route_of_window_lambda
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : WindowLambdaCompatibility inputs g lambda) :
    SourceWindowControlsRestrictedRoute inputs g lambda where
  windowLambdaCompatibility := h
  windowSupportContainment := h.windowSupportContainment

theorem window_lambda_compatibility_of_source_window_controls
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : SourceWindowControlsRestrictedRoute inputs g lambda) :
    WindowLambdaCompatibility inputs g lambda :=
  h.windowLambdaCompatibility

theorem window_support_containment_of_source_window_controls
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : SourceWindowControlsRestrictedRoute inputs g lambda) :
    WindowSupportContainment inputs g lambda :=
  h.windowSupportContainment

structure SourceFinitePrimeSignOwnedByPackage
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  windowLambdaCompatibility : WindowLambdaCompatibility inputs g lambda
  finitePrimeConcreteObject :
    Source.CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda
  finitePrimeNormalization :
    WeilFormSymbols.FinitePrimeNormalizationStatement inputs.ccm25.weilSymbols
  globalFinitePrimeSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum pkg
  restrictedFinitePrimeSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        pkg
  globalVonMangoldtPairingSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n *
        W.primePowerPairing n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg
  restrictedVonMangoldtPairingSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n *
        W.primePowerPairing n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
        pkg

structure PackageFinitePrimeSupportStabilization
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  globalIndexSourceData :
    ∀ n : ℕ,
      n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet →
        Source.CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
          Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
          (Source.CCM25Concrete.Package.source_test_of_package
            pkg).sourceAtomVisible n
  restrictedIndexSourceData :
    ∀ n : ℕ,
      n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda →
        Source.CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
          Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
          (Source.CCM25Concrete.Package.source_test_of_package
            pkg).sourceAtomVisible lambda n
  visibleAtomsInLambdaCut :
    ∀ n : ℕ,
      inputs.ccm25.weilSymbols.finitePrimeAtomVisible n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest) →
        Source.CCM25Concrete.PrimePowerSupport.SourceLambdaCut lambda n
  restrictedIndexSet_eq_global :
    inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda =
      inputs.ccm25.weilSymbols.globalPrimeIndexSet
  sourceRestrictedSum_eq_global :
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg
  globalFinitePrimeSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet,
      inputs.ccm25.weilSymbols.finitePrimeTerm n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg
  restrictedFinitePrimeSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda,
      inputs.ccm25.weilSymbols.finitePrimeTerm n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        pkg
  globalVonMangoldtPairingSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet,
      inputs.ccm25.weilSymbols.vonMangoldtWeight n *
        inputs.ccm25.weilSymbols.primePowerPairing
          n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg
  restrictedVonMangoldtPairingSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda,
      inputs.ccm25.weilSymbols.vonMangoldtWeight n *
        inputs.ccm25.weilSymbols.primePowerPairing
          n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
        pkg

abbrev PackageExactFinitePrimeSupportAtLambda
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (_pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
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
  Source.CCM25Concrete.Package.exact_support_of_package pkg

theorem package_exact_support_uses_common_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :
    package_exact_finite_prime_support_at_lambda pkg =
      Source.CCM25Concrete.FinitePrimeCertificate.exact_support_of_arithmetic_certificate
        (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate :=
  Source.CCM25Concrete.Package.exact_support_uses_common_certificate_of_package
    pkg

theorem package_exact_support_source_test_eq_package_source_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :
    (package_exact_finite_prime_support_at_lambda pkg).sourceAtomVisible =
      (Source.CCM25Concrete.Package.source_test_of_package pkg).sourceAtomVisible := by
  exact
    Source.CCM25Concrete.Package.exact_support_source_test_eq_package_source_test
      pkg

noncomputable def package_exact_finite_prime_support_at_lambda_holds
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda} :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg :=
  package_exact_finite_prime_support_at_lambda pkg

noncomputable def exact_support_of_package_exact_support
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg) :
    Source.CCM25Concrete.FinitePrimeExact.ExactSupportAtLambda
      inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda :=
  h

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
  let exactSupport := package_exact_finite_prime_support_at_lambda pkg
  exact
  { globalIndexSourceData := by
      intro n hn
      exact
      Source.CCM25Concrete.Package.common_certificate_global_index_source_data_of_package
        pkg hn,
    restrictedIndexSourceData := by
      intro n hn
      exact
      Source.CCM25Concrete.Package.common_certificate_restricted_index_source_data_of_package
        pkg hn,
    visibleAtomsInLambdaCut := by
      intro n hn
      exact exactSupport.visibleAtomsInLambdaCut n hn
    restrictedIndexSet_eq_global :=
      Source.CCM25Concrete.Package.restricted_index_set_eq_global_of_package
        pkg
    sourceRestrictedSum_eq_global :=
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum_eq_global
        pkg
    globalFinitePrimeSumReadOff :=
      Source.CCM25Concrete.Package.global_finite_prime_sum_of_package_components
        pkg
    restrictedFinitePrimeSumReadOff :=
      Source.CCM25Concrete.Package.restricted_finite_prime_sum_of_package_components
        pkg
    globalVonMangoldtPairingSumReadOff :=
      Source.CCM25Concrete.Package.finite_prime_concrete_object_global_pairing_sum_read_off
        pkg
    restrictedVonMangoldtPairingSumReadOff :=
      Source.CCM25Concrete.Package.finite_prime_concrete_object_restricted_pairing_sum_read_off
        pkg }

theorem global_index_source_data_of_package_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageFinitePrimeSupportStabilization inputs g lambda pkg)
    {n : ℕ} (hn : n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet) :
    Source.CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
      Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
      (Source.CCM25Concrete.Package.source_test_of_package
        pkg).sourceAtomVisible n :=
  h.globalIndexSourceData n hn

theorem restricted_index_source_data_of_package_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageFinitePrimeSupportStabilization inputs g lambda pkg)
    {n : ℕ}
    (hn : n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda) :
    Source.CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
      Source.CCM25Concrete.PrimePowerArithmetic.SourcePrimePowerIndex
      (Source.CCM25Concrete.Package.source_test_of_package
        pkg).sourceAtomVisible lambda n :=
  h.restrictedIndexSourceData n hn

theorem visible_atom_lambda_cut_of_package_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageFinitePrimeSupportStabilization inputs g lambda pkg)
    {n : ℕ}
    (hn :
      inputs.ccm25.weilSymbols.finitePrimeAtomVisible n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest)) :
    Source.CCM25Concrete.PrimePowerSupport.SourceLambdaCut lambda n :=
  h.visibleAtomsInLambdaCut n hn

theorem restricted_index_set_eq_global_of_package_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageFinitePrimeSupportStabilization inputs g lambda pkg) :
    inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda =
      inputs.ccm25.weilSymbols.globalPrimeIndexSet :=
  h.restrictedIndexSet_eq_global

theorem finite_prime_term_sums_match_of_package_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageFinitePrimeSupportStabilization inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg :=
  h.sourceRestrictedSum_eq_global

theorem global_pairing_sum_of_package_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageFinitePrimeSupportStabilization inputs g lambda pkg) :
    (∑ n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet,
      inputs.ccm25.weilSymbols.vonMangoldtWeight n *
        inputs.ccm25.weilSymbols.primePowerPairing
          n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg :=
  h.globalVonMangoldtPairingSumReadOff

theorem restricted_pairing_sum_of_package_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageFinitePrimeSupportStabilization inputs g lambda pkg) :
    (∑ n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda,
      inputs.ccm25.weilSymbols.vonMangoldtWeight n *
        inputs.ccm25.weilSymbols.primePowerPairing
          n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
        pkg :=
  h.restrictedVonMangoldtPairingSumReadOff

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

abbrev FixedTestSupportThresholdAtLarge
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) :=
  FixedTestSupportCutoffData inputs g lambda

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
    window_lambda_compatibility_of_source_backed hlambda

def fixed_test_support_threshold_at_large_of_source_backed
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} (hlambda : 1 < lambda) :
    FixedTestSupportThresholdAtLarge inputs g lambda :=
  fixed_test_support_cutoff_data_of_source_backed hlambda

theorem window_support_containment_of_fixed_test_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedTestSupportThresholdAtLarge inputs g lambda) :
    WindowSupportContainment inputs g lambda :=
  h.windowSupportContainment

theorem window_lambda_compatibility_of_fixed_test_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : FixedTestSupportThresholdAtLarge inputs g lambda) :
    WindowLambdaCompatibility inputs g lambda :=
  h.windowLambdaCompatibility

structure PrimePowerAtomStabilizationAtLarge
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  finitePrimeSignOwned :
    SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg
  supportStabilization :
    PackageFinitePrimeSupportStabilization inputs g lambda pkg

structure FinitePrimeStabilizationAtLarge
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  fixedTestSupport :
    FixedTestSupportThresholdAtLarge inputs g lambda
  primePowerAtomStabilization :
    PrimePowerAtomStabilizationAtLarge inputs g lambda pkg

structure SourceRestrictedQWLambdaDefinitionReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  qwLambdaFormulaReadOff : CCM25QWLambdaFormulaReadOff inputs g lambda
  packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg

structure SourceFullQWDefinitionReadOff
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  qwDefinitionReadOff : CCM25QWDefinitionReadOff inputs g
  packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg

abbrev RestrictedFinitePrimeSupportStabilizes
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  FinitePrimeStabilizationAtLarge inputs g lambda pkg

structure SourceFinitePrimeEvaluatorSumsMatchForRestriction
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  restrictedEvaluatorSum_eq_global :
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg
  restrictedCommonEvaluatorSum_eq_global :
    Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg

structure SourceArchimedeanPoleStabilityForRestriction
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  poleNormalizationReadOff : CCM25PoleNormalizationReadOff inputs g
  packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg

structure SourceArchimedeanContributionMatchesForRestriction
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  archimedeanContributionMatches :
    let W := inputs.ccm25.weilSymbols
    W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            pkg =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg

def SourceCommonAtomArchimedeanContributionMatchesForRestriction
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
      W.polePairing g.weilTest -
        Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
          pkg =
    W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
        Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
          pkg

theorem source_common_atom_archimedean_contribution_matches_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (h :
      SourceArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    SourceCommonAtomArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg := by
  exact
    Source.CCM25Concrete.Package.common_atom_archimedean_contribution_matches_of_package
      pkg h.archimedeanContributionMatches

theorem source_restricted_qw_lambda_definition_read_off_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    SourceRestrictedQWLambdaDefinitionReadOff inputs g lambda pkg :=
  { qwLambdaFormulaReadOff :=
      ccm25_qw_lambda_formula_read_off_of_package pkg
    packageReadOff := h.packageReadOff }

theorem source_full_qw_definition_read_off_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    SourceFullQWDefinitionReadOff inputs g lambda pkg :=
  { qwDefinitionReadOff := ccm25_qw_definition_read_off_of_package pkg
    packageReadOff := h.packageReadOff }

theorem source_archimedean_pole_stability_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg :=
  { poleNormalizationReadOff := ccm25_pole_normalization_read_off_of_package pkg
    packageReadOff := h.packageReadOff }

theorem pole_normalization_of_archimedean_pole_stability
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg) :
    CCM25PoleNormalizationReadOff inputs g :=
  h.poleNormalizationReadOff

theorem package_read_off_of_archimedean_pole_stability
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg) :
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg :=
  h.packageReadOff

theorem pole_pairing_eq_pole_functional_of_archimedean_pole_stability
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.polePairing g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) :=
  pole_normalization_of_archimedean_pole_stability h

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
  finitePrimeEvaluatorSumsMatch :
    SourceFinitePrimeEvaluatorSumsMatchForRestriction inputs g lambda pkg
  exactFinitePrimeSupport :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg
  archimedeanPoleStability :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg
  archimedeanContributionMatches :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg

abbrev SourceQWLambdaIsRestrictionOfQW
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  SourceQWLambdaRestrictionRows inputs g lambda pkg

noncomputable def source_qw_lambda_restriction_rows_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hstabilization :
      RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg)
    (harch :
      SourceArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    SourceQWLambdaRestrictionRows inputs g lambda pkg where
  restrictedDefinition :=
    source_restricted_qw_lambda_definition_read_off_of_common_tuple hcommon
  fullDefinition :=
    source_full_qw_definition_read_off_of_common_tuple hcommon
  finitePrimeStabilization := hstabilization
  finitePrimeEvaluatorSumsMatch :=
    { restrictedEvaluatorSum_eq_global :=
        Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum_eq_global
          pkg
      restrictedCommonEvaluatorSum_eq_global :=
        Source.CCM25Concrete.Package.source_common_restricted_sum_eq_common_global_of_package
          pkg }
  exactFinitePrimeSupport :=
    package_exact_finite_prime_support_at_lambda_holds
  archimedeanPoleStability :=
    source_archimedean_pole_stability_of_common_tuple hcommon
  archimedeanContributionMatches := harch

noncomputable def source_qw_lambda_is_restriction_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hstabilization :
      RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg)
    (harch :
      SourceArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg :=
  source_qw_lambda_restriction_rows_of_common_tuple
    hcommon hstabilization harch

theorem restricted_definition_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceRestrictedQWLambdaDefinitionReadOff inputs g lambda pkg :=
  h.restrictedDefinition

theorem qw_lambda_formula_read_off_of_restricted_definition
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceRestrictedQWLambdaDefinitionReadOff inputs g lambda pkg) :
    CCM25QWLambdaFormulaReadOff inputs g lambda :=
  h.qwLambdaFormulaReadOff

theorem package_read_off_of_restricted_definition
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceRestrictedQWLambdaDefinitionReadOff inputs g lambda pkg) :
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg :=
  h.packageReadOff

theorem full_definition_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceFullQWDefinitionReadOff inputs g lambda pkg :=
  h.fullDefinition

theorem qw_definition_read_off_of_full_definition
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFullQWDefinitionReadOff inputs g lambda pkg) :
    CCM25QWDefinitionReadOff inputs g :=
  h.qwDefinitionReadOff

theorem package_read_off_of_full_definition
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFullQWDefinitionReadOff inputs g lambda pkg) :
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg :=
  h.packageReadOff

def finite_prime_stabilization_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg :=
  h.finitePrimeStabilization

theorem finite_prime_evaluator_sums_match_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceFinitePrimeEvaluatorSumsMatchForRestriction inputs g lambda pkg :=
  h.finitePrimeEvaluatorSumsMatch

theorem restricted_evaluator_sum_eq_global_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg :=
  h.finitePrimeEvaluatorSumsMatch.restrictedEvaluatorSum_eq_global

theorem restricted_common_evaluator_sum_eq_global_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
      pkg =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg :=
  h.finitePrimeEvaluatorSumsMatch.restrictedCommonEvaluatorSum_eq_global

def exact_finite_prime_support_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg :=
  h.exactFinitePrimeSupport

theorem archimedean_pole_stability_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg :=
  h.archimedeanPoleStability

theorem archimedean_contribution_matches_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg :=
  h.archimedeanContributionMatches

theorem archimedean_contribution_equality_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            pkg =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg :=
  h.archimedeanContributionMatches.archimedeanContributionMatches

theorem common_atom_archimedean_contribution_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceCommonAtomArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg :=
  source_common_atom_archimedean_contribution_matches_of_package
    (package_read_off_of_archimedean_pole_stability
      h.archimedeanPoleStability)
    h.archimedeanContributionMatches

theorem package_read_off_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg :=
  h.restrictedDefinition.packageReadOff

structure RestrictedToFullNoSpectralConvergenceImport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  commonTuple :
    SourceCommonTestTupleContract inputs g lambda F_g pkg
  sourceWindowControlsRestrictedRoute :
    SourceWindowControlsRestrictedRoute inputs g lambda
  restrictedFormIsRestriction :
    SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg
  finitePrimeSupportStabilizes :
    RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg
  finitePrimeEvaluatorSumsMatch :
    SourceFinitePrimeEvaluatorSumsMatchForRestriction inputs g lambda pkg
  archimedeanPoleStability :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg
  archimedeanContributionMatches :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg

structure RestrictedToFullQWScalarRestrictionWitness
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  commonTuple :
    SourceCommonTestTupleContract inputs g lambda F_g pkg
  sourceWindowControlsRestrictedRoute :
    SourceWindowControlsRestrictedRoute inputs g lambda
  restrictedFormIsRestriction :
    SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg
  finitePrimeSupportStabilizes :
    RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg
  finitePrimeEvaluatorSumsMatch :
    SourceFinitePrimeEvaluatorSumsMatchForRestriction inputs g lambda pkg
  exactFinitePrimeSupport :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg
  archimedeanPoleStability :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg
  archimedeanContributionMatches :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg
  noSpectralConvergenceImport :
    RestrictedToFullNoSpectralConvergenceImport
      inputs g lambda F_g pkg

def no_spectral_convergence_import_of_scalar_witness
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    RestrictedToFullNoSpectralConvergenceImport
      inputs g lambda F_g pkg :=
  h.noSpectralConvergenceImport

theorem finite_prime_evaluator_sums_match_of_scalar_witness
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    SourceFinitePrimeEvaluatorSumsMatchForRestriction
      inputs g lambda pkg :=
  h.finitePrimeEvaluatorSumsMatch

theorem archimedean_pole_stability_of_scalar_witness
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg :=
  h.archimedeanPoleStability

theorem archimedean_contribution_matches_of_scalar_witness
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg :=
  h.archimedeanContributionMatches

theorem pole_pairing_eq_pole_functional_of_scalar_witness
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    let W := inputs.ccm25.weilSymbols
    W.polePairing g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) :=
  pole_pairing_eq_pole_functional_of_archimedean_pole_stability
    (archimedean_pole_stability_of_scalar_witness h)

theorem scalar_equality_from_witness_components
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest := by
  let W := inputs.ccm25.weilSymbols
  have harch :=
    archimedean_contribution_matches_of_scalar_witness h
  calc
    W.qwLambda lambda g.weilTest g.weilTest =
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
          W.polePairing g.weilTest -
            Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
              pkg := package_backed_qw_lambda_source_evaluator
                (package_read_off_of_archimedean_pole_stability
                  (archimedean_pole_stability_of_scalar_witness h))
    _ =
        W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
              pkg :=
        harch.archimedeanContributionMatches
    _ = W.qw g.weilTest g.weilTest :=
        (package_backed_qw_source_evaluator
          (package_read_off_of_archimedean_pole_stability
            (archimedean_pole_stability_of_scalar_witness h))).symm

theorem scalar_equality_from_common_atom_witness_components
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest := by
  have harch :=
    archimedean_contribution_matches_of_scalar_witness h
  exact
    Source.CCM25Concrete.Package.qw_lambda_eq_qw_of_archimedean_contribution
      pkg harch.archimedeanContributionMatches

theorem scalar_equality_of_scalar_witness
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest :=
  scalar_equality_from_common_atom_witness_components h

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
  scalarRestrictionAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        ∀ pkg :
          Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
            inputs.ccm25.weilSymbols g.weilTest lambda,
          SourceCommonTestTupleContract inputs g lambda F_g pkg →
            RestrictedToFullQWScalarRestrictionWitness
              inputs g lambda F_g pkg

abbrev RestrictedToFullQWLambdaThreshold
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (F_g : TestFunction) :=
  RestrictedToFullQWLargeLambdaThreshold inputs g F_g

structure RestrictedToFullCurrentThresholdData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  largeLambdaThreshold :
    RestrictedToFullQWLargeLambdaThreshold inputs g F_g
  currentAboveThreshold :
    largeLambdaThreshold.lambda0 ≤ lambda
  commonTuple :
    SourceCommonTestTupleContract inputs g lambda F_g pkg
  fixedTestSupport :
    FixedTestSupportThresholdAtLarge inputs g lambda
  primePowerAtomStabilization :
    PrimePowerAtomStabilizationAtLarge inputs g lambda pkg
  finitePrimeStabilization :
    RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg

def current_threshold_data_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    RestrictedToFullCurrentThresholdData inputs g lambda F_g pkg where
  largeLambdaThreshold := threshold
  currentAboveThreshold := habove
  commonTuple := hcommon
  fixedTestSupport := threshold.supportThresholdAtLarge lambda habove
  primePowerAtomStabilization :=
    threshold.primePowerAtomStabilizationAtLarge
      lambda habove pkg hcommon
  finitePrimeStabilization :=
    { fixedTestSupport := threshold.supportThresholdAtLarge lambda habove
      primePowerAtomStabilization :=
        threshold.primePowerAtomStabilizationAtLarge
          lambda habove pkg hcommon }

theorem fixed_test_support_of_current_threshold_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullCurrentThresholdData inputs g lambda F_g pkg) :
    FixedTestSupportThresholdAtLarge inputs g lambda :=
  h.fixedTestSupport

def prime_power_atom_stabilization_of_current_threshold_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullCurrentThresholdData inputs g lambda F_g pkg) :
    PrimePowerAtomStabilizationAtLarge inputs g lambda pkg :=
  h.primePowerAtomStabilization

def finite_prime_stabilization_of_current_threshold_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullCurrentThresholdData inputs g lambda F_g pkg) :
    RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg :=
  h.finitePrimeStabilization

structure RestrictedToFullQWScalarRestrictionData
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  commonTuple :
    SourceCommonTestTupleContract inputs g lambda F_g pkg
  restrictionRows :
    SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg
  exactFinitePrimeSupport :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg
  scalarRestrictionWitness :
    RestrictedToFullQWScalarRestrictionWitness
      inputs g lambda F_g pkg
  scalarEquality :
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest

abbrev RestrictedToFullQWScalarRestrictionEquality
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  RestrictedToFullQWScalarRestrictionData inputs g lambda F_g pkg

def restricted_to_full_scalar_restriction_data_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hwitness :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    RestrictedToFullQWScalarRestrictionData inputs g lambda F_g pkg where
  commonTuple := hwitness.commonTuple
  restrictionRows := hwitness.restrictedFormIsRestriction
  exactFinitePrimeSupport := hwitness.exactFinitePrimeSupport
  scalarRestrictionWitness := hwitness
  scalarEquality := scalar_equality_from_common_atom_witness_components hwitness

def restricted_to_full_scalar_restriction_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hwitness :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    RestrictedToFullQWScalarRestrictionEquality
      inputs g lambda F_g pkg :=
  restricted_to_full_scalar_restriction_data_of_common_tuple
    hwitness

def restriction_rows_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg :=
  h.restrictionRows

theorem common_tuple_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    SourceCommonTestTupleContract inputs g lambda F_g pkg :=
  h.commonTuple

def exact_finite_prime_support_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg :=
  h.exactFinitePrimeSupport

theorem scalar_equality_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest :=
  h.scalarEquality

def scalar_witness_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    RestrictedToFullQWScalarRestrictionWitness
      inputs g lambda F_g pkg :=
  h.scalarRestrictionWitness

def no_spectral_convergence_import_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    RestrictedToFullNoSpectralConvergenceImport
      inputs g lambda F_g pkg :=
  no_spectral_convergence_import_of_scalar_witness
    (scalar_witness_of_scalar_restriction h)

theorem finite_prime_evaluator_sums_match_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    SourceFinitePrimeEvaluatorSumsMatchForRestriction
      inputs g lambda pkg :=
  finite_prime_evaluator_sums_match_of_scalar_witness
    (scalar_witness_of_scalar_restriction h)

theorem archimedean_pole_stability_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg :=
  archimedean_pole_stability_of_scalar_witness
    (scalar_witness_of_scalar_restriction h)

theorem archimedean_contribution_matches_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg :=
  archimedean_contribution_matches_of_scalar_witness
    (scalar_witness_of_scalar_restriction h)

theorem pole_pairing_eq_pole_functional_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    let W := inputs.ccm25.weilSymbols
    W.polePairing g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) :=
  pole_pairing_eq_pole_functional_of_scalar_witness
    (scalar_witness_of_scalar_restriction h)

def RestrictedToFullQWLowerBoundEvidence
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (L : RouteLedgers) : Prop :=
  SourceEndpointStripRemainderCdefDomination inputs g lambda L

structure RestrictedToFullQWLowerBoundTransfer
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  scalarRestrictionEquality :
    RestrictedToFullQWScalarRestrictionEquality inputs g lambda F_g pkg
  lowerBoundEvidence :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L

def restricted_to_full_lower_bound_transfer_of_parts
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

def restricted_to_full_lower_bound_transfer_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hwitness :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg)
    (hevidence :
      RestrictedToFullQWLowerBoundEvidence inputs g lambda L) :
    RestrictedToFullQWLowerBoundTransfer inputs g lambda F_g L pkg :=
  restricted_to_full_lower_bound_transfer_of_parts
    (restricted_to_full_scalar_restriction_of_common_tuple
      hwitness)
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
  currentThresholdData :
    RestrictedToFullCurrentThresholdData inputs g lambda F_g pkg
  scalarRestrictionWitness :
    RestrictedToFullQWScalarRestrictionWitness inputs g lambda F_g pkg
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
  currentThresholdData :=
    current_threshold_data_of_large_lambda_threshold
      threshold habove hcommon
  scalarRestrictionWitness :=
    threshold.scalarRestrictionAtLarge lambda habove pkg hcommon
  scalarRestrictionEquality :=
    restricted_to_full_scalar_restriction_of_common_tuple
      (threshold.scalarRestrictionAtLarge lambda habove pkg hcommon)
  exactFinitePrimeSupport :=
    exact_finite_prime_support_of_scalar_restriction
      (restricted_to_full_scalar_restriction_of_common_tuple
        (threshold.scalarRestrictionAtLarge lambda habove pkg hcommon))
  lowerBoundEvidence := hevidence

abbrev RestrictedToFullQWBridgeContract
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  RestrictedToFullQWBridgeData inputs g lambda F_g L pkg

structure RestrictedToFullAllowedInputRows
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  commonTuple :
    SourceCommonTestTupleContract inputs g lambda F_g pkg
  fixedTestSupport :
    FixedTestSupportThresholdAtLarge inputs g lambda
  primePowerAtomStabilization :
    PrimePowerAtomStabilizationAtLarge inputs g lambda pkg
  finitePrimeStabilization :
    RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg
  exactFinitePrimeSupport :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg
  restrictedFormIsRestriction :
    SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg
  finitePrimeEvaluatorSumsMatch :
    SourceFinitePrimeEvaluatorSumsMatchForRestriction inputs g lambda pkg
  archimedeanPoleStability :
    SourceArchimedeanPoleStabilityForRestriction inputs g lambda pkg
  archimedeanContributionMatches :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg
  noSpectralConvergenceImport :
    RestrictedToFullNoSpectralConvergenceImport inputs g lambda F_g pkg
  lowerBoundEvidence :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L

abbrev RestrictedToFullNoFiniteOperatorSpectralConvergenceImport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  RestrictedToFullAllowedInputRows inputs g lambda F_g L pkg

abbrev RestrictedToFullNoDeterminantConvergenceImport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  RestrictedToFullAllowedInputRows inputs g lambda F_g L pkg

abbrev RestrictedToFullNoNumericalEigenvalueImport
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  RestrictedToFullAllowedInputRows inputs g lambda F_g L pkg

def restricted_to_full_bridge_contract_of_common_tuple
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
  restricted_to_full_bridge_data_of_common_tuple
    threshold habove hcommon hevidence

def restricted_to_full_allowed_input_rows_of_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullAllowedInputRows inputs g lambda F_g L pkg where
  commonTuple := h.currentThresholdData.commonTuple
  fixedTestSupport := h.currentThresholdData.fixedTestSupport
  primePowerAtomStabilization :=
    h.currentThresholdData.primePowerAtomStabilization
  finitePrimeStabilization :=
    h.currentThresholdData.finitePrimeStabilization
  exactFinitePrimeSupport := h.exactFinitePrimeSupport
  restrictedFormIsRestriction :=
    h.scalarRestrictionWitness.restrictedFormIsRestriction
  finitePrimeEvaluatorSumsMatch :=
    h.scalarRestrictionWitness.finitePrimeEvaluatorSumsMatch
  archimedeanPoleStability :=
    h.scalarRestrictionWitness.archimedeanPoleStability
  archimedeanContributionMatches :=
    h.scalarRestrictionWitness.archimedeanContributionMatches
  noSpectralConvergenceImport :=
    h.scalarRestrictionWitness.noSpectralConvergenceImport
  lowerBoundEvidence := h.lowerBoundEvidence

def no_finite_operator_spectral_convergence_import_of_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullNoFiniteOperatorSpectralConvergenceImport
      inputs g lambda F_g L pkg :=
  restricted_to_full_allowed_input_rows_of_contract h

def no_determinant_convergence_import_of_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullNoDeterminantConvergenceImport
      inputs g lambda F_g L pkg :=
  restricted_to_full_allowed_input_rows_of_contract h

def no_numerical_eigenvalue_import_of_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullNoNumericalEigenvalueImport
      inputs g lambda F_g L pkg :=
  restricted_to_full_allowed_input_rows_of_contract h

structure SourceQWUsesCommonTest
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop where
  commonTestTuple : SourceCommonTestTupleContract inputs g lambda F_g pkg
  packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg
  squareCompatibility :
    SourceConvolutionSquareCompatibility inputs g lambda F_g pkg

theorem source_qw_uses_common_test_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    SourceQWUsesCommonTest inputs g lambda F_g pkg :=
  { commonTestTuple := h
    packageReadOff := h.packageReadOff
    squareCompatibility := h.squareCompatibility }

theorem source_qw_common_tuple_of_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    SourceCommonTestTupleContract inputs g lambda F_g pkg :=
  h.commonTestTuple

theorem source_qw_square_compatibility_of_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    SourceConvolutionSquareCompatibility inputs g lambda F_g pkg :=
  h.squareCompatibility

theorem source_qw_package_read_off_of_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    PackageBackedCCM25WeilFormReadOff inputs g lambda pkg :=
  h.packageReadOff

noncomputable def source_finite_prime_sign_owned_by_common_test
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWUsesCommonTest inputs g lambda F_g pkg) :
    SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg := by
  let hread := source_qw_package_read_off_of_common_test h
  exact
    { windowLambdaCompatibility := hread.windowLambdaCompatibility
      finitePrimeConcreteObject :=
        Source.CCM25Concrete.Package.finite_prime_concrete_object_of_package
          pkg
      finitePrimeNormalization :=
        Source.CCM25Concrete.Package.finite_prime_normalization_of_package
          pkg
      globalFinitePrimeSumReadOff :=
        package_backed_global_finite_prime_sum hread
      restrictedFinitePrimeSumReadOff :=
        package_backed_restricted_finite_prime_sum hread
      globalVonMangoldtPairingSumReadOff :=
        Source.CCM25Concrete.Package.finite_prime_concrete_object_global_pairing_sum_read_off
          pkg
      restrictedVonMangoldtPairingSumReadOff :=
        Source.CCM25Concrete.Package.finite_prime_concrete_object_restricted_pairing_sum_read_off
          pkg }

def SourcePsiSignExpansion
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  SourceQWUsesCommonTest inputs g lambda F_g pkg

structure SourceArchimedeanSignBridge
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (_g : SourceBackedFixedSTest inputs) where
  traceLegality : CC20TraceLegality inputs a
  positiveTraceNonnegative : CC20PositiveTraceNonnegative inputs a
  signsAndNormalizations :
    (Source.cc20SignsAndNormalizations
      inputs.cc20.archimedeanSymbols).Holds
  mellinHalfDensityConvention :
    (Source.cc20MellinHalfDensityConvention
      inputs.cc20.archimedeanSymbols).Holds

structure LegacySourceFinitePrimeSignOwnedByFormula
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) where
  package :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda
  signOwned :
    SourceFinitePrimeSignOwnedByPackage inputs g lambda package

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

structure SourceQWEqualsNegCC20WeilSum
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  sourceQWUsesCommonTest : SourceQWUsesCommonTest inputs g lambda F_g pkg
  sourcePsiSignExpansion : SourcePsiSignExpansion inputs g lambda F_g pkg
  sourceArchimedeanSignBridge : SourceArchimedeanSignBridge inputs a g
  sourceFinitePrimeSignOwnedByPackage :
    SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg
  sourcePoleSignInCC20LocalSum :
    SourcePoleSignInCC20LocalSum inputs g lambda F_g pkg

abbrev SourceQWNonnegativeToCC20Nonpositive
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  SourceQWEqualsNegCC20WeilSum inputs a g lambda F_g pkg

noncomputable def source_qw_equals_neg_cc20_weil_sum_of_common_test
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
  { sourceQWUsesCommonTest := hcommon
    sourcePsiSignExpansion := source_psi_sign_expansion_of_common_test hcommon
    sourceArchimedeanSignBridge := hsign
    sourceFinitePrimeSignOwnedByPackage :=
      source_finite_prime_sign_owned_by_common_test hcommon
    sourcePoleSignInCC20LocalSum :=
      source_pole_sign_in_cc20_local_sum_of_common_test hcommon }

noncomputable def source_qw_nonnegative_to_cc20_nonpositive_of_common_test
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

abbrev FinalSignBridgeContract
    (inputs : RouteInputs) (a : inputs.cc20.archimedeanSymbols.Test)
    (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) :=
  FinalSignBridgeData inputs a g lambda F_g pkg

def final_sign_bridge_contract_of_common_test
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
  final_sign_bridge_data_of_common_test hcommon hsign

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

def restricted_to_full_qw_lambda_threshold_of_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullQWLambdaThreshold inputs g F_g :=
  h.largeLambdaThreshold

theorem current_above_threshold_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    h.largeLambdaThreshold.lambda0 ≤ lambda :=
  h.currentAboveThreshold

theorem fixed_test_support_threshold_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    FixedTestSupportThresholdAtLarge inputs g lambda :=
  h.currentThresholdData.fixedTestSupport

def prime_power_atom_stabilization_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    PrimePowerAtomStabilizationAtLarge inputs g lambda pkg :=
  h.currentThresholdData.primePowerAtomStabilization

def finite_prime_stabilization_at_large_of_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    FinitePrimeStabilizationAtLarge inputs g lambda pkg :=
  h.currentThresholdData.finitePrimeStabilization

theorem finite_prime_stabilization_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    PackageFinitePrimeSupportStabilization inputs g lambda pkg :=
  (prime_power_atom_stabilization_of_large_lambda_threshold h).supportStabilization

def scalar_restriction_equality_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullQWScalarRestrictionEquality inputs g lambda F_g pkg :=
  h.scalarRestrictionEquality

def exact_finite_prime_support_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    PackageExactFinitePrimeSupportAtLambda inputs g lambda pkg :=
  h.exactFinitePrimeSupport

theorem lower_bound_evidence_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L :=
  h.lowerBoundEvidence

def lower_bound_transfer_of_restricted_to_full_contract
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

noncomputable def final_sign_bridge_of_contract
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
    h.sourceQWUsesCommonTest
    h.sourceArchimedeanSignBridge

noncomputable def final_sign_nonnegative_to_nonpositive_of_contract
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
  h.finitePrimeNormalization

def finite_prime_concrete_object_of_sign_owned_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg) :
    Source.CCM25Concrete.FinitePrimeCertificate.FixedLambdaFinitePrimeConcreteObject
      inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda :=
  h.finitePrimeConcreteObject

theorem finite_prime_concrete_object_weight_of_sign_owned_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg)
    (n : ℕ) :
    inputs.ccm25.weilSymbols.vonMangoldtWeight n =
      Source.CCM25Concrete.PrimePowerArithmetic.SourceVonMangoldtWeight n :=
  h.finitePrimeConcreteObject.weightReadOff n

theorem finite_prime_concrete_object_term_of_sign_owned_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg)
    (n : ℕ) :
    let W := inputs.ccm25.weilSymbols
    W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest) =
      Source.CCM25Concrete.PrimePowerArithmetic.SourceFinitePrimeEvaluatorAtom
        W g.weilTest g.weilTest n
          (h.finitePrimeConcreteObject.atomData n) :=
  h.finitePrimeConcreteObject.termFormulaSourceEvaluator n

theorem finite_prime_concrete_object_pairing_of_sign_owned_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg)
    (n : ℕ) :
    let W := inputs.ccm25.weilSymbols
    let atom := h.finitePrimeConcreteObject.atomData n
    W.primePowerPairing n g.weilTest g.weilTest =
      (1 / Real.sqrt (n : ℝ)) *
        (atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar g.weilTest g.weilTest) (n : ℝ) +
          atom.sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
            (W.convolutionStar g.weilTest g.weilTest) ((n : ℝ)⁻¹)) :=
  h.finitePrimeConcreteObject.pairingFormulaSourceEvaluator n

theorem finite_prime_concrete_object_global_pairing_sum_of_sign_owned_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n *
        W.primePowerPairing n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg :=
  h.globalVonMangoldtPairingSumReadOff

theorem finite_prime_concrete_object_restricted_pairing_sum_of_sign_owned_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceFinitePrimeSignOwnedByPackage inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n *
        W.primePowerPairing n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
        pkg :=
  h.restrictedVonMangoldtPairingSumReadOff

theorem finite_prime_normalization_of_legacy_sign_owned_formula
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    (h : LegacySourceFinitePrimeSignOwnedByFormula inputs g lambda) :
    WeilFormSymbols.FinitePrimeNormalizationStatement inputs.ccm25.weilSymbols :=
  finite_prime_normalization_of_sign_owned_package h.signOwned

def restricted_to_full_qw_bridge_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : RouteBridgeCertificate inputs g L) :
    RestrictedToFullQWBridgeContract inputs g h.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      L h.sourceTraceReadOff.ccm25ArithmeticPackage :=
  h.restrictedToFullQWBridge

def final_sign_bridge_of_route_bridge_certificate
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
