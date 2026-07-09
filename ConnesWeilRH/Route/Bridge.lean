/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Route.Exhaustion
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeSourceData
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
  globalFinitePrimeScopedSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
        pkg
  restrictedFinitePrimeSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        pkg
  restrictedFinitePrimeScopedSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
        pkg
  psiSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.psi (W.convolutionStar g.weilTest g.weilTest) =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg
  psiScopedSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.psi (W.convolutionStar g.weilTest g.weilTest) =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
            pkg
  qwSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.qw g.weilTest g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg
  qwScopedSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.qw g.weilTest g.weilTest =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
            pkg
  qwLambdaSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.qwLambda lambda g.weilTest g.weilTest =
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            pkg
  qwLambdaScopedSourceEvaluatorReadOff :
    let W := inputs.ccm25.weilSymbols
    W.qwLambda lambda g.weilTest g.weilTest =
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
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
    globalFinitePrimeScopedSumReadOff :=
      Source.CCM25Concrete.Package.global_finite_prime_scoped_sum_of_package_components
        pkg
    restrictedFinitePrimeSumReadOff :=
      Source.CCM25Concrete.Package.restricted_finite_prime_sum_of_package_components
        pkg
    restrictedFinitePrimeScopedSumReadOff :=
      Source.CCM25Concrete.Package.restricted_finite_prime_scoped_sum_of_package_components
        pkg
    psiSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.psi_source_evaluator_of_package_components
        pkg
    psiScopedSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.psi_scoped_source_evaluator_of_package_components
        pkg
    qwSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.qw_source_evaluator_of_package_components
        pkg
    qwScopedSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.qw_scoped_source_evaluator_of_package_components
        pkg
    qwLambdaSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.qw_lambda_formula_source_evaluator_of_package_components
        pkg
    qwLambdaScopedSourceEvaluatorReadOff :=
      Source.CCM25Concrete.Package.qw_lambda_formula_scoped_source_evaluator_of_package_components
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

theorem package_backed_global_finite_prime_scoped_sum
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
        pkg :=
  h.globalFinitePrimeScopedSumReadOff

theorem package_backed_restricted_finite_prime_scoped_sum
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
        pkg :=
  h.restrictedFinitePrimeScopedSumReadOff

theorem package_backed_source_global_scoped_sum_eq_global_sum
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
      pkg =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg :=
  Source.CCM25Concrete.Package.source_global_scoped_sum_eq_global_sum_of_package
    pkg

theorem package_backed_source_restricted_scoped_sum_eq_restricted_sum
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
      pkg =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        pkg :=
  Source.CCM25Concrete.Package.source_restricted_scoped_sum_eq_restricted_sum_of_package
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

theorem package_backed_source_global_scoped_sum_eq_common_atoms
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
      pkg =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
        pkg :=
  Source.CCM25Concrete.Package.source_global_scoped_sum_eq_common_scoped_atoms_of_package
    pkg

theorem package_backed_source_restricted_scoped_sum_eq_common_atoms
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
      pkg =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_scoped_sum
        pkg :=
  Source.CCM25Concrete.Package.source_restricted_scoped_sum_eq_common_scoped_atoms_of_package
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

theorem package_backed_psi_scoped_source_evaluator
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
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
            pkg :=
  h.psiScopedSourceEvaluatorReadOff

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

theorem package_backed_psi_scoped_source_evaluator_common_atoms
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
          Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
            pkg :=
  Source.CCM25Concrete.Package.psi_scoped_source_evaluator_common_atoms_of_package
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

theorem package_backed_qw_scoped_source_evaluator
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
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
            pkg :=
  h.qwScopedSourceEvaluatorReadOff

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

theorem package_backed_qw_scoped_source_evaluator_common_atoms
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
          Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
            pkg :=
  Source.CCM25Concrete.Package.qw_scoped_source_evaluator_common_atoms_of_package
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

theorem package_backed_qw_lambda_scoped_source_evaluator
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
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
            pkg :=
  h.qwLambdaScopedSourceEvaluatorReadOff

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

theorem package_backed_qw_lambda_scoped_source_evaluator_common_atoms
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
          Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_scoped_sum
            pkg :=
  Source.CCM25Concrete.Package.qw_lambda_formula_scoped_source_evaluator_common_atoms_of_package
    pkg

theorem package_backed_qw_lambda_scoped_restricted_archimedean_formula
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_h : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.qwLambda lambda g.weilTest g.weilTest =
      Source.CCM25Concrete.Package.ScopedRestrictedArchimedeanFormula
        W g.weilTest lambda pkg :=
  Source.CCM25Concrete.Package.qwLambda_eq_scopedRestrictedArchimedeanFormula_of_package
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

theorem source_common_test_tuple_contract_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (windowLambdaCompatibility : WindowLambdaCompatibility inputs g lambda)
    (packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (squareCompatibility :
      SourceConvolutionSquareCompatibility inputs g lambda F_g pkg) :
    SourceCommonTestTupleContract inputs g lambda F_g pkg :=
  { windowLambdaCompatibility := windowLambdaCompatibility
    packageReadOff := packageReadOff
    squareCompatibility := squareCompatibility }

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
  globalFinitePrimeSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum pkg
  globalFinitePrimeScopedSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
        pkg
  restrictedFinitePrimeSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        pkg
  restrictedFinitePrimeScopedSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
        pkg
  globalVonMangoldtPairingSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n *
        W.primePowerPairing n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg
  globalVonMangoldtPairingScopedSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.globalPrimeIndexSet,
      W.vonMangoldtWeight n *
        W.primePowerPairing n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
        pkg
  restrictedVonMangoldtPairingSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n *
        W.primePowerPairing n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
        pkg
  restrictedVonMangoldtPairingScopedSumReadOff :
    let W := inputs.ccm25.weilSymbols
    (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.vonMangoldtWeight n *
        W.primePowerPairing n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_scoped_sum
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
          inputs.ccm25.weilSymbols g.weilTest g.weilTest n
  restrictedIndexSourceData :
    ∀ n : ℕ,
      n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda →
        Source.CCM25Concrete.PrimePowerSupport.SourceRestrictedIndexData
          inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda n
  globalFinitePrimeSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet,
      inputs.ccm25.weilSymbols.finitePrimeTerm n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
        pkg
  globalFinitePrimeScopedSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet,
      inputs.ccm25.weilSymbols.finitePrimeTerm n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
        pkg
  restrictedFinitePrimeSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda,
      inputs.ccm25.weilSymbols.finitePrimeTerm n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
        pkg
  restrictedFinitePrimeScopedSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda,
      inputs.ccm25.weilSymbols.finitePrimeTerm n
        (inputs.ccm25.weilSymbols.convolutionStar
          g.weilTest g.weilTest)) =
      Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
        pkg
  globalVonMangoldtPairingSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet,
      inputs.ccm25.weilSymbols.vonMangoldtWeight n *
        inputs.ccm25.weilSymbols.primePowerPairing
          n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_sum
        pkg
  globalVonMangoldtPairingScopedSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet,
      inputs.ccm25.weilSymbols.vonMangoldtWeight n *
        inputs.ccm25.weilSymbols.primePowerPairing
          n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
        pkg
  restrictedVonMangoldtPairingSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda,
      inputs.ccm25.weilSymbols.vonMangoldtWeight n *
        inputs.ccm25.weilSymbols.primePowerPairing
          n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_sum
        pkg
  restrictedVonMangoldtPairingScopedSumReadOff :
    (∑ n ∈ inputs.ccm25.weilSymbols.restrictedPrimeIndexSet lambda,
      inputs.ccm25.weilSymbols.vonMangoldtWeight n *
        inputs.ccm25.weilSymbols.primePowerPairing
          n g.weilTest g.weilTest) =
      Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_scoped_sum
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
  let hrestrictedScopedPairing :=
    Source.CCM25Concrete.Package.restricted_von_mangoldt_pairing_scoped_sum_common_atoms_of_package
      pkg
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
    globalFinitePrimeSumReadOff :=
      Source.CCM25Concrete.Package.global_finite_prime_sum_of_package_components
        pkg
    globalFinitePrimeScopedSumReadOff :=
      Source.CCM25Concrete.Package.global_finite_prime_scoped_sum_common_atoms_of_package
        pkg
    restrictedFinitePrimeSumReadOff :=
      Source.CCM25Concrete.Package.restricted_finite_prime_sum_of_package_components
        pkg
    restrictedFinitePrimeScopedSumReadOff :=
      Source.CCM25Concrete.Package.restricted_finite_prime_scoped_sum_common_atoms_of_package
        pkg
    globalVonMangoldtPairingSumReadOff :=
      Source.CCM25Concrete.Package.finite_prime_concrete_object_global_pairing_sum_read_off
        pkg
    globalVonMangoldtPairingScopedSumReadOff :=
      Source.CCM25Concrete.Package.global_von_mangoldt_pairing_scoped_sum_common_atoms_of_package
        pkg
    restrictedVonMangoldtPairingSumReadOff :=
      Source.CCM25Concrete.Package.finite_prime_concrete_object_restricted_pairing_sum_read_off
        pkg
    restrictedVonMangoldtPairingScopedSumReadOff :=
      hrestrictedScopedPairing }

theorem global_index_source_data_of_package_stabilization
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : PackageFinitePrimeSupportStabilization inputs g lambda pkg)
    {n : ℕ} (hn : n ∈ inputs.ccm25.weilSymbols.globalPrimeIndexSet) :
    Source.CCM25Concrete.PrimePowerSupport.SourceGlobalIndexData
      inputs.ccm25.weilSymbols g.weilTest g.weilTest n :=
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
      inputs.ccm25.weilSymbols g.weilTest g.weilTest lambda n :=
  h.restrictedIndexSourceData n hn

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
    inputs.ccm24.supportInWindow
      g.semilocalTest g.window
  fourierSupportInWindow :
    inputs.ccm24.fourierSupportInWindow
      g.semilocalTest g.window
  convolutionSupportTransported :
    inputs.ccm24.convolutionSupportTransported
      g.semilocalTest g.window
  windowContainedInLambda :
    inputs.ccm24.windowContainedInLambda
      g.window lambda
  lambdaCompatible :
    inputs.ccm24.lambdaCompatible g.window lambda
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
  supportInWindow := g.ccm24RouteConsumerRows.supportInWindow
  fourierSupportInWindow := g.ccm24RouteConsumerRows.fourierSupportInWindow
  convolutionSupportTransported :=
    g.ccm24RouteConsumerRows.convolutionSupportTransported
  windowContainedInLambda :=
    g.ccm24RouteConsumerRows.windowContainedInLambda lambda hlambda
  lambdaCompatible :=
    lambda_compatible_of_source_backed g hlambda
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

structure SourceArchimedeanPoleStabilityForRestriction
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  poleNormalizationReadOff : CCM25PoleNormalizationReadOff inputs g
  packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg

def SourceScopedArchimedeanContributionMatchesForRestriction
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  Source.CCM25Concrete.Package.ScopedArchimedeanContributionBalance
    W g.weilTest lambda pkg

def SourceScopedFinitePrimeArchimedeanBalance
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
      pkg -
    Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
      pkg =
    2 * W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)

def SourceFinitePrimeIndexDifferenceArchimedeanBalance
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  let W := inputs.ccm25.weilSymbols
  (∑ n ∈ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) -
    (∑ n ∈ W.globalPrimeIndexSet,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest)) =
    2 * W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)

def SourceFinitePrimeOutsideGlobalMass
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) : Prop :=
  let W := inputs.ccm25.weilSymbols
  ∑ n ∈ W.globalPrimeIndexSet \ W.restrictedPrimeIndexSet lambda,
      W.finitePrimeTerm n (W.convolutionStar g.weilTest g.weilTest) =
    -2 * W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)

theorem source_scoped_finite_prime_archimedean_balance_of_index_difference
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (hbalance :
      SourceFinitePrimeIndexDifferenceArchimedeanBalance inputs g lambda) :
    SourceScopedFinitePrimeArchimedeanBalance inputs g lambda pkg := by
  let W := inputs.ccm25.weilSymbols
  let C := W.convolutionStar g.weilTest g.weilTest
  let A := W.archimedeanTerm C
  let R0 := ∑ n ∈ W.restrictedPrimeIndexSet lambda, W.finitePrimeTerm n C
  let G0 := ∑ n ∈ W.globalPrimeIndexSet, W.finitePrimeTerm n C
  let R :=
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
      pkg
  let G :=
    Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
      pkg
  have hR : R0 = R := by
    simpa [W, C, R0, R] using hread.restrictedFinitePrimeScopedSumReadOff
  have hG : G0 = G := by
    simpa [W, C, G0, G] using hread.globalFinitePrimeScopedSumReadOff
  have hdiff : R0 - G0 = 2 * A := by
    simpa [SourceFinitePrimeIndexDifferenceArchimedeanBalance, W, C, A, R0, G0]
      using hbalance
  dsimp [SourceScopedFinitePrimeArchimedeanBalance]
  change R - G = 2 * A
  rw [← hR, ← hG]
  exact hdiff

def SourceCommonScopedFinitePrimeArchimedeanBalance
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_scoped_sum
      pkg -
    Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
      pkg =
    2 * W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)

def SourceCommonScopedFinitePrimeArchimedeanMathlibBalance
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  Source.CCM25Concrete.PrimePowerArithmetic.MathlibRestrictedFinitePrimeEvaluatorSumOnIndexSet
      W g.weilTest g.weilTest lambda
        (Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
          (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate) -
    Source.CCM25Concrete.PrimePowerArithmetic.MathlibGlobalFinitePrimeEvaluatorSumOnIndexSet
      W g.weilTest g.weilTest
        (Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
          (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate) =
    2 * W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)

def SourceCommonScopedFinitePrimeArchimedeanFilterBalance
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  let hrestricted :=
    Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
      (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate
  let hglobal :=
    Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
      (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate
  (∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
      if hn : n ∈ W.restrictedPrimeIndexSet lambda then
        Source.CCM25Concrete.PrimePowerArithmetic.MathlibFinitePrimeEvaluatorAtom
          W g.weilTest g.weilTest n (hrestricted.atIndex n hn)
      else
        0) -
    (∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
      if hn : n ∈ W.globalPrimeIndexSet then
        Source.CCM25Concrete.PrimePowerArithmetic.MathlibFinitePrimeEvaluatorAtom
          W g.weilTest g.weilTest n (hglobal.atIndex n hn)
      else
        0) =
    2 * W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)

def SourceCommonScopedFinitePrimeArchimedeanSourceEvaluationBalance
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  let hrestricted :=
    Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
      (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate
  let hglobal :=
    Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
      (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate
  (∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
      if hn : n ∈ W.restrictedPrimeIndexSet lambda then
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            ((hrestricted.atIndex n hn).sourcePairing.model.sourceEvaluation.forwardValue +
              (hrestricted.atIndex n hn).sourcePairing.model.sourceEvaluation.inverseValue))
      else
        0) -
    (∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
      if hn : n ∈ W.globalPrimeIndexSet then
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            ((hglobal.atIndex n hn).sourcePairing.model.sourceEvaluation.forwardValue +
              (hglobal.atIndex n hn).sourcePairing.model.sourceEvaluation.inverseValue))
      else
        0) =
    2 * W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)

def SourceCommonScopedFinitePrimeArchimedeanEvaluatorValueBalance
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  let hrestricted :=
    Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
      (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate
  let hglobal :=
    Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
      (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate
  (∑ n ∈ (W.restrictedPrimeIndexSet lambda).filter IsPrimePow,
      if hn : n ∈ W.restrictedPrimeIndexSet lambda then
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            ((hrestricted.atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
                (W.convolutionStar g.weilTest g.weilTest) (n : ℝ) +
              (hrestricted.atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
                (W.convolutionStar g.weilTest g.weilTest) ((n : ℝ)⁻¹)))
      else
        0) -
    (∑ n ∈ W.globalPrimeIndexSet.filter IsPrimePow,
      if hn : n ∈ W.globalPrimeIndexSet then
        ArithmeticFunction.vonMangoldt n *
          ((1 / Real.sqrt (n : ℝ)) *
            ((hglobal.atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
                (W.convolutionStar g.weilTest g.weilTest) (n : ℝ) +
              (hglobal.atIndex n hn).sourcePairing.model.sourceEvaluation.sourceEvaluator.valueAt
                (W.convolutionStar g.weilTest g.weilTest) ((n : ℝ)⁻¹)))
      else
        0) =
    2 * W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)

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
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
            pkg =
        W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
              pkg

/--
The source-facing archimedean balance row stored at scoped finite-prime
support.  The full wrapper `SourceArchimedeanContributionMatchesForRestriction`
is reconstructed from this row, so downstream restricted-to-full code cannot
hide the finite-prime scoped equality inside a broader package field.
-/
structure SourceArchimedeanContributionBalanceRows
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  scopedBalance :
    SourceScopedArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg

def source_archimedean_contribution_matches_of_balance_rows
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (rows : SourceArchimedeanContributionBalanceRows inputs g lambda pkg) :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg where
  archimedeanContributionMatches := by
    simpa [SourceScopedArchimedeanContributionMatchesForRestriction,
      Source.CCM25Concrete.Package.ScopedArchimedeanContributionBalance,
      Source.CCM25Concrete.Package.ScopedRestrictedArchimedeanFormula,
      Source.CCM25Concrete.Package.ScopedGlobalArchimedeanFormula]
      using rows.scopedBalance

theorem source_scoped_archimedean_contribution_matches_of_finite_prime_balance
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (hbalance :
      SourceScopedFinitePrimeArchimedeanBalance inputs g lambda pkg) :
    SourceScopedArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg := by
  let W := inputs.ccm25.weilSymbols
  let A := W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)
  let P := W.polePairing g.weilTest
  let PF := W.poleFunctional (W.convolutionStar g.weilTest g.weilTest)
  let R :=
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
      pkg
  let G :=
    Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
      pkg
  have hp : P = PF := by
    simpa [P, PF] using hread.poleNormalizationReadOff
  have hdiff : R - G = 2 * A := by
    simpa [SourceScopedFinitePrimeArchimedeanBalance, W, A, R, G] using hbalance
  dsimp [SourceScopedArchimedeanContributionMatchesForRestriction,
    Source.CCM25Concrete.Package.ScopedArchimedeanContributionBalance,
    Source.CCM25Concrete.Package.ScopedRestrictedArchimedeanFormula,
    Source.CCM25Concrete.Package.ScopedGlobalArchimedeanFormula]
  change A + P - R = PF - A - G
  rw [hp]
  linarith

theorem source_scoped_finite_prime_archimedean_balance_of_common_balance
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (hbalance :
      SourceCommonScopedFinitePrimeArchimedeanBalance inputs g lambda pkg) :
    SourceScopedFinitePrimeArchimedeanBalance inputs g lambda pkg := by
  let W := inputs.ccm25.weilSymbols
  let R :=
    Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
      pkg
  let G :=
    Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
      pkg
  let Rc :=
    Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_scoped_sum
      pkg
  let Gc :=
    Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
      pkg
  let A := W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest)
  have hR : R = Rc := by
    simpa [R, Rc] using
      package_backed_source_restricted_scoped_sum_eq_common_atoms hread
  have hG : G = Gc := by
    simpa [G, Gc] using
      package_backed_source_global_scoped_sum_eq_common_atoms hread
  have hc : Rc - Gc = 2 * A := by
    simpa [SourceCommonScopedFinitePrimeArchimedeanBalance, W, Rc, Gc, A]
      using hbalance
  dsimp [SourceScopedFinitePrimeArchimedeanBalance]
  change R - G = 2 * A
  rw [hR, hG]
  exact hc

theorem source_common_scoped_finite_prime_archimedean_balance_of_mathlib_balance
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hbalance :
      SourceCommonScopedFinitePrimeArchimedeanMathlibBalance
        inputs g lambda pkg) :
    SourceCommonScopedFinitePrimeArchimedeanBalance inputs g lambda pkg := by
  simpa [SourceCommonScopedFinitePrimeArchimedeanMathlibBalance,
    SourceCommonScopedFinitePrimeArchimedeanBalance,
    Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_scoped_sum,
    Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum]
    using hbalance

theorem source_common_scoped_finite_prime_archimedean_mathlib_balance_of_filter_balance
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hbalance :
      SourceCommonScopedFinitePrimeArchimedeanFilterBalance
        inputs g lambda pkg) :
    SourceCommonScopedFinitePrimeArchimedeanMathlibBalance
      inputs g lambda pkg := by
  let W := inputs.ccm25.weilSymbols
  let hrestricted :=
    Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_restricted_index_set_of_certificate
      (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate
  let hglobal :=
    Source.CCM25Concrete.FinitePrimeCertificate.arithmetic_data_on_global_index_set_of_certificate
      (Source.CCM25Concrete.Package.formula_components pkg).commonCertificate
  have hr :=
    Source.CCM25Concrete.PrimePowerArithmetic.mathlib_restricted_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
      (W := W) (f := g.weilTest) (g := g.weilTest)
      (lambda := lambda) hrestricted
  have hg :=
    Source.CCM25Concrete.PrimePowerArithmetic.mathlib_global_finite_prime_evaluator_sum_on_index_set_eq_prime_power_filter
      (W := W) (f := g.weilTest) (g := g.weilTest) hglobal
  dsimp [SourceCommonScopedFinitePrimeArchimedeanMathlibBalance]
  rw [hr, hg]
  simpa [SourceCommonScopedFinitePrimeArchimedeanFilterBalance, W,
    hrestricted, hglobal] using hbalance

theorem source_common_scoped_finite_prime_archimedean_filter_balance_of_source_evaluation_balance
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hbalance :
      SourceCommonScopedFinitePrimeArchimedeanSourceEvaluationBalance
        inputs g lambda pkg) :
    SourceCommonScopedFinitePrimeArchimedeanFilterBalance
      inputs g lambda pkg := by
  simpa [SourceCommonScopedFinitePrimeArchimedeanFilterBalance,
    SourceCommonScopedFinitePrimeArchimedeanSourceEvaluationBalance,
    Source.CCM25Concrete.PrimePowerArithmetic.MathlibFinitePrimeEvaluatorAtom]
    using hbalance

theorem source_common_scoped_finite_prime_archimedean_source_evaluation_balance_of_evaluator_value_balance
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hbalance :
      SourceCommonScopedFinitePrimeArchimedeanEvaluatorValueBalance
        inputs g lambda pkg) :
    SourceCommonScopedFinitePrimeArchimedeanSourceEvaluationBalance
      inputs g lambda pkg := by
  simpa [SourceCommonScopedFinitePrimeArchimedeanSourceEvaluationBalance,
    SourceCommonScopedFinitePrimeArchimedeanEvaluatorValueBalance,
    Source.CCM25Concrete.PrimePowerEvaluation.source_forward_value_at_source_points,
    Source.CCM25Concrete.PrimePowerEvaluation.source_inverse_value_at_source_points]
    using hbalance

def SourceCommonAtomArchimedeanContributionMatchesForRestriction
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) : Prop :=
  let W := inputs.ccm25.weilSymbols
  W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
      W.polePairing g.weilTest -
        Source.CCM25Concrete.Package.source_common_restricted_finite_prime_evaluator_scoped_sum
          pkg =
    W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
      W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
        Source.CCM25Concrete.Package.source_common_global_finite_prime_evaluator_scoped_sum
          pkg

def SourceCommonAtomFullArchimedeanContributionMatchesForRestriction
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

theorem source_full_archimedean_contribution_matches_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (h :
      SourceArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    let W := inputs.ccm25.weilSymbols
    W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
        W.polePairing g.weilTest -
          Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_sum
            pkg =
      W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_sum
            pkg := by
  rw [← Source.CCM25Concrete.Package.source_restricted_scoped_sum_eq_restricted_sum_of_package
    pkg]
  rw [← Source.CCM25Concrete.Package.source_global_scoped_sum_eq_global_sum_of_package
    pkg]
  exact h.archimedeanContributionMatches

theorem source_common_atom_full_archimedean_contribution_matches_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceCommonAtomArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    SourceCommonAtomFullArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg := by
  dsimp [SourceCommonAtomArchimedeanContributionMatchesForRestriction,
    SourceCommonAtomFullArchimedeanContributionMatchesForRestriction] at h ⊢
  let hrestricted :=
    Package.source_common_restricted_scoped_sum_eq_common_restricted_sum_of_package
      pkg
  let hglobal :=
    Package.source_common_global_scoped_sum_eq_common_global_sum_of_package pkg
  rw [← hrestricted]
  rw [← hglobal]
  exact h

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
  have hcommonFull :
      SourceCommonAtomFullArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg :=
    Source.CCM25Concrete.Package.common_atom_archimedean_contribution_matches_of_package
      pkg (source_full_archimedean_contribution_matches_of_package _hread h)
  dsimp [SourceCommonAtomArchimedeanContributionMatchesForRestriction,
    SourceCommonAtomFullArchimedeanContributionMatchesForRestriction] at hcommonFull ⊢
  let hrestricted :=
    Package.source_common_restricted_scoped_sum_eq_common_restricted_sum_of_package
      pkg
  let hglobal :=
    Package.source_common_global_scoped_sum_eq_common_global_sum_of_package pkg
  rw [hrestricted]
  rw [hglobal]
  exact hcommonFull

theorem source_scoped_archimedean_contribution_matches_of_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (_hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (h :
      SourceArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    SourceScopedArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg := by
  simpa [SourceScopedArchimedeanContributionMatchesForRestriction,
    Source.CCM25Concrete.Package.ScopedArchimedeanContributionBalance,
    Source.CCM25Concrete.Package.ScopedRestrictedArchimedeanFormula,
    Source.CCM25Concrete.Package.ScopedGlobalArchimedeanFormula]
    using h.archimedeanContributionMatches

theorem source_scoped_archimedean_contribution_matches_of_scalar_equality
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (hscalar :
      inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
        inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest) :
    SourceScopedArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg := by
  let W := inputs.ccm25.weilSymbols
  dsimp [SourceScopedArchimedeanContributionMatchesForRestriction,
    Source.CCM25Concrete.Package.ScopedArchimedeanContributionBalance,
    Source.CCM25Concrete.Package.ScopedRestrictedArchimedeanFormula,
    Source.CCM25Concrete.Package.ScopedGlobalArchimedeanFormula]
  calc
    W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
          W.polePairing g.weilTest -
            Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
              pkg =
        W.qwLambda lambda g.weilTest g.weilTest :=
      (package_backed_qw_lambda_scoped_source_evaluator hread).symm
    _ = W.qw g.weilTest g.weilTest := hscalar
    _ =
        W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
              pkg :=
      package_backed_qw_scoped_source_evaluator hread

def source_archimedean_balance_rows_of_scalar_equality
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hwindow : WindowLambdaCompatibility inputs g lambda)
    (hscalar :
      inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
        inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest) :
    SourceArchimedeanContributionBalanceRows inputs g lambda pkg where
  scopedBalance :=
    source_scoped_archimedean_contribution_matches_of_scalar_equality
      (package_backed_ccm25_weil_form_read_off hwindow)
      hscalar

theorem source_scalar_equality_of_no_defect_global_formula
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {a : inputs.cc20.archimedeanSymbols.Test}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (hNoDefectQWLambda :
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
        inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest)
    (hNoDefectGlobal :
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
        inputs.ccm25.weilSymbols.poleFunctional
            (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) -
          inputs.ccm25.weilSymbols.archimedeanTerm
            (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
              pkg) :
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest := by
  let W := inputs.ccm25.weilSymbols
  calc
    W.qwLambda lambda g.weilTest g.weilTest =
        inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a :=
      hNoDefectQWLambda.symm
    _ =
        W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
              pkg :=
      hNoDefectGlobal
    _ = W.qw g.weilTest g.weilTest :=
      (package_backed_qw_scoped_source_evaluator hread).symm

theorem source_no_defect_global_formula_of_scalar_equality
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {a : inputs.cc20.archimedeanSymbols.Test}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hread : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (hNoDefectQWLambda :
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
        inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest)
    (hscalar :
      inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
        inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest) :
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
      inputs.ccm25.weilSymbols.poleFunctional
          (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) -
        inputs.ccm25.weilSymbols.archimedeanTerm
          (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) -
          Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
            pkg := by
  let W := inputs.ccm25.weilSymbols
  calc
    inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
        W.qwLambda lambda g.weilTest g.weilTest := hNoDefectQWLambda
    _ = W.qw g.weilTest g.weilTest := hscalar
    _ =
        W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
              pkg := package_backed_qw_scoped_source_evaluator hread

def source_archimedean_balance_rows_of_no_defect_global_formula
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {a : inputs.cc20.archimedeanSymbols.Test}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hwindow : WindowLambdaCompatibility inputs g lambda)
    (hNoDefectQWLambda :
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
        inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest)
    (hNoDefectGlobal :
      inputs.cc20.archimedeanSymbols.sourceNoDefectTrace a =
        inputs.ccm25.weilSymbols.poleFunctional
            (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) -
          inputs.ccm25.weilSymbols.archimedeanTerm
            (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
              pkg) :
    SourceArchimedeanContributionBalanceRows inputs g lambda pkg :=
  source_archimedean_balance_rows_of_scalar_equality
    hwindow
    (source_scalar_equality_of_no_defect_global_formula
      (package_backed_ccm25_weil_form_read_off hwindow)
      hNoDefectQWLambda
      hNoDefectGlobal)

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
  source_full_archimedean_contribution_matches_of_package
    (package_read_off_of_archimedean_pole_stability
      h.archimedeanPoleStability)
    h.archimedeanContributionMatches

theorem scoped_archimedean_contribution_equality_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    SourceScopedArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg :=
  h.archimedeanContributionMatches.archimedeanContributionMatches

theorem source_qw_lambda_eq_qw_of_qw_lambda_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg) :
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest := by
  let W := inputs.ccm25.weilSymbols
  calc
    W.qwLambda lambda g.weilTest g.weilTest =
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
          W.polePairing g.weilTest -
            Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
              pkg := package_backed_qw_lambda_scoped_source_evaluator
                h.restrictedDefinition.packageReadOff
    _ =
        W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
              pkg := by
      simpa [SourceScopedArchimedeanContributionMatchesForRestriction,
        Source.CCM25Concrete.Package.ScopedArchimedeanContributionBalance,
        Source.CCM25Concrete.Package.ScopedRestrictedArchimedeanFormula,
        Source.CCM25Concrete.Package.ScopedGlobalArchimedeanFormula]
        using h.archimedeanContributionMatches.archimedeanContributionMatches
    _ = W.qw g.weilTest g.weilTest :=
        (package_backed_qw_scoped_source_evaluator
          h.fullDefinition.packageReadOff).symm

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

noncomputable def restricted_to_full_no_spectral_convergence_import_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hwindow : SourceWindowControlsRestrictedRoute inputs g lambda)
    (hstabilization :
      RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg)
    (harch :
      SourceArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    RestrictedToFullNoSpectralConvergenceImport
      inputs g lambda F_g pkg where
  commonTuple := hcommon
  sourceWindowControlsRestrictedRoute := hwindow
  restrictedFormIsRestriction :=
    source_qw_lambda_is_restriction_of_common_tuple
      hcommon hstabilization harch
  finitePrimeSupportStabilizes := hstabilization
  archimedeanPoleStability :=
    source_archimedean_pole_stability_of_common_tuple hcommon
  archimedeanContributionMatches := harch

noncomputable def restricted_to_full_scalar_restriction_witness_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hwindow : SourceWindowControlsRestrictedRoute inputs g lambda)
    (hstabilization :
      RestrictedFinitePrimeSupportStabilizes inputs g lambda pkg)
    (harch :
      SourceArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    RestrictedToFullQWScalarRestrictionWitness
      inputs g lambda F_g pkg where
  commonTuple := hcommon
  sourceWindowControlsRestrictedRoute := hwindow
  restrictedFormIsRestriction :=
    source_qw_lambda_is_restriction_of_common_tuple
      hcommon hstabilization harch
  finitePrimeSupportStabilizes := hstabilization
  exactFinitePrimeSupport := package_exact_finite_prime_support_at_lambda_holds
  archimedeanPoleStability :=
    source_archimedean_pole_stability_of_common_tuple hcommon
  archimedeanContributionMatches := harch
  noSpectralConvergenceImport :=
    restricted_to_full_no_spectral_convergence_import_of_parts
      hcommon hwindow hstabilization harch

noncomputable def restricted_to_full_scalar_restriction_witness_of_common_tuple
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
    RestrictedToFullQWScalarRestrictionWitness
      inputs g lambda F_g pkg :=
  restricted_to_full_scalar_restriction_witness_of_parts
    hcommon
    (source_window_controls_restricted_route_of_window_lambda
      hcommon.windowLambdaCompatibility)
    hstabilization harch

theorem scoped_archimedean_contribution_matches_of_scalar_witness
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg) :
    SourceScopedArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg :=
  h.archimedeanContributionMatches.archimedeanContributionMatches

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

theorem scalar_equality_from_scoped_witness_components
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
  let hread :=
    package_read_off_of_archimedean_pole_stability
      (archimedean_pole_stability_of_scalar_witness h)
  have harchScoped :
      SourceScopedArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg :=
    scoped_archimedean_contribution_matches_of_scalar_witness h
  calc
    W.qwLambda lambda g.weilTest g.weilTest =
        W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) +
          W.polePairing g.weilTest -
            Source.CCM25Concrete.Package.source_restricted_finite_prime_evaluator_scoped_sum
              pkg := package_backed_qw_lambda_scoped_source_evaluator hread
    _ =
        W.poleFunctional (W.convolutionStar g.weilTest g.weilTest) -
          W.archimedeanTerm (W.convolutionStar g.weilTest g.weilTest) -
            Source.CCM25Concrete.Package.source_global_finite_prime_evaluator_scoped_sum
              pkg := by
      simpa [SourceScopedArchimedeanContributionMatchesForRestriction,
        Source.CCM25Concrete.Package.ScopedArchimedeanContributionBalance,
        Source.CCM25Concrete.Package.ScopedRestrictedArchimedeanFormula,
        Source.CCM25Concrete.Package.ScopedGlobalArchimedeanFormula]
        using harchScoped
    _ = W.qw g.weilTest g.weilTest :=
        (package_backed_qw_scoped_source_evaluator hread).symm

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
  scalar_equality_from_scoped_witness_components h

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

/--
Large-lambda restricted-to-full source rows before scalar restriction is
assembled.

These are the three upstream rows needed by
`restricted_to_full_large_lambda_threshold_of_archimedean_balance`: fixed-test
support containment, prime-power stabilization, and the archimedean
contribution balance.  The final scalar restriction witness is derived from
these rows rather than assumed directly.
-/
structure RestrictedToFullAsymptoticRows
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda0 : ℝ) (F_g : TestFunction) where
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
  archimedeanContributionAtLarge :
    ∀ lambda : ℝ,
      lambda0 ≤ lambda →
        ∀ pkg :
          Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
            inputs.ccm25.weilSymbols g.weilTest lambda,
          SourceCommonTestTupleContract inputs g lambda F_g pkg →
            SourceArchimedeanContributionMatchesForRestriction
              inputs g lambda pkg

noncomputable def restricted_to_full_large_lambda_threshold_of_archimedean_balance
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {F_g : TestFunction}
    (lambda0 : ℝ)
    (hlambda0 : 1 < lambda0)
    (thresholdPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda0)
    (thresholdTuple :
      SourceCommonTestTupleContract
        inputs g lambda0 F_g thresholdPackage)
    (supportThresholdAtLarge :
      ∀ lambda : ℝ,
        lambda0 ≤ lambda →
          FixedTestSupportThresholdAtLarge inputs g lambda)
    (primePowerAtomStabilizationAtLarge :
      ∀ lambda : ℝ,
        lambda0 ≤ lambda →
          ∀ pkg :
            Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
              inputs.ccm25.weilSymbols g.weilTest lambda,
            SourceCommonTestTupleContract inputs g lambda F_g pkg →
              PrimePowerAtomStabilizationAtLarge inputs g lambda pkg)
    (archimedeanContributionAtLarge :
      ∀ lambda : ℝ,
        lambda0 ≤ lambda →
          ∀ pkg :
            Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
              inputs.ccm25.weilSymbols g.weilTest lambda,
            SourceCommonTestTupleContract inputs g lambda F_g pkg →
              SourceArchimedeanContributionMatchesForRestriction
                inputs g lambda pkg) :
    RestrictedToFullQWLargeLambdaThreshold inputs g F_g where
  lambda0 := lambda0
  oneLtLambda0 := hlambda0
  thresholdPackage := thresholdPackage
  thresholdTuple := thresholdTuple
  supportThresholdAtLarge := supportThresholdAtLarge
  primePowerAtomStabilizationAtLarge := primePowerAtomStabilizationAtLarge
  scalarRestrictionAtLarge := by
    intro lambda habove pkg hcommon
    exact
      restricted_to_full_scalar_restriction_witness_of_common_tuple
        hcommon
        { fixedTestSupport := supportThresholdAtLarge lambda habove
          primePowerAtomStabilization :=
            primePowerAtomStabilizationAtLarge lambda habove pkg hcommon }
        (archimedeanContributionAtLarge lambda habove pkg hcommon)

noncomputable def restricted_to_full_large_lambda_threshold_of_asymptotic_rows
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda0 : ℝ} {F_g : TestFunction}
    (hlambda0 : 1 < lambda0)
    (thresholdPackage :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda0)
    (thresholdTuple :
      SourceCommonTestTupleContract
        inputs g lambda0 F_g thresholdPackage)
    (rows : RestrictedToFullAsymptoticRows inputs g lambda0 F_g) :
    RestrictedToFullQWLargeLambdaThreshold inputs g F_g :=
  restricted_to_full_large_lambda_threshold_of_archimedean_balance
    lambda0 hlambda0 thresholdPackage thresholdTuple
    rows.supportThresholdAtLarge
    rows.primePowerAtomStabilizationAtLarge
    rows.archimedeanContributionAtLarge

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

theorem current_one_lt_lambda_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda) :
    1 < lambda :=
  lt_of_lt_of_le threshold.oneLtLambda0 habove

noncomputable def current_threshold_data_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    RestrictedToFullCurrentThresholdData inputs g lambda F_g pkg :=
  current_threshold_data_of_large_lambda_threshold
    threshold habove hcommon

noncomputable def scalar_restriction_witness_of_large_lambda_threshold
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (harch :
      SourceArchimedeanContributionMatchesForRestriction
        inputs g lambda pkg) :
    RestrictedToFullQWScalarRestrictionWitness
      inputs g lambda F_g pkg :=
  restricted_to_full_scalar_restriction_witness_of_common_tuple
    hcommon
    (current_threshold_data_of_large_lambda_threshold
      threshold habove hcommon).finitePrimeStabilization
    harch

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
  scalarEquality := scalar_equality_from_scoped_witness_components hwitness

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

theorem scoped_archimedean_contribution_matches_of_scalar_restriction
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullQWScalarRestrictionEquality
        inputs g lambda F_g pkg) :
    SourceScopedArchimedeanContributionMatchesForRestriction
      inputs g lambda pkg :=
  scoped_archimedean_contribution_matches_of_scalar_witness
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

structure RestrictedToFullCurrentCutoffBinding
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  commonTuple :
    SourceCommonTestTupleContract inputs g lambda F_g pkg
  currentThresholdData :
    RestrictedToFullCurrentThresholdData inputs g lambda F_g pkg
  scalarRestrictionWitness :
    RestrictedToFullQWScalarRestrictionWitness inputs g lambda F_g pkg
  lowerBoundEvidence :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L
  currentUsesCommonTuple : currentThresholdData.commonTuple = commonTuple
  witnessUsesCommonTuple : scalarRestrictionWitness.commonTuple = commonTuple

noncomputable def restricted_to_full_current_cutoff_binding_of_common_tuple
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
    RestrictedToFullCurrentCutoffBinding inputs g lambda F_g L pkg where
  commonTuple := hcommon
  currentThresholdData :=
    current_threshold_data_of_large_lambda_threshold
      threshold habove hcommon
  scalarRestrictionWitness :=
    threshold.scalarRestrictionAtLarge lambda habove pkg hcommon
  lowerBoundEvidence := hevidence
  currentUsesCommonTuple := Subsingleton.elim _ _
  witnessUsesCommonTuple := Subsingleton.elim _ _

noncomputable def restricted_to_full_current_cutoff_binding_of_sign_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hsign : SourceSignDefectClassification inputs g lambda L) :
    RestrictedToFullCurrentCutoffBinding inputs g lambda F_g L pkg :=
  restricted_to_full_current_cutoff_binding_of_common_tuple
    threshold habove hcommon
    (row7_endpoint_strip_cdef_domination_of_sign_defect_classification hsign)

noncomputable def restricted_to_full_current_cutoff_binding_of_route_ledger_semantics
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hledger : RouteLedgerSemanticData inputs g lambda L) :
    RestrictedToFullCurrentCutoffBinding inputs g lambda F_g L pkg :=
  restricted_to_full_current_cutoff_binding_of_common_tuple
    threshold habove hcommon hledger.endpointStripCdefDomination

noncomputable def restricted_to_full_current_cutoff_binding_of_s2b1_route_ledger_input
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hledger : S2B1RouteLedgerSemanticInput inputs g lambda L) :
    RestrictedToFullCurrentCutoffBinding inputs g lambda F_g L pkg :=
  restricted_to_full_current_cutoff_binding_of_route_ledger_semantics
    threshold habove hcommon hledger.toRouteLedgerSemanticData

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

def restricted_to_full_bridge_contract_of_current_threshold_data
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcurrent :
      RestrictedToFullCurrentThresholdData inputs g lambda F_g pkg)
    (hwitness :
      RestrictedToFullQWScalarRestrictionWitness
        inputs g lambda F_g pkg)
    (hevidence :
      RestrictedToFullQWLowerBoundEvidence inputs g lambda L) :
    RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg where
  largeLambdaThreshold := hcurrent.largeLambdaThreshold
  currentAboveThreshold := hcurrent.currentAboveThreshold
  currentThresholdData := hcurrent
  scalarRestrictionWitness := hwitness
  scalarRestrictionEquality :=
    restricted_to_full_scalar_restriction_of_common_tuple hwitness
  exactFinitePrimeSupport :=
    exact_finite_prime_support_of_scalar_restriction
      (restricted_to_full_scalar_restriction_of_common_tuple hwitness)
  lowerBoundEvidence := hevidence

def restricted_to_full_bridge_contract_of_current_cutoff_binding
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullCurrentCutoffBinding inputs g lambda F_g L pkg) :
    RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg :=
  restricted_to_full_bridge_contract_of_current_threshold_data
    h.currentThresholdData h.scalarRestrictionWitness h.lowerBoundEvidence

structure RestrictedToFullThresholdBridgePackage
    (inputs : RouteInputs) (g : SourceBackedFixedSTest inputs)
    (lambda : ℝ) (F_g : TestFunction) (L : RouteLedgers)
    (pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda) where
  currentCutoff :
    RestrictedToFullCurrentCutoffBinding inputs g lambda F_g L pkg
  bridgeContract :
    RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg
  bridgeContractMatchesCurrentCutoff :
    bridgeContract =
      restricted_to_full_bridge_contract_of_current_cutoff_binding
        currentCutoff

noncomputable def restricted_to_full_threshold_bridge_package_of_current_cutoff
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullCurrentCutoffBinding inputs g lambda F_g L pkg) :
    RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg where
  currentCutoff := h
  bridgeContract :=
    restricted_to_full_bridge_contract_of_current_cutoff_binding h
  bridgeContractMatchesCurrentCutoff := rfl

noncomputable def restricted_to_full_threshold_bridge_package_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hlower : RestrictedToFullQWLowerBoundEvidence inputs g lambda L) :
  RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg :=
  restricted_to_full_threshold_bridge_package_of_current_cutoff
    (restricted_to_full_current_cutoff_binding_of_common_tuple
      threshold habove hcommon hlower)

noncomputable def restricted_to_full_threshold_bridge_package_of_sign_defect
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hsign : SourceSignDefectClassification inputs g lambda L) :
    RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg :=
  restricted_to_full_threshold_bridge_package_of_current_cutoff
    (restricted_to_full_current_cutoff_binding_of_sign_defect
      threshold habove hcommon hsign)

noncomputable def restricted_to_full_threshold_bridge_package_of_route_ledger_semantics
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hledger : RouteLedgerSemanticData inputs g lambda L) :
    RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg :=
  restricted_to_full_threshold_bridge_package_of_current_cutoff
    (restricted_to_full_current_cutoff_binding_of_route_ledger_semantics
      threshold habove hcommon hledger)

noncomputable def restricted_to_full_threshold_bridge_package_of_s2b1_route_ledger_input
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (threshold : RestrictedToFullQWLargeLambdaThreshold inputs g F_g)
    (habove : threshold.lambda0 ≤ lambda)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hledger : S2B1RouteLedgerSemanticInput inputs g lambda L) :
    RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg :=
  restricted_to_full_threshold_bridge_package_of_route_ledger_semantics
    threshold habove hcommon hledger.toRouteLedgerSemanticData

def large_lambda_threshold_of_restricted_to_full_threshold_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg) :
    RestrictedToFullQWLargeLambdaThreshold inputs g F_g :=
  h.currentCutoff.currentThresholdData.largeLambdaThreshold

def current_above_threshold_of_restricted_to_full_threshold_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg) :
    h.currentCutoff.currentThresholdData.largeLambdaThreshold.lambda0 ≤
      lambda :=
  h.currentCutoff.currentThresholdData.currentAboveThreshold

def restricted_to_full_bridge_contract_of_threshold_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg) :
    RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg :=
  h.bridgeContract

theorem bridge_contract_matches_current_cutoff_of_threshold_package
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h :
      RestrictedToFullThresholdBridgePackage inputs g lambda F_g L pkg) :
    restricted_to_full_bridge_contract_of_threshold_package h =
      restricted_to_full_bridge_contract_of_current_cutoff_binding
        h.currentCutoff := by
  rw [restricted_to_full_bridge_contract_of_threshold_package,
    h.bridgeContractMatchesCurrentCutoff]

noncomputable def restricted_to_full_bridge_contract_of_common_tuple_binding
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
  restricted_to_full_bridge_contract_of_current_cutoff_binding
    (restricted_to_full_current_cutoff_binding_of_common_tuple
      threshold habove hcommon hevidence)

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

theorem source_qw_uses_common_test_of_parts
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (windowLambdaCompatibility : WindowLambdaCompatibility inputs g lambda)
    (packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (squareCompatibility :
      SourceConvolutionSquareCompatibility inputs g lambda F_g pkg) :
    SourceQWUsesCommonTest inputs g lambda F_g pkg :=
  { commonTestTuple :=
      source_common_test_tuple_contract_of_parts
        windowLambdaCompatibility packageReadOff squareCompatibility
    packageReadOff := packageReadOff
    squareCompatibility := squareCompatibility }

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
  let hrestrictedScopedPairing :=
    Source.CCM25Concrete.Package.restricted_von_mangoldt_pairing_scoped_sum_common_atoms_of_package
      pkg
  exact
    { windowLambdaCompatibility := hread.windowLambdaCompatibility
      finitePrimeConcreteObject :=
        Source.CCM25Concrete.Package.finite_prime_concrete_object_of_package
          pkg
      globalFinitePrimeSumReadOff :=
        package_backed_global_finite_prime_sum hread
      globalFinitePrimeScopedSumReadOff :=
        Source.CCM25Concrete.Package.global_finite_prime_scoped_sum_common_atoms_of_package
          pkg
      restrictedFinitePrimeSumReadOff :=
        package_backed_restricted_finite_prime_sum hread
      restrictedFinitePrimeScopedSumReadOff :=
        Source.CCM25Concrete.Package.restricted_finite_prime_scoped_sum_common_atoms_of_package
          pkg
      globalVonMangoldtPairingSumReadOff :=
        Source.CCM25Concrete.Package.finite_prime_concrete_object_global_pairing_sum_read_off
          pkg
      globalVonMangoldtPairingScopedSumReadOff :=
        Source.CCM25Concrete.Package.global_von_mangoldt_pairing_scoped_sum_common_atoms_of_package
          pkg
      restrictedVonMangoldtPairingSumReadOff :=
        Source.CCM25Concrete.Package.finite_prime_concrete_object_restricted_pairing_sum_read_off
          pkg
      restrictedVonMangoldtPairingScopedSumReadOff :=
        hrestrictedScopedPairing }

noncomputable def prime_power_atom_stabilization_of_common_tuple
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    PrimePowerAtomStabilizationAtLarge inputs g lambda pkg where
  finitePrimeSignOwned :=
    source_finite_prime_sign_owned_by_common_test
      (source_qw_uses_common_test_of_common_tuple hcommon)
  supportStabilization :=
    package_finite_prime_support_stabilization

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
  hilbertSchmidtGate : inputs.cc20.archimedeanSymbols.hilbertSchmidtGate a
  signsAndNormalizations :
    (Source.cc20SignsAndNormalizations
      inputs.cc20.archimedeanSymbols).Holds
  mellinHalfDensityConvention :
    (Source.cc20MellinHalfDensityConvention
      inputs.cc20.archimedeanSymbols).Holds

def source_archimedean_sign_bridge_of_source_trace_read_off
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    (h : SourceTraceReadOffData inputs g) :
    SourceArchimedeanSignBridge inputs h.archimedeanTest g where
  hilbertSchmidtGate := h.hilbertSchmidtGate
  signsAndNormalizations := inputs.cc20.signsAndNormalizations
  mellinHalfDensityConvention := inputs.cc20.mellinHalfDensityConvention

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
  traceLegality : CC20TraceLegality inputs a
  positiveTraceNonnegative : CC20PositiveTraceNonnegative inputs a
  signsAndNormalizations :
    (Source.cc20SignsAndNormalizations
      inputs.cc20.archimedeanSymbols).Holds
  mellinHalfDensityConvention :
    (Source.cc20MellinHalfDensityConvention
      inputs.cc20.archimedeanSymbols).Holds
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

noncomputable def source_qw_equals_neg_cc20_weil_sum_of_common_test_parts
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (windowLambdaCompatibility : WindowLambdaCompatibility inputs g lambda)
    (packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (squareCompatibility :
      SourceConvolutionSquareCompatibility inputs g lambda F_g pkg)
    (hilbertSchmidtGate :
      inputs.cc20.archimedeanSymbols.hilbertSchmidtGate a)
    (signsAndNormalizations :
      (Source.cc20SignsAndNormalizations
        inputs.cc20.archimedeanSymbols).Holds)
    (mellinHalfDensityConvention :
      (Source.cc20MellinHalfDensityConvention
        inputs.cc20.archimedeanSymbols).Holds) :
    SourceQWEqualsNegCC20WeilSum inputs a g lambda F_g pkg :=
  let hcommon :=
    source_qw_uses_common_test_of_parts
      windowLambdaCompatibility packageReadOff squareCompatibility
  let traceLegality :=
    (cc20_trace_legality_template_output hilbertSchmidtGate).traceLegality
  let traceSquare :=
    cc20_archimedean_trace_square_output traceLegality
  { sourceQWUsesCommonTest := hcommon
    sourcePsiSignExpansion := source_psi_sign_expansion_of_common_test hcommon
    traceLegality := traceLegality
    positiveTraceNonnegative := traceSquare.positiveTraceNonnegative
    signsAndNormalizations := signsAndNormalizations
    mellinHalfDensityConvention := mellinHalfDensityConvention
    sourceFinitePrimeSignOwnedByPackage :=
      source_finite_prime_sign_owned_by_common_test hcommon
    sourcePoleSignInCC20LocalSum :=
      source_pole_sign_in_cc20_local_sum_of_common_test hcommon }

noncomputable def source_qw_nonnegative_to_cc20_nonpositive_of_common_test_parts
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (windowLambdaCompatibility : WindowLambdaCompatibility inputs g lambda)
    (packageReadOff : PackageBackedCCM25WeilFormReadOff inputs g lambda pkg)
    (squareCompatibility :
      SourceConvolutionSquareCompatibility inputs g lambda F_g pkg)
    (hilbertSchmidtGate :
      inputs.cc20.archimedeanSymbols.hilbertSchmidtGate a)
    (signsAndNormalizations :
      (Source.cc20SignsAndNormalizations
        inputs.cc20.archimedeanSymbols).Holds)
    (mellinHalfDensityConvention :
      (Source.cc20MellinHalfDensityConvention
        inputs.cc20.archimedeanSymbols).Holds) :
    SourceQWNonnegativeToCC20Nonpositive inputs a g lambda F_g pkg :=
  source_qw_equals_neg_cc20_weil_sum_of_common_test_parts
    windowLambdaCompatibility
    packageReadOff
    squareCompatibility
    hilbertSchmidtGate
    signsAndNormalizations
    mellinHalfDensityConvention

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
  sourceTraceReadOff : SourceRouteTraceData inputs g
  ledgerPackage :
    LedgerSignDefectPackage inputs g sourceTraceReadOff.lambda
  ledgerPackageLedgers : ledgerPackage.ledgers = L
  finalSignNonpositive :
    SourceQWNonnegativeToCC20Nonpositive inputs sourceTraceReadOff.archimedeanTest g
      sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      sourceTraceReadOff.ccm25ArithmeticPackage

def route_bridge_certificate_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (sourceTraceReadOff : SourceRouteTraceData inputs g)
    (signDefectClassification :
      SourceSignDefectClassification inputs g sourceTraceReadOff.lambda L)
    (finalSignNonpositive :
      SourceQWNonnegativeToCC20Nonpositive inputs sourceTraceReadOff.archimedeanTest g
        sourceTraceReadOff.lambda
        (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
        sourceTraceReadOff.ccm25ArithmeticPackage) :
    RouteBridgeCertificate inputs g L where
  sourceTraceReadOff := sourceTraceReadOff
  ledgerPackage :=
    ledger_sign_defect_package_of_source_backed_ledgers
      (source_backed_ledgers_of_sign_defect_classification
        signDefectClassification)
  ledgerPackageLedgers := rfl
  finalSignNonpositive := finalSignNonpositive

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

def source_qw_lambda_restriction_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    SourceQWLambdaIsRestrictionOfQW inputs g lambda pkg :=
  h.scalarRestrictionWitness.restrictedFormIsRestriction

theorem source_qw_lambda_eq_qw_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    inputs.ccm25.weilSymbols.qwLambda lambda g.weilTest g.weilTest =
      inputs.ccm25.weilSymbols.qw g.weilTest g.weilTest :=
  scalar_equality_of_scalar_restriction
    (scalar_restriction_equality_of_restricted_to_full_contract h)

theorem archimedean_contribution_matches_of_restricted_to_full_contract
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction} {L : RouteLedgers}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (h : RestrictedToFullQWBridgeContract inputs g lambda F_g L pkg) :
    SourceArchimedeanContributionMatchesForRestriction inputs g lambda pkg :=
  h.scalarRestrictionWitness.archimedeanContributionMatches

theorem lower_bound_evidence_of_sign_defect_classification
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : SourceSignDefectClassification inputs g lambda L) :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L :=
  row7_endpoint_strip_cdef_domination_of_sign_defect_classification h

theorem lower_bound_evidence_of_route_ledger_semantics
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : RouteLedgerSemanticData inputs g lambda L) :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L :=
  h.endpointStripCdefDomination

theorem lower_bound_evidence_of_s2b1_route_ledger_input
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {L : RouteLedgers}
    (h : S2B1RouteLedgerSemanticInput inputs g lambda L) :
    RestrictedToFullQWLowerBoundEvidence inputs g lambda L :=
  h.endpointStripCdefDomination

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
  source_qw_equals_neg_cc20_weil_sum_of_common_test_parts
    h.sourceQWUsesCommonTest.commonTestTuple.windowLambdaCompatibility
    h.sourceQWUsesCommonTest.packageReadOff
    h.sourceQWUsesCommonTest.squareCompatibility
    h.sourceArchimedeanSignBridge.hilbertSchmidtGate
    h.sourceArchimedeanSignBridge.signsAndNormalizations
    h.sourceArchimedeanSignBridge.mellinHalfDensityConvention

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

def final_sign_bridge_contract_of_common_tuple
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hsign : SourceArchimedeanSignBridge inputs a g) :
    FinalSignBridgeContract inputs a g lambda F_g pkg :=
  final_sign_bridge_contract_of_common_test
    (source_qw_uses_common_test_of_common_tuple hcommon)
    hsign

def final_sign_bridge_contract_of_common_tuple_and_source_trace
    {inputs : RouteInputs}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (htrace : SourceTraceReadOffData inputs g)
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg) :
    FinalSignBridgeContract inputs htrace.archimedeanTest g lambda F_g pkg :=
  final_sign_bridge_contract_of_common_tuple
    hcommon
    (source_archimedean_sign_bridge_of_source_trace_read_off htrace)

noncomputable def final_sign_nonnegative_to_nonpositive_of_common_tuple
    {inputs : RouteInputs}
    {a : inputs.cc20.archimedeanSymbols.Test}
    {g : SourceBackedFixedSTest inputs}
    {lambda : ℝ} {F_g : TestFunction}
    {pkg :
      Source.CCM25Concrete.Package.ConcreteCCM25ArithmeticPackage
        inputs.ccm25.weilSymbols g.weilTest lambda}
    (hcommon : SourceCommonTestTupleContract inputs g lambda F_g pkg)
    (hsign : SourceArchimedeanSignBridge inputs a g) :
    SourceQWNonnegativeToCC20Nonpositive inputs a g lambda F_g pkg :=
  final_sign_nonnegative_to_nonpositive_of_contract
    (final_sign_bridge_contract_of_common_tuple hcommon hsign)

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
      ArithmeticFunction.vonMangoldt n :=
  Source.CCM25Concrete.FinitePrimeCertificate.concrete_object_weight_read_off
    h.finitePrimeConcreteObject n

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
  Source.CCM25Concrete.FinitePrimeCertificate.concrete_object_term_formula_source_evaluator
    h.finitePrimeConcreteObject n

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
  Source.CCM25Concrete.FinitePrimeCertificate.concrete_object_pairing_formula_source_evaluator
    h.finitePrimeConcreteObject n

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

def final_sign_nonpositive_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : RouteBridgeCertificate inputs g L) :
    SourceQWNonnegativeToCC20Nonpositive inputs h.sourceTraceReadOff.archimedeanTest g
      h.sourceTraceReadOff.lambda
      (inputs.ccm25.weilSymbols.convolutionStar g.weilTest g.weilTest)
      h.sourceTraceReadOff.ccm25ArithmeticPackage :=
  h.finalSignNonpositive

def source_backed_full_positivity_of_route_bridge_certificate
    {inputs : RouteInputs} {g : SourceBackedFixedSTest inputs}
    {L : RouteLedgers}
    (h : RouteBridgeCertificate inputs g L) :
    SourceBackedFullPositivity inputs g L :=
  ⟨h.sourceTraceReadOff, h.ledgerPackage, h.ledgerPackageLedgers⟩

end Route
end ConnesWeilRH
