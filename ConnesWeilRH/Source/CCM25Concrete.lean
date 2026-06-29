/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.CCM25Concrete.Global
import ConnesWeilRH.Source.CCM25Concrete.Restricted
import ConnesWeilRH.Source.CCM25Concrete.FinitePrime
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeExact
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerTest
import ConnesWeilRH.Source.CCM25Concrete.CommonSourceTest
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerEvaluation
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerPairing
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerArithmetic
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerSupport
import ConnesWeilRH.Source.CCM25Concrete.PrimePowerTerm
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeCertificate
import ConnesWeilRH.Source.CCM25Concrete.FinitePrimeInterface
import ConnesWeilRH.Source.CCM25Concrete.Rows
import ConnesWeilRH.Source.CCM25Concrete.Interface
import ConnesWeilRH.Source.CCM25Concrete.GlobalComponent
import ConnesWeilRH.Source.CCM25Concrete.RestrictedComponent
import ConnesWeilRH.Source.CCM25Concrete.FormulaComponents
import ConnesWeilRH.Source.CCM25Concrete.Package

/-!
# CCM25 concrete normalization spine

This aggregate module imports the small CCM25 normalization modules. The files
are split so each source-interface row can be built and audited independently.
-/
