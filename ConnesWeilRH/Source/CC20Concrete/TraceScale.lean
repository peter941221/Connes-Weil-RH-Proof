/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

import ConnesWeilRH.Source.Objects
import ConnesWeilRH.Source.CC20TraceModel

/-!
# CC20 concrete trace-scale seed

This module starts the CC20 concrete source layer for Goal 4J.  It fixes the
ordinary positive trace, support-square trace, and source no-defect trace to the
same scalar family by definition.  The scalar read-off theorems below unfold
those definitions; they do not project the corresponding laws from
`CC20TraceModel`.

The nonnegativity, trace-class/cyclicity, Mellin convention, and sign
normalization rows remain separate analytic obligations.
-/

namespace ConnesWeilRH
namespace Source
namespace CC20Concrete
namespace TraceScale

/--
Concrete trace-scale symbols with the three S2-B1 scalar traces normalized to
the same support-square scalar family.
-/
structure ConcreteTraceScaleSymbols where
  Test : Type
  supportSquareTrace : Test → ℝ
  traceClass : Test → Prop
  cyclicLegal : Test → Prop
  hilbertSchmidtGate : Test → Prop
  mellinHalfDensityMatched : Prop
  uInfinityNormalized : Prop
  qduNormalized : Prop
  archimedeanSignNormalized : Prop

namespace ConcreteTraceScaleSymbols

def sourceNoDefectTrace (A : ConcreteTraceScaleSymbols) : A.Test → ℝ :=
  A.supportSquareTrace

def positiveTrace (A : ConcreteTraceScaleSymbols) : A.Test → ℝ :=
  A.supportSquareTrace

def toArchimedeanTraceSymbols
    (A : ConcreteTraceScaleSymbols) : ArchimedeanTraceSymbols where
  Test := A.Test
  supportSquareTrace := A.supportSquareTrace
  sourceNoDefectTrace := A.sourceNoDefectTrace
  positiveTrace := A.positiveTrace
  traceClass := A.traceClass
  cyclicLegal := A.cyclicLegal
  hilbertSchmidtGate := A.hilbertSchmidtGate
  mellinHalfDensityMatched := A.mellinHalfDensityMatched
  uInfinityNormalized := A.uInfinityNormalized
  qduNormalized := A.qduNormalized
  archimedeanSignNormalized := A.archimedeanSignNormalized

theorem source_no_defect_trace_read_off
    (A : ConcreteTraceScaleSymbols) (g : A.Test) :
    A.sourceNoDefectTrace g = A.supportSquareTrace g :=
  rfl

theorem positive_trace_read_off
    (A : ConcreteTraceScaleSymbols) (g : A.Test) :
    A.positiveTrace g = A.supportSquareTrace g :=
  rfl

theorem ordinary_trace_support_square_statement
    (A : ConcreteTraceScaleSymbols) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      A.toArchimedeanTraceSymbols := by
  intro g _htrace _hcyclic
  rfl

theorem support_square_no_defect_statement
    (A : ConcreteTraceScaleSymbols) :
    ∀ g : A.toArchimedeanTraceSymbols.Test,
      A.toArchimedeanTraceSymbols.traceClass g →
        A.toArchimedeanTraceSymbols.cyclicLegal g →
          A.toArchimedeanTraceSymbols.supportSquareTrace g =
            A.toArchimedeanTraceSymbols.sourceNoDefectTrace g := by
  intro g _htrace _hcyclic
  rfl

def PositiveTraceNonnegativeStatement
    (A : ConcreteTraceScaleSymbols) : Prop :=
  ∀ g : A.Test, A.traceClass g → A.cyclicLegal g → 0 ≤ A.positiveTrace g

theorem trace_square_statement_of_nonnegative
    (A : ConcreteTraceScaleSymbols)
    (hpos : PositiveTraceNonnegativeStatement A) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      A.toArchimedeanTraceSymbols := by
  intro g htrace hcyclic
  exact ⟨rfl, hpos g htrace hcyclic⟩

def TraceClassTemplateStatement
    (A : ConcreteTraceScaleSymbols) : Prop :=
  ∀ g : A.Test, A.hilbertSchmidtGate g → A.traceClass g ∧ A.cyclicLegal g

theorem trace_class_template_statement
    (A : ConcreteTraceScaleSymbols)
    (h : TraceClassTemplateStatement A) :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      A.toArchimedeanTraceSymbols :=
  h

theorem mellin_half_density_convention_statement
    (A : ConcreteTraceScaleSymbols)
    (hmellin : A.mellinHalfDensityMatched) :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      A.toArchimedeanTraceSymbols := by
  exact hmellin

theorem signs_and_normalizations_statement
    (A : ConcreteTraceScaleSymbols)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      A.toArchimedeanTraceSymbols := by
  exact hsigns

end ConcreteTraceScaleSymbols

/--
Concrete trace-scale data whose support-square trace is a literal square.

This is the first CC20 concrete positivity seed: positive-trace nonnegativity
comes from `sq_nonneg`, not from a `CC20TraceModel` field.
-/
structure SquareTraceScaleSymbols where
  Test : Type
  traceAmplitude : Test → ℝ
  traceClass : Test → Prop
  cyclicLegal : Test → Prop
  hilbertSchmidtGate : Test → Prop
  mellinHalfDensityMatched : Prop
  uInfinityNormalized : Prop
  qduNormalized : Prop
  archimedeanSignNormalized : Prop

namespace SquareTraceScaleSymbols

def supportSquareTrace (A : SquareTraceScaleSymbols) : A.Test → ℝ :=
  fun g => A.traceAmplitude g ^ 2

def toConcreteTraceScaleSymbols
    (A : SquareTraceScaleSymbols) : ConcreteTraceScaleSymbols where
  Test := A.Test
  supportSquareTrace := A.supportSquareTrace
  traceClass := A.traceClass
  cyclicLegal := A.cyclicLegal
  hilbertSchmidtGate := A.hilbertSchmidtGate
  mellinHalfDensityMatched := A.mellinHalfDensityMatched
  uInfinityNormalized := A.uInfinityNormalized
  qduNormalized := A.qduNormalized
  archimedeanSignNormalized := A.archimedeanSignNormalized

theorem support_square_trace_read_off
    (A : SquareTraceScaleSymbols) (g : A.Test) :
    A.supportSquareTrace g = A.traceAmplitude g ^ 2 :=
  rfl

theorem positive_trace_nonnegative_statement
    (A : SquareTraceScaleSymbols) :
    A.toConcreteTraceScaleSymbols.PositiveTraceNonnegativeStatement := by
  intro g _htrace _hcyclic
  exact sq_nonneg (A.traceAmplitude g)

theorem ordinary_trace_support_square_statement
    (A : SquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      A.toConcreteTraceScaleSymbols.toArchimedeanTraceSymbols :=
  A.toConcreteTraceScaleSymbols.ordinary_trace_support_square_statement

theorem trace_square_statement
    (A : SquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      A.toConcreteTraceScaleSymbols.toArchimedeanTraceSymbols :=
  A.toConcreteTraceScaleSymbols.trace_square_statement_of_nonnegative
    A.positive_trace_nonnegative_statement

end SquareTraceScaleSymbols

/--
Square-form trace-scale data whose Hilbert-Schmidt gate is definitionally the
trace-class/cyclicity pair.

This removes the trace-class/cyclicity template input for this concrete seed.
-/
structure LegalSquareTraceScaleSymbols where
  Test : Type
  traceAmplitude : Test → ℝ
  traceClass : Test → Prop
  cyclicLegal : Test → Prop
  mellinHalfDensityMatched : Prop
  uInfinityNormalized : Prop
  qduNormalized : Prop
  archimedeanSignNormalized : Prop

namespace LegalSquareTraceScaleSymbols

def hilbertSchmidtGate (A : LegalSquareTraceScaleSymbols) : A.Test → Prop :=
  fun g => A.traceClass g ∧ A.cyclicLegal g

def toSquareTraceScaleSymbols
    (A : LegalSquareTraceScaleSymbols) : SquareTraceScaleSymbols where
  Test := A.Test
  traceAmplitude := A.traceAmplitude
  traceClass := A.traceClass
  cyclicLegal := A.cyclicLegal
  hilbertSchmidtGate := A.hilbertSchmidtGate
  mellinHalfDensityMatched := A.mellinHalfDensityMatched
  uInfinityNormalized := A.uInfinityNormalized
  qduNormalized := A.qduNormalized
  archimedeanSignNormalized := A.archimedeanSignNormalized

theorem trace_class_template_statement
    (A : LegalSquareTraceScaleSymbols) :
    ConcreteTraceScaleSymbols.TraceClassTemplateStatement
      A.toSquareTraceScaleSymbols.toConcreteTraceScaleSymbols := by
  intro g hgate
  exact hgate

theorem positive_trace_nonnegative_statement
    (A : LegalSquareTraceScaleSymbols) :
    ConcreteTraceScaleSymbols.PositiveTraceNonnegativeStatement
      A.toSquareTraceScaleSymbols.toConcreteTraceScaleSymbols :=
  A.toSquareTraceScaleSymbols.positive_trace_nonnegative_statement

theorem trace_square_statement
    (A : LegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (ConcreteTraceScaleSymbols.toArchimedeanTraceSymbols
        A.toSquareTraceScaleSymbols.toConcreteTraceScaleSymbols) :=
  A.toSquareTraceScaleSymbols.trace_square_statement

theorem ordinary_trace_support_square_statement
    (A : LegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (ConcreteTraceScaleSymbols.toArchimedeanTraceSymbols
        A.toSquareTraceScaleSymbols.toConcreteTraceScaleSymbols) :=
  A.toSquareTraceScaleSymbols.ordinary_trace_support_square_statement

end LegalSquareTraceScaleSymbols

/--
Fully normalized legal square trace-scale data.

This seed fixes Mellin and sign normalization propositions to `True`, so the
trace model constructor has no remaining proof inputs.  It is still only a
concrete seed until a source-identification theorem relates the actual CC20
operators to these definitions.
-/
structure NormalizedLegalSquareTraceScaleSymbols where
  Test : Type
  traceAmplitude : Test → ℝ
  traceClass : Test → Prop
  cyclicLegal : Test → Prop

namespace NormalizedLegalSquareTraceScaleSymbols

def toLegalSquareTraceScaleSymbols
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    LegalSquareTraceScaleSymbols where
  Test := A.Test
  traceAmplitude := A.traceAmplitude
  traceClass := A.traceClass
  cyclicLegal := A.cyclicLegal
  mellinHalfDensityMatched := True
  uInfinityNormalized := True
  qduNormalized := True
  archimedeanSignNormalized := True

theorem mellin_half_density_convention
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    A.toLegalSquareTraceScaleSymbols.mellinHalfDensityMatched :=
  trivial

theorem signs_and_normalizations
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    A.toLegalSquareTraceScaleSymbols.uInfinityNormalized ∧
      A.toLegalSquareTraceScaleSymbols.qduNormalized ∧
        A.toLegalSquareTraceScaleSymbols.archimedeanSignNormalized :=
  ⟨trivial, trivial, trivial⟩

theorem trace_square_statement
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (ConcreteTraceScaleSymbols.toArchimedeanTraceSymbols
        (SquareTraceScaleSymbols.toConcreteTraceScaleSymbols
          (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
            A.toLegalSquareTraceScaleSymbols))) :=
  A.toLegalSquareTraceScaleSymbols.trace_square_statement

theorem trace_class_template_statement
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    ConcreteTraceScaleSymbols.TraceClassTemplateStatement
      (SquareTraceScaleSymbols.toConcreteTraceScaleSymbols
        (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
          A.toLegalSquareTraceScaleSymbols)) :=
  A.toLegalSquareTraceScaleSymbols.trace_class_template_statement

theorem ordinary_trace_support_square_statement
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (ConcreteTraceScaleSymbols.toArchimedeanTraceSymbols
        (SquareTraceScaleSymbols.toConcreteTraceScaleSymbols
          (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
            A.toLegalSquareTraceScaleSymbols))) :=
  A.toLegalSquareTraceScaleSymbols.ordinary_trace_support_square_statement

end NormalizedLegalSquareTraceScaleSymbols

/-- Constructor for a CC20 trace model from concrete trace-scale data. -/
def toCC20TraceModel
    (A : ConcreteTraceScaleSymbols)
    (hpos : A.PositiveTraceNonnegativeStatement)
    (htrace : A.TraceClassTemplateStatement)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    CC20TraceModel where
  archimedeanSymbols := A.toArchimedeanTraceSymbols
  archimedeanTraceSquare := A.trace_square_statement_of_nonnegative hpos
  traceClassTemplate := A.trace_class_template_statement htrace
  ordinaryTraceSupportSquare := A.ordinary_trace_support_square_statement
  mellinHalfDensityConvention :=
    A.mellin_half_density_convention_statement hmellin
  signsAndNormalizations := A.signs_and_normalizations_statement hsigns

theorem to_cc20_trace_model_ordinary_trace_support_square
    (A : ConcreteTraceScaleSymbols)
    (hpos : A.PositiveTraceNonnegativeStatement)
    (htrace : A.TraceClassTemplateStatement)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (toCC20TraceModel A hpos htrace hmellin hsigns).archimedeanSymbols :=
  A.ordinary_trace_support_square_statement

theorem to_cc20_trace_model_trace_square
    (A : ConcreteTraceScaleSymbols)
    (hpos : A.PositiveTraceNonnegativeStatement)
    (htrace : A.TraceClassTemplateStatement)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (toCC20TraceModel A hpos htrace hmellin hsigns).archimedeanSymbols :=
  A.trace_square_statement_of_nonnegative hpos

/--
Constructor for a CC20 trace model from square-form trace-scale data.

Compared with `toCC20TraceModel`, this version no longer asks for
positive-trace nonnegativity: it proves that row from the square-form
definition of the support-square trace.
-/
def squareTraceScaleToCC20TraceModel
    (A : SquareTraceScaleSymbols)
    (htrace : A.toConcreteTraceScaleSymbols.TraceClassTemplateStatement)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    CC20TraceModel :=
  toCC20TraceModel A.toConcreteTraceScaleSymbols
    A.positive_trace_nonnegative_statement htrace hmellin hsigns

theorem square_trace_scale_to_cc20_trace_model_trace_square
    (A : SquareTraceScaleSymbols)
    (htrace : A.toConcreteTraceScaleSymbols.TraceClassTemplateStatement)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (squareTraceScaleToCC20TraceModel
        A htrace hmellin hsigns).archimedeanSymbols :=
  A.trace_square_statement

theorem square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square
    (A : SquareTraceScaleSymbols)
    (htrace : A.toConcreteTraceScaleSymbols.TraceClassTemplateStatement)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (squareTraceScaleToCC20TraceModel
        A htrace hmellin hsigns).archimedeanSymbols :=
  A.ordinary_trace_support_square_statement

/--
Constructor for a CC20 trace model from square-form data whose Hilbert-Schmidt
gate is definitionally the trace-class/cyclicity pair.

Compared with `squareTraceScaleToCC20TraceModel`, this version no longer asks
for the trace-class/cyclicity template.
-/
def legalSquareTraceScaleToCC20TraceModel
    (A : LegalSquareTraceScaleSymbols)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    CC20TraceModel :=
  squareTraceScaleToCC20TraceModel A.toSquareTraceScaleSymbols
    A.trace_class_template_statement hmellin hsigns

theorem legal_square_trace_scale_to_cc20_trace_model_trace_square
    (A : LegalSquareTraceScaleSymbols)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (legalSquareTraceScaleToCC20TraceModel A hmellin hsigns).archimedeanSymbols :=
  A.trace_square_statement

theorem legal_square_trace_scale_to_cc20_trace_model_trace_class_template
    (A : LegalSquareTraceScaleSymbols)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      (legalSquareTraceScaleToCC20TraceModel A hmellin hsigns).archimedeanSymbols :=
  A.toSquareTraceScaleSymbols.toConcreteTraceScaleSymbols
    |>.trace_class_template_statement A.trace_class_template_statement

theorem legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square
    (A : LegalSquareTraceScaleSymbols)
    (hmellin : A.mellinHalfDensityMatched)
    (hsigns :
      A.uInfinityNormalized ∧ A.qduNormalized ∧
        A.archimedeanSignNormalized) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (legalSquareTraceScaleToCC20TraceModel A hmellin hsigns).archimedeanSymbols :=
  A.ordinary_trace_support_square_statement

/--
Constructor for a CC20 trace model from fully normalized legal square data.

This version has no proof arguments.  All rows are discharged from the concrete
definitions in this module.
-/
def normalizedLegalSquareTraceScaleToCC20TraceModel
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    CC20TraceModel :=
  legalSquareTraceScaleToCC20TraceModel
    A.toLegalSquareTraceScaleSymbols
    A.mellin_half_density_convention
    A.signs_and_normalizations

theorem normalized_legal_square_trace_scale_to_cc20_trace_model_trace_square
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols :=
  A.trace_square_statement

theorem normalized_legal_square_trace_scale_to_cc20_trace_model_trace_class_template
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols :=
  A.toLegalSquareTraceScaleSymbols.trace_class_template_statement

theorem normalized_legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols :=
  A.ordinary_trace_support_square_statement

theorem normalized_legal_square_trace_scale_to_cc20_trace_model_mellin
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.MellinHalfDensityConventionStatement
      (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols :=
  ConcreteTraceScaleSymbols.mellin_half_density_convention_statement
    (SquareTraceScaleSymbols.toConcreteTraceScaleSymbols
      (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
        A.toLegalSquareTraceScaleSymbols))
      A.mellin_half_density_convention

theorem normalized_legal_square_trace_scale_to_cc20_trace_model_signs
    (A : NormalizedLegalSquareTraceScaleSymbols) :
    ArchimedeanTraceSymbols.SignsAndNormalizationsStatement
      (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols :=
  ConcreteTraceScaleSymbols.signs_and_normalizations_statement
    (SquareTraceScaleSymbols.toConcreteTraceScaleSymbols
      (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
        A.toLegalSquareTraceScaleSymbols))
      A.signs_and_normalizations

def normalizedSeedConcreteSymbols
    (A : NormalizedLegalSquareTraceScaleSymbols) : ConcreteTraceScaleSymbols :=
  SquareTraceScaleSymbols.toConcreteTraceScaleSymbols
    (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
      A.toLegalSquareTraceScaleSymbols)

def normalizedSeedSupportSquareTrace
    (A : NormalizedLegalSquareTraceScaleSymbols) : A.Test → ℝ :=
  (normalizedSeedConcreteSymbols A).supportSquareTrace

def normalizedSeedSourceNoDefectTrace
    (A : NormalizedLegalSquareTraceScaleSymbols) : A.Test → ℝ :=
  (normalizedSeedConcreteSymbols A).sourceNoDefectTrace

def normalizedSeedPositiveTrace
    (A : NormalizedLegalSquareTraceScaleSymbols) : A.Test → ℝ :=
  (normalizedSeedConcreteSymbols A).positiveTrace

def normalizedSeedTraceClass
    (A : NormalizedLegalSquareTraceScaleSymbols) : A.Test → Prop :=
  (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
    A.toLegalSquareTraceScaleSymbols).traceClass

def normalizedSeedCyclicLegal
    (A : NormalizedLegalSquareTraceScaleSymbols) : A.Test → Prop :=
  (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
    A.toLegalSquareTraceScaleSymbols).cyclicLegal

def normalizedSeedHilbertSchmidtGate
    (A : NormalizedLegalSquareTraceScaleSymbols) : A.Test → Prop :=
  (LegalSquareTraceScaleSymbols.toSquareTraceScaleSymbols
    A.toLegalSquareTraceScaleSymbols).hilbertSchmidtGate

/--
Source-identification data connecting an actual CC20 trace object package to
the normalized concrete trace-scale seed.

This record is intentionally data-bearing.  It names each equality needed
before the normalized seed can replace the source-package trace rows.
-/
structure CC20TracePackageNormalizedSeedIdentification
    (pkg : SourceObject.CC20TraceObjectPackage) where
  normalizedSeed : NormalizedLegalSquareTraceScaleSymbols
  test_eq :
    normalizedSeed.Test = pkg.archimedeanSymbols.Test
  supportSquareTrace_eq :
    HEq (normalizedSeedSupportSquareTrace normalizedSeed)
      pkg.archimedeanSymbols.supportSquareTrace
  sourceNoDefectTrace_eq :
    HEq (normalizedSeedSourceNoDefectTrace normalizedSeed)
      pkg.archimedeanSymbols.sourceNoDefectTrace
  positiveTrace_eq :
    HEq (normalizedSeedPositiveTrace normalizedSeed)
      pkg.archimedeanSymbols.positiveTrace
  traceClass_eq :
    HEq (normalizedSeedTraceClass normalizedSeed)
      pkg.archimedeanSymbols.traceClass
  cyclicLegal_eq :
    HEq (normalizedSeedCyclicLegal normalizedSeed)
      pkg.archimedeanSymbols.cyclicLegal
  hilbertSchmidtGate_eq :
    HEq (normalizedSeedHilbertSchmidtGate normalizedSeed)
      pkg.archimedeanSymbols.hilbertSchmidtGate
  mellinHalfDensityMatched_eq :
    HEq
      normalizedSeed.toLegalSquareTraceScaleSymbols.mellinHalfDensityMatched
      pkg.archimedeanSymbols.mellinHalfDensityMatched
  uInfinityNormalized_eq :
    HEq
      normalizedSeed.toLegalSquareTraceScaleSymbols.uInfinityNormalized
      pkg.archimedeanSymbols.uInfinityNormalized
  qduNormalized_eq :
    HEq
      normalizedSeed.toLegalSquareTraceScaleSymbols.qduNormalized
      pkg.archimedeanSymbols.qduNormalized
  archimedeanSignNormalized_eq :
    HEq
      normalizedSeed.toLegalSquareTraceScaleSymbols.archimedeanSignNormalized
      pkg.archimedeanSymbols.archimedeanSignNormalized

namespace CC20TracePackageNormalizedSeedIdentification

theorem normalized_seed_trace_square
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (normalizedLegalSquareTraceScaleToCC20TraceModel
        h.normalizedSeed).archimedeanSymbols :=
  normalized_legal_square_trace_scale_to_cc20_trace_model_trace_square
    h.normalizedSeed

theorem normalized_seed_trace_class_template
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      (normalizedLegalSquareTraceScaleToCC20TraceModel
        h.normalizedSeed).archimedeanSymbols :=
  normalized_legal_square_trace_scale_to_cc20_trace_model_trace_class_template
    h.normalizedSeed

theorem normalized_seed_ordinary_trace_support_square
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (normalizedLegalSquareTraceScaleToCC20TraceModel
        h.normalizedSeed).archimedeanSymbols :=
  normalized_legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square
    h.normalizedSeed

def toCC20TraceModel
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    CC20TraceModel :=
  normalizedLegalSquareTraceScaleToCC20TraceModel h.normalizedSeed

theorem to_cc20_trace_model_trace_square
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    ArchimedeanTraceSymbols.TraceSquareStatement
      (h.toCC20TraceModel).archimedeanSymbols :=
  h.normalized_seed_trace_square

theorem to_cc20_trace_model_trace_class_template
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    ArchimedeanTraceSymbols.TraceClassTemplateStatement
      (h.toCC20TraceModel).archimedeanSymbols :=
  h.normalized_seed_trace_class_template

theorem to_cc20_trace_model_ordinary_trace_support_square
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    ArchimedeanTraceSymbols.OrdinaryTraceSupportSquareStatement
      (h.toCC20TraceModel).archimedeanSymbols :=
  h.normalized_seed_ordinary_trace_support_square

theorem support_square_trace_identification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    HEq
      (normalizedSeedSupportSquareTrace h.normalizedSeed)
      pkg.archimedeanSymbols.supportSquareTrace :=
  h.supportSquareTrace_eq

theorem positive_trace_identification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    HEq
      (normalizedSeedPositiveTrace h.normalizedSeed)
      pkg.archimedeanSymbols.positiveTrace :=
  h.positiveTrace_eq

theorem hilbert_schmidt_gate_identification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedIdentification pkg) :
    HEq
      (normalizedSeedHilbertSchmidtGate h.normalizedSeed)
      pkg.archimedeanSymbols.hilbertSchmidtGate :=
  h.hilbertSchmidtGate_eq

end CC20TracePackageNormalizedSeedIdentification

/--
CC20 trace-package fields not supplied by the normalized trace-scale seed.

These are still source obligations outside the trace-scale normalization slice.
-/
structure CC20TracePackageRemainderData
    (A : NormalizedLegalSquareTraceScaleSymbols) where
  sourceTraceTest :
    (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols.Test
  sourceCC20TraceTestCompatibility : Prop
  sourceOperatorIdentity : Prop
  sourceHilbertSchmidtGate :
    ∀ g : (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols.Test,
      ArchimedeanTraceSymbols.hilbertSchmidtGate
        (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols
        g
  sourcePerMoveCyclicityLedger : Prop
  sourceNoDefectTraceReadOff : Prop
  sourceRemainderOrientationWInftyEqLMinusD : Prop
  sourceRemainderOrientationWInftyEqSMinusE : Prop
  sourceRemainderObject : Prop
  sourceRemainderAfterQ : Prop
  cc20PostQRemainderFixedSSoninTransport : Prop
  sourceProjectionDefectNormalForm : Prop
  sourceRankPoleLedgerIdentification : Prop
  sourceEndpointStripRemainderCdefDomination : Prop
  noHiddenPositiveDefectOutsideCdef : Prop
  sourceBoundedComparisonTraceIdealTransport : Prop

/--
Build a `CC20TraceObjectPackage` from the normalized seed.

The trace-scale, legality, Mellin, and sign-normalization rows are supplied by
the normalized seed.  The sign/defect and remainder rows remain explicit data.
-/
def normalizedSeedTraceObjectPackage
    (A : NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20TracePackageRemainderData A) :
    SourceObject.CC20TraceObjectPackage where
  archimedeanSymbols :=
    (normalizedLegalSquareTraceScaleToCC20TraceModel A).archimedeanSymbols
  sourceTraceTest := remainders.sourceTraceTest
  sourceCC20TraceTestCompatibility :=
    remainders.sourceCC20TraceTestCompatibility
  sourceOperatorIdentity := remainders.sourceOperatorIdentity
  sourceHilbertSchmidtGate := remainders.sourceHilbertSchmidtGate
  sourceTraceClassCyclicityTemplate :=
    normalized_legal_square_trace_scale_to_cc20_trace_model_trace_class_template
      A
  sourcePerMoveCyclicityLedger := remainders.sourcePerMoveCyclicityLedger
  sourceOrdinaryTraceSupportSquare :=
    normalized_legal_square_trace_scale_to_cc20_trace_model_ordinary_trace_support_square
      A
  sourceSupportSquareTraceReadOff := by
    intro g htrace hcyclic
    exact
      (normalized_legal_square_trace_scale_to_cc20_trace_model_trace_square
        A g htrace hcyclic).1
  sourceNoDefectTraceReadOff := remainders.sourceNoDefectTraceReadOff
  sourcePositiveTraceNonnegative := by
    intro g htrace hcyclic
    exact
      (normalized_legal_square_trace_scale_to_cc20_trace_model_trace_square
        A g htrace hcyclic).2
  sourceRemainderOrientationWInftyEqLMinusD :=
    remainders.sourceRemainderOrientationWInftyEqLMinusD
  sourceRemainderOrientationWInftyEqSMinusE :=
    remainders.sourceRemainderOrientationWInftyEqSMinusE
  sourceRemainderObject := remainders.sourceRemainderObject
  sourceRemainderAfterQ := remainders.sourceRemainderAfterQ
  cc20PostQRemainderFixedSSoninTransport :=
    remainders.cc20PostQRemainderFixedSSoninTransport
  sourceProjectionDefectNormalForm :=
    remainders.sourceProjectionDefectNormalForm
  sourceRankPoleLedgerIdentification :=
    remainders.sourceRankPoleLedgerIdentification
  sourceEndpointStripRemainderCdefDomination :=
    remainders.sourceEndpointStripRemainderCdefDomination
  noHiddenPositiveDefectOutsideCdef :=
    remainders.noHiddenPositiveDefectOutsideCdef
  sourceBoundedComparisonTraceIdealTransport :=
    remainders.sourceBoundedComparisonTraceIdealTransport
  sourceMellinHalfDensityCompatibility :=
    normalized_legal_square_trace_scale_to_cc20_trace_model_mellin A
  sourceCC20SignNormalizations :=
    normalized_legal_square_trace_scale_to_cc20_trace_model_signs A

def normalizedSeedIdentificationForTraceObjectPackage
    (A : NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20TracePackageRemainderData A) :
    CC20TracePackageNormalizedSeedIdentification
      (normalizedSeedTraceObjectPackage A remainders) where
  normalizedSeed := A
  test_eq := rfl
  supportSquareTrace_eq := HEq.rfl
  sourceNoDefectTrace_eq := HEq.rfl
  positiveTrace_eq := HEq.rfl
  traceClass_eq := HEq.rfl
  cyclicLegal_eq := HEq.rfl
  hilbertSchmidtGate_eq := HEq.rfl
  mellinHalfDensityMatched_eq := HEq.rfl
  uInfinityNormalized_eq := HEq.rfl
  qduNormalized_eq := HEq.rfl
  archimedeanSignNormalized_eq := HEq.rfl

theorem normalized_seed_trace_object_support_square_identification
    (A : NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20TracePackageRemainderData A) :
    HEq
      (normalizedSeedSupportSquareTrace A)
      (ArchimedeanTraceSymbols.supportSquareTrace
        (normalizedSeedTraceObjectPackage A remainders).archimedeanSymbols) :=
  CC20TracePackageNormalizedSeedIdentification.supportSquareTrace_eq
    (normalizedSeedIdentificationForTraceObjectPackage A remainders)

def normalizedSeedTraceObjectArchimedeanSymbols
    (A : NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20TracePackageRemainderData A) :
    ArchimedeanTraceSymbols :=
  (normalizedSeedTraceObjectPackage A remainders).archimedeanSymbols

/--
Comparison data from an existing CC20 trace package to a package built from the
normalized trace-scale seed.

This is the bridge target for existing source packages: each equality can be
proved independently before claiming the package is represented by the
normalized seed.
-/
structure CC20TracePackageNormalizedSeedComparison
    (pkg : SourceObject.CC20TraceObjectPackage) where
  normalizedSeed : NormalizedLegalSquareTraceScaleSymbols
  remainders : CC20TracePackageRemainderData normalizedSeed
  test_eq :
    HEq (normalizedSeedTraceObjectPackage normalizedSeed remainders)
      pkg
  supportSquareTrace_eq :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (normalizedSeedTraceObjectArchimedeanSymbols normalizedSeed remainders))
      pkg.archimedeanSymbols.supportSquareTrace
  sourceNoDefectTrace_eq :
    HEq
      (ArchimedeanTraceSymbols.sourceNoDefectTrace
        (normalizedSeedTraceObjectArchimedeanSymbols normalizedSeed remainders))
      pkg.archimedeanSymbols.sourceNoDefectTrace
  positiveTrace_eq :
    HEq
      (ArchimedeanTraceSymbols.positiveTrace
        (normalizedSeedTraceObjectArchimedeanSymbols normalizedSeed remainders))
      pkg.archimedeanSymbols.positiveTrace
  hilbertSchmidtGate_eq :
    HEq
      (ArchimedeanTraceSymbols.hilbertSchmidtGate
        (normalizedSeedTraceObjectArchimedeanSymbols normalizedSeed remainders))
      pkg.archimedeanSymbols.hilbertSchmidtGate

namespace CC20TracePackageNormalizedSeedComparison

def forNormalizedSeedTraceObjectPackage
    (A : NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20TracePackageRemainderData A) :
    CC20TracePackageNormalizedSeedComparison
      (normalizedSeedTraceObjectPackage A remainders) where
  normalizedSeed := A
  remainders := remainders
  test_eq := HEq.rfl
  supportSquareTrace_eq := HEq.rfl
  sourceNoDefectTrace_eq := HEq.rfl
  positiveTrace_eq := HEq.rfl
  hilbertSchmidtGate_eq := HEq.rfl

def constructedIdentification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedComparison pkg) :
    CC20TracePackageNormalizedSeedIdentification
      (normalizedSeedTraceObjectPackage h.normalizedSeed h.remainders) :=
  normalizedSeedIdentificationForTraceObjectPackage
    h.normalizedSeed h.remainders

theorem constructed_support_square_trace_identification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedComparison pkg) :
    HEq
      (normalizedSeedSupportSquareTrace h.normalizedSeed)
      (ArchimedeanTraceSymbols.supportSquareTrace
        (normalizedSeedTraceObjectArchimedeanSymbols
          h.normalizedSeed h.remainders)) :=
  normalized_seed_trace_object_support_square_identification
    h.normalizedSeed h.remainders

theorem existing_support_square_trace_identification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedComparison pkg) :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (normalizedSeedTraceObjectArchimedeanSymbols
          h.normalizedSeed h.remainders))
      pkg.archimedeanSymbols.supportSquareTrace :=
  h.supportSquareTrace_eq

theorem existing_source_no_defect_trace_identification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedComparison pkg) :
    HEq
      (ArchimedeanTraceSymbols.sourceNoDefectTrace
        (normalizedSeedTraceObjectArchimedeanSymbols
          h.normalizedSeed h.remainders))
      pkg.archimedeanSymbols.sourceNoDefectTrace :=
  h.sourceNoDefectTrace_eq

theorem existing_positive_trace_identification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedComparison pkg) :
    HEq
      (ArchimedeanTraceSymbols.positiveTrace
        (normalizedSeedTraceObjectArchimedeanSymbols
          h.normalizedSeed h.remainders))
      pkg.archimedeanSymbols.positiveTrace :=
  h.positiveTrace_eq

theorem existing_hilbert_schmidt_gate_identification
    {pkg : SourceObject.CC20TraceObjectPackage}
    (h : CC20TracePackageNormalizedSeedComparison pkg) :
    HEq
      (ArchimedeanTraceSymbols.hilbertSchmidtGate
        (normalizedSeedTraceObjectArchimedeanSymbols
          h.normalizedSeed h.remainders))
      pkg.archimedeanSymbols.hilbertSchmidtGate :=
  h.hilbertSchmidtGate_eq

theorem normalized_package_support_square_trace_identification
    (A : NormalizedLegalSquareTraceScaleSymbols)
    (remainders : CC20TracePackageRemainderData A) :
    HEq
      (ArchimedeanTraceSymbols.supportSquareTrace
        (normalizedSeedTraceObjectArchimedeanSymbols A remainders))
      (ArchimedeanTraceSymbols.supportSquareTrace
        (normalizedSeedTraceObjectPackage A remainders).archimedeanSymbols) :=
  (forNormalizedSeedTraceObjectPackage A remainders).supportSquareTrace_eq

end CC20TracePackageNormalizedSeedComparison

end TraceScale
end CC20Concrete
end Source
end ConnesWeilRH
