/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: ConnesWeilRH contributors
-/

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

end TraceScale
end CC20Concrete
end Source
end ConnesWeilRH
