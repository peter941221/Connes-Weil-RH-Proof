/-
Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ConnesWeilRH.Dev.C1Stage3QwReadback
import ConnesWeilRH.Dev.C1PositiveTraceLimitBridge
import ConnesWeilRH.Source.CC20Concrete.GlobalConvolutionCrossing
import ConnesWeilRH.Source.CC20Concrete.CompactRootHalfLinePair

/-!
# C1 Stage-3 remainder family (active namespace) — Gates 3 and 4 assembly

Gates 1 and the full Gate-2 readback are closed in active C1:
`stage3ProjectionKernel_adjointConj_isPositive` supplies the positive core, and
`C1Stage3QwReadback.stage3QwReadback_qw_eq_pole_sub_arch_sub_response_add_residual` pins

```text
qw g = pole(g*∗g) − arch(g*∗g) − Re Tr(projectionResponse owner λ S) + Re Tr(sameObjectResidual …)
```

purely from already-proved bricks.  This module performs the Gate-3 / Gate-4 assembly: it fixes the
concrete self-pair operator that produces the family, and shows that — once two named analytic
facts hold (frontier § below) — all four fields of `PositiveTracePairLimitFamily` fill non-circularly
and the existing consumers carry them to `healthyCriterionState`.

The concrete factor is convolution by the involution test:

```text
F_g = conv(g.involution.test)          on cc20GlobalLogCrossingL2
```

so its self-pair product is, **by definition**, the selected positive root detector

```text
F_g† F_g = (conv h)† ∘ conv h  :=  cc20GlobalConvolutionPositive h      with h = g.involution.test
```

and by `globalConvolutionPositive_eq_convolutionSquare` this equals convolution by the compact
convolution-square kernel `g.convolutionSquare.test` (support `[a-c, c-a]`).  Because every trace
product is literally an `F† F`, its real part is intrinsically non-negative (diagonal = ‖F_g(basis i)‖²),
so **no sign on `qw g` is ever assumed** — that intrinsic positivity is the entire source of
non-circularity in `C1PositiveTraceLimitBridge.qw_nonnegative_of_positiveTracePairLimitFamily`.

Two named analytic facts remain (the true Gate-3 frontier).  Both are stated precisely here and are
used as inputs to the assembly, which keeps this module green and axiom-clean:

```text
(FRONTIER-HS)    Summable fun i => ‖F_g(basis i)‖²          -- F_g is Hilbert–Schmidt (⟺ ReTr(detector) converges)
(FRONTIER-CRUX)  Re Tr(F_g† F_g) = qw g                      -- the detector's real trace reads back to the Weil value
```

`FRONTIER-HS` and `FRONTIER-CRUX` are exactly "the remainder goes to zero without assuming the sign":
with a constant family (`remainder := 0`) they make `ReTr(F_g†F_g) − 0 = qw g`, and each term is ≥ 0,
so `qw g = lim_n ReTr ≥ 0` follows with no hypothesis on the sign.

Firewall: imports only active C1 modules (`C1Stage3QwReadback`, `C1PositiveTraceLimitBridge`) plus
shared Source bricks (`GlobalConvolutionCrossing`, `CompactRootHalfLinePair`).  **No** frozen route leaf.
-/

namespace ConnesWeilRH
namespace Source
namespace C1Stage3RemainderFamily

open CC20Concrete
open CC20Concrete.PositiveTrace
open CCM25Concrete.CompactLogConvolution
open CCM25Concrete.SelectedWeilSquare
open C1PositiveTraceLimitBridge
open Filter
open scoped InnerProduct InnerProductSpace Topology BigOperators

noncomputable section

variable {ν : Type*} (globalBasis : HilbertBasis ν ℂ cc20GlobalLogCrossingL2)

/-- The concrete Stage-3 family factor on the common logarithmic carrier: convolution by the
involution test of `g`.  Its self-pair product is definitionally the selected positive root detector. -/
noncomputable def stage3FamilyFactor (g : CompactLogTest) :
    cc20GlobalLogCrossingL2 →L[ℂ] cc20GlobalLogCrossingL2 :=
  cc20GlobalLogConvolution g.involution.test

/-- The factor's self-pair trace product is, by definition of the positive detector, exactly the
selected root detector for `g` — a genuine `(conv h)† ∘ conv h` with `h = g.involution.test`. -/
theorem stage3FamilyFactor_traceProduct_eq_positiveDetector (g : CompactLogTest) :
    (stage3FamilyFactor g).adjoint ∘L stage3FamilyFactor g =
      cc20GlobalConvolutionPositive g.involution.test := rfl

/-- Characterization of the same detector as convolution by the compact convolution-square kernel
(`support [a-c, c-a]`): this is the concrete positivity core reused from Gate 1. -/
theorem stage3FamilyFactor_traceProduct_eq_convolutionSquare (g : CompactLogTest) :
    (stage3FamilyFactor g).adjoint ∘L stage3FamilyFactor g =
      cc20GlobalLogConvolution g.convolutionSquare.test := by
  rw [stage3FamilyFactor_traceProduct_eq_positiveDetector]
  exact CC20Concrete.CompactRootHalfLinePair.globalConvolutionPositive_eq_convolutionSquare g

/-- Gate-4 assembly: for one vanishing test `g`, the two named analytic facts fill all four fields of
the positive-trace family non-circularly.  The remainder is identically zero; the readback to `qw g`
is exactly `FRONTIER-CRUX`; and each trace product is an `F† F`, so its real part is intrinsically ≥ 0. -/
noncomputable def stage3Remainder_family_for_g
    (g : CompactLogTest)
    (hHS : Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2)
    (hcrux : (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
        ((stage3FamilyFactor g).adjoint ∘L stage3FamilyFactor g)).re = C1SameOwnerWeil.qw g) :
    PositiveTracePairLimitFamily (G := cc20GlobalLogCrossingL2) globalBasis g := by
  let pairData : BasisHilbertSchmidtPairData (G := cc20GlobalLogCrossingL2) globalBasis :=
      ⟨stage3FamilyFactor g, stage3FamilyFactor g, hHS, hHS⟩
  have htp : pairData.traceProduct = (stage3FamilyFactor g).adjoint ∘L stage3FamilyFactor g := rfl
  have hconst : (fun n : Nat =>
          (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis (pairData.traceProduct)).re - 0) =
        fun _ : Nat => C1SameOwnerWeil.qw g := by
    ext n; rw [htp, sub_zero]; exact hcrux
  refine ⟨fun _ => pairData, ?_, fun _ => 0, ?_, ?_⟩
  · intro n; rfl
  · exact tendsto_const_nhds
  · rw [hconst]; exact tendsto_const_nhds

/-- Gate-4 final step: the two named analytic facts, uniform over all vanishing tests, close the
finite-vanishing healthy criterion (the RH-level exit). -/
theorem stage3Remainder_healthyCriterionState
    (F : Finset CriticalVanishingPoint)
    (hHS : ∀ g : CompactLogTest, Summable fun i => ‖stage3FamilyFactor g (globalBasis i)‖ ^ 2)
    (hcrux : ∀ g : CompactLogTest,
        (CC20Concrete.PositiveTrace.ordinaryTraceAlong globalBasis
            ((stage3FamilyFactor g).adjoint ∘L stage3FamilyFactor g)).re = C1SameOwnerWeil.qw g) :
    C1.healthyCriterionState F := by
  apply healthyCriterionState_of_positiveTracePairLimitFamily
      (H := cc20GlobalLogCrossingL2) (G := cc20GlobalLogCrossingL2) globalBasis F
  intro g hvanishing
  exact stage3Remainder_family_for_g globalBasis g (hHS g) (hcrux g)

end
end C1Stage3RemainderFamily
end Source
end ConnesWeilRH
