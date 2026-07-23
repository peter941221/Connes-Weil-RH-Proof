# Proof 501: orthogonal completed Julia synthesis

Date: 2026-07-22

## Result

The result is good for the operator-theoretic connection requested after
Proof 500.  The genuine completed Julia column now has an adjoint synthesis,
the old rectangular history is proved to be only a contractive readout of
that column, and Proof 500's relative ordinary-trace recurrence is read back
through this exact synthesis.

The result does not prove the unscaled family-uniform estimate required by
Gate 3U.  It instead puts the missing factor in an exact Lean equivalence.
The finite-S sign, Burnol identity, and RH remain open.

```text
+----------------------------------------------------+------------------+
| layer                                              | status           |
+----------------------------------------------------+------------------+
| completed survivor plus Julia co-defect carrier    | closed           |
| isometric Julia analysis                           | closed           |
| adjoint synthesis and left-inverse identity        | closed           |
| rectangular history as a contractive readout       | closed           |
| local polar boundary through the true co-defect     | closed           |
| Proof 500 relative trace through Julia synthesis   | closed           |
| complete raw owner localized in defect slots        | open             |
| unscaled family-uniform Gate 3U bound               | open             |
| finite-S sign / Burnol identity / RH                | open             |
+----------------------------------------------------+------------------+
```

## 1. Genuine completed column

For a chronological list of Julia steps, define

```text
A_S x = (juliaSurvivor(S,x), juliaDefectColumn(S,x)).
```

The target uses the Hilbert `L2` product, not the ordinary product norm:

```lean
noncomputable abbrev completedJuliaCarrier ... :=
  WithLp 2 (H x PiLp 2 (fun _ : Fin steps.length => H))
```

The existing Pythagorean telescope gives

```text
norm(A_S x)^2
  =norm(juliaSurvivor(S,x))^2
   +norm(juliaDefectColumn(S,x))^2
  =norm(x)^2.
```

Lean ownership:

```text
completedJuliaAnalysis_normSq_eq
completedJuliaAnalysis_norm_eq
completedJuliaAnalysis_norm_le_one
```

This is the distinction missing from the rectangular history.  The complete
Julia column is genuinely orthogonal and isometric.

## 2. Adjoint synthesis

The synthesis is not separately postulated:

```lean
completedJuliaSynthesis steps := (completedJuliaAnalysis steps).adjoint
```

Mathlib's Hilbert-space adjoint theorem and the norm identity prove

```text
A_S^dagger A_S=I.
```

The exact Lean statements are

```text
completedJuliaAnalysis_adjoint_comp_self
completedJuliaSynthesis_comp_analysis_eq_id
completedJuliaSynthesis_norm_le_one
```

Thus a source operator `T` has the lossless completed lift

```text
Lift_S(T)=A_S T A_S^dagger,

A_S^dagger Lift_S(T) A_S=T.
```

The lift is an exact same-object embedding.  By itself it supplies no new
decay estimate for `T`.

## 3. Rectangular history is only a readout

For actual rectangular Schur steps, Proof 495 used

```text
(terminal survivor, rectangular boundary-dagger history).
```

Proof 501 applies the identity to the survivor coordinate and the existing
Douglas contraction to the Julia co-defect coordinates.  It constructs

```text
C_S : completedJuliaCarrier(S)
        -> completedRectangularBoundaryCarrier(S)
```

and proves

```text
norm(C_S)<=1,
C_S A_S=completedRectangularBoundaryColumn(S),
completedRectangularBoundaryColumn(S)^dagger=A_S^dagger C_S^dagger.
```

Lean ownership:

```text
completedRectangularBoundaryCompression_norm_le_one
completedRectangularBoundaryCompression_comp_analysis
completedRectangularBoundaryColumn_adjoint_factorization
suffixEulerRectangularHistory_factors_through_completedJulia
```

This prevents the earlier semantic mistake:

```text
contractive physical history
  -X-> orthogonal or invertible Julia column.
```

## 4. Genuine local polar slot

The local polar detector defect is not attached to the Julia column by a
generic lift.  Its existing formula is unfolded on the actual adjacent polar
frames:

```text
BoundaryDefect(p,S)
 =-boundary(p,S) detector newFrame(S).
```

The rectangular Douglas theorem then gives

```text
BoundaryDefect(p,S)
 =-leftCoDefect(p,S)
    factor(p,S)^dagger detector newFrame(S).
```

Here `leftCoDefect(p,S)` is exactly the canonical Julia co-defect of the
adjoint source transition.  The relevant declarations are

```text
suffixEulerDetectorBoundaryDefect_eq_stepBoundary
suffixEulerDetectorBoundaryDefect_eq_juliaCoDefect
```

This closes the real polar-boundary-to-Julia-slot connection.  It does not
yet prove that the complete first-jet-minus-endpoint raw term, including its
ordering correction, is supported only in those defect coordinates.

## 5. Proof 500 readback

For each local raw defect, Proof 501 uses the actual larger-suffix analysis:

```text
Lift(p,S)
 =A_(p::S) LocalRawDefect(p,S) A_(p::S)^dagger.
```

Lean proves the exact readback

```text
A_(p::S)^dagger Lift(p,S) A_(p::S)
 =LocalRawDefect(p,S).
```

The relative recurrence is therefore

```text
JuliaRelativeTrace([])=0,

JuliaRelativeTrace(p::S)
 =JuliaRelativeTrace(S)
  +rho_p^-1 Tr(A_(p::S)^dagger Lift(p,S) A_(p::S)).
```

Using Proof 500's legal four-branch Hilbert--Schmidt cycles, Lean proves

```text
Tr(Raw(S))=JuliaRelativeTrace(S).
```

Lean ownership:

```text
suffixActualBandLocalRawDefect_eq_completedJuliaReadback
suffixActualBandCompletedJuliaRelativeTrace_eq_relativeCollapsed
ordinaryTraceAlong_suffixActualBandRawResponse_eq_completedJulia
```

The lift of the full local raw defect is lossless but generic.  The
source-specific gain still requires a factorization of the full signed owner
through the actual defect coordinates, extending the polar result in
Section 4 to the first jet and ordering correction.

## 6. Exact Gate 3U boundary

For the arithmetic visible-prime list, the corrected signed cocycle satisfies

```text
Tr(correctedSignedCocycle_S)
 =rho_S * JuliaRelativeTrace(S).
```

Consequently Lean proves the exact equivalence

```text
norm(Tr(correctedSignedCocycle_S))<=rho_S*P
  iff
norm(JuliaRelativeTrace(S))<=P.
```

The declarations are

```text
ordinaryTraceAlong_completedSignedCocycle_eq_rho_mul_completedJulia
completedSignedCocycle_rho_bound_iff_completedJulia_bound
```

Proof 498 supplies only

```text
rho_S * norm(JuliaRelativeTrace(S))
 <=(18+6 H_lambda)(c-a)^2 seminorm_0,0(g)^2.
```

This is formalized as

```text
rho_mul_completedJulia_trace_norm_le_supportEnergy
```

The desired Gate 3U conclusion removes `rho_S` from the left.  Orthogonal
readback alone cannot do that.  A valid successor must keep the complete
first-jet, polar, and ordering terms together and prove their right synthesis
column has a family-independent square-energy bound.

## 7. RH boundary

No axiom-clean producer currently supplies that unscaled bound or the later
finite-S sign and Burnol identity.  The apparent no-argument theorem in
`Dev/UnconditionalSkeleton.lean` is not a solution: it consumes explicit
user axioms, including

```lean
axiom normalizedSelectedFinalRouteCertificateCarrierRoot :
  NormalizedSelectedFinalRouteCertificateCarrier
```

Therefore Proof 501 cannot be consumed into
`_root_.RiemannHypothesis` without adding an unproved premise.

## 8. Lean ownership

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSCompletedJuliaSynthesis.lean

ConnesWeilRH/Dev/
  CCM24FiniteSCompletedJuliaSynthesisAudit.lean

ConnesWeilRH/Source/
  CCM25Concrete.lean
```

The focused audit checks the public types and prints the axiom set of every
principal theorem.  No `sorry`, `admit`, or user axiom is introduced.
