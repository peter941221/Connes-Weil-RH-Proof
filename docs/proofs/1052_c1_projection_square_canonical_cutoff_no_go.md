# 1052 - C1 projection-square canonical-cutoff closure guard

Date: 2026-08-29.

Status: NO-GO for closing the current Stage-3 projection-square ledger by
letting its canonical window-to-response defect tend to zero. This is a
Lean-checked obstruction. It does not reject a different finite-part,
renormalized, or otherwise new semilocal owner.

## 1. The Exact Rejected Claim

The active positive finite-window owner is built from

```text
K_S = E Q_S E - R_S >= 0,
D2_n = windowedBoundaryDetector_n - projectionResponse.
```

The bridge is an exact operator identity:

```text
finiteWindowPositiveTrace
  = projectionResponse + D1_n + D2_n.
```

The former closure proposal required the real trace of `D2_n` to tend to zero
as the canonical cutoff grows. The following is the actual Lean theorem now
exposed by `C1ProjectionSquareCanonicalCutoffGuard.lean`:

```lean
theorem canonicalCutoffWindowToResponseDefect_not_tendsto_zero
    (owner : SelectedWeilSquareOwner)
    (lambda : CCM24SoninScale) (S : List CCM24VisiblePrime)
    {nu : Type*} (globalBasis : HilbertBasis nu Complex cc20GlobalLogCrossingL2)
    (hresponse : IsTraceClassAlong globalBasis
      (projectionResponse owner lambda S))
    (hg : Not (owner.sourceTest.test = 0)) :
    Not (Tendsto
      (fun n =>
        (ordinaryTraceAlong globalBasis
          (cutoffWindowToResponseDefect owner lambda S n)).re)
      atTop (nhds (0 : Real)))
```

## 2. Why It Is A Mathematical No-Go

The proof is an exact subtraction followed by a growth theorem:

```text
Re Tr(D2_n)
  = Re Tr(windowedBoundaryDetector_n)
    - Re Tr(projectionResponse).
```

For a nonzero source test, the first summand has the canonical positive-window
bulk and is cofinally unbounded. The second summand is fixed once the response
has a trace. Hence, for every real `B`, some cutoff satisfies

```text
B < Re Tr(D2_n).
```

An unbounded real sequence cannot converge to zero. No estimate on the first
defect `D1_n`, compactness of a residual, or stronger trace-class bookkeeping
can change this identity.

```text
positive kernel K_S
        |
        v
canonical finite window
        |
        v
windowed detector has linear bulk
        |
        v
D2_n = bulk - fixed response
        |
        v
D2_n -> 0 is impossible for every nonzero test.
```

## 3. Evidence

The operator bridge is in:

```text
ConnesWeilRH/Dev/C1Stage3ProjectionResponseBridge.lean
  fullBoundaryProjectionPairData_traceProduct_eq_projectionResponse_add_defects
```

The two decisive source theorems are in:

```text
ConnesWeilRH/Dev/C1Stage3ProjectionDefectBounds.lean:466
  cutoffWindowToResponseDefect_trace_re_unbounded_of_sourceTest_ne_zero

ConnesWeilRH/Dev/C1Stage3ProjectionDefectBounds.lean:506
  not_tendsto_zero_cutoffWindowToResponseDefect_trace_re_of_sourceTest_ne_zero
```

The new guard is only a named import-facing consequence of the second theorem;
it adds no analytic premise and no axiom. Its paired audit prints the theorem
type and its axioms.

## 4. Relation To The Prime-Square Diagnostic

Proof 1051 establishes in Lean that the active response is the Gram-projection
difference

```text
projectionResponse = detector (R_0 - R_S).
```

Its `p^2` factor-two calculation is a strong design diagnostic, but its final
noncompact-channel conclusion needs an additional source-specific statement:
the relevant Sonin principal crossing must survive the detector trace and be
the same nonzero channel as the radial Euler boundary crossing. The current
checked finite-prime readback is for the radial crossing, not yet for that
Sonin principal channel.

Therefore the precise evidence boundary is:

```text
Lean-checked no-go:
  canonical D2_n -> 0 closure of the positive projection-square route.

Conditional diagnostic:
  direct Gram-projection Euler-log readback has a factor-two p^2 conflict
  once the source-Sonin principal-channel readback is supplied.
```

This qualification prevents the coefficient calculation from being used as a
standalone formal rejection of every possible metric or semilocal construction.

## 5. Remaining GO Boundary

A successor cannot retain the same `D2_n` and merely seek a sharper limit. It
must instead provide a new same-owner construction that does all of the
following before a positivity conclusion is consumed:

```text
1. carries or cancels the linear window bulk internally;
2. produces the Euler coefficient a^m / m before a crossing contributes
   m log(p);
3. has a positive or otherwise sign-controlled finite part; and
4. proves a direct same-owner readback, rather than appending the radial
   Euler boundary and declaring the difference negligible.
```

The root-relative determinant / completed Hardy-prolate direction remains a
research candidate for such a new owner. This record makes no feasibility
claim for it.

## 6. Verification

The focused WSL2 build was:

```text
lake build ConnesWeilRH.Dev.C1ProjectionSquareCanonicalCutoffGuard \
  ConnesWeilRH.Dev.C1ProjectionSquareCanonicalCutoffGuardAudit
```

It ended with `Build completed successfully (3822 jobs)`. The audit printed
only `[propext, Classical.choice, Quot.sound]`, with no `sorryAx`.
