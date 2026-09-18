# 1659 — Endpoint limit positivity from the survivor core

Date: 2026-09-19.

Status: formal conditional consumer. RH is not claimed.

## Result

The endpoint operator is exactly a source-side positive composition.  With

```text
C = rootConvolution owner
A = I + (finiteEulerPulledObliqueShear lambda family)†
J = sourceInclusion lambda
F = C ∘ A ∘ C ∘ J,
```

the formal identity is

```text
g8EndpointSourceCutoffLimitOperator = F† ∘ F.
```

The existing exact equivalence
`g8EndpointGate_iff_survivorCore` converts the survivor-core square-sum into
the square-sum of `C ∘ J`.  Bounded postcomposition by `C ∘ A` then gives the
square-sum of `F`.  The generic positive-trace pair consumer consequently
proves

```text
0 <= Re ordinaryTraceAlong sourceBasis
     (g8EndpointSourceCutoffLimitOperator owner lambda family).
```

The Lean declarations are in
`Dev/C1G8R3EndpointPositiveTrace.lean`, with the paired audit module beside
it.  The focused build completed successfully with no `sorryAx`; the audit
prints only the standard proof axioms.

## Boundary of the result

This closes the endpoint sign/readback half conditionally.  It does not prove
the survivor-core hypothesis itself.  The remaining S3 producer is exactly

```text
Summable i,
  ‖(sourceInclusion lambda)† ∘L rootConvolution owner ∘L
      sourceInclusion lambda (sourceBasis i)‖².
```

The finite-window root energy brick from 1657 and the already formal range
leg do not control the infinite source-compressed tail.  The no-go result
1655 still rules out replacing this source-compressed estimate by a global
ambient Hilbert–Schmidt premise.
