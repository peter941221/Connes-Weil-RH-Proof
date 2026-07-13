# Proof 200: Whole-line finite-S crossing operator sum

Status: accepted crossing-layer milestone. The finite-prime main term is now
the ordinary trace of one genuine compact self-adjoint operator backed by an
operator-norm nuclear expansion. RH remains unproved.

## Route obligation

```text
route obligation:
  assemble the selected finite-prime main term before taking the trace

old weak path:
  a finite sum of scalar trace values with no named operator sum

new mathematical owner:
  eulerLogWeightedGlobalPairTraceOperatorSum

consumer to rewire:
  the single-crossing component of a genuine finite-S positive owner

forbidden circular inputs:
  SourceRH, detector coverage, stored positivity, or a stored remainder sign

smallest verification target:
  ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

focused axiom audits:
  ConnesWeilRH.Dev.GlobalLogCrossingTraceClassAudit
  ConnesWeilRH.Dev.SelectedCrossingMultiPrimeAudit
  ConnesWeilRH.Dev.SelectedCrossingOperatorBridgeAudit
```

## Result

For one prime power, the new operator is

```text
K_(p,m) = 1/(m sqrt(p^m)) * (T_(p,m) + T_(p,m)^dagger),
```

where `T_(p,m)` is the existing whole-line convolution crossing on the same
`SelectedWeilSquareOwner`. The coefficient is a real scalar. Therefore
`eulerLogWeightedGlobalPairTraceOperator_isSelfAdjoint` proves that every
`K_(p,m)` is self-adjoint.

For a finite family `terms`, the definition
`eulerLogWeightedGlobalPairTraceOperatorSum` gives

```text
K_S = sum_((p,m) in terms) K_(p,m)
```

on one whole-line Hilbert space. Theorems now prove all four operator-level
invariants:

```text
K_S is a genuine compact bounded operator,
K_S has an operator-norm absolutely convergent rank-one expansion,
K_S has an absolutely summable diagonal along the named whole-line basis,
K_S is self-adjoint,
Tr(K_S) = sum_((p,m) in terms) finitePrimeTerm(p^m).
```

Trace linearity is not assumed for a conditionally convergent diagonal
series. `PositiveTrace` first proves `IsTraceClassAlong` for adjoints, sums,
scalar multiples, and finite sums. The trace identities consume these explicit
summability witnesses.

The canonical positive-interval theorem
`positiveInterval_operatorSum_trace_eq_finitePrimeTerm_pow_sum`
uses the Yoshida source support theorem directly. It introduces neither a
second log test nor a second convolution square.

```text
one selected square
       |
       +--> K_(p1,m1) --+
       +--> K_(p2,m2) --+--> K_S = K_S^dagger
       +--> ...         --+          |
                                  ordinary trace
                                       |
                                       v
                         selected finite-prime sum
```

## Boundary of the result

Compact and self-adjoint does not mean positive. The result does not construct the
semilocal metric/prolate owner, identify its single-crossing expansion with
`K_S`, or prove that the remaining words form a compact post-`Q` remainder of
the required sign. Those are the active Gate 3 obligations.

## Verification

The later nuclear upgrade is recorded in proof 201. Its generic build passes
`2356/2356`, the whole-line source passes `2979/2979`, and the three
import-facing audits pass `2983/2983`.

The printed generic theorem type contains only the explicit mathematical
premises: prime/nonzero-exponent guards, one source support bound, one common
whole-line basis, and genuine interval-basis data. The positive-interval type
removes the support premise through the canonical source theorem. The
diagonal-trace, compactness, and self-adjoint declarations report only:

```text
propext
Classical.choice
Quot.sound
```

The next mathematical bottom is one genuine finite-S positive owner with a
proved operator decomposition

```text
positiveOwnerSingleCrossing = K_S
positiveOwner = K_S + postQRemainder,
```

followed by same-domain compactness, self-adjointness, and the sign estimate
for `postQRemainder`.
