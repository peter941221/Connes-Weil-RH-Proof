# Sonin Prolate Defect Cdef Theorem Contract

Status: theorem contract for the sign/defect hard blocker.

This contract strengthens the current route-evidence packages into a
formal/import target. It does not prove the CC20 prolate analysis, the fixed-S
transport theorem, or the endpoint-strip trace ideal. It states the exact
theorem that must be proved, imported, or rejected before the positive trace
can be used as a Weil-positivity input.

The source-readiness audit for this contract is:

```text
docs/audits/sonin-prolate-defect-source-readiness-audit.md
```

That audit finds relevant CC20 and CCM24 ingredients, but no source theorem
that directly identifies the source prolate/Sonin difference with the route's
rank, pole, and endpoint-strip `Cdef` classes.

## Evidence Lock

| item | evidence |
|---|---|
| public route read-off claim | `README.md:160-172` |
| hostile sign/defect audit | `docs/audits/sign-defect-blocker-audit.md` |
| Battle 2 fixed-S support-square transport | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:225-271` |
| Battle 3 trace-norm `Cdef` and fixed-test exhaustion | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:94-315` |
| graph/prolate fixed-test exhaustion package | `docs/proofs/fixed-test-graph-cdef-exhaustion.md:13-15,187-221` |
| Row 3 source-remainder transport | `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` |
| Row 4 source-remainder projection-defect normal form | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md` |
| Row 5 source rank/pole ledger identification | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md` |
| Row 6 endpoint-strip Cdef domination | `docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md` |
| Row 7 no-hidden-defect equality | `docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md` |
| Sonin/prolate source-readiness audit | `docs/audits/sonin-prolate-defect-source-readiness-audit.md` |
| CC20 external warning | arXiv:2006.13771 abstract, https://arxiv.org/abs/2006.13771 |

The CC20 abstract says the Weil distribution and the Sonin trace differ by a
prolate-spheroidal term. The route therefore needs a theorem that identifies
the route's defect ledger with the source prolate/Sonin difference. Naming
`Cdef` is not enough.

## Boundary

The contract sits between two current packages:

```text
Battle 2 fixed-S transport
        |
        v
Sonin/prolate source defect identification
        |
        v
Battle 3 endpoint-strip Cdef trace norm
```

The route may use:

```text
QW_lambda(g,g) >= -C Cdef(g)
```

only after this middle leg is discharged.

## Objects Fixed Before The Theorem

For an admissible tuple:

```text
(S, I, lambda, g)
```

fix the source-backed objects:

```text
A_(S,lambda,g)          positive-trace Hilbert-Schmidt operator
F_g = g^* * g           common source convolution square
SoninTrace_(S,lambda)   source Sonin/compressed trace side
QW_lambda(g,g)          CCM25 restricted Weil form
Rank_(S,I)(g)           no-strip rank ledger
PoleJetExtra_(S,I)(g)   no-strip pole ledger
Cdef_(S,I,lambda,J)(g)  endpoint-strip trace-norm defect
```

The theorem must use the same source test, same fixed-S model, and same window
for all objects.

## Contract Theorem 1. Source Defect Decomposition

Target:

```text
SourceSoninProlateDefectDecomposition(S,I,lambda,g,J):
  SourceSoninProlateDefect_(S,I,lambda)(g)
    =
  RankDefect_(S,I)(g)
    +
  PoleDefect_(S,I)(g)
    +
  EndpointStripDefect_(S,I,lambda,J)(g).
```

Meaning:

The source prolate/Sonin difference must split into exactly the same three
classes used by the route. A proof cannot introduce another residual term.

Blocked shortcut:

```text
defect is small
```

with no equality tying the source defect to the route ledger.

## Contract Theorem 2. Rank And Pole Identification

Target:

```text
SourceRankPoleDefectIdentification(S,I,lambda,g):
  RankDefect_(S,I)(g) = Rank_(S,I)(g)
  PoleDefect_(S,I)(g) = PoleJetExtra_(S,I)(g).
```

Meaning:

The no-strip part of the source defect must be the same no-strip ledger killed
by triple vanishing. A source pole term inside `QW_lambda` cannot be confused
with the separate route `PoleJetExtra` ledger.

Current route-evidence:

```text
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
```

This identifies the no-strip channels as route rank and pole ledgers at
route-evidence level and proves the triple-vanishing gate for those ledgers. It
does not prove endpoint-strip `Cdef` domination or no-hidden-defect equality.

Blocked shortcut:

```text
triple vanishing kills the defect
```

unless the killed defect has first been identified with these two ledgers.

## Contract Theorem 3. Endpoint-Strip Normal Form

Target:

```text
SourceEndpointStripDefectNormalForm(S,I,lambda,g,J):
  every summand of EndpointStripDefect_(S,I,lambda,J)(g)
  has an endpoint-strip factor before boundary evaluation.
```

The permitted normal form is the route's trace-norm form:

```text
theta(D^r g) X_0 M_b T_a X_1 theta(D^s g)^*
```

with `b` supported in a finite endpoint strip, plus the corresponding
boundary-strip traces after `Q`.

Meaning:

The route must prove that source prolate/Sonin terms do not produce bulk
defects outside the endpoint-strip trace ideal.

Current route-evidence:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
```

This proves the endpoint-strip normal-form part for the transported source
remainder at route-evidence level. Row 6 supplies the trace-norm domination at
route-evidence level, and Row 7 supplies the no-hidden-defect equality at
route-evidence level.

## Contract Theorem 4. Cdef Trace-Norm Domination

Target:

```text
SourceEndpointStripDefectCdefBound(S,I,lambda,g,J):
  |EndpointStripDefect_(S,I,lambda,J)(g)|
    <=
  C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Meaning:

The theorem must turn the endpoint-strip class into the exact normed `Cdef`
quantity used by the route. A role name or qualitative compactness statement
does not pass.

Current route-evidence:

```text
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
```

This matches endpoint-strip source-remainder terms to route `Cdef` summands,
proves the trace-norm domination, and records fixed-test exhaustion at
route-evidence level. It does not prove the final read-off equality or exclude
a fourth defect class by itself.

## Contract Theorem 5. No Hidden Positive Defect

Target:

```text
NoHiddenPositiveDefectOutsideCdef(S,I,lambda,g,J):
  PositiveTrace^G_(S,lambda)(g)
    =
  QW_lambda(g,g)
    +
  Rank_(S,I)(g)
    +
  PoleJetExtra_(S,I)(g)
    +
  R_(S,I,lambda,J)(g)
```

with:

```text
|R_(S,I,lambda,J)(g)|
  <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Meaning:

This is the point where the hostile objection must fail. If the true source
identity has:

```text
QW_lambda = PositiveTrace - Defect
```

then the theorem must prove that this `Defect` is exactly the killed ledgers
plus endpoint-strip `Cdef`, not a separate nonnegative quantity.

Current route-evidence:

```text
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md
```

This composes Rows 3 through 6 into the exact positive-trace read-off equality
and defines the remainder as the endpoint-strip source remainder. It closes
Row 7 only at route-evidence level.

## Combined Contract

The formal/import target is:

```text
SoninProlateDefectEqualsEndpointStripCdef(S,I,lambda,g,J):
  SourceSoninProlateDefectDecomposition
  SourceRankPoleDefectIdentification
  SourceEndpointStripDefectNormalForm
  SourceEndpointStripDefectCdefBound
  NoHiddenPositiveDefectOutsideCdef
```

Projection target:

```text
SoninProlateDefectEqualsEndpointStripCdef
  ->
FixedSPositiveTraceReadOffTheorem
```

where `FixedSPositiveTraceReadOffTheorem` is allowed to produce:

```text
QW_lambda(g,g)
  >=
-C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g)
```

only after rank and pole ledgers vanish.

## Import Acceptance Checklist

A source import or formal proof can discharge this contract only if it supplies:

| item | required evidence |
|---|---|
| source defect object | exact source prolate/Sonin difference term |
| route defect object | exact fixed-S projection-order remainder |
| equality bridge | theorem identifying source defect with route rank, pole, and endpoint-strip classes |
| no-extra-residue statement | proof that no fourth defect class remains |
| trace-norm bound | displayed domination by route `Cdef` |
| sign consequence | positive trace yields only the stated lower bound for `QW_lambda` |

## Current Judgment

| question | answer |
|---|---|
| Does this contract prove the sign/defect bridge? | no |
| Does it state the theorem needed to defeat the hostile defect objection? | yes |
| Does source review find a direct import for the theorem? | no |
| Does it permit an uncontrolled positive prolate defect? | no |
| Can the current route treat this as route-evidence discharged? | yes |
| Can the current route treat this as accepted-source or Lean discharged? | no |

The next pass must either formalize or source-certify this theorem before the
route can claim accepted proof status for
`PositiveTrace = QW_lambda + ledgers + Cdef`.
