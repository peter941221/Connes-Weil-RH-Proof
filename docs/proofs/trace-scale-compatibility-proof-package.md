# Trace Scale Compatibility Proof Package

Status: route-evidence proof package for the B1 trace-scale compatibility
blocker.

This package targets:

```text
docs/proofs/trace-scale-compatibility-theorem-contract.md
```

It proves the route-evidence version of `TraceScaleCompatibilityContract`. It
does not prove accepted source-import status, Lean theorem status, or RH.

## Result

Good result:

```text
B1 trace-scale compatibility is closed at project proof-package level.
```

Boundary:

```text
accepted-source certification: open
external referee certification: open
Lean proof status: open
public proof status: source-conditional
```

The package answers the external trace-scale objection inside the current
route model. A referee still has to accept the CC20/CCM source formulas and the
fixed-S transport statements used below.

## Fixed Objects

Fix one admissible route tuple:

```text
S                 finite source place set
I                 source support window
lambda            restricted CCM25 cutoff, 1 < lambda
g                 common source test
F_g = g^* * g     common convolution square
J                 endpoint-strip graph order
```

Every scalar below uses this tuple. The proof rejects any step that changes
the cutoff, test, square, or fixed-S coordinate.

## Theorem

For the fixed tuple:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
CdefRemainder_(S,I,lambda,J)(g),
```

with:

```text
|CdefRemainder_(S,I,lambda,J)(g)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

No additional scalar term:

```text
BulkScaleTerm_(S,I,lambda,g)
```

appears outside the displayed rank, pole, and endpoint-strip classes.

## Dependency Graph

```text
ordinary positive trace
        |
        v
ordinary support-square trace
        |
        v
fixed-S quantized differential main term
        |
        +-- rank ledger
        |
        +-- pole ledger
        |
        +-- endpoint-strip Cdef remainder
        |
        v
CCM25 restricted scalar QW_lambda(g,g)
```

The first two arrows live in ordinary trace-class calculus. The final read-off
uses the source no-defect convention only for the fixed-S quantized
differential main term.

## Lemma 1. Ordinary Positive Trace Owns The Cutoff

Statement:

```text
OrdinaryPositiveTraceScaleOwner(S,I,lambda,g):
  PositiveTrace^G_(S,lambda)(g)
    =
  Tr(A_(S,I,lambda,g)^* A_(S,I,lambda,g)),

  A_(S,I,lambda,g)
    =
  P_hat_(S,G)(lambda) P_(S,G)(lambda) theta_S(g).
```

Proof.

The trace-legality package fixes the order:

```text
operator identity
  -> Hilbert-Schmidt gate
  -> trace-class square
  -> ordinary positive trace.
```

Evidence:

```text
README.md:237-251
docs/manuscripts/connes-weil-rh-proof-draft.md:648-659
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md:95-184
```

The same `lambda` appears in both support projections inside `A`. No later
step may replace this ordinary positive trace by a finite-part scalar without
naming the conversion.

Output:

```text
ordinary_trace_scalar
same_lambda_in_P_and_P_hat
positive_trace_not_a_free_scalar
```

## Lemma 2. Support-Square Same-Scalar Equality

Statement:

```text
SupportSquareSameScalar(S,I,lambda,g):
  PositiveTrace^G_(S,lambda)(g)
    =
  Tr(theta_S(g)^*
     P_(S,G)(lambda) P_hat_(S,G)(lambda) P_(S,G)(lambda)
     theta_S(g)).
```

Proof.

Since:

```text
A=P_hat P theta_S(g)
```

and `P_hat` is an orthogonal projection in the fixed Hilbert structure:

```text
A^*A
  =
theta_S(g)^* P P_hat P theta_S(g).
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:675-677
docs/manuscripts/connes-weil-rh-proof-draft.md:951-963
docs/proofs/cc20-analytic-trace-legality-theorem-contract.md:219-237
```

This is an equality of ordinary finite-lambda trace-class scalars, not an
asymptotic statement.

Output:

```text
ordinary_positive_trace_equals_support_square_trace
same_tuple_S_I_lambda_g
same_trace_class_witness
```

## Lemma 3. Source Convention Conversion Ledger

Statement:

```text
SourceConventionConversionLedger(S,I,lambda,g,J):
  SupportSquareTrace(S,I,lambda,g)
    =
  NoDefectSourceTrace(S,I,lambda,g)
    +
  Rank_(S,I)(g)
    +
  PoleJetExtra_(S,I)(g)
    +
  CdefRemainder_(S,I,lambda,J)(g).
```

Proof.

Battle 2 proves the finite-lambda support-square transport identity:

```text
Tr(theta_S(g)^*
   P_(S,G) P_hat_(S,G) P_(S,G)
   theta_S(g))

=

Tr(theta_S(g)^*
   [-P_(S,G)(1/2)u_S^(-1)d^-u_S P_(S,G)]
   theta_S(g))

+ Rank_(S,I)(g)
+ PoleJetExtra_(S,I)(g)
+ CdefRemainder_(S,I,lambda)(g).
```

Evidence:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:15-46
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:296-350
```

The first trace on the right is the only place where the Connes--Consani
source no-defect convention enters. The route does not apply source
regularized cyclicity to the whole positive trace. It first separates:

```text
rank channel,
pole channel,
endpoint-strip projection defects.
```

Evidence:

```text
docs/manuscripts/connes-weil-rh-proof-draft.md:720-724
docs/proofs/cc20-trace-object-normalization-discharge.md:181-221
docs/proofs/fixed-s-no-defect-compact-form-read-off.md:193-227
```

Thus the ordinary-to-source conversion ledger is:

```text
SourceConventionLedger
  =
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
CdefRemainder_(S,I,lambda,J)(g).
```

If the source convention subtracts any finite-part scalar, this package forces
that scalar into the no-defect source trace or one of the displayed ledger
classes. It cannot sit outside the equality.

Output:

```text
ordinary_to_source_scalar_equality
source_convention_used_only_on_no_defect_main_term
rank_pole_cdef_own_all_terms_outside_no_defect
```

## Lemma 4. No-Defect Trace Equals Restricted CCM Scalar

Statement:

```text
NoDefectTraceEqualsRestrictedCCMScalar(S,I,lambda,g):
  NoDefectSourceTrace(S,I,lambda,g)
    =
  QW_lambda(g,g).
```

Proof.

The fixed-S no-defect compact-form package identifies the main trace with the
CCM25 restricted form for the same support-square test:

```text
F_g=g^* * g.
```

It reads the source main term through:

```text
QW(f,g)=Psi(f^* * g),
W_(0,2) + W_infty - sum_p W_p,
QW_lambda(g,g).
```

Evidence:

```text
docs/proofs/fixed-s-no-defect-compact-form-read-off.md:15-38
docs/proofs/fixed-s-no-defect-compact-form-read-off.md:139-190
docs/manuscripts/connes-weil-rh-proof-draft.md:988-1033
```

The read-off uses the same restricted window `[lambda^(-1),lambda]`, the same
pole convention, and the same finite-prime cutoff as the route tuple.

Output:

```text
no_defect_main_term_equals_QW_lambda
same_F_g
same_lambda_window
same_CCM25_pole_and_prime_convention
```

## Lemma 5. No Missing Trace-Scale Bulk

Statement:

```text
NoMissingTraceScaleBulk(S,I,lambda,g,J):
  no scalar term BulkScaleTerm_(S,I,lambda,g)
  remains outside

    QW_lambda(g,g),
    Rank_(S,I)(g),
    PoleJetExtra_(S,I)(g),
    CdefRemainder_(S,I,lambda,J)(g).
```

Proof.

Combine Lemmas 2 through 4:

```text
PositiveTrace
  =
SupportSquareTrace

  =
NoDefectSourceTrace
  +
Rank
  +
PoleJetExtra
  +
CdefRemainder

  =
QW_lambda
  +
Rank
  +
PoleJetExtra
  +
CdefRemainder.
```

This is a finite-lambda equality of named scalar objects. A hidden bulk term
would have to enter in one of four places:

| possible entry point | blocked by |
|---|---|
| before support-square trace | Lemmas 1 and 2 identify the ordinary trace scalar |
| in support-square transport | Battle 2 splits all fixed-S leftovers as no-defect, rank, pole, or projection defect |
| in no-defect read-off | Fixed-S no-defect package reads the whole main term as `QW_lambda` and proves no extra no-strip channel |
| in projection defects | Rows 4-7 and Battle 3 route every endpoint-strip term into `CdefRemainder` |

Evidence:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:249-350
docs/proofs/source-rank-pole-ledger-identification-proof-package.md:270-318
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md:54-169
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md:255-289
```

Therefore the external failure mode:

```text
PositiveTrace = QW_lambda + killed ledgers + small Cdef + divergent bulk
```

does not occur inside the project route-evidence calculus. If a referee finds
such a bulk term in the source formulas, it must contradict one of the cited
finite-lambda equalities and become a new named source obstruction.

Output:

```text
no_untracked_bulk_scale_term
no_hidden_finite_part_subtraction
positive_trace_and_QW_lambda_have_same_read_off_scale
```

## Lemma 6. Lambda-Limit Compatibility

Statement:

```text
TraceScaleLimitCompatibility(S_A,I,g,J):
  after triple vanishing,
  PositiveTrace >= 0 gives

    QW_lambda(g,g)
      >=
    - C_(S_A,I,J)(g) Cdef_(S_A,I,lambda,J)(g),

  and the right side tends to 0 for fixed S_A,I,g,J.
```

Proof.

Rows 5 and 7 give the finite-lambda lower bound after ledger killing:

```text
QW_lambda(g,g)
  >=
- C_(S_A,I,J)(g) Cdef_(S_A,I,lambda,J)(g).
```

Evidence:

```text
docs/proofs/no-hidden-positive-defect-outside-cdef-proof-package.md:354-377
docs/proofs/sonin-prolate-defect-referee-discharge.md:373-401
```

Battle 3 gives fixed-test `Cdef` exhaustion:

```text
Cdef_(S_A,I,lambda,J)(g) -> 0.
```

Evidence:

```text
docs/proofs/battle-3-cdef-exhaustion-proof-package.md:234-337
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md:174-220
```

The restricted-to-full bridge gives eventual fixed-test scalar equality:

```text
QW_lambda(g,g)=QW(g,g)
```

for large enough `lambda`.

Evidence:

```text
docs/proofs/restricted-to-full-qw-bridge-proof-package.md:257-288
```

Since Lemma 5 excludes any untracked lambda-growing term outside `Cdef`, the
limit reads the same scalar that becomes `QW(g,g)`.

Output:

```text
ledger_killed_lower_bound
fixed_test_Cdef_to_zero
same_scalar_enters_restricted_to_full_bridge
```

## Combined Proof

The six lemmas prove:

```text
TraceScaleCompatibilityContract(S,I,lambda,g,F_g,J).
```

The route obtains the finite-lambda identity:

```text
PositiveTrace^G_(S,lambda)(g)
  =
QW_lambda(g,g)
  +
Rank_(S,I)(g)
  +
PoleJetExtra_(S,I)(g)
  +
CdefRemainder_(S,I,lambda,J)(g).
```

This identity is enough to answer B1 at project proof-package level:

```text
the ordinary positive trace and the restricted CCM scalar use the same
finite-lambda read-off scale, and any discrepancy is named as rank, pole, or
endpoint-strip Cdef.
```

## What This Does Not Prove

This package does not prove:

```text
CC20 source formulas from first principles,
CCM24 fixed-S transport from first principles,
CCM25 restricted read-off from first principles,
accepted-source certification,
Lean theorem status,
RH.
```

It also does not claim:

```text
QW_lambda(g,g) >= 0 at finite lambda.
```

The finite-lambda sign conclusion remains:

```text
QW_lambda(g,g)
  >=
- C_(S_A,I,J)(g) Cdef_(S_A,I,lambda,J)(g).
```

## Current Judgment

| question | answer |
|---|---|
| Does this package close B1 at project proof-package level? | yes |
| Does it close B1 at accepted-source or Lean level? | no |
| Does it identify the ordinary-to-source conversion ledger? | yes |
| Does it rule out an untracked bulk scale term inside the route model? | yes |
| Does it preserve the source-conditional boundary? | yes |

The next external-opinion target is B2: the Sonin-projection repair direction.
It should be recorded as a rejected repair path, since the current route uses
the positive support-square trace above rather than replacing it with
`S_lambda theta_S(g)`.
