# Source Endpoint-Strip Cdef Domination Proof Package

Status: route-evidence proof package for Row 6 of the sign/defect discharge
ledger.

This package proves the project-level bridge targeted by:

```text
docs/proofs/source-endpoint-strip-cdef-domination-theorem-contract.md
```

It is not a CC20, CCM24, or CCM25 source import. It is not a Lean theorem. It
does not prove the final no-hidden-positive-defect equality.

## Result

Good result:

```text
SourceEndpointStripRemainderCdefDomination is closed at route-evidence level.
```

Boundary:

```text
This package itself does not prove final no-hidden-positive-defect equality.
Global ledger status now has Row 7 closed at route-evidence level.
The RH proof is not complete.
```

## Target

For the endpoint-strip part left after Rows 4 and 5:

```text
EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J),
```

prove:

```text
|EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g),
```

with fixed-test exhaustion of `Cdef` available after the standard order of
choices.

## Evidence Boundary

| claim | evidence |
|---|---|
| endpoint-strip normal form from source remainder | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md:227-332` |
| rank/pole channels removed before Cdef | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md:270-318` |
| endpoint-strip index set | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:54-93` |
| `Cdef` norm formula | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:94-138` |
| trace-norm and boundary-strip bounds | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:139-233` |
| fixed-test exhaustion | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:267-315`; `docs/proofs/fixed-test-graph-cdef-exhaustion.md:182-221` |

## Proof Skeleton

```text
Row 4 endpoint-strip normal forms
        |
        v
R_(S,I,lambda,J) and Q R_(S,I,lambda,J)
        |
        v
Cdef trace-norm summands
        |
        v
finite-strip Hilbert-Schmidt / boundary trace bounds
        |
        v
|EndpointStripSourceRemainder| <= C Cdef
        |
        v
fixed-test Cdef exhaustion available for Row 7
```

The proof stops before the final read-off equality.

## Lemma 1. Source Endpoint-Strip Terms Enter The Cdef Index Set

Statement:

```text
SourceEndpointStripTermsCdefIndexed(S,I,lambda,g,F_g,J):
  every endpoint-strip term from the transported source remainder is indexed
  by R_(S,I,lambda,J) or Q R_(S,I,lambda,J).
```

Proof.

Row 4 proves that every non-no-strip term in the transported source remainder
has normal form:

```text
theta(D^r g) X_0 M_b T_a X_1 theta(D^s g)^*
```

with `b` supported on a finite endpoint strip, plus post-`Q` boundary terms
with a strip factor before evaluation.

Evidence:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md:227-332
```

Battle 3 defines the endpoint-strip index set `R_(S,I,lambda,J)` from the same
data:

```text
alpha=(r,s,a,X_0,X_1,b,T_a),
supp(b) subset E_(lambda,a).
```

Evidence:

```text
docs/proofs/battle-3-cdef-exhaustion-proof-package.md:54-93
```

The post-`Q` boundary-strip terms belong to the associated family:

```text
Q R_(S,I,lambda,J).
```

Output:

```text
source_endpoint_strip_terms_from_Row4
finite_endpoint_strip_index_set
same_S_I_lambda_g
bulk_terms_in_R
postQ_boundary_terms_in_QR
```

## Lemma 2. Trace-Norm Bound For Cdef Summands

Statement:

```text
SourceEndpointStripTraceNormDomination(S,I,lambda,g,F_g,J):
  every source endpoint-strip summand has the trace-norm or boundary-strip
  bound used by the route Cdef norm.
```

Proof.

For a bulk strip summand:

```text
theta(D^r g) X_0 M_b T_a X_1 theta(D^s g)^*,
```

Battle 3 factors it through the endpoint strip:

```text
L2(R) --B_s--> L2(E_(lambda,a)) --A_r--> L2(R).
```

The Hilbert-Schmidt estimate gives:

```text
||A_r B_s||_1 <= ||A_r||_2 ||B_s||_2.
```

Evidence:

```text
docs/proofs/battle-3-cdef-exhaustion-proof-package.md:139-189
```

For post-`Q` boundary terms, Battle 3 proves that an endpoint-strip factor
remains before evaluation:

```text
evaluation o theta(D^r g) X_0 M_b T_a.
```

The finite-strip trace theorem gives:

```text
|evaluation(A_r v)|
  <=
C_(S,I,J)(g) ||v||_(L2(E_(lambda,a))).
```

Evidence:

```text
docs/proofs/battle-3-cdef-exhaustion-proof-package.md:190-233
```

Output:

```text
trace_class_for_bulk_strip_terms
boundary_strip_trace_bound
fixed_finiteS_coefficient_budget
constant_C_S_I_J_g
```

## Lemma 3. Endpoint-Strip Source Remainder Is Bounded By Cdef

Statement:

```text
SourceEndpointStripRemainderCdefBound(S,I,lambda,g,F_g,J):
  |EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J)|
    <=
  C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Proof.

Battle 3 defines:

```text
Cdef_(S,I,lambda,J)(g)
  :=
sum_(alpha in R_(S,I,lambda,J))
  || theta(D^r g) X_0 M_b T_a X_1 theta(D^s g)^* ||_1

+
sum_(beta in Q R_(S,I,lambda,J))
  |BoundaryStripTrace_beta(g)|.
```

Evidence:

```text
docs/proofs/battle-3-cdef-exhaustion-proof-package.md:94-138
```

By Lemma 1, every endpoint-strip source-remainder term appears in one of these
two sums. By Lemma 2, each term is bounded by the corresponding trace-norm or
boundary-strip summand, up to the fixed finite-S coefficient budget. Summing
over the fixed index family gives:

```text
|EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J)|
  <=
C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

The constant depends on fixed `S,I,J` and fixed seminorms of `g`. It does not
depend on a place set growing with `lambda`.

Output:

```text
endpoint_strip_remainder_object
sum_over_source_terms
termwise_Cdef_summand_domination
absolute_value_bound
```

## Lemma 4. Fixed-Test Cdef Exhaustion

Statement:

```text
SourceEndpointStripFixedTestCdefExhaustion(S_A,I,g,J):
  Cdef_(S_A,I,lambda,J)(g) -> 0
  as lambda -> infinity,
```

with `S_A`, `I`, `g`, and graph order fixed first.

Proof.

Battle 3 gives:

```text
Cdef_(S_A,I,lambda,J)(g)
  <=
C'_(S_A,I,J)(g) Cdef_graph_(S_A,I,lambda,J')(g).
```

Evidence:

```text
docs/proofs/battle-3-cdef-exhaustion-proof-package.md:234-315
```

The fixed-test graph exhaustion package proves:

```text
Cdef_graph_(S_A,I,lambda,J')(g) -> 0.
```

Evidence:

```text
docs/proofs/fixed-test-graph-cdef-exhaustion.md:182-221
```

Since the comparison constant is fixed in this limit:

```text
Cdef_(S_A,I,lambda,J)(g) -> 0.
```

Output:

```text
fixed_test_order_of_choices
S_A_fixed_before_lambda_limit
graph_order_fixed_before_lambda_limit
Cdef_graph_comparison
fixed_test_graph_exhaustion
```

## Theorem. Source Endpoint-Strip Cdef Domination

Statement:

```text
SourceEndpointStripRemainderCdefDomination(S,I,lambda,g,F_g,J):
  every endpoint-strip source-remainder term is a Cdef summand and the
  endpoint-strip source remainder satisfies the route Cdef bound, with
  fixed-test Cdef exhaustion available.
```

Proof.

Combine Lemmas 1 through 4.

The proof uses:

```text
Row 4 endpoint-strip normal form,
Row 5 removal of rank/pole ledgers,
Battle 3 Cdef norm formula,
finite-strip trace estimates,
fixed-test graph Cdef exhaustion.
```

It does not use:

```text
final read-off equality,
no-hidden-positive-defect equality,
full QW positivity,
or RH.
```

## Output To The Discharge Ledger

This package supplies, at route-evidence level:

```text
SourceEndpointStripRemainderCdefDomination
SourceEndpointStripFixedTestCdefExhaustion
```

It does not supply:

```text
NoHiddenPositiveDefectOutsideCdef
SoninProlateDefectEqualsEndpointStripCdef
```

## Current Status

```text
Source endpoint-strip Cdef indexing:    proved at route-evidence level
Trace-norm domination:                  proved at route-evidence level
Endpoint-strip source remainder bound:  proved at route-evidence level
Fixed-test Cdef exhaustion:             proved at route-evidence level
Row 6 Cdef domination:                  proved at route-evidence level

Row 7 global ledger status:             proved at route-evidence level
Accepted source-import status:          open
Lean proof status:                      open
RH proof:                               not complete
```
