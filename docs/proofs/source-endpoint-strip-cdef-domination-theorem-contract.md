# Source Endpoint-Strip Cdef Domination Theorem Contract

Status: project-proof theorem contract for Row 6 of the sign/defect discharge
ledger.

This contract sits after:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
docs/proofs/source-rank-pole-ledger-identification-proof-package.md
```

and before no-hidden-positive-defect equality.

The route-evidence proof package is:

```text
docs/proofs/source-endpoint-strip-cdef-domination-proof-package.md
```

It aims to prove, inside the project route:

```text
SourceEndpointStripRemainderCdefDomination(S,I,lambda,g,F_g,J).
```

## Boundary

This contract covers only the endpoint-strip domination step:

```text
endpoint-strip source-remainder terms
  ->
exact summands of Cdef_(S,I,lambda,J)(g)
  ->
trace-norm bound and fixed-test Cdef exhaustion.
```

It does not prove:

```text
the final read-off equality,
no-hidden-positive-defect equality,
full QW positivity,
or RH.
```

Those remain Row 7 and the final exit.

## Evidence Inputs

| input | current evidence |
|---|---|
| Row 4 endpoint-strip normal forms | `docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md:227-332` |
| Row 5 rank/pole removal gate | `docs/proofs/source-rank-pole-ledger-identification-proof-package.md:270-318` |
| endpoint-strip index set | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:54-93` |
| `Cdef` norm formula | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:94-138` |
| endpoint-strip trace-norm bound | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:139-189` |
| `Q` endpoint-strip stability | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:190-233` |
| graph comparison and fixed-test exhaustion | `docs/proofs/battle-3-cdef-exhaustion-proof-package.md:234-315`; `docs/proofs/fixed-test-graph-cdef-exhaustion.md:182-221` |

## Contract Theorem 1. Source Endpoint-Strip Terms Are Cdef-Indexed

Target:

```text
SourceEndpointStripTermsCdefIndexed(S,I,lambda,g,F_g,J):
  every endpoint-strip term from the transported source remainder belongs to
  the same finite endpoint-strip index set R_(S,I,lambda,J) or Q R_(S,I,lambda,J)
  used in the route Cdef norm.
```

Required projections:

```text
source_endpoint_strip_terms_from_Row4
finite_endpoint_strip_index_set
same_S_I_lambda_g
same_graph_order_or_named_enlargement
bulk_terms_in_R
postQ_boundary_terms_in_QR
```

Reject:

```text
endpoint-strip term is small.
```

The proof must identify the term with a summand in the displayed `Cdef` norm.

## Contract Theorem 2. Trace-Norm Domination

Target:

```text
SourceEndpointStripTraceNormDomination(S,I,lambda,g,F_g,J):
  each source endpoint-strip remainder term satisfies the finite-strip
  Hilbert-Schmidt trace-norm bound used in Cdef.
```

Required projections:

```text
trace_class_for_bulk_strip_terms
boundary_strip_trace_bound
fixed_finiteS_coefficient_budget
constant_C_S_I_J_g
no_constant_depends_on_growing_place_set
```

## Contract Theorem 3. Cdef Remainder Bound

Target:

```text
SourceEndpointStripRemainderCdefBound(S,I,lambda,g,F_g,J):
  if EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J) denotes the endpoint-strip
  part left after Rows 4 and 5, then

    |EndpointStripSourceRemainder_(S,I,lambda,g,F_g,J)|
      <= C_(S,I,J)(g) Cdef_(S,I,lambda,J)(g).
```

Required projections:

```text
endpoint_strip_remainder_object
sum_over_source_terms
termwise_Cdef_summand_domination
finite_or_summable_fixed_index_sum
absolute_value_bound
```

## Contract Theorem 4. Fixed-Test Cdef Exhaustion Is Available

Target:

```text
SourceEndpointStripFixedTestCdefExhaustion(S_A,I,g,J):
  after S_A, I, g, and graph order are fixed,

    Cdef_(S_A,I,lambda,J)(g) -> 0

  as lambda -> infinity.
```

Required projections:

```text
fixed_test_order_of_choices
S_A_fixed_before_lambda_limit
graph_order_fixed_before_lambda_limit
Cdef_graph_comparison
fixed_test_graph_exhaustion
```

## Combined Contract

Target:

```text
SourceEndpointStripRemainderCdefDomination(S,I,lambda,g,F_g,J):
  SourceEndpointStripTermsCdefIndexed
  + SourceEndpointStripTraceNormDomination
  + SourceEndpointStripRemainderCdefBound
  + SourceEndpointStripFixedTestCdefExhaustion.
```

Projection target:

```text
SourceEndpointStripRemainderCdefDomination
  ->
Row 7 may combine QW_lambda, killed ledgers, and a Cdef-bounded remainder.
```

## Proof Acceptance Checklist

This project proof can be accepted only if it supplies:

| requirement | required evidence |
|---|---|
| source ownership | endpoint-strip terms come from the transported source remainder |
| exact indexing | terms enter `R_(S,I,lambda,J)` or `Q R_(S,I,lambda,J)` |
| trace norm | each term has the finite-strip Hilbert-Schmidt or boundary-strip bound |
| fixed constants | constants depend only on fixed `S,I,J,g`, not on a growing place set |
| Cdef bound | endpoint-strip source remainder is bounded by route `Cdef` |
| exhaustion | fixed-test `Cdef -> 0` is available after choices are fixed |
| no overclaim | final read-off equality and sign consequence remain Row 7 |

## Current Judgment

| question | answer |
|---|---|
| Is this a source import? | no |
| Does this use Rows 4 and 5 output? | yes |
| Does this discharge sign/defect once stated? | no |
| What would it discharge if proved? | Row 6 endpoint-strip `Cdef` domination |

The current status is:

```text
project proof target stated;
route-evidence proof package written;
not a Lean theorem or accepted source import.
```
