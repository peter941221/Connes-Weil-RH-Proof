# Fixed-S Post-Q Series Tail Bounded-Comparison Theorem Contract

Status: project-proof theorem contract for the third Row 3 subcontract.

This contract is the next bridge named by:

```text
docs/audits/cc20-post-q-series-tail-source-decision-audit.md
```

The route-evidence proof package is:

```text
docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md
```

It aims to prove, inside the project route rather than by source import:

```text
PostQSeriesTailBoundedComparison(S,I,lambda,g,F_g,N)
PostQFullTransportedRemainderLimit(S,I,lambda,g,F_g).
```

## Boundary

This contract covers only the passage from finite transported partial sums to
the full transported CC20 post-`Q` source remainder.

It does not cover:

```text
rank or pole ledger classification,
endpoint-strip Cdef domination,
fixed-test Cdef exhaustion,
or no-hidden-defect equality.
```

Those remain separate Rows 4-7 targets.

## Evidence Inputs

| input | current evidence |
|---|---|
| source infinite series | `weil-compo.tex:1338-1346` |
| source bulk estimates | `weil-compo.tex:2178-2211` |
| source boundary estimates | `weil-compo.tex:2215-2240` |
| source uniform tail estimate | `weil-compo.tex:2243-2250` |
| CCM24 bounded comparison | `mainc2m24fine.tex:805-823` |
| CCM24 Sonin isomorphism | `mainc2m24fine.tex:1022-1029` |
| termwise bulk transport | `docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md` |
| termwise boundary transport | `docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md` |
| fixed finite-S graph boundedness | `docs/proofs/fixed-test-graph-cdef-exhaustion.md:112-141` |

## Contract Theorem 1. Source Summable Tail Majorant

Target:

```text
CC20PostQSourceSummableTailMajorant(N):
  the CC20 post-Q source tail after N has a summable majorant built from the
  displayed A_n and B_n estimates.
```

Required projections:

```text
source_partial_sum_object
source_tail_object
bulk_majorant_A_n
boundary_majorant_B_n
majorant_summable
source_tail_bound_uniform_in_rho_range
```

Reject:

```text
source scalar convergence is already route Cdef convergence.
```

The source majorant is only the input to the route Cauchy argument.

## Contract Theorem 2. Fixed-S Tail Norm

Target:

```text
FixedSPostQTailNorm(S,I,lambda,J_Q):
  name the graph or trace class in which transported post-Q partial sums are
  compared before Row 4 classification.
```

Required projections:

```text
fixedS_tail_norm_name
tail_norm_uses_same_VS_coordinate
tail_norm_uses_same_window_I
tail_norm_uses_same_lambda
tail_norm_graph_order_JQ_named
tail_norm_before_Cdef_classification
```

Meaning:

The theorem must not hide convergence in an unnamed topology. The route uses
this norm only to build the full transported source remainder.

## Contract Theorem 3. Termwise Transported Partial Sums

Target:

```text
FixedSPostQTransportedPartialSums(S,I,lambda,g,F_g,N):
  finite sums through N are transported term by term using the already proved
  bulk and boundary transfer packages.
```

Required projections:

```text
partial_sum_terms_source_owned
bulk_terms_use_FixedSPostQBulkGraphTransfer
boundary_terms_use_FixedSPostQBoundaryFunctionalTransfer
partial_sum_uses_same_tuple
partial_sum_lives_in_fixedS_tail_norm
```

Reject:

```text
full infinite series transport before finite partial sums are defined.
```

## Contract Theorem 4. Bounded-Comparison Cauchy Control

Target:

```text
FixedSPostQTailCauchyControl(S,I,lambda,g,F_g,N):
  the transported tail after N is bounded by a fixed comparison constant times
  the CC20 source majorant tail.
```

Required projections:

```text
comparison_operator_iotaS
comparison_constant_C_S_I_JQ
constant_fixed_before_N_limit
transported_tail_bound
transported_tail_Cauchy
tail_limit_commutes_with_fixedS_transport
```

Meaning:

For fixed `S,I,lambda,g,F_g,J_Q`, the bounded comparison constant may multiply
the CC20 tail majorant. Since the source majorant is summable, the transported
partial sums form a Cauchy sequence in the named fixed-S tail norm.

## Contract Theorem 5. Full Transported Remainder Limit

Target:

```text
FixedSPostQSeriesTailBoundedComparison(S,I,lambda,g,F_g,N):
  FixedSPostQTransportedPartialSums
  + FixedSPostQTailCauchyControl
  -> PostQSeriesTailBoundedComparison(S,I,lambda,g,F_g,N)
  and PostQFullTransportedRemainderLimit(S,I,lambda,g,F_g).
```

Required projections:

```text
full_transported_remainder_object
full_limit_is_limit_of_source_owned_partial_sums
tail_goes_to_zero_in_fixedS_tail_norm
same_tuple_identification
same_window_identification
limit_before_projection_defect_classification
```

Meaning:

Row 4 may classify the transported full source remainder only after this limit
object is named.

## Proof Acceptance Checklist

This project proof can be accepted only if it supplies:

| requirement | required evidence |
|---|---|
| source majorant | exact CC20 bulk and boundary tail estimates |
| finite partial sums | each finite term uses source-owned bulk and boundary pieces |
| fixed-S norm | named fixed-S graph or trace class before `Cdef` classification |
| bounded comparison | constants fixed for the route tuple and graph order |
| Cauchy convergence | transported tails tend to zero in the named class |
| full limit object | full transported source remainder is defined as the limit |
| no Cdef overclaim | rank/pole/Cdef classification and domination are deferred to Rows 4-6 |

## Current Judgment

| question | answer |
|---|---|
| Is this a source import? | no |
| Is this the next proof bridge for the third Row 3 subcontract? | yes |
| Does it discharge sign/defect once stated? | no |
| What would it discharge if proved? | finite-to-full transport for the source post-`Q` remainder |

The current status is:

```text
project proof target stated;
route-evidence proof package written;
not a Lean theorem or accepted source import.
```
