# CC20 Post-Q Series Tail Bounded-Comparison Theorem Contract

Status: theorem contract for the third Row 3 subcontract in the sign/defect
discharge ledger.

This contract refines:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/audits/cc20-post-q-remainder-term-map.md
docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md
docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md
docs/proofs/cc20-post-q-boundary-evaluation-transport-theorem-contract.md
docs/audits/cc20-post-q-series-tail-source-decision-audit.md
docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-theorem-contract.md
docs/proofs/fixed-s-post-q-series-tail-bounded-comparison-proof-package.md
```

It targets the infinite series tail in the CC20 post-`Q` formula:

```text
Q epsilon(rho)
  =
sum_n lambda(n)/sqrt(1-lambda(n)^2) * T_n(rho).
```

The point is narrow:

```text
After finite partial sums are transported term by term, the route must prove
that the CC20 tail estimate survives the CCM24 fixed-S bounded comparison in
the norm or graph class later consumed by Cdef.
```

## Boundary

This contract does not prove:

```text
the transported tail is endpoint-strip Cdef,
the transported tail vanishes as lambda -> infinity,
or the sign/defect bridge is discharged.
```

It proves only the legality of passing from finite transported partial sums
to the full transported source remainder.

Rejected shortcut:

```text
CC20 proves convergence,
therefore the fixed-S transported series converges in the route Cdef norm.
```

CC20's displayed estimate is a source-side scalar bound in the stated
`rho` range. The route must still prove that the bounded comparison and graph
norms preserve the required tail control.

## Evidence Lock

| source | lines | content |
|---|---|---|
| CC20 | `weil-compo.tex:1338-1346` | states `Q epsilon` as an infinite series of `T_n` terms and refers convergence to the appendix |
| CC20 | `weil-compo.tex:2168-2176` | introduces the convergence appendix and the bulk estimate `A_n(rho)` |
| CC20 | `weil-compo.tex:2178-2188` | bounds the `D_u zeta_n` contribution |
| CC20 | `weil-compo.tex:2190-2211` | bounds the `D_u xi_n` contribution and gets `boundAn` |
| CC20 | `weil-compo.tex:2215-2240` | bounds the boundary contribution `B_n(rho)` and gets `boundBn` |
| CC20 | `weil-compo.tex:2243-2250` | states convergence and an explicit uniform remainder bound for `rho in [1,2]` |
| CCM24 | `mainc2m24fine.tex:806-823` | gives bounded comparison `iota_S` with bounded inverse |
| CCM24 | `mainc2m24fine.tex:1022-1029` | gives Sonin-space isomorphism, not graph/trace-norm tail preservation |

## Source Diagnosis

CC20 controls the source-side series by splitting:

```text
T_n(rho)
  =
bulk derivative term
  +
boundary terms.
```

The appendix then derives:

```text
|A_n(rho)| <= explicit n-dependent bound
|B_n(rho)| <= explicit n-dependent bound
```

and combines them with rapid decay to get:

```text
|Q epsilon(rho) - finite partial sum through N|
  <= explicit tail sum,
  uniformly for rho in [1,2].
```

Source:

```text
weil-compo.tex:2243-2250
```

This is strong source evidence for scalar convergence. It is not yet the
fixed-S route statement:

```text
transported tail is small in the graph/trace class used by Cdef.
```

## Contract Theorem 1. Source Tail Estimate

Target:

```text
CC20PostQSourceTailEstimate(N):
  the CC20 post-Q series tail has the source uniform estimate

    |Q epsilon(rho) - sum_{k=0}^N lambda(k)/sqrt(1-lambda(k)^2) T_k(rho)|
      <= TailBound(N)

  for the source range of rho used by the theorem.
```

Required projections:

```text
tail_bound_source_formula
tail_bound_uniform_rho_range
tail_bound_uses_A_n_and_B_n
tail_bound_goes_to_zero
tail_bound_not_route_Cdef_norm_yet
```

Reject:

```text
finite numerical N=10 estimate
  ->
asymptotic fixed-S Cdef exhaustion.
```

The numerical bound is useful evidence for the source estimate, not a route
limit theorem.

## Contract Theorem 2. Fixed-S Bounded-Comparison Tail Transport

Target:

```text
PostQSeriesTailBoundedComparison(S,I,lambda,g,F_g,N):
  CC20PostQSourceTailEstimate(N)
  + termwise fixed-S transport for k <= N
  + CCM24 bounded comparison data
  ->
  the transported finite partial sums converge to the transported source
  remainder in the named fixed-S graph or trace class used before Cdef.
```

Required projections:

```text
source_tail_norm
fixedS_tail_norm
comparison_operator_iotaS
comparison_constants_tracked
finite_partial_sums_transport_termwise
tail_limit_commutes_with_fixedS_transport
tail_class_matches_later_Cdef_input
```

Meaning:

The route can pass from termwise Row 3 transport to the full post-`Q`
remainder only after the tail estimate survives the comparison map in the
right topology.

Reject:

```text
bounded comparison exists,
therefore convergence is preserved in every norm needed later.
```

The norm or graph class must be named.

## Contract Theorem 3. Full Transported Remainder Limit

Target:

```text
PostQFullTransportedRemainderLimit(S,I,lambda,g,F_g):
  PostQDerivativeDomainCompatibility for each term
  + PostQBoundaryEvaluationTransport for each term
  + PostQSeriesTailBoundedComparison
  ->
  the full source `Q epsilon` remainder is transported into the fixed-S Row 3
  coordinate as the limit of source-owned transported partial sums.
```

Required projections:

```text
partial_sum_objects_are_source_owned
partial_sum_transport_uses_same_tuple
tail_goes_to_zero_in_fixedS_tail_norm
full_limit_object_named
full_limit_not_classified_as_Cdef_in_Row3
```

Meaning:

This is the bridge from finite termwise transport to the full Row 3 input for
Rows 4-6.

## Import Acceptance Checklist

An accepted source import or formal proof can discharge this contract only if
it supplies:

| requirement | required evidence |
|---|---|
| source tail estimate | CC20 tail estimate with explicit norm/range |
| fixed-S comparison norm | the norm or graph class after CCM24 transport |
| comparison constants | constants from bounded comparison tracked or bounded uniformly for the fixed tuple |
| termwise partial-sum transport | every finite partial sum uses the same `(S,I,lambda,g,F_g)` |
| limit interchange | fixed-S transport commutes with the source tail limit in the named class |
| no Cdef overclaim | final limit remains a Row 3 transported source remainder, not yet endpoint-strip `Cdef` |

## Current Judgment

| question | answer |
|---|---|
| Does CC20 provide a source tail estimate? | yes |
| Is the estimate uniform in the source `rho` range? | yes, for `rho in [1,2]` in the displayed lemma |
| Does CCM24 automatically preserve it in Cdef trace norm? | no |
| Does this contract discharge Row 3? | no |
| What does it unlock if discharged? | finite termwise Row 3 transport can be promoted to the full source remainder |

The fast-search status is:

```text
third Row 3 subcontract stated;
classified as project-proof-required;
closed at route-evidence level by the fixed-S series-tail package;
not a source import, Lean theorem, or sign/defect discharge.
```
