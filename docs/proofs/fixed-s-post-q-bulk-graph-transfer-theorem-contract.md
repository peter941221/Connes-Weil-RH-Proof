# Fixed-S Post-Q Bulk Graph Transfer Theorem Contract

Status: project-proof theorem contract for the first Row 3 subcontract.

This contract is the next bridge named by:

```text
docs/audits/cc20-post-q-derivative-domain-source-decision-audit.md
```

The route-evidence proof package is:

```text
docs/proofs/fixed-s-post-q-bulk-graph-transfer-proof-package.md
```

It aims to prove, inside the project route rather than by source import:

```text
PostQDerivativeDomainCompatibility(S,I,lambda,g,F_g,n)
PostQBulkFixedSEquality(S,I,lambda,g,F_g,n).
```

## Boundary

This contract covers only the CC20 post-`Q` bulk term:

```text
rho^(1/2) int_(rho^-1)^1
  (D_u xi_n)(x) (D_u zeta_n)(rho x) dx.
```

It does not cover:

```text
boundary evaluation transport,
series-tail bounded comparison,
endpoint-strip Cdef domination,
rank or pole ledger classification,
or no-hidden-defect equality.
```

Those remain separate Row 3 through Row 7 targets.

## Evidence Inputs

| input | current evidence |
|---|---|
| source bulk formula | `weil-compo.tex:1267-1270`, `1338-1346` |
| source domain warning | `weil-compo.tex:1260-1264` |
| source derivative estimates | `weil-compo.tex:2171-2211` |
| CCM24 fixed-S Hilbert comparison | `mainc2m24fine.tex:805-823` |
| CCM24 non-commutation warning | `mainc2m24fine.tex:846-852` |
| project graph/Cdef route | `docs/proofs/fixed-test-graph-cdef-exhaustion.md:73-85`, `112-141` |
| derivative-shift commutation route evidence | `docs/proofs/rank-repair-finite-normal-form.md:226-236` |
| `Q` graph-order route evidence | `docs/proofs/semilocal-q-compact-form.md:279-289` |

## Contract Theorem 1. Source-To-Log Graph Translation

Target:

```text
SourcePostQBulkLogGraphTranslation(n):
  the CC20 bulk derivative object built from
    (D_u xi_n)(x), (D_u zeta_n)(rho x)
  is represented in the same logarithmic graph calculus used by the route.
```

Required projections:

```text
source_Du_equals_log_scaling_derivative
source_bulk_interval_maps_to_log_strip
rho_window_maps_to_route_window
source_L2_estimates_become_graph_seminorm_inputs
domain_failure_boundary_terms_remain_separate
```

Reject:

```text
D_u is only a notation, so graph translation is automatic.
```

The translation must preserve the fact that boundary terms have already been
split off by Lemma `devil3`.

## Contract Theorem 2. Fixed-S Euler Graph Boundedness

Target:

```text
FixedSEulerGraphBoundedness(S,I,J):
  for fixed finite S and fixed graph order J, the finite-S Euler multipliers,
  their adjoints, and the finite shift operators appearing in M_S preserve the
  route graph domain with constants depending only on S,I,J.
```

Required projections:

```text
MS_preserves_graph_domain
MS_star_preserves_graph_domain
finite_shift_Ta_preserves_graph_domain
Du_commutes_with_finite_shift_Ta_in_log_coordinate
constants_fixed_before_lambda_limit
```

Reject:

```text
iota_S is bounded on L2,
therefore it is bounded on every graph domain.
```

The graph order must be named.

## Contract Theorem 3. Fixed-S Bulk Representative

Target:

```text
FixedSPostQBulkRepresentative(S,I,lambda,g,F_g,n):
  SourcePostQBulkLogGraphTranslation(n)
  + FixedSEulerGraphBoundedness(S,I,J_Q)
  + CCM24 fixed-S coordinate transport
  ->
  the CC20 post-Q bulk term has a fixed-S representative in the common
  coordinate V_S=M_S U_S.
```

Required projections:

```text
fixedS_bulk_uses_same_S
fixedS_bulk_uses_same_I
fixedS_bulk_uses_same_lambda
fixedS_bulk_uses_same_g_and_Fg
fixedS_bulk_lives_in_VS_coordinate
fixedS_bulk_graph_order_JQ_named
```

Meaning:

This is the concrete content of derivative/domain compatibility for the bulk
term.

## Contract Theorem 4. Source-Bulk Equality Before Row 4

Target:

```text
FixedSPostQBulkGraphTransfer(S,I,lambda,g,F_g,n):
  FixedSPostQBulkRepresentative(S,I,lambda,g,F_g,n)
  ->
  PostQDerivativeDomainCompatibility(S,I,lambda,g,F_g,n)
  and PostQBulkFixedSEquality(S,I,lambda,g,F_g,n).
```

Required projections:

```text
source_bulk_object
fixedS_bulk_object
source_to_fixedS_identification
same_tuple_identification
same_window_identification
equality_before_projection_defect_classification
```

Meaning:

Row 4 may classify the fixed-S bulk term only after this equality is proved.
Otherwise Row 4 might classify a route-local lookalike rather than the CC20
source post-`Q` bulk term.

## Proof Acceptance Checklist

This project proof can be accepted only if it supplies:

| requirement | required evidence |
|---|---|
| source ownership | exact CC20 bulk term from Lemma `devil3` |
| log graph translation | explicit relation between source `D_u` and route graph derivative |
| fixed-S graph boundedness | `M_S`, `M_S^*`, finite shifts, and derivative commutation at named graph order |
| common coordinate | all terms live in the `V_S=M_S U_S` coordinate |
| common tuple | same `S,I,lambda,g,F_g` as positive trace and `QW_lambda` |
| equality | the fixed-S graph object is the transported CC20 bulk term |
| no Cdef overclaim | classification and domination are deferred to Rows 4-6 |

## Current Judgment

| question | answer |
|---|---|
| Is this a source import? | no |
| Is this the next proof bridge for the first Row 3 subcontract? | yes |
| Does it discharge sign/defect once stated? | no |
| What would it discharge if proved? | derivative/domain compatibility for the source-owned bulk term |

The current status is:

```text
project proof target stated;
route-evidence proof package written;
not a Lean theorem or accepted source import.
```
