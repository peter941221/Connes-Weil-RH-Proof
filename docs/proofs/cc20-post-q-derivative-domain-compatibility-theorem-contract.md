# CC20 Post-Q Derivative Domain Compatibility Theorem Contract

Status: theorem contract for the first Row 3 subcontract in the
sign/defect discharge ledger.

This contract refines:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/audits/cc20-post-q-remainder-term-map.md
docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md
docs/audits/cc20-post-q-derivative-domain-source-decision-audit.md
```

It targets the bulk term in the CC20 post-`Q` formula:

```text
rho^(1/2) int_(rho^-1)^1
  (D_u xi_n)(x) (D_u zeta_n)(rho x) dx.
```

The point is narrow:

```text
Before Row 4 can classify the transported bulk term as a fixed-S
projection-order defect, the route must prove that the derivative pieces have
fixed-S graph/domain representatives in the same coordinate as the route
projections.
```

## Boundary

This contract does not prove:

```text
the bulk term is endpoint-strip Cdef,
the boundary terms transport,
the infinite series tail transports,
or the sign/defect bridge is discharged.
```

It proves only the derivative/domain part needed before fixed-S
projection-defect classification can start.

Rejected shortcut:

```text
CCM24 gives a Sonin isomorphism,
therefore D_u xi_n and D_u zeta_n transport automatically.
```

That shortcut is blocked both by CC20 and CCM24 source text.

## Evidence Lock

| source | lines | content |
|---|---|---|
| CC20 | `weil-compo.tex:1201-1215` | defines `D_u(f)(x)=x f'(x)`, `D_u^*=-1-D_u`, and the formal operator `D_u^2+D_u` |
| CC20 | `weil-compo.tex:1260-1264` | says the formal identity using `D_u` cannot be applied directly to `xi_n,zeta_n` because they are not in the domain of `D_u` |
| CC20 | `weil-compo.tex:1267-1270` | states Lemma `devil3`, replacing the formal domain argument with a bulk-plus-boundary formula |
| CC20 | `weil-compo.tex:1320-1333` | derives the bulk term by integration by parts and exposes boundary terms |
| CC20 | `weil-compo.tex:1338-1346` | states `Q epsilon` as a series of the `T_n` terms and defers convergence to the appendix |
| CC20 | `weil-compo.tex:2171-2188` | bounds the `D_u zeta_n` part of the bulk term |
| CC20 | `weil-compo.tex:2190-2207` | bounds the `D_u xi_n` part of the bulk term |
| CCM24 | `mainc2m24fine.tex:806-823` | gives bounded comparison `iota_S` with bounded inverse |
| CCM24 | `mainc2m24fine.tex:846-852` | warns that semilocal Hermite and multiplication structures do not commute naively with `eta_S` |

## Source Diagnosis

CC20 itself explains why this subcontract is necessary:

```text
formal smooth-domain identity
        |
        v
cannot be applied to xi_n,zeta_n
because they have discontinuities at x=+-1
        |
        v
Lemma devil3 replaces it with:
bulk derivative term + two boundary terms.
```

That means the bulk term is not an abstract harmless derivative expression.
It is a source-owned graph-term produced after a domain failure has already
been repaired by explicit boundary accounting.

CCM24 then adds a second obstruction:

```text
eta_S carries filtrations and Sonin spaces,
but does not make N_S eta_S = eta_S N_infty,
and does not make |.|_S^2 eta_S(f) = eta_S(|.|^2 f).
```

Therefore the route needs a graph/domain compatibility theorem, not a
Hilbert-space isomorphism slogan.

## Contract Theorem 1. Source Bulk Derivative Object

Target:

```text
CC20PostQBulkDerivativeObject(n):
  the bulk expression

    rho^(1/2) int_(rho^-1)^1
      (D_u xi_n)(x) (D_u zeta_n)(rho x) dx

  is a named CC20 source object produced by Lemma devil3 after the
  `xi_n,zeta_n` domain failure is repaired by boundary terms.
```

Required projections:

```text
bulk_uses_Du_xi_n
bulk_uses_Du_zeta_n
bulk_comes_from_devil3
bulk_separated_from_boundary_terms
bulk_not_formal_smooth_domain_identity
```

Reject:

```text
D_u commutes with scaling, so the bulk term is automatic.
```

CC20 uses that commutation only inside a formula that must be repaired because
`xi_n,zeta_n` are not in the domain of `D_u`.

## Contract Theorem 2. Fixed-S Graph Representative

Target:

```text
PostQDerivativeDomainCompatibility(S,I,lambda,g,F_g,n):
  CC20PostQBulkDerivativeObject(n)
  + CC20PostQRemainderFixedSCoordinateTransport(S,I,lambda,g,F_g)
  + CCM24 bounded comparison data
  ->
  the two derivative factors have fixed-S graph/domain representatives in the
  common `V_S=M_S U_S` coordinate consumed by the route projections.
```

Required projections:

```text
fixedS_DuXi_representative
fixedS_DuZeta_representative
representatives_use_same_tuple_S_I_lambda_g_Fg
representatives_live_in_route_coordinate_VS
graph_norm_or_domain_class_named
bounded_comparison_constants_tracked
no_etaS_domain_commutation_shortcut
```

Meaning:

The route may use the bulk term in Row 4 only after it knows which fixed-S
graph/domain class the derivative factors occupy.

Reject:

```text
theta_S is a Sonin-space isomorphism,
therefore it transports D_u.
```

The source theorem must state the graph/domain transport or derive it from
explicit bounded-comparison estimates.

## Contract Theorem 3. Bulk-Term Coordinate Equality

Target:

```text
PostQBulkFixedSEquality(S,I,lambda,g,F_g,n):
  PostQDerivativeDomainCompatibility(S,I,lambda,g,F_g,n)
  ->
  the transported fixed-S bulk object is equal to the source CC20 bulk object
  under the common-test and common-coordinate identifications.
```

Required projections:

```text
source_bulk_object
fixedS_bulk_object
common_test_identification
common_coordinate_identification
same_rho_window
equality_before_projection_defect_classification
```

Meaning:

Row 4 may classify only the fixed-S image of the CC20 source bulk term. It may
not classify a route-local bulk lookalike.

## Import Acceptance Checklist

An accepted source import or formal proof can discharge this contract only if
it supplies:

| requirement | required evidence |
|---|---|
| exact source bulk term | the `D_u xi_n` / `D_u zeta_n` integral from CC20 Lemma `devil3` |
| domain-failure awareness | acknowledgement that `xi_n,zeta_n` are not in `Dom(D_u)` globally |
| fixed-S graph representatives | concrete representatives after CCM24 transport |
| common coordinate | representatives live in the `V_S=M_S U_S` coordinate |
| same tuple | no fresh test, window, finite set, or lambda |
| comparison constants | bounded-comparison constants are explicit or absorbed by a named norm theorem |
| equality before classification | the source bulk term equals the object Row 4 later classifies |

## Current Judgment

| question | answer |
|---|---|
| Does CC20 provide the post-`Q` bulk formula? | yes |
| Does CC20 show why a domain theorem is needed? | yes |
| Does CCM24 automatically provide the fixed-S derivative-domain transport? | no |
| Does this contract discharge Row 3? | no |
| What does it unlock if discharged? | Row 4 can try projection-defect classification for the source-owned bulk term |

The fast-search status is:

```text
first Row 3 subcontract stated;
derivative/domain compatibility not yet proved.
```

The source-import decision is:

```text
project-proof-required;
not source-import-discharged.
```

The next proof bridge named by the decision audit is:

```text
FixedSPostQBulkGraphTransfer(S,I,lambda,g,F_g,n).
```

Its project-proof contract is:

```text
docs/proofs/fixed-s-post-q-bulk-graph-transfer-theorem-contract.md
```
