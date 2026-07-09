# CC20 Post-Q Boundary Evaluation Transport Theorem Contract

Status: theorem contract for the second Row 3 subcontract in the
sign/defect discharge ledger.

This contract refines:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-theorem-contract.md
docs/audits/cc20-post-q-remainder-term-map.md
docs/audits/ccm24-fixed-s-post-q-transport-obstruction-audit.md
docs/proofs/cc20-post-q-derivative-domain-compatibility-theorem-contract.md
docs/audits/cc20-post-q-boundary-evaluation-source-decision-audit.md
docs/proofs/fixed-s-post-q-boundary-functional-transfer-theorem-contract.md
docs/proofs/fixed-s-post-q-boundary-functional-transfer-proof-package.md
```

It targets the two boundary terms in the CC20 post-`Q` formula:

```text
rho^(-1/2) (D_u xi_n)(rho^-1) zeta_n(1)

- rho^(1/2) xi_n(1) (D_u zeta_n)(rho).
```

The point is narrow:

```text
Before Row 5/6 can decide whether these terms are rank, pole, or
endpoint-strip Cdef, the route must prove that the endpoint evaluations are
transported as fixed-S boundary functionals in the same route window.
```

## Boundary

This contract does not prove:

```text
the boundary terms vanish,
the boundary terms are rank or pole,
the boundary terms are endpoint-strip Cdef,
or the sign/defect bridge is discharged.
```

It only states the source-to-fixed-S transport target for the two endpoint
functionals.

Rejected shortcut:

```text
triple vanishing kills the boundary terms.
```

Triple vanishing may be applied only after the terms have been identified as
the correct rank or pole ledgers. The boundary terms here are source-owned
post-`Q` endpoint evaluations and must be transported first.

## Evidence Lock

| source | lines | content |
|---|---|---|
| CC20 | `weil-compo.tex:1260-1264` | the formal `D_u` identity fails for `xi_n,zeta_n`, so boundary terms appear |
| CC20 | `weil-compo.tex:1267-1270` | Lemma `devil3` states the bulk term plus lower and upper boundary terms |
| CC20 | `weil-compo.tex:1308-1318` | computes the intermediate boundary expression `B` |
| CC20 | `weil-compo.tex:1320-1333` | integration by parts gives the final two endpoint terms |
| CC20 | `weil-compo.tex:1338-1346` | `Q epsilon` is the series of the `T_n` terms and convergence is deferred to the appendix |
| CC20 | `weil-compo.tex:2215-2236` | defines `B_n(rho)` and bounds the two endpoint pieces separately |
| CCM24 | `mainc2m24fine.tex:761-771` | transports support and Fourier support through the semilocal window |
| CCM24 | `mainc2m24fine.tex:983-1003` | gives `theta_S` Fourier compatibility and the dual pairing diagram |
| CCM24 | `mainc2m24fine.tex:1022-1029` | gives the Sonin-space isomorphism but not endpoint functional transport |

## Source Diagnosis

CC20 produces the boundary terms as a correction to the failed formal-domain
argument:

```text
xi_n,zeta_n not in Dom(D_u)
        |
        v
integration by parts on [rho^-1,1]
        |
        v
lower moving endpoint:
  rho^(-1/2) (D_u xi_n)(rho^-1) zeta_n(1)

upper fixed endpoint:
  -rho^(1/2) xi_n(1) (D_u zeta_n)(rho)
```

These are not optional decoration. They are the terms that make the post-`Q`
formula valid after the domain obstruction.

CC20 also estimates them separately in the appendix:

```text
B_n(rho)
  =
lambda(n)/sqrt(1-lambda(n)^2)
  *
  (
    rho^(-1/2)(D_u xi_n)(rho^-1) zeta_n(1)
    -
    rho^(1/2) xi_n(1)(D_u zeta_n)(rho)
  ).
```

Source:

```text
weil-compo.tex:2215-2236
```

## Contract Theorem 1. Source Boundary Terms

Target:

```text
CC20PostQBoundaryTerms(n):
  the lower and upper endpoint terms in `T_n(rho)` are named CC20 source
  objects produced by Lemma devil3:

    LowerBoundary_n(rho)
      = rho^(-1/2) (D_u xi_n)(rho^-1) zeta_n(1)

    UpperBoundary_n(rho)
      = -rho^(1/2) xi_n(1) (D_u zeta_n)(rho).
```

Required projections:

```text
lower_boundary_from_devil3
upper_boundary_from_devil3
boundary_terms_repair_domain_failure
boundary_terms_separated_from_bulk
boundary_terms_not_triple_vanishing_ledgers_yet
```

Reject:

```text
boundary term
  =
pole term
```

until the fixed-S transport and rank/pole ledger identification are proved.

## Contract Theorem 2. Fixed-S Boundary Functional Transport

Target:

```text
PostQBoundaryEvaluationTransport(S,I,lambda,g,F_g,n):
  CC20PostQBoundaryTerms(n)
  + CC20PostQRemainderFixedSCoordinateTransport(S,I,lambda,g,F_g)
  + CCM24 support/Fourier window transport
  ->
  the lower and upper endpoint evaluations transport to fixed-S boundary
  functionals in the same route coordinate and window.
```

Required projections:

```text
fixedS_lowerBoundary_functional
fixedS_upperBoundary_functional
lowerBoundary_uses_moving_endpoint_rho_inverse
upperBoundary_uses_fixed_endpoint_one
same_tuple_S_I_lambda_g_Fg
same_route_window_I
same_route_lambda
same_coordinate_VS
no_sonin_isomorphism_endpoint_shortcut
```

Meaning:

The endpoint evaluations must be transported as functionals. A Hilbert-space
isomorphism of Sonin spaces does not by itself transport point evaluations,
especially after the source formula has already singled them out as boundary
corrections.

## Contract Theorem 3. Boundary Ledger Entry Gate

Target:

```text
PostQBoundaryLedgerEntryGate(S,I,lambda,g,F_g,n):
  PostQBoundaryEvaluationTransport(S,I,lambda,g,F_g,n)
  ->
  the transported boundary terms are available as inputs to Row 5/6
  classification, but are not yet classified.
```

Required projections:

```text
transported_lowerBoundary_input_for_Row5_or_Row6
transported_upperBoundary_input_for_Row5_or_Row6
classification_not_performed_in_Row3
triple_vanishing_not_applied_in_Row3
```

Meaning:

Row 3 ends at transport. It must not decide whether the boundary terms are
rank, pole, or endpoint-strip `Cdef`.

## Import Acceptance Checklist

An accepted source import or formal proof can discharge this contract only if
it supplies:

| requirement | required evidence |
|---|---|
| exact lower endpoint term | `rho^(-1/2)(D_u xi_n)(rho^-1) zeta_n(1)` |
| exact upper endpoint term | `-rho^(1/2) xi_n(1)(D_u zeta_n)(rho)` |
| domain-repair origin | terms are produced by the failed `D_u` domain argument and integration by parts |
| fixed-S endpoint functionals | transported endpoint evaluations are named in the fixed-S model |
| same route window | lower moving endpoint and upper fixed endpoint use the route window `I` |
| same tuple | no fresh `S`, `I`, `lambda`, `g`, or `F_g` |
| no premature classification | rank/pole/Cdef decision is deferred to Rows 5/6 |

## Current Judgment

| question | answer |
|---|---|
| Does CC20 provide the boundary terms explicitly? | yes |
| Are they source-owned domain-repair terms? | yes |
| Does CCM24 automatically transport endpoint functionals? | no |
| Does this contract discharge Row 3? | no |
| What does it unlock if discharged? | Row 5/6 can classify the source-owned boundary terms |

The fast-search status is:

```text
second Row 3 subcontract stated;
classified as project-proof-required;
closed at route-evidence level by the fixed-S boundary-functional package;
not a source import, Lean theorem, or full Row 3 discharge.
```
