# Fixed-S Source Remainder Projection Defect Normal Form Theorem Contract

Status: project-proof theorem contract for Row 4 of the sign/defect discharge
ledger.

This contract sits after:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md
```

and before rank/pole ledger identification and endpoint-strip `Cdef`
domination.

The route-evidence proof package is:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-proof-package.md
```

It aims to prove, inside the project route:

```text
FixedSProjectionDefectNormalFormForSourceRemainder(S,I,lambda,g,F_g,J).
```

## Boundary

This contract covers only the Row 4 normal-form step:

```text
TransportedCC20PostQRemainder
  ->
no-strip channels plus projection-order defects
  ->
projection-order defects have endpoint-strip shifted-kernel normal form.
```

It does not prove:

```text
rank ledger identification,
pole ledger identification,
endpoint-strip Cdef trace-norm domination,
fixed-test Cdef exhaustion,
or no-hidden-positive-defect equality.
```

Those remain Rows 5-7.

## Evidence Inputs

| input | current evidence |
|---|---|
| transported source remainder | `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md` |
| support-square projection transport | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:84-174` |
| no-defect support-square template | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:175-224` |
| projection-defect classification | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:225-271` |
| canonical projection-defect normal form | `docs/proofs/semilocal-q-compact-form.md:144-218` |
| endpoint-strip trace ideal stability | `docs/proofs/semilocal-q-compact-form.md:220-312` |
| rank-repair finite normal form | `docs/proofs/rank-repair-finite-normal-form.md:144-270` |

## Contract Theorem 1. Source Remainder Ownership For Row 4

Target:

```text
SourceRemainderOwnershipForProjectionDefectRow(S,I,lambda,g,F_g):
  the object classified in Row 4 is exactly
  TransportedCC20PostQRemainder(S,I,lambda,g,F_g), not a route-local
  support-square leftover.
```

Required projections:

```text
transported_source_remainder_object
same_source_Fg
same_route_tuple
same_fixedS_coordinate_VS
same_window_I
same_lambda
```

Reject:

```text
the same expansion applies
```

unless the object being expanded is the transported CC20 source remainder from
Row 3.

## Contract Theorem 2. No-Strip Versus Projection-Order Split

Target:

```text
SourceRemainderNoStripProjectionSplit(S,I,lambda,g,F_g,J):
  every term in the transported source remainder is either a no-strip channel
  for Rows 5/6, or contains a projection-order commutator with M_S or M_S^*.
```

Required projections:

```text
no_strip_part_named
projection_order_part_named
no_unclassified_part
commutator_occurs_after_common_coordinate
```

The permitted projection-order commutators are:

```text
[P,M_S]
[P_hat,M_S]
[P,M_S^*]
[P_hat,M_S^*]
```

## Contract Theorem 3. Endpoint-Strip Shifted-Kernel Normal Form

Target:

```text
SourceProjectionOrderEndpointStripNormalForm(S,I,lambda,g,F_g,J):
  every projection-order term from the transported source remainder expands as
  a finite graph-bounded sum of endpoint-strip shifted kernels.
```

Required normal form:

```text
theta(D^r g) X_0 M_b T_a X_1 theta(D^s g)^*
```

with:

```text
b supported on a finite endpoint strip,
X_0 and X_1 fixed graph-bounded,
T_a a fixed finite-S shift,
r+s <= J',
```

plus the corresponding post-`Q` boundary forms with a strip factor before the
evaluation functional.

Required projections:

```text
finite_endpoint_strip_index_set
graph_bounded_X_factors
fixed_finiteS_shift_set
strip_factor_before_boundary_evaluation
graph_order_Jprime_named
```

## Contract Theorem 4. Row 4 Classification Output

Target:

```text
FixedSProjectionDefectNormalFormForSourceRemainder(S,I,lambda,g,F_g,J):
  SourceRemainderOwnershipForProjectionDefectRow
  + SourceRemainderNoStripProjectionSplit
  + SourceProjectionOrderEndpointStripNormalForm
  ->
  TransportedCC20PostQRemainder is ready for Rows 5/6.
```

Required projections:

```text
source_remainder_no_strip_input_for_Row5
source_remainder_endpoint_strip_input_for_Row6
no_fourth_Row4_class
rank_pole_not_identified_here
Cdef_bound_not_proved_here
```

Meaning:

Row 4 ends once the transported source remainder has only no-strip channels and
endpoint-strip normal-form channels. Row 5 identifies no-strip channels as
rank or pole. Row 6 proves the trace-norm `Cdef` domination.

## Proof Acceptance Checklist

This project proof can be accepted only if it supplies:

| requirement | required evidence |
|---|---|
| source ownership | the classified object is `TransportedCC20PostQRemainder` from Row 3 |
| common coordinate | all commutators are formed in `V_S=M_S U_S` |
| exhaustive split | every term is no-strip or projection-order |
| listed commutators | projection-order terms contain one of the four named commutators |
| endpoint-strip normal form | commutators expand into finite shifted kernels with strip support |
| boundary control shape | post-`Q` boundary terms keep a strip factor before evaluation |
| no overclaim | rank/pole identification and `Cdef` bounds remain Rows 5/6 |

## Current Judgment

| question | answer |
|---|---|
| Is this a source import? | no |
| Does this use Row 3 output? | yes |
| Does this discharge sign/defect once stated? | no |
| What would it discharge if proved? | Row 4 projection-defect normal form for the transported source remainder |

The current status is:

```text
project proof target stated;
route-evidence proof package written;
not a Lean theorem or accepted source import.
```
