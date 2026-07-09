# Fixed-S Source Remainder Projection Defect Normal Form Proof Package

Status: route-evidence proof package for Row 4 of the sign/defect discharge
ledger.

This package proves the project-level bridge targeted by:

```text
docs/proofs/fixed-s-source-remainder-projection-defect-normal-form-theorem-contract.md
```

It is not a CC20, CCM24, or CCM25 source import. It is not a Lean theorem. It
does not identify the no-strip channels as rank or pole, and it does not prove
the endpoint-strip `Cdef` trace-norm bound.

## Result

Good result:

```text
FixedSProjectionDefectNormalFormForSourceRemainder is closed at
route-evidence level.
```

Boundary:

```text
This package itself does not identify rank/pole, prove Cdef domination, or
prove no-hidden-defect equality.
Global ledger status now has Rows 5-7 closed at route-evidence level.
The RH proof is not complete.
```

## Target

For the Row 3 output:

```text
TransportedCC20PostQRemainder(S,I,lambda,g,F_g),
```

prove:

```text
FixedSProjectionDefectNormalFormForSourceRemainder(S,I,lambda,g,F_g,J):
  every non-no-strip term contains a projection-order commutator and therefore
  has endpoint-strip shifted-kernel normal form.
```

## Evidence Boundary

| claim | evidence |
|---|---|
| source-owned transported remainder | `docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md:145-178` |
| common fixed-S coordinate | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:133-174` |
| projection commutators are the only model-change leftovers | `docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:161-170`, `204-223` |
| projection-defect normal form | `docs/proofs/semilocal-q-compact-form.md:144-218` |
| fixed-S endpoint-strip trace shape | `docs/proofs/semilocal-q-compact-form.md:220-312` |
| rank-repair endpoint-strip normal form | `docs/proofs/rank-repair-finite-normal-form.md:144-270` |

## Proof Skeleton

```text
TransportedCC20PostQRemainder
        |
        v
common fixed-S coordinate V_S=M_S U_S
        |
        v
support/Fourier projection transport
        |
        v
no-strip terms
  plus
projection-order commutator terms
        |
        v
endpoint-strip shifted-kernel normal form
        |
        v
inputs for Rows 5 and 6
```

The proof stops before ledger identification and trace-norm domination.

## Lemma 1. Row 4 Uses The Row 3 Source Object

Statement:

```text
SourceRemainderOwnershipForProjectionDefectRow(S,I,lambda,g,F_g):
  Row 4 classifies the transported CC20 source remainder from Row 3.
```

Proof.

Row 3 defines:

```text
TransportedCC20PostQRemainder(S,I,lambda,g,F_g)
```

as the limit of source-owned transported partial sums. Evidence:

```text
docs/proofs/cc20-post-q-remainder-fixed-s-transport-proof-package.md:145-178
```

Every transport step uses the same:

```text
S, I, lambda, g, F_g, V_S=M_S U_S.
```

Thus Row 4 may apply the fixed-S projection calculus only to that object. It
cannot replace it by a support-square leftover with matching notation.

Output:

```text
transported_source_remainder_object
same_source_Fg
same_route_tuple
same_fixedS_coordinate_VS
same_window_I
same_lambda
```

## Lemma 2. Common-Coordinate Projection Transport

Statement:

```text
SourceRemainderProjectionTransportInCommonCoordinate(S,I,lambda,g,F_g):
  support and Fourier projection terms acting on the transported source
  remainder are formed only after moving to V_S=M_S U_S.
```

Proof.

Battle 2 proves that the fixed-S projection transport and phase pullback occur
in the canonical coordinate:

```text
V_S=M_S U_S.
```

Evidence:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:84-174
```

In that coordinate, the Fourier projection is the phase pullback modulo terms
created by moving `M_S` and `M_S^*` through support or Fourier projections.
Those are the only model-change leftovers.

Output:

```text
commutators_formed_in_VS
support_projection_uses_same_window
fourier_projection_uses_same_window
phase_pullback_defects_listed
```

## Lemma 3. No-Strip Versus Projection-Order Split

Statement:

```text
SourceRemainderNoStripProjectionSplit(S,I,lambda,g,F_g,J):
  every term in the transported source remainder is either no-strip or contains
  one projection-order commutator.
```

Proof.

Battle 2 replaces the phrase:

```text
same quantized-calculus expansion
```

with a term split:

```text
fixed-S support square
  =
no-defect u_S template
  +
terms containing M_S or M_S^* projection commutators.
```

Evidence:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:204-223
```

The possible commutators are:

```text
[P,M_S]
[P_hat,M_S]
[P,M_S^*]
[P_hat,M_S^*]
```

Evidence:

```text
docs/proofs/battle-2-fixed-s-support-square-transport-proof-package.md:161-170
```

By Lemma 1, the object being split is the transported source remainder, not a
route-local leftover. Therefore the split is source-owned at Row 4.

Output:

```text
no_strip_part_named
projection_order_part_named
no_unclassified_part
listed_commutators_only
```

## Lemma 4. Endpoint-Strip Shifted-Kernel Normal Form

Statement:

```text
SourceProjectionOrderEndpointStripNormalForm(S,I,lambda,g,F_g,J):
  every projection-order term from Lemma 3 expands into finite endpoint-strip
  shifted-kernel normal form.
```

Proof.

For `R=P_I` or `R=P_hat_I`, the canonical projection-defect calculation uses:

```text
R G (1-R) = -R [G,R](1-R),
G=M_S^*M_S,
[G,R]=M_S^*[M_S,R]+[M_S^*,R]M_S.
```

Evidence:

```text
docs/proofs/semilocal-q-compact-form.md:156-180
```

For fixed finite `S`, expand:

```text
M_S=sum_alpha c_alpha T_alpha.
```

Then:

```text
[R,M_S]
  =
sum_alpha c_alpha M_(b_(R,alpha)) T_alpha,
```

where `b_(R,alpha)` is supported on a shifted endpoint strip. Evidence:

```text
docs/proofs/semilocal-q-compact-form.md:181-210
```

Thus every projection-order term has the normal form:

```text
theta(D^r g) X_0 M_b T_a X_1 theta(D^s g)^*
```

with `b` supported on a finite endpoint strip and fixed graph-bounded `X`
factors.

Output:

```text
finite_endpoint_strip_index_set
graph_bounded_X_factors
fixed_finiteS_shift_set
endpoint_strip_shifted_kernel_normal_form
graph_order_Jprime_named
```

## Lemma 5. Post-Q Boundary Terms Keep A Strip Factor

Statement:

```text
SourceProjectionDefectBoundaryStripShape(S,I,lambda,g,F_g,J):
  post-Q boundary terms from projection-order defects keep an endpoint-strip
  factor before the evaluation functional.
```

Proof.

The semilocal compact-form package proves that applying `Q` raises graph order
but does not remove the middle endpoint-strip factor. Bulk terms keep the
Hilbert-Schmidt factorization, and boundary terms have shape:

```text
evaluation o theta(D^r g) X_0 M_b T_a.
```

Evidence:

```text
docs/proofs/semilocal-q-compact-form.md:279-302
```

Rank-repair records the same post-`Q` stability:

```text
docs/proofs/rank-repair-finite-normal-form.md:211-270
```

Therefore the boundary terms created after `Q` do not become new no-strip
channels in Row 4. They remain endpoint-strip normal-form inputs for Row 6.

Output:

```text
strip_factor_before_boundary_evaluation
postQ_graph_order_increase_named
no_new_no_strip_boundary_channel_from_projection_defect
```

## Theorem. Fixed-S Projection Defect Normal Form For Source Remainder

Statement:

```text
FixedSProjectionDefectNormalFormForSourceRemainder(S,I,lambda,g,F_g,J):
  TransportedCC20PostQRemainder(S,I,lambda,g,F_g)
  splits into no-strip channels and endpoint-strip projection-defect normal
  forms, with no fourth Row 4 class.
```

Proof.

Combine Lemmas 1 through 5.

The proof uses:

```text
Row 3 source ownership,
common fixed-S coordinate,
Battle 2 projection transport,
semilocal projection-defect normal form,
post-Q strip stability.
```

It does not use:

```text
triple vanishing,
rank/pole identification,
endpoint-strip Cdef domination,
fixed-test Cdef exhaustion,
or lambda -> infinity.
```

## Output To The Discharge Ledger

This package supplies, at route-evidence level:

```text
FixedSProjectionDefectNormalFormForSourceRemainder
source_remainder_no_strip_input_for_Row5
source_remainder_endpoint_strip_input_for_Row6
no_fourth_Row4_class
```

It does not supply:

```text
SourceRankPoleLedgerIdentification
SourceEndpointStripRemainderCdefDomination
NoHiddenPositiveDefectOutsideCdef
SoninProlateDefectEqualsEndpointStripCdef
```

## Current Status

```text
Source ownership for Row 4:             proved at route-evidence level
Common-coordinate projection transport: proved at route-evidence level
No-strip/projection-order split:        proved at route-evidence level
Endpoint-strip shifted-kernel form:     proved at route-evidence level
Post-Q boundary strip shape:            proved at route-evidence level
Row 4 projection-defect normal form:    proved at route-evidence level

Rows 5-7 global ledger status:          proved at route-evidence level
Accepted source-import status:          open
Lean proof status:                      open
RH proof:                               not complete
```
