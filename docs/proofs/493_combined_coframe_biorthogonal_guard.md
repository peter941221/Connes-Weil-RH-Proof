# Proof 493: Combined coframe biorthogonal guard

## Result

Proof 493 is a correct structural advance, but it does not close Gate 3U.
It proves that the Proof 492 combined right coframe has one fixed source-Sonin
component and one genuine off-Sonin component:

```text
                   D_S = V_S + C_S
                            |
             +--------------+--------------+
             |                             |
             v                             v
       R D_S = J                 L_S = (I-R)D_S
       J^dagger D_S = I                    |
                                             v
                               V_S + source leakage
```

Equivalently,

```text
D_S = J + L_S,
J^dagger L_S = 0,
R L_S = 0.
```

Here `J` is the source Sonin inclusion, `R=J J^dagger` is its orthogonal
projection, `V_S=B A_S J` is the forward actual-band coframe, and `C_S` is
the raw metric coframe.

## Why this is the correct next object

Proof 492 established the exact raw remainder owner

```text
raw remainder
  = J^dagger T(V_S+C_S) - V_S^dagger T J.
```

The unresolved Hilbert--Schmidt column is therefore `M(V_S+C_S)`.  Existing
Julia-column contractions apply to different normalized carriers and cannot
be substituted for this raw combined coframe.

The source-specific projection identities give exactly the following ledger:

```text
+----------------------+----------------------+----------------------+
| column               | J^dagger compression| R compression        |
+----------------------+----------------------+----------------------+
| V_S = B A_S J        | 0                    | 0                    |
| C_S                  | I                    | J                    |
| D_S = V_S + C_S      | I                    | J                    |
| L_S = (I-R)D_S       | 0                    | 0                    |
+----------------------+----------------------+----------------------+
```

The zero row for `V_S` comes from the actual quotient-band relation `RB=0`.
It is not an abstract frame assumption.

## Lean owner

The source module is
`ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCombinedCoframeGuard.lean`.
Its main declarations are:

```text
sourceSoninProjection_comp_sourceActualBandForwardCoframe_eq_zero
sourceInclusionAdjoint_comp_sourceActualBandForwardCoframe_eq_zero
sourceInclusionAdjoint_comp_sourceActualBandForwardEndpointCoframe
sourceSoninProjection_comp_sourceActualBandForwardEndpointCoframe
sourceActualBandCombinedCoframeLeakage
sourceActualBandForwardEndpointCoframe_eq_inclusion_add_leakage
sourceActualBandCombinedCoframeLeakage_eq_forward_add_metricLeakage
sourceInclusionAdjoint_comp_sourceActualBandCombinedCoframeLeakage_eq_zero
sourceSoninProjection_comp_sourceActualBandCombinedCoframeLeakage_eq_zero
sourceActualBandForwardEndpointPairData_right_apply_eq_guardedCoframe
```

The final theorem rewrites the actual first right leg from Proof 492 as

```text
M(D_S u) = M((J+L_S)u)
```

without distributing `M` over the sum.

## Guard

Biorthogonality fixes only the component seen by `J^dagger`.  It does not
bound the orthogonal component.  In the elementary Hilbert-space model

```text
J x   = (x,0),
D_A x = (x,A x),
J^dagger D_A = I,
```

the norm satisfies

```text
norm(D_A x)^2 = norm(x)^2 + norm(A x)^2.
```

Thus `J^dagger D_A=I` permits arbitrarily large off-range leakage.  The Lean
identities in this proof must not be promoted to
`norm(D_S)<=1`, a Julia contraction, or a family-uniform Gate 3U estimate.

## Remaining analytic bottom

The next valid target is still the source-specific estimate

```text
sum_i norm(M((J+L_S)e_i))^2
  <= support--Sobolev polynomial independent of S,
```

with all of the following kept together:

```text
compact root support
  -> complete outer/reflected/second-support/prolate physical leg M
  -> coherent off-Sonin leakage L_S
  -> first absolute value only after recombination.
```

Splitting `M(J+L_S)` into separate Hilbert--Schmidt energies discards the
remaining cancellation.  Gate 3U, the finite-S sign, negative-owner
integration, Burnol's identity, and RH remain open.
