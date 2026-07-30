# Proof 571: Physical Owner for the Transition-Skew Moment

## Result

For a forward coframe `F` and endpoint coframe `E`, the consumer-facing
interface records

```text
P_S F = 0,
P_S E = J,
```

where `P_S` is the source Sonin projection and `J` is the source inclusion.
Then the adjoint of the signed boundary moment is exactly

```text
rawCoframeBoundaryMoment(F,E)†
  = J† B E - F† B J,
```

with `B` the existing physical three-branch commutator.

The Lean theorem is stronger than that interface: its proof only uses
`P_S F = 0`, so this identity applies to an arbitrary `E`. The module also
specializes the identity to the actual named Schur boundary row used by the
Proof 570 transition ledger.

The proof uses only:

```text
B† = -B,
B J = -(I-P_S) D J,
```

and the forward carrier equation above. Thus the transition-skew coboundary from
Proof 570 has a physical signed owner after the Hilbert--Schmidt pair is built
from the two coframes.

At the actual transition-skew row, with `A = T - T†`, the module therefore
also proves the direct signed owner

```text
(M_S A - A M_(p::S))†
  = A† (J† B E_S - F_S† B J)
    - (J† B E_(p::S) - F_(p::S)† B J) A†.
```

This is an exact adjoint expansion. It does not identify `A` with zero or
bound the displayed expression uniformly in the finite set.

## Boundary

This is an exact operator identity.  It does not prove that the skew
coboundary cancels, has a favorable sign, or satisfies the family-uniform
Douglas estimate required by Gate 3U.  The two terms remain one signed
physical difference until a later trace estimate is supplied.

## Lean owner

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSActualSchurSkewPhysicalOwner.lean
ConnesWeilRH/Dev/
  CCM24FiniteSActualSchurSkewPhysicalOwnerAudit.lean
```

Primary external source for the distinction between Sonin transport and the
missing positivity producer: [Connes--Consani--Moscovici, arXiv:2310.18423v2](https://arxiv.org/abs/2310.18423).
