# Record 1931: fixed-owner grouped residual is exactly the gate

Date: 2026-09-24

## Formal result

For every actual `OrbitG8Geometry rho g`, the complete grouped residual is
read back without changing owner or splitting the visible-prime aggregate:

```text
archimedeanTerm(g.square) + intervalIntegral(actual residual)
  = ICgate(g.square).
```

`C1RouteAFixedOwnerGroupedResidual.lean` composes the exact coboundary
integration identity, the finite visible-prime aggregate to physical-kernel
interval identity, and the existing `p2AggregateValue = ICgate` readback.

It also proves that strict grouped-residual negativity for this fixed owner is
equivalent to `ICgate g.convolutionSquare < 0`.

The same leaf now proves the explicit-margin form: there exists an
`epsilon > 0` with the grouped residual bounded above by `-epsilon` if and
only if the same-owner gate is strictly negative.  The reverse direction uses
the concrete choice `epsilon = -ICgate / 2`; this is an exact existence
reduction, not a numerical margin claim.

This removes the duplicate residual formulation. The finite visible-prime
sum remains grouped throughout.

## Verification

Focused build `20260924_routeA_fixed_grouped_residual7.log`: 3794 jobs,
successful. The paired audit reports only `[propext, Classical.choice,
Quot.sound]`; no `sorryAx` occurs.

## Remaining certificate input

The reduction does not itself prove the strict sign. The next producer input
must be an owner-specific certificate for `ICgate g.convolutionSquare < 0`.
No committed exact matrix entries, interval witness, or analytic inequality
currently supplies that sign for the actual healthy owner.
