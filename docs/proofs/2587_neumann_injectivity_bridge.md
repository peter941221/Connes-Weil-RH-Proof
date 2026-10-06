# Record 2587: Neumann defect to injectivity bridge

Date: 2026-10-05

Status: LEAN-NEUMANN-INJECTIVITY-BRIDGE-PASS.

This record formalizes the algebraic core of the 2338 invertibility argument.
For continuous linear maps `A` and `X` on the same normed complex space, the
hypothesis

    ||I - X.comp A|| < 1

implies that `X.comp A` is injective, and therefore `A` is injective. The
proof uses only the triangle inequality and the operator-norm bound; it does
not assume a geometric-series instance for the continuous-linear-map ring.

In plain language, if `X A` differs from the identity by less than one in
operator norm, it cannot send a nonzero vector to zero. This is the algebraic
meaning of the Neumann defect gate.

## Evidence

- `ConnesWeilRH/Dev/C1RouteACorrectionNeumann2587.lean`
- `ConnesWeilRH/Dev/C1RouteACorrectionNeumann2587Audit.lean`
- `results/2587_neumann_injectivity_validation.json`

The clean Linux-side build and axiom audit pass. The audit reports only
`[propext, Classical.choice, Quot.sound]`.

## Boundary

This does not yet instantiate the theorem with the actual 2338 analytic
moment operator. The following facts remain open:

- the 900 analytic matrix-entry intervals are sound enclosures of Lean's
  `ownerMomentMatrix2351`;
- the exported defect bound is a Lean fact for that operator;
- the resulting injectivity is connected to `hdet` and the exact coefficient
  interval;
- owner transfer, producer GO, and RH.

The next implementation target is therefore the matrix/operator realization
and its entrywise enclosure interface, not additional second-chord cells.