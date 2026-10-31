3218 Route-A Concrete-Owner Phase Scaling
=========================================

Status
------

PASS_LEAN_EXACT_PHASE_SCALING

The family-4 phase at the cell-0 midpoint has absolute value about 257, so
the existing small-angle Taylor pins cannot be applied directly. This record
introduces an exact decomposition into 512 bounded factors:

    exp(angle * I) = exp((angle / 512) * I) ^ 512

The equality is proved with `Complex.exp_nat_mul`; it is not a numerical
approximation. Lean also proves that the actual cell-0 scaled phase satisfies
`|angle / 512| <= 1`, which is the precondition required by the existing
26th-order cosine and sine pins.

The file also proves a generic repeated-squaring rectangle-power membership theorem:
membership of one factor implies membership of the corresponding exact power
in the recursively multiplied rectangle.

For the actual record2680 cell-0 phase, Lean now proves membership in the
512-factor rectangle produced by `complexRectPowSq3218`, using nine repeated-squaring levels. This is the owner- and
coordinate-specific handoff needed before multiplying by the coefficient and
bump rectangle.

The coarse phase rectangle `re in [0.9, 1]`, `im in [-0.4, -0.3]` is also proved
for the repeated-squaring enclosure. Lean also proves a coarse exact-binary64
coefficient box for family 4 and a strictly negative real upper after
coefficient-phase multiplication. The remaining local step is bump positivity
at the actual midpoint and transport through the family-4 real-part formula.
------------

- WSL2 ext4 workspace: `/home/peter/rh-native`
- `lean-toolchain`: `leanprover/lean4:v4.30.0`
- focused target: `ConnesWeilRH.Dev.C1RouteAConcreteOwnerPhaseScaling3218`
- axiom audit: `[propext, Classical.choice, Quot.sound]`
Cell-0 sign closure
-------------------

The same-owner support theorem now gives strict bump positivity at the actual
cell-0 midpoint. Combining it with the coarse coefficient-phase rectangle and
the exact family-4 support reduction proves a strict negative physical real
part. The positive exponential factor in `weightedExternal3201` preserves the
sign, so Lean proves the cell-0 weighted midpoint upper with `valueUpper = 0`.
This closes only one `hvalue` instance; the universal 40960-cell arrays and
finite aggregate cancellation remain open.
