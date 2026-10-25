# Row-B D4/D7 arithmetic does not yet certify the Lean integrals (record 3067)

Date: 2026-10-19.

Update 2026-10-25: record 3103 closes the actual smoothSeed D4/D7 integral
bounds with a new, kernel-checked rational certificate ledger. The old
3040-row comparison described below remains unproved and is not used by
that proof. See `3103_seed_d4_d7_kernel_certificates.md` and
`results/3103_seed_d4_d7_audit.json` for the completed replacement route.

Status: source-level gate audit for the reopened row-B campaign. The stored
finite sums clear their numerical thresholds. Exact-real and rational derivative
semantics are already proved in Lean; the remaining link is the per-cell
comparison of rational jet charges with the exported rational rows. This is a
scoped transfer gap, not a no-go for Route B or a producer result.

## What the current artifacts prove

For derivative order `k` (the number of derivatives), the target quantity is
`D_k = 4*integral_(0,1/2) |T^(k)(x)| dx`, where `T` is
`Real.smoothTransition`. An interval enclosure means a proved interval that
contains the actual derivative value at every point of a cell.

The current chain is:

```text
Real.smoothTransition derivatives
       +--> Lean rational-box derivative theorem 2738
       `--> Python interval rows 3040
                    |
                    v
              rational rows 3041
                    |
                    v
             exact sums 3042

2738 rational jet + 3040 rational row
                    |
                    v
          per-cell charge comparison (open)
```

The rational Lean box and numerical ledger have not been compared cell by cell.

- `scripts/generate_seed_d4d7_cell_upper_3040.py` evaluates the 8192 cells
  through the imported `p3_certified_strip_constants_2720.py` mpmath interval
  evaluator. Each exported row is `4*cellWidth*derivativeIntervalRadius`
  plus an endpoint-majorant share. The evaluator's row comparison with the
  2738 rational boxes remains unproved in Lean.
- `scripts/generate_seed_d4d7_arithmetic_3041.py` copies the 3040 rational
  row strings into Lean lists and proves their lengths and sums with
  `norm_num`. This proves exact arithmetic about the stored rationals.
- `C1RouteBSeedD4D7Aggregate3042.lean` proves the aggregate constants are
  below 1500 and 2,000,000,000. The bounds are useful only after the row
  enclosures are connected to the actual derivatives.
- `C1RouteBSeedCellGeometry2809.lean` proves each actual fourth and seventh
  derivative lies in the exact-real `seedTransitionJetInterval2734` cell
  interval.
- `C1SeedRationalTransitionJet2738.lean` proves that
  `rationalSeedTransitionJet2738 B m n` contains the actual derivative for
  any cell `B`, scale `m` satisfying its phase cap, and order `n`.
  `C1RepresentativeD4D7Boxes2755.lean` instantiates that theorem on one
  representative cell. The derivative-to-rational-box semantics are closed.
- `C1RouteBSeedLedgerSoundnessContract3025.lean` and
  `C1RouteBSeedLedgerAllowanceContract3031.lean` correctly expose the missing
  pointwise comparison as a hypothesis. They do not prove it.

## Exact next theorem

For each `i < 8192`, choose a scale `m_i` satisfying the 2738 phase cap and
prove the rational endpoint comparison
`4*cellWidth*endpointAbsMax(rationalSeedTransitionJet2738(cell,m_i,k)) <=
rowHead3040(i,k) + allowance` for `k=4,7`, where `rowHead` is the stored 3040
row minus `endpoint[k]/8192`. The factor four and cell width make this an
integral charge; a pointwise derivative magnitude cannot be compared directly
to an integral row. Summing the head rows and adding the proved endpoint
integral charges recovers the 3040 aggregate convention exactly. Existing
3032-3036 consumers assemble the cell integrals once these pointwise
comparisons are supplied.

```text
Rational jet theorem 2738
        |
        v
per-cell rational endpoint comparison against row 3040
        |
        v
4 * cellWidth * rationalJetAbsUpper <= rowHead3040 + allowance
        |
        v
8192-cell sum + allowance sum < D4/D7 threshold
```

The rational endpoint comparison is the blocking proof obligation. A 3040 row
is `rowHead3040 + endpointShare/8192`; the pointwise comparison uses
`rowHead3040`, then the separately proved 2803 endpoint integral is added once
after summing. This recovers the full 3040 aggregate without double counting.
Record 3070 evaluates the 2738 recurrence on all 8192 cells with
`m_i=ceil(-phaseCell.lo)` and compares each charge with the corresponding
3040 row head. Its
largest excess is `1.5462928573392617565e-17` for D4 at cell 2010 and
`1.2820844044711306088e-10` for D7 at cell 1249. All cells fit a uniform
`2e-10` allowance, costing `1.6384e-6` total, well below the aggregate margins.
This is an mpmath routing diagnostic, not a Lean theorem. The next formal brick
is to prove the generated rational inequalities or a uniform theorem for their
excess, then use the larger allowance in the new arithmetic consumer
`C1RouteBSeedLedgerAllowance3071.lean` and the existing 3032-3036 assembly.
The 3071 source proves generic allowance arithmetic and adds the endpoint
integral to a full-target inequality, conditional on the cell and ledger
bounds. Record 3096 adds its Linux build and paired axiom audit. Connecting
the actual row-head vector to the 3042 aggregate and proving the per-cell
comparisons remain open; that audit does not supply either premise.

## Scope

This gate advances only the row-B seed derivative pins. It does not establish
the poweredSeed carrier transfer, the rho-quantified detector duties, Route-A
selected-owner `qw >= 0`, `SourceRH`, or RH. Route A remains the binding
producer lane under the project rules.

Evidence: `results/3040_seed_d4d7_cell_upper.json`,
`scripts/generate_seed_d4d7_cell_upper_3040.py`,
`scripts/generate_seed_d4d7_arithmetic_3041.py`,
`ConnesWeilRH/Dev/C1RouteBSeedCellGeometry2809.lean`,
`ConnesWeilRH/Dev/C1RouteBSeedD4D7Arithmetic3041.lean`,
`ConnesWeilRH/Dev/C1RouteBSeedD4D7Aggregate3042.lean`, and
`ConnesWeilRH/Dev/C1RouteBSeedLedgerSoundnessContract3025.lean`,
`ConnesWeilRH/Dev/C1SeedRationalTransitionJet2738.lean`, and
`results/3070_seed_rational_box_margin.json` from
`scripts/diag_seed_rational_charge_3070.py`.
