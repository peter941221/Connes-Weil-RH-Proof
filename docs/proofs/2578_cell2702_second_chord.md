Record 2578: cell 2702 correction second-chord certificate

Verdict: the first new chord cell compiles and verifies at both signs.
The 2577 fresh-node owners supply order-two endpoint bounds at nodes 2702
and 2703. The 2558 cell-specific fourth envelopes close the whole-cell
remainder. The resulting cell bounds are pointwise Lean certificates, not a
full-grid sum and not an exact coefficient-membership proof.

Construction

For a cell [x_j, x_{j+1}], the second-chord bound has the shape

  integral <= h/2 * (endpoint_left + endpoint_right)
              + h^3/12 * fourth_cell_upper.

Here h = 2 * stripRadius / 10240. The endpoint objects use the order-two
factor at each node. The fourth-cell envelope is a separate base-owner
certificate generated for cell 2702; the correction coefficient boxes weight
its per-family bounds in Lean.

```text
                 endpoint order-2 bounds
                         |       |
                         v       v
                  +------+-------+------+
                  | signed endpoint sum |
                  +----------+----------+
                             |
        fourth-cell envelope + h^3 / 12
                             |
                             v
                   certified cell integral
```

Results

```text
+--------+----------------------+-------------------+-------------------+
| sigma  | fourth upper         | cell upper        | endpoint nodes    |
+--------+----------------------+-------------------+-------------------+
| -1/2   | 90679.62224956072    | 0.03187287738422  | 2702, 2703        |
| +1/2   |  4107.984983057736   | 0.001456834994262  | 2702, 2703        |
+--------+----------------------+-------------------+-------------------+
```

The minus result is larger because the signed fourth envelope is strongly
sign-dependent. The cell upper remains a local quantity; multiplying either
row by 10240 would not prove the global integral because neighboring cells
need their own endpoint and fourth certificates.

Verification

The focused Lean build completes 3937 jobs with zero errors. The audit
requests 154 declarations, each depending only on
[propext, Classical.choice, Quot.sound]. The source/config mirror closure
checks 225 files. The independent validator replays both endpoint signs,
recomputes the fourth weighted sum and exact rational cell total, and checks
that outputs are unchanged by deterministic generation. The root build from
2577 remains valid with 4148 jobs and the 22 record-2271 integration tests.

The endpoint proofs come from the fresh-node owner record 2577. The fourth
modules are cell-specific 2558 base envelopes; their use here is a checked
upper-bound transfer through signedFourthCellUpper2574, not an assertion
that the base and correction functions are identical.

Scope boundary

The certificate still assumes the correction coefficient distance premise.
Exact interpolation-coefficient membership, full-grid numerical tables,
base-norm coverage, producer GO and RH remain open. No global extrapolation
is made from this cell.

Next work: connect adjacent 2578 cells through a short continuous span,
then price the full endpoint/fourth/assembly path before any mass
production.

Evidence

  scripts/generate_second_chord_cell_2578.py
  scripts/validate_second_chord_cell_2578.py
  ConnesWeilRH/Dev/C1RouteACorrectionSecondChordCell2702_2578.lean
  ConnesWeilRH/Dev/C1RouteACorrectionSecondChordCell2702_2578Audit.lean
  results/2578_second_chord_validation.json
