Record 2559: both signs across the production grid origin

The two cells5119 and5120 meet at node5120, whose position is exactly zero.
All thirty families are nonzero at their endpoints and midpoints. The four
cell certificates cover both sigma signs and retain the stored squared
widths, signed modulations and actual coefficient-ball membership premise.
Their continuous segment runs from node5119 to node5121.

The old fourth-envelope generator required near>0 only because it passed
growth/closest to a family evaluator, with closest=near*radius. The analytic
bound uses exp(max(sigma*a,sigma*b)-30/(1-near^2)), which is finite at near=0.
The implementation now evaluates that exact exponent directly using the
same rational Horner-and-squaring arithmetic and error propagation. No
analytic bound, evaluator precision or trust assumption was weakened.

At these cells every family's near value is zero. The exponent is exactly
-30 on the decaying side and -30+65536001/102400000000 on the growing side.
The independent reader checks those two values for all thirty families,
in addition to its independent replay of each exponential and polynomial.

```text
+----------------------+------------------+------------------+
| Integral upper       | sigma=+1/2       | sigma=-1/2       |
+----------------------+------------------+------------------+
| Cell5119             | 0.017653882879   | 0.017665182856   |
| Cell5120             | 0.017661081262   | 0.017649787517   |
| Continuous segment   | 0.035314964141   | 0.035314970373   |
+----------------------+------------------+------------------+
```

All displayed decimals are exact rational bounds, not rounded measurements.
centralBothSignsIntegralBound2559 proves the sum of both signed integrals
is at most 35314967257/500000000000, exactly 0.070629934514. The two signs use
the same coefficient function; endpoint equality is proved before adding
their inequalities. The result bounds integrals of norms and is not a
Weil-positivity conclusion.

The all-thirty-active branch also exposed a packaging issue: the underlying
fourth generator already emitted its aggregate definitions, while the
boundary wrapper added another aggregate and left the original names
unscoped. That branch now renames and reuses the existing aggregate; the
partial-support branch is unchanged. Record-aware generated names allow
the new cells to coexist with the previously accepted boundary cells.

Generate with scripts/generate_central_cells_2559.py. Build the four cells
in order with scripts/build_central_cells_2559.sh, then build ConnesWeilRH
and ConnesWeilRH.Dev.C1RouteACentralSegment2559. Validate with
scripts/validate_central_cells_2559.py using --log, --mirror and --cost-log.
The reader checks all forty generated cell/node modules, the generated
segment, six old-versus-extracted exponent controls, independent numeric
readback, zeroed-integral rejection and opposite-sign exponent rejection.
The prior record2558 and2557 readers were also rerun successfully.

The Linux verification environment has 16 logical CPUs. Cells were built in
sequence to limit concurrent heavy dependency groups; endpoints shared by
neighboring cells were reused. The first row includes more new dependencies.

```text
+-----------+-------+-----------+----------+--------------+
| Cell      | Sign  | Elapsed s | User s   | Peak RSS KiB |
+-----------+-------+-----------+----------+--------------+
| 5119      | +     | 99.07     | 304.45   | 4721500      |
| 5120      | +     | 42.77     | 226.25   | 4657912      |
| 5119      | -     | 44.24     | 309.84   | 4680540      |
| 5120      | -     | 40.24     | 225.41   | 4635872      |
+-----------+-------+-----------+----------+--------------+
```

These are single build measurements with accepted dependencies already
built. They exclude generation, independent readback and final root/segment
integration, and do not establish the cost of the remaining grid.

Final integration passed 4587 build jobs. All 737 terminal declarations in
the new modules use exactly the permitted three axioms, 776 project source
dependencies match the verification environment byte-for-byte, and the new
modules have no warnings.

Evidence: results/2559_central_cell_inputs.json and
results/2559_central_cell_readback.json. Full-grid numeric coverage, exact
coefficient membership, correction channels and the complete selected-owner
signed budget remain open.
