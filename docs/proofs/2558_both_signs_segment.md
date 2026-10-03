Record 2558: both signs on the same continuous production segment

The segment from grid node2700 to node2702 now has separate integral bounds
for sigma=+1/2 and sigma=-1/2, and a theorem adding those two bounds. Here
sigma is the real exponential weight parameter. Changing its sign changes
the function being bounded; it is not a relabeling of the positive result.
The same thirty families, squared stored widths, signed modulations and
coefficient-ball premise are retained throughout.

The new generator accepts a starting cell, a cell count and a sign. It
selects existing endpoint owners when available and emits one new endpoint
evaluator per missing grid node, shared by the neighboring cells. The
accepted batch uses the negative sign on cells2700 and2701: nodes2700/2701
reuse record2555, their signed values reuse record2556, and only node2702
and the two midpoints need new endpoint/midpoint exponential witnesses.
Each cell still has its own fourth-derivative envelope evaluations.

The fourth-envelope exponent is

    max(sigma*a, sigma*b) - 30/(1-near^2).

Here a and b are the cell endpoints, and near is the smaller endpoint
distance from zero divided by the family's squared width. On a negative
cell the negative sigma sign selects a, not b. The independent reader
recomputes this maximum and rejects both negative certificates when asked
to interpret their exponent payloads with the opposite sign.

```text
+----------------------+----------------------+----------------------+
| Integral bound       | sigma=+1/2           | sigma=-1/2           |
+----------------------+----------------------+----------------------+
| Cell2700             | 114/1000000000000    | 2501/1000000000000   |
| Cell2701             | 111/1000000000000    | 2433/1000000000000   |
| Continuous segment   | 225/1000000000000    | 4934/1000000000000   |
+----------------------+----------------------+----------------------+
| Sum of both signs    | 5159/1000000000000   |                      |
+----------------------+----------------------+----------------------+
```

The negative-sign bound is about21.93 times the positive-sign bound. These
are certified upper bounds on integrals of norms, not measured integrals
and not a Weil-positivity conclusion. negativeSegmentIntegralBound2558
uses adjacent-interval additivity. bothSignsSegmentIntegralBound2558
proves endpoint equality across the existing positive and new negative
modules before adding the two inequalities for the same coefficients.

Generation: scripts/generate_signed_cells_2558.py, with the default batch
--start 2700 --cells 2 --sign -1.
Build new cell modules with scripts/build_signed_cells_2558.sh; final
integration also builds ConnesWeilRH and
ConnesWeilRH.Dev.C1RouteASignedSegment2558. Read back with
scripts/validate_signed_cells_2558.py using --log, --mirror and --cost-log.

The first cell-module build, on the existing Linux verification environment
with 16 logical CPUs and accepted dependencies already built, took 87.22s
elapsed, 386.00s user CPU, 22.99s system CPU and 4663452KiB peak RSS. This
includes the new endpoint, midpoint, norm, fourth-envelope and cell-integral
modules. It excludes source generation, independent readback and the final
segment/root build. It is a single batch measurement, not a full-grid
projection or a comparison against a cold dependency build.

The reader checks exact arithmetic independently, regeneration, zeroed
integral rejection, opposite-sign exponent rejection and unchanged outputs
of six prior default outputs. Wrapped real-number casts are normalized
before parsing; a focused split-line cast regression accompanies that fix.

Final integration passed 4590 build jobs. All 303 terminal declarations in
the new modules have exactly the permitted three axioms, 779 project
dependency sources match the verification environment byte-for-byte, and
no new-module warnings remain. The complete readback and build-cost fields
are recorded in results/2558_signed_cell_readback.json; generation inputs
are in results/2558_signed_cell_inputs.json.

Scope remains two cells at both signs, conditional on actual coefficient
membership. Cells meeting zero are outside the current fourth-envelope
generator's nonzero-near guard; arbitrary CLI ranges are not claimed as
verified. Remaining cells, exact coefficient membership, correction channels
and the complete selected-owner signed budget are still open.
