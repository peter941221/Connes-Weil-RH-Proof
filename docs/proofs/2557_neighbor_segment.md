Record 2557: a continuous two-cell bound with shared endpoints

Cell2701 at sigma=+1/2 reuses the accepted node2701 derivative and signed
value certificates. In the endpoint/midpoint channels, only node2702 and
midpoint5403/2 require new paired 160-bit exponential witnesses. The
fourth-envelope channel has its own certified evaluations. The new right endpoint's order-zero bound
consumes its order-three evaluator's BaseError proof, with no additional
exponential replay. All thirty families, stored squared widths, signed
modulations and coefficient boxes remain unchanged.

The new cell bound combines signed endpoint values with a signed midpoint
second-derivative bound and a whole-cell third-derivative allowance. The
fourth-derivative envelope controls movement between endpoints; its near
and far coordinates retain the original support geometry.

```text
+---------------------------+-------------------------+
| Quantity                  | Exact upper             |
+---------------------------+-------------------------+
| Node2702 signed value     | 849/10000000000          |
| Midpoint second bound     | 17521/100000000          |
| Cell third allowance      | 2221/250000              |
| Cell curvature allowance  | 181/1000000              |
| Cell2701 integral         | 111/1000000000000        |
| Prior cell2700 integral   | 114/1000000000000        |
| Continuous two-cell sum   | 225/1000000000000        |
+---------------------------+-------------------------+
```

neighborSegmentIntegralBound2557 uses adjacent-interval integral additivity
and continuity to combine the accepted cell2700 theorem with the new
cell2701 theorem. Equality of the shared endpoint positions is proved
explicitly. Both inequalities use the same coefficient function and the
same coefficient-ball membership premise. The result bounds the integral
of the complex norm over the entire segment, not a sum of sampled values.

Generate with scripts/generate_neighbor_cell_2557.py --assembly. Build the
project and all new modules with scripts/build_neighbor_milestone_2557.sh.
The independent reader scripts/validate_neighbor_cell_2557.py recomputes
the exponent traces, derivative factors, endpoint norms, midpoint signed
sum, fourth envelopes and final rational charges. It rejects a zeroed
integral upper and checks exact regeneration plus six prior default outputs.
With --log and --mirror it also checks terminal axiom reports and source
identity against the verification environment. The shared endpoint reader
from record2556 checks the eight reused-value modules separately.

Final integration completed 4583 build jobs. The 168 terminal declarations
in record2557 and 16 in record2556 have exactly the permitted three axioms.
The segment reader checked 758 project dependency sources byte-for-byte;
the shared-value reader checked 743. No new-module warnings remain.
Evidence: results/2557_neighbor_numeric_readback.json and
results/2556_shared_value_readback.json.

The scope is two adjacent cells at one sigma sign, conditional on actual
coefficient membership. Remaining grid cells and the other sign, exact
coefficient membership, correction channels and the complete selected-owner
signed budget remain open. No full-grid or RH conclusion follows here.
