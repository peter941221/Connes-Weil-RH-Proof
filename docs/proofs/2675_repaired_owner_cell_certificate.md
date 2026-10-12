# Record 2675 - one repaired-owner cell certificate

Verdict: ONE-CELL-PRICE-AND-INTEGRAL-BRIDGE-PASS; evaluator containment remains the load-bearing premise.

The exporter `scripts/routea_repaired_owner_cell_price_certificate_2675.py`
replays the repaired owner used by record 2670 and selects cell 4096 of the
8192-cell partition. The cell is `[0, 450359962737/281474976710656]`. It
stores the four 2242 rectangle hulls, every final endpoint as an IEEE-754
binary64 bit pattern and exact rational, and the upward-rounded scalar price
chain (width, exponential weight, corner norm, and charge).

The four channel upper charges are:

```text
base_M0       6704819272940723 / 288230376151711744
base_D2       7455900885837357 / 140737488355328
correction_M0 6379944602934969 / 1125899906842624
correction_D2 4868726497393463 / 549755813888
total         4900979105982291 / 549755813888
```

The exported upward-binary64 chain is one binary64 ulp above the same-cell
256-bit reference (`2450489552991145/274877906944`), so this certificate does
not undercut the original directed-MPFR scalar chain. The total is below the
`knownError2109` budget `74601530.30234718` by exact rational comparison.

`ConnesWeilRH/Dev/C1RouteACellIntegralCharge2675.lean` supplies the formal
bridge. It proves the corner norm from a rational rectangle, a general
cell-integral bound from rectangle containment and a weight bound, then checks
all four decoded rectangles, all four channel charges, their conditional
four-integral sum, and the budget comparison. The audit source prints the
axioms for each declaration; Linux Mathlib v4.30 compilation exits 0 and every declaration uses exactly
`[propext, Classical.choice, Quot.sound]`.

The remaining premise is explicit: the 2242 natural interval evaluator must be
proved to contain the actual repaired-owner channel function on this entire
cell. Point samples and MPFR endpoint conversion do not establish that
continuum statement. The finite 8192-cell Lean sum, the live-owner
`chargeRest` identity, the signed infinite-xi tail, Producer GO, SourceRH, and
RH therefore remain open.
