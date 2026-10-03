"""Same-run control of the historical price and the repaired fallback.

Replays 2517 without overwriting it, requires all 640 entries for both signs
to reproduce, and separately prices the old global-weight Lean expression.
The 2522 table replaces only fallback entries by its proved scalar 1387328.
Totals remain external prices: safe-cell hcell and the node sum are open.
"""
import contextlib
import hashlib
import io
import json
import re
import tempfile
from fractions import Fraction as F
from pathlib import Path

import routea_owner_production_exp_remainder_2517 as parent
import routea_owner_family_binding_2493 as binding

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "results/2521_fallback_reprice.json"


def main():
    original_path = parent.OUT
    historical = json.loads(original_path.read_text(encoding="utf-8"))
    original_bytes = original_path.read_bytes()
    with tempfile.TemporaryDirectory() as temporary:
        parent.OUT = Path(temporary) / "replay.json"
        try:
            with contextlib.redirect_stdout(io.StringIO()):
                parent.main()
            replay = json.loads(parent.OUT.read_text(encoding="utf-8"))
        finally:
            parent.OUT = original_path
    assert replay == historical, "2517 same-run bitwise control failed"
    assert original_path.read_bytes() == original_bytes

    # Full-repo source identity remains Lean's job; this is exact input binding.
    scalar, coefficients = binding.parse_lean_defs()
    repair = json.loads(parent.REPAIR.read_text(encoding="utf-8"))
    capture = json.loads(parent.CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    factors = []
    radius = F(2076918743413931858457251756481, 316912650057057350374175801344)
    for i, (row, pair) in enumerate(zip(repair["coefficient_rows"], capture["families_hex"])):
        rad = F.from_float(float.fromhex(pair[0]))**2
        mod = F.from_float(float.fromhex(pair[1]))
        c = row["ideal_base_coefficient"]
        parts = tuple((F(c[k]["lower_exact"])+F(c[k]["upper_exact"]))/2
                      for k in ("real", "imag"))
        assert rad == scalar[f"rad{i}_2460"] and mod == scalar[f"mod{i}_2460"]
        assert parts == coefficients[f"coef{i}_2460"]
        factor = sum(map(abs, parts)) * (3720/rad**2+120*abs(mod)/rad+
                 mod**2+60/rad+abs(mod)+F(1, 4))
        factors.append((rad, factor))
    assert len(factors) == 30
    mpfr, iv = parent.mpfr, parent.iv
    local = (0.0, 0.0)
    for rad, factor in factors:
        local = mpfr.add(local, mpfr.mul(
            mpfr.unary("mpfr_exp", iv(rad/2-30)), iv(factor)))
    global_value = mpfr.mul(mpfr.unary("mpfr_exp", iv(radius/2-30)),
                           iv(sum((f for _, f in factors), F(0))))
    table_text = (ROOT/"ConnesWeilRH/Dev/C1RouteAExpProductionTable2519.lean").read_text(encoding="utf-8")
    literals = re.findall(r"if index.val = \d+ then \((-?\d+) : ℚ\) / (\d+) else", table_text)
    assert len(literals) == 640
    old_table = [F(int(a), int(b)) for a, b in literals]
    factor = (radius/320)**3/12
    result_rows = []
    for row in replay["rows"]:
        expected_table = [F.from_float(float.fromhex(x)) for x in row["cell_upper_nextup_hex"]]
        assert old_table == expected_table, "2519 payload/source mismatch"
        fallback = row["cell_upper"][0]
        assert abs(local[1]/fallback-1) < 1e-12, "independent scalar assembly mismatch"
        assert F.from_float(global_value[0]) > old_table[0], "global mismatch not reproduced"
        assert local[1] < 1387328
        table = [old_table[i] if 196 <= i <= 443 else F(1387328) for i in range(640)]
        new_total = factor * sum(table, F(0))
        corrected_old = factor * sum((F.from_float(row["cell_upper"][i])
                          if 196 <= i <= 443 else F.from_float(global_value[1])
                          for i in range(640)), F(0))
        result_rows.append({"sigma": row["sigma"],
            "historical_price": row["production_remainder"],
            "historical_fallback": fallback,
            "family_fallback_interval": local,
            "global_fallback_interval": global_value,
            "global_to_historical_ratio": global_value[0]/fallback,
            "old_2516_definition_total_upper_display": float(corrected_old),
            "repaired_2522_table_total_exact": str(new_total),
            "repaired_2522_table_total_display": float(new_total),
            "rounding_cost_display": float(new_total)-row["production_remainder"]})
    paths = [Path(__file__).resolve(), Path(parent.__file__).resolve(),
        Path(binding.__file__).resolve(), parent.REPAIR, parent.CAPTURE, binding.LEAN,
        original_path, ROOT/"scripts/routea_owner_local_curvature_mpfr_2478.py",
        ROOT/"scripts/routea_mpfr_owner_atom_preflight_2286.py",
        ROOT/"ConnesWeilRH/Dev/C1RouteAExpProductionRemainder2516.lean",
        ROOT/"ConnesWeilRH/Dev/C1RouteAOwnerWeightedCurvature2480.lean",
        ROOT/"ConnesWeilRH/Dev/C1RouteAExpFamilyFallback2521.lean",
        ROOT/"ConnesWeilRH/Dev/C1RouteAExpProductionTable2519.lean"]
    result = {"record": 2521, "status": "PASS_EXTERNAL_PRICE_NOT_FULL_CERTIFICATE",
        "same_run_2517_full_artifact_equal": True,
        "2519_all_640_literals_equal_both_signs": True,
        "exact_owner_families_checked": 30, "fallback_cells": 392, "safe_cells": 248,
        "rows": result_rows,
        "sources": {str(p.relative_to(ROOT)).replace('\\', '/'):
                    hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
        "open": ["safe-cell hcell", "node-sum numeric certificate",
                 "midpoint to exact interpolant", "selected-detector signed margin"]}
    OUT.write_text(json.dumps(result, indent=2)+"\n", encoding="utf-8")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
