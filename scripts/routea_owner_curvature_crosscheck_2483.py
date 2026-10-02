"""Compare the independent 2477 interval smoke with the 2478 MPFR table."""

import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
IV = ROOT / "results/2483_owner_local_curvature_iv.json"
MPFR = ROOT / "results/2478_owner_local_curvature_mpfr.json"


def main():
    iv = json.loads(IV.read_text())
    mpfr = json.loads(MPFR.read_text())
    assert iv["cells"] == mpfr["cells"] == 40
    assert iv["subdiv"] == mpfr["subdiv"] == 16
    assert iv["effective_cells"] == mpfr["rows"][0]["effective_cells"] == 640
    rows = []
    for iv_row, mpfr_row in zip(iv["rows"], mpfr["rows"]):
        assert float(iv_row["sigma"]) == mpfr_row["sigma"]
        iv_values = [float.fromhex(payload["hex"])
                     for payload in iv_row["cell_upper_bounds"]]
        mpfr_values = [float.fromhex(payload["hex"])
                       for payload in mpfr_row["cell_upper_bounds"]]
        assert len(iv_values) == len(mpfr_values) == 640
        assert all(iv_value <= mpfr_value
                   for iv_value, mpfr_value in zip(iv_values, mpfr_values))
        assert iv_row["binding_index"] == mpfr_row["binding_index"]
        assert iv_row["max_cell"] <= mpfr_row["max_cell"]
        rows.append({
            "sigma": mpfr_row["sigma"],
            "iv_max_cell": iv_row["max_cell"],
            "mpfr_l1_max_cell": mpfr_row["max_cell"],
            "max_ratio_iv_to_mpfr_l1": iv_row["max_cell"] / mpfr_row["max_cell"],
            "cells_checked": len(iv_values),
            "iv_remainder": iv_row["remainder"],
            "mpfr_l1_remainder": mpfr_row["remainder"],
        })
    result = {
        "record": 2483,
        "status": "INDEPENDENT_IV_BELOW_MPFR_L1_SAME_GRID",
        "grid": {"cells": 40, "subdiv": 16, "effective_cells": 640},
        "rows": rows,
        "nonclaims": ["not a Lean certificate", "no producer GO", "no RH"],
    }
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
