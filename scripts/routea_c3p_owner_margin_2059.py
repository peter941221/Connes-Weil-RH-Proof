import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE_2037 = ROOT / "results" / "2037_route_a_g8h_basis_comparison.json"
SOURCE_2058 = ROOT / "results" / "2058_l5_solve.json"
OUTPUT = ROOT / "results" / "2059_route_a_c3p_owner_margin.json"


def load_json(path):
    with path.open("r", encoding="utf-8") as handle:
        return json.load(handle)


def main():
    basis = load_json(SOURCE_2037)
    l2 = load_json(SOURCE_2058)

    one_copy = [row for row in basis["rows"] if row["basis"] == "one-copy"]
    if len(one_copy) != 2:
        raise RuntimeError("expected exactly two one-copy basis rows")

    owner_matches = {
        "owner": l2["owner"] == "one-copy G8-H",
        "support": all(row["support"] == l2["support"] for row in one_copy),
        "book_size": all(row["prime_power_count"] == l2["book_size"] for row in one_copy),
        "basis_size": all(row["basis_size"] == 17 and row["rank"] == 17 for row in one_copy),
        "no_nullspace": all(row["nullity"] == 0 for row in one_copy),
    }

    q400 = float(l2["sections"]["C1C2_window"]["Q400"])
    q1600 = float(l2["sections"]["C1C2_window"]["Q1600"])
    l2_charge = float(l2["assembly"]["total_ideal"])
    sampled_margin_1600 = abs(q1600) - l2_charge
    sampled_margin_ratio = l2_charge / abs(q1600)
    sampled_margin_400_ratio = l2_charge / abs(q400)

    result = {
        "record": 2059,
        "status": "OWNER-ALIGNED-L2-MARGIN-AUDIT",
        "consumer": "C1P2DirectSemiLocalGate -> orbitWindowSemiLocalGate -> SourceRH",
        "owner": l2["owner"],
        "rho": l2["rho"],
        "scale": l2["scale"],
        "support": l2["support"],
        "book_size": l2["book_size"],
        "owner_matches": owner_matches,
        "owner_match_all": all(owner_matches.values()),
        "q400": q400,
        "q1600": q1600,
        "l2_charge": l2_charge,
        "sampled_margin_1600": sampled_margin_1600,
        "sampled_margin_ratio_1600": sampled_margin_ratio,
        "sampled_margin_ratio_400": sampled_margin_400_ratio,
        "decision": (
            "L2-BUDGET-BELOW-SAMPLED-NEGATIVE-MARGIN"
            if all(owner_matches.values()) and sampled_margin_1600 > 0
            else "OWNER-MISMATCH-OR-L2-BUDGET-FAIL"
        ),
        "nonclaims": [
            "q400 and q1600 are inherited sampled/refinement readings, not full-line interval enclosures",
            "the L2 charge is not yet a model-to-real enclosure for the selected detector",
            "Gram, a_mat idealisation, and COVER obligations remain open",
            "no producer theorem or RH claim",
        ],
        "provenance": {
            "source_2037": os.fspath(SOURCE_2037.relative_to(ROOT)),
            "source_2058": os.fspath(SOURCE_2058.relative_to(ROOT)),
            "script": os.fspath(Path(__file__).relative_to(ROOT)),
        },
    }

    with OUTPUT.open("w", encoding="utf-8", newline="\n") as handle:
        json.dump(result, handle, indent=2)
        handle.write("\n")

    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
