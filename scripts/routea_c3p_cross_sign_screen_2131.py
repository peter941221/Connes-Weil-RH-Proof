#!/usr/bin/env python3
"""2131: screen whether opposite diagonal signs force the C3' cross sign."""

import json
from pathlib import Path

ARTIFACT = Path("results/1798_twospan_cross_gate.json")
OUTPUT = Path("results/2131_routea_c3p_cross_sign_screen.json")


def ordered_opposite(row, first, second):
    return (
        row[f"arch_{first}"] <= 0.0
        and row[f"arch_{second}"] >= 0.0
        and row[f"prime_{first}"] <= 0.0
        and row[f"prime_{second}"] >= 0.0
    )


def main():
    source = json.loads(ARTIFACT.read_text())
    rows = []
    counterexamples = []
    for row in source["rows"]:
        arch_cross = row["arch_AB"]
        prime_cross = row["prime_AB"]
        cross_product = arch_cross * prime_cross
        signs_uv = ordered_opposite(row, "AA", "BB")
        signs_vu = ordered_opposite(row, "BB", "AA")
        opposite = signs_uv or signs_vu
        result = {
            "pair": row["pair"],
            "opposite_diagonal_signs": opposite,
            "orientation": "u,v" if signs_uv else ("v,u" if signs_vu else None),
            "arch_cross": arch_cross,
            "prime_cross": prime_cross,
            "cross_product": cross_product,
            "directed_cross_nonneg": cross_product >= 0.0,
        }
        rows.append(result)
        if opposite and cross_product < 0.0:
            counterexamples.append(result)

    output = {
        "record": 2131,
        "status": "SCOPED-NO-GO-FOR-DIAGONAL-SIGNS-IMPLYING-CROSS-SIGN",
        "source_artifact": str(ARTIFACT).replace("\\", "/"),
        "rows": rows,
        "counterexample_count": len(counterexamples),
        "counterexamples": counterexamples,
        "interpretation": (
            "Opposite diagonal signs do not imply the directed cross-product "
            "condition. This screens an algebraic shortcut only; it is not a "
            "no-go for the actual zeta owner or for a separately proved cross "
            "certificate."
        ),
    }
    OUTPUT.write_text(json.dumps(output, indent=1) + "\n")
    print(json.dumps(output, indent=2))


if __name__ == "__main__":
    main()
