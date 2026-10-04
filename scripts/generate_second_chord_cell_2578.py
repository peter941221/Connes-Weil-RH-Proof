"""Generate the first correction second-chord certificate for cell 2702."""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import re

import generate_node_exp_owner_2577 as owner
from generate_second_chord_cell_2575 import DEV, CAPTURE, STEP, fourth_price, real
from generate_second_chord_cell_2575 import point_names as old_names
from generate_second_chord_cell_2575 import side_name
from validate_adaptive_nodes_2542 import scalar_def
from format_lean_source_2553 import wrap_source

ROOT = owner.ROOT
CELL = 2702
RECORD = 2578
ASSEMBLY = "C1RouteACorrectionSecondChordCell2702_2578"


def new_point(index, sign):
    return owner.names(index, sign, 2)


def endpoint_upper(index, sign):
    return scalar_def((DEV / (new_point(index, sign)["bounds"] + ".lean")).read_text(),
                      new_point(index, sign)["signed"] + "Upper2577")


def correction_fourth(sign):
    side = side_name(sign)
    source = (DEV / f"C1RouteABatchC02702{side}Fourth2558.lean").read_text()
    total = Q(0)
    rows = json.loads((ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    for index, row in enumerate(rows):
        box = row["ideal_correction_coefficient"]
        center = [(Q(box[part]["lower_exact"]) + Q(box[part]["upper_exact"])) / 2
                  for part in ("real", "imag")]
        upper = scalar_def(source, f"batchC02702{side}FourthP{index:03d}Upper2558")
        total += (sum(abs(value) for value in center) + Q(1, 10**28)) * upper
    return total


def transform_assembly():
    source = (DEV / "C1RouteACorrectionSecondChordCell2700_2575.lean").read_text()
    for sign in (-1, 1):
        side = side_name(sign)
        for old_index, new_index in ((2700, 2702), (2701, 2703)):
            old = old_names(old_index, sign)
            new = new_point(new_index, sign)
            source = source.replace(old["prefix"], new["prefix"])
            source = source.replace(old["point"], new["point"])
            source = source.replace(old["signed"], new["signed"])
            source = source.replace(old["deriv"], new["module"])
            source = source.replace(old["bounds"], new["bounds"])
        source = source.replace(f"batchC02700{side}", f"batchC02702{side}")
        source = source.replace(f"kernelN02700{side}", f"batchN02702{side}")
        source = source.replace(f"kernelN02701{side}", f"batchN02703{side}")
    source = source.replace("C1RouteACorrectionSecondChordCell2700_2575", ASSEMBLY)
    source = source.replace("2575", str(RECORD))
    source = source.replace("C1RouteABatchC02700", "C1RouteABatchC02702")
    source = source.replace("C1RouteABatchC02702MinusFourth2558", "C1RouteABatchC02702MinusFourth2558")
    source = source.replace("C1RouteABatchC02702PlusFourth2558", "C1RouteABatchC02702PlusFourth2558")
    source = source.replace("corrSecondChordMinus2578", "nodeSecondChordMinus2578")
    source = source.replace("corrSecondChordPlus2578", "nodeSecondChordPlus2578")
    for sign in (-1, 1):
        for index in (2702, 2703):
            prefix = new_point(index, sign)["prefix"]
            source = source.replace(prefix + "PointPosition2578", prefix + "PointPosition2577")
            source = source.replace(new_point(index, sign)["signed"] + "2578",
                                    new_point(index, sign)["signed"] + "2577")
    source = source.replace("Position2555", "Position2558")
    source = re.sub(r"(nodeJet2N0270[23](?:Minus|Plus)\w*)2578\b", r"\g<1>2577", source)
    source = source.replace("import ConnesWeilRH.Dev.C1RouteABatchC02702MinusFourth2558",
                            "import ConnesWeilRH.Dev.C1RouteABatchC02702MinusFourth2558\nimport ConnesWeilRH.Dev.C1RouteANeighborRight2557")
    source = source.replace("batchN02702PlusPosition2558", "neighborRightPosition2557")
    source = source.replace("-stripRadius2303 + 2700 *", "-stripRadius2303 + 2702 *")
    source = source.replace("-stripRadius2303 + 2701 *", "-stripRadius2303 + 2703 *")
    for sign in (-1, 1):
        side = side_name(sign)
        fourth = correction_fourth(sign)
        prefix = f"nodeSecondChord{side}{RECORD}"
        def replace_definition(text, name, value):
            marker = f"noncomputable def {name} : ℝ :="
            start = text.index(marker)
            end = text.index("\n\n", start)
            return text[:start] + marker + " " + value + text[end:]
        source = replace_definition(source, prefix + "FourthUpper", real(fourth))
        left = endpoint_upper(2702, sign)
        right = endpoint_upper(2703, sign)
        total = STEP / 2 * (left + right) + fourth * STEP**3 / 12
        source = replace_definition(source, prefix + "Upper", real(total))
    source = source.replace("C1RouteACorrSecondN02702", "C1RouteANodeJet2N02702")
    source = source.replace("C1RouteACorrSecondN02703", "C1RouteANodeJet2N02703")
    source = wrap_source(source)
    return source


def main():
    source = transform_assembly()
    path = DEV / (ASSEMBLY + ".lean")
    path.write_text(source, encoding="utf-8", newline="\n")
    audit = ["import ConnesWeilRH.Dev." + ASSEMBLY, ""]
    names = []
    for sign in (-1, 1):
        side = side_name(sign)
        for index in (2702, 2703):
            point = new_point(index, sign)["point"]
            names += [point + f"P{i:03d}DerivativeError2577" for i in range(30)]
            names += [point + "Grid2577"]
            signed = new_point(index, sign)["signed"]
            names += [signed + suffix + "2577" for suffix in ("ExpError", "Sum_eq", "Charge", "Upper_le")]
            names += [new_point(index, sign)["prefix"] + "Physical2577"]
        names += [f"nodeSecondChord{side}2578" + suffix for suffix in ("Fourth_bound", "Fourth_eq", "Summand_le", "ProductionSummand_le", "Integral_le")]
    audit += ["#print axioms ConnesWeilRH.Dev." + name for name in names]
    (DEV / (ASSEMBLY + "Audit.lean")).write_text("\n".join(audit) + "\n", encoding="utf-8", newline="\n")
    print("SECOND_CHORD_2578_GENERATED", len(names), flush=True)


if __name__ == "__main__":
    main()
