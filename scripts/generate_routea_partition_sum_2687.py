"""Generate Lean's exact rational sum for the 2048-cell screen in record 2687."""

from __future__ import annotations

import hashlib
import json
import struct
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "results/2687_repaired_owner_2048_grid_screen.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteAWeightedPartitionSum2687.lean"
AUDIT = ROOT / "ConnesWeilRH/Dev/C1RouteAWeightedPartitionSum2687Audit.lean"
CELL_COUNT = 2048
CHUNK_SIZE = 32
SOURCE_PATHS = {
    "grid_screen": ROOT / "scripts/routea_repaired_owner_grid_screen_2684.py",
    "continuous_price_probe": ROOT / "scripts/routea_repaired_owner_continuous_box_price_2670.py",
    "cell_exporter": ROOT / "scripts/routea_repaired_owner_cell_price_certificate_2675.py",
    "interval_evaluator": ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py",
    "strip_owner": ROOT / "scripts/routea_corrected_strip_envelope_2303.py",
}


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def exact_binary64(bits: str) -> Fraction:
    value = struct.unpack(">d", struct.pack(">Q", int(bits, 16)))[0]
    return Fraction.from_float(value)


def main() -> None:
    artifact = json.loads(INPUT.read_text(encoding="utf-8"))
    cells = artifact["cells_data"]
    if artifact.get("cells") != CELL_COUNT or len(cells) != CELL_COUNT:
        raise ValueError("record 2687 must contain exactly 2048 cells")
    if [row[0] for row in cells] != list(range(CELL_COUNT)):
        raise ValueError("record 2687 cell indices are not ordered")
    if not artifact.get("below_knownError2109"):
        raise ValueError("record 2687 does not pass its recorded budget")
    if artifact.get("continuum_enclosure_proved") is not False:
        raise ValueError("record 2687 must remain labeled as a numerical screen")
    for key, path in SOURCE_PATHS.items():
        if sha256(path) != artifact["source_sha256"][key]:
            raise ValueError(f"record 2687 source hash changed: {key}")

    bits = [row[6] for row in cells]
    exact_total = sum((exact_binary64(value) for value in bits), Fraction(0))
    rounded_total = exact_binary64(artifact["total_upper_sum"]["bits"])
    if f"{rounded_total.numerator}/{rounded_total.denominator}" != \
            artifact["total_upper_sum"]["exact"]:
        raise ValueError("record 2687 rounded total bits and exact value disagree")
    if Fraction.from_float(float(exact_total)) != rounded_total:
        raise ValueError("record 2687 total is not the nearest-rounded exact cell sum")

    chunks = [bits[i:i + CHUNK_SIZE]
              for i in range(0, len(bits), CHUNK_SIZE)]
    if len(chunks) != 64 or any(len(chunk) != CHUNK_SIZE for chunk in chunks):
        raise ValueError("unexpected record 2687 chunk layout")

    lines = [
        "import ConnesWeilRH.Dev.C1RouteAWeightedCellPartition2684",
        "import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic",
        "",
        "set_option maxRecDepth 4096",
        "set_option exponentiation.threshold 1200",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
    ]
    for index, chunk in enumerate(chunks):
        start = index * CHUNK_SIZE
        stop = start + CHUNK_SIZE
        chunk_total = sum((exact_binary64(value) for value in chunk), Fraction(0))
        lines.extend([
            f"/-- Record 2687 cells {start} through {stop - 1},",
            "decoded and summed as exact rationals. -/",
            f"def record2687ChunkBits{index:03d} : List Nat :=",
            "  [" + ",\n   ".join(chunk) + "]",
            "",
            f"theorem record2687ChunkBits{index:03d}Length :",
            f"    (record2687ChunkBits{index:03d}).length = {CHUNK_SIZE} := by",
            "  decide",
            "",
            f"theorem record2687ChunkSum{index:03d} :",
            f"    ((record2687ChunkBits{index:03d}).map binary64Value2674).sum =",
            f"      ({chunk_total.numerator} : ℚ) / {chunk_total.denominator} := by",
            f"  norm_num [record2687ChunkBits{index:03d}, binary64Value2674,",
            "    binary64ExponentBits2674, binary64Significand2674,",
            "    binary64FractionBits2674, binary64Sign2674]",
            "",
        ])

    lines.extend([
        "/-- The 2048-cell finite price ledger, grouped into certified chunks. -/",
        "def record2687CellTotalBits : List Nat :=",
        "  " + " ++\n    ".join(
            f"record2687ChunkBits{i:03d}" for i in range(len(chunks))),
        "",
        "theorem record2687GridCellCount :",
        "    record2687CellTotalBits.length = 2048 := by",
        "  simp only [record2687CellTotalBits, List.length_append, " +
        ", ".join(f"record2687ChunkBits{i:03d}Length"
                   for i in range(len(chunks))) + "]",
        "",
        "theorem record2687GridChargeExact :",
        "    (record2687CellTotalBits.map binary64Value2674).sum =",
        f"      ({exact_total.numerator} : ℚ) / {exact_total.denominator} := by",
        "  simp only [record2687CellTotalBits, List.map_append,",
        "    List.sum_append, " + ", ".join(
            f"record2687ChunkSum{i:03d}" for i in range(len(chunks))) + "]",
        "  norm_num",
        "",
        "theorem record2687GridChargeBelowKnownError :",
        "    (((record2687CellTotalBits.map binary64Value2674).sum : ℚ) : ℝ) <",
        "      ConnesWeilRH.Source.C1RouteAItem5Arithmetic.knownError2109 := by",
        "  rw [record2687GridChargeExact]",
        "  norm_num [ConnesWeilRH.Source.C1RouteAItem5Arithmetic.knownError2109]",
        "",
        "end ConnesWeilRH.Dev",
        "",
    ])
    OUTPUT.write_text("\n".join(lines), encoding="utf-8")
    AUDIT.write_text("\n".join([
        "import ConnesWeilRH.Dev.C1RouteAWeightedPartitionSum2687",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
        "#print axioms record2687GridChargeExact",
        "#print axioms record2687GridChargeBelowKnownError",
        "",
        "end ConnesWeilRH.Dev",
        "",
    ]), encoding="utf-8")
    print(f"cells={len(bits)} chunks={len(chunks)} chunk_size={CHUNK_SIZE}")
    print(f"exact_sum={exact_total.numerator}/{exact_total.denominator}")
    print(f"lean={OUTPUT.relative_to(ROOT)}")
    print(f"audit={AUDIT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
