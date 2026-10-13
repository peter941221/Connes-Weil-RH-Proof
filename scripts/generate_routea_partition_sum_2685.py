"""Generate Lean's exact rational sum of record-2684 cell charges.

The input is the committed binary64 bit-pattern artifact.  Lean decodes every
cell total through the existing IEEE-754-to-rational definition, proves 256
chunk sums of 32 cells, then proves the 8192-cell total and budget check.
"""

from __future__ import annotations

import hashlib
import json
import struct
from fractions import Fraction
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
INPUT = ROOT / "results/2684_repaired_owner_8192_cell_grid_screen.json"
OUTPUT = ROOT / "ConnesWeilRH/Dev/C1RouteAWeightedPartitionSum2685.lean"
AUDIT = ROOT / "ConnesWeilRH/Dev/C1RouteAWeightedPartitionSum2685Audit.lean"
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
    if len(cells) != 8192 or [row[0] for row in cells] != list(range(8192)):
        raise ValueError("record 2684 must contain the ordered 8192-cell grid")
    if not artifact["below_knownError2109"]:
        raise ValueError("record 2684 does not pass its recorded budget")
    for key, path in SOURCE_PATHS.items():
        if sha256(path) != artifact["source_sha256"][key]:
            raise ValueError(f"record 2684 source hash changed: {key}")

    bits = [row[6] for row in cells]
    exact_total = sum((exact_binary64(value) for value in bits), Fraction(0))
    reported_total = exact_binary64(artifact["total_upper_sum"]["bits"])
    if f"{reported_total.numerator}/{reported_total.denominator}" != \
            artifact["total_upper_sum"]["exact"]:
        raise ValueError("record 2684 total's bit pattern and exact value disagree")
    if Fraction.from_float(float(exact_total)) != reported_total:
        raise ValueError("record 2684 total does not match the rounded exact cell sum")
    chunks = [bits[i:i + CHUNK_SIZE]
              for i in range(0, len(bits), CHUNK_SIZE)]
    if len(chunks) != 256 or any(len(chunk) != CHUNK_SIZE for chunk in chunks):
        raise ValueError("unexpected record 2684 chunk layout")

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

    for chunk_index, chunk in enumerate(chunks):
        start = chunk_index * CHUNK_SIZE
        stop = start + CHUNK_SIZE
        literals = ",\n   ".join(chunk)
        chunk_total = sum((exact_binary64(value) for value in chunk), Fraction(0))
        lines.extend([
            f"/-- Record 2684 cells {start} through {stop - 1},",
            "decoded and summed as exact rationals. -/",
            f"def record2684ChunkBits{chunk_index:03d}2685 : List Nat :=",
            "  [" + literals + "]",
            "",
            f"theorem record2684ChunkBits{chunk_index:03d}Length2685 :",
            f"    (record2684ChunkBits{chunk_index:03d}2685).length = {CHUNK_SIZE} := by",
            "  decide",
            "",
            f"theorem record2684ChunkSum{chunk_index:03d}2685 :",
            f"    ((record2684ChunkBits{chunk_index:03d}2685).map binary64Value2674).sum =",
            f"      ({chunk_total.numerator} : ℚ) / {chunk_total.denominator} := by",
            "  norm_num [record2684ChunkBits%03d2685, binary64Value2674, " % chunk_index +
            "binary64ExponentBits2674, binary64Significand2674, " +
            "binary64FractionBits2674, binary64Sign2674]",
            "",
        ])

    lines.extend([
        f"/-- The complete bit-pattern ledger, grouped into the {len(chunks)} certified",
        "chunks below so its exact sum can be checked incrementally. -/",
        "def record2684CellTotalBits2685 : List Nat :=",
        "  " + " ++\n    ".join(
            f"record2684ChunkBits{i:03d}2685" for i in range(len(chunks))),
        "",
    ])

    lines.extend([
        "/-- The imported ledger contains exactly the 8192 partition cells. -/",
        "theorem record2684GridCellCount2685 :",
        "    record2684CellTotalBits2685.length = 8192 := by",
        "  simp only [record2684CellTotalBits2685, List.length_append, " +
        ", ".join(f"record2684ChunkBits{i:03d}Length2685"
                   for i in range(len(chunks))) + "]",
        "",
        "/-- The full finite-grid charge, reconstructed solely from the cell",
        "bit patterns. -/",
        "theorem record2684GridChargeExact2685 :",
        "    (record2684CellTotalBits2685.map binary64Value2674).sum =",
        f"      ({exact_total.numerator} : ℚ) / {exact_total.denominator} := by",
        "  simp only [record2684CellTotalBits2685, List.map_append,",
        "    List.sum_append, " + ", ".join(
            f"record2684ChunkSum{i:03d}2685" for i in range(len(chunks))) + "]",
        "  norm_num",
        "",
        "/-- The displayed binary64 total in record 2684 rounds upward for this",
        "input, so it is a valid readable upper bound on the exact rational sum. -/",
        "theorem record2684RoundedTotalUpper2685 :",
        "    (record2684CellTotalBits2685.map binary64Value2674).sum ≤",
        f"      binary64Value2674 {artifact['total_upper_sum']['bits']} := by",
        "  rw [record2684GridChargeExact2685]",
        "  norm_num [binary64Value2674, binary64ExponentBits2674,",
        "    binary64Significand2674, binary64FractionBits2674, binary64Sign2674]",
        "",
        "/-- The exact grid charge is below record 2109's known-error budget.",
        "This certifies the finite rational ledger only; cell containment and",
        "the live-owner identity remain explicit premises of the integral route. -/",
        "theorem record2684GridChargeBelowKnownError2685 :",
        "    (((record2684CellTotalBits2685.map binary64Value2674).sum : ℚ) : ℝ) <",
        "      ConnesWeilRH.Source.C1RouteAItem5Arithmetic.knownError2109 := by",
        "  rw [record2684GridChargeExact2685]",
        "  norm_num [ConnesWeilRH.Source.C1RouteAItem5Arithmetic.knownError2109]",
        "",
        "end ConnesWeilRH.Dev",
        "",
    ])
    OUTPUT.write_text("\n".join(lines), encoding="utf-8")

    AUDIT.write_text("\n".join([
        "import ConnesWeilRH.Dev.C1RouteAWeightedPartitionSum2685",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
        "#print axioms record2684GridChargeExact2685",
        "#print axioms record2684RoundedTotalUpper2685",
        "#print axioms record2684GridChargeBelowKnownError2685",
        "",
        "end ConnesWeilRH.Dev",
        "",
    ]), encoding="utf-8")

    print(f"cells={len(bits)} chunks={len(chunks)} chunk_size={CHUNK_SIZE}")
    print(f"lean={OUTPUT.relative_to(ROOT)}")
    print(f"audit={AUDIT.relative_to(ROOT)}")


if __name__ == "__main__":
    main()
