"""Generate the corrected exact-rational table from the 2495 replay."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2495_owner_family_hybrid_mpfr_exact.json"
OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerFamilyHybridTable2496.lean"


def lit(payload):
    numerator, denominator = int(payload["numerator"]), int(payload["denominator"])
    value = float.fromhex(payload["hex"])
    if denominator <= 0 or numerator < 0 or value.as_integer_ratio() != (numerator, denominator):
        raise ValueError("invalid binary64 payload")
    return f"({numerator} : ℚ) / {denominator}"


def row(name, values):
    lines, chunks = [], []
    for c in range(16):
        chunk = f"{name}Chunk{c}"
        chunks.append(chunk)
        part = values[c * 40:(c + 1) * 40]
        lines.append(f"def {chunk} (index : Fin 40) : ℚ :=")
        for i, value in enumerate(part[:-1]):
            lines.append(f"if index.val = {i} then {lit(value)} else")
        lines.append(lit(part[-1]))
        lines.append("")
    lines.append(f"def {name} (index : Fin 640) : ℚ :=")
    lines.append("  match index.val / 40 with")
    for c, chunk in enumerate(chunks[:-1]):
        lines.append(f"  | {c} => {chunk} ⟨index.val % 40, Nat.mod_lt _ (by decide)⟩")
    lines.append(f"  | _ => {chunks[-1]} ⟨index.val % 40, Nat.mod_lt _ (by decide)⟩")
    return "\n".join(lines)


def main():
    raw = ARTIFACT.read_bytes()
    artifact = json.loads(raw)
    if artifact["record"] != 2495 or artifact["grid"]["effective_cells"] != 640:
        raise ValueError("unexpected 2495 shape")
    rows = artifact["rows"]
    for item in rows:
        for field in ("baseline_cell_upper_bounds", "hybrid_cell_upper_bounds"):
            if len(item[field]) != 640:
                raise ValueError("unexpected cell count")
            for payload in item[field]:
                lit(payload)
    sha = hashlib.sha256(raw).hexdigest()
    text = [
        "import ConnesWeilRH.Dev.C1RouteAOwnerWeightedFamily2488", "",
        "/-! Corrected 2495 exact-input directed-MPFR payloads.",
        f"Artifact SHA256: `{sha}`.",
        "Data only; the analytic enclosure remains an explicit premise. -/", "",
        "namespace ConnesWeilRH.Dev", "", "set_option linter.style.longLine false",
        "set_option maxRecDepth 100000", "",
        f'def ownerFamilyHybridArtifactSha256_2496 : String := "{sha}"', "",
    ]
    text += [row("ownerFamilyHybridBaselineMinusQ_2496", rows[0]["baseline_cell_upper_bounds"]), ""]
    text += [row("ownerFamilyHybridBaselinePlusQ_2496", rows[1]["baseline_cell_upper_bounds"]), ""]
    text += [row("ownerFamilyHybridMinusQ_2496", rows[0]["hybrid_cell_upper_bounds"]), ""]
    text += [row("ownerFamilyHybridPlusQ_2496", rows[1]["hybrid_cell_upper_bounds"]), ""]
    text += [
        "def ownerFamilyHybridBaselineQ_2496 (side : Fin 2) (index : Fin 640) : ℚ :=",
        "  if side.val = 0 then ownerFamilyHybridBaselineMinusQ_2496 index else",
        "  ownerFamilyHybridBaselinePlusQ_2496 index", "",
        "def ownerFamilyHybridQ_2496 (side : Fin 2) (index : Fin 640) : ℚ :=",
        "  if side.val = 0 then ownerFamilyHybridMinusQ_2496 index else",
        "  ownerFamilyHybridPlusQ_2496 index", "", "end ConnesWeilRH.Dev", "",
    ]
    OUT.write_text("\n".join(text), encoding="utf-8", newline="\n")
    print({"record": 2496, "artifact_sha256": sha, "cells_per_row": 640})


if __name__ == "__main__":
    main()
