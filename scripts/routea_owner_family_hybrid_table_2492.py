"""Generate exact rational payloads from the 2491 directed-MPFR artifact.

The output is data only.  It reconstructs each stored binary64 RNDU endpoint
as an exact rational and does not prove that the endpoint bounds the analytic
family expression; that remains an explicit external obligation.
"""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2491_owner_family_hybrid_mpfr.json"
OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerFamilyHybridTable2492.lean"


def payload_literal(payload):
    numerator = int(payload["numerator"])
    denominator = int(payload["denominator"])
    value = float.fromhex(payload["hex"])
    if denominator <= 0 or numerator < 0 or value.as_integer_ratio() != (numerator, denominator):
        raise ValueError("invalid binary64 rational payload")
    return f"({numerator} : ℚ) / {denominator}"


def emit_chunk(name, payloads):
    lines = [f"def {name} (index : Fin 40) : ℚ :="]
    for index, payload in enumerate(payloads[:-1]):
        lines.append(f"if index.val = {index} then {payload_literal(payload)} else")
    lines.append(payload_literal(payloads[-1]))
    return "\n".join(lines)


def emit_row(name, payloads):
    lines = []
    chunks = []
    for chunk_index in range(16):
        chunk_name = f"{name}Chunk{chunk_index}"
        chunks.append(chunk_name)
        lines.append(emit_chunk(chunk_name, payloads[chunk_index * 40:(chunk_index + 1) * 40]))
        lines.append("")
    lines.append(f"def {name} (index : Fin 640) : ℚ :=")
    lines.append("  match index.val / 40 with")
    for chunk_index, chunk_name in enumerate(chunks[:-1]):
        lines.append(
            f"  | {chunk_index} => {chunk_name}"
            f" ⟨index.val % 40, Nat.mod_lt _ (by decide)⟩")
    lines.append(
        f"  | _ => {chunks[-1]}"
        f" ⟨index.val % 40, Nat.mod_lt _ (by decide)⟩")
    return "\n".join(lines)


def main():
    artifact_bytes = ARTIFACT.read_bytes()
    artifact = json.loads(artifact_bytes)
    if artifact["record"] != 2491 or artifact["grid"]["effective_cells"] != 640:
        raise ValueError("unexpected 2491 artifact shape")
    rows = artifact["rows"]
    if [row["sigma"] for row in rows] != [-0.5, 0.5]:
        raise ValueError("unexpected sigma ordering")
    for row in rows:
        for field in ("baseline_cell_upper_bounds", "hybrid_cell_upper_bounds"):
            if len(row[field]) != 640:
                raise ValueError("unexpected cell payload length")
            for payload in row[field]:
                payload_literal(payload)
    source_hash = hashlib.sha256(artifact_bytes).hexdigest()
    lines = [
        "import ConnesWeilRH.Dev.C1RouteAOwnerWeightedFamily2488",
        "",
        "/-!",
        "# 2491 directed-MPFR family-hybrid price payloads",
        "",
        "This file is generated from `results/2491_owner_family_hybrid_mpfr.json`.",
        f"Artifact SHA256: `{source_hash}`.",
        "",
        "Entries are exact rational reconstructions of stored binary64 RNDU",
        "endpoints.  They are data, not a proof of the analytic enclosure;",
        "the directed family bound remains an explicit external premise.",
        "-/",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
        "set_option linter.style.longLine false",
        "set_option maxRecDepth 100000",
        "",
        f"def ownerFamilyHybridArtifactSha256_2492 : String := \"{source_hash}\"",
        "",
    ]
    lines.append(emit_row("ownerFamilyHybridBaselineMinusQ_2492", rows[0]["baseline_cell_upper_bounds"]))
    lines.append("")
    lines.append(emit_row("ownerFamilyHybridBaselinePlusQ_2492", rows[1]["baseline_cell_upper_bounds"]))
    lines.append("")
    lines.append(emit_row("ownerFamilyHybridMinusQ_2492", rows[0]["hybrid_cell_upper_bounds"]))
    lines.append("")
    lines.append(emit_row("ownerFamilyHybridPlusQ_2492", rows[1]["hybrid_cell_upper_bounds"]))
    lines += [
        "",
        "def ownerFamilyHybridBaselineQ_2492 (side : Fin 2) (index : Fin 640) : ℚ :=",
        "  if side.val = 0 then ownerFamilyHybridBaselineMinusQ_2492 index else",
        "  ownerFamilyHybridBaselinePlusQ_2492 index",
        "",
        "def ownerFamilyHybridQ_2492 (side : Fin 2) (index : Fin 640) : ℚ :=",
        "  if side.val = 0 then ownerFamilyHybridMinusQ_2492 index else",
        "  ownerFamilyHybridPlusQ_2492 index",
        "",
        "end ConnesWeilRH.Dev",
        "",
    ]
    OUT.write_text("\n".join(lines), encoding="utf-8", newline="\n")
    print({"record": 2492, "artifact_sha256": source_hash,
           "rows": 2, "cells_per_row": 640, "out": str(OUT)})


if __name__ == "__main__":
    main()
