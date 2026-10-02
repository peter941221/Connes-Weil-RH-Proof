"""Emit the exact-rational payload for the 2478 cell-bound artifact.

This generator deliberately emits data only.  It does not emit a theorem that
the MPFR values bound the analytic derivative; that obligation remains an
explicit hypothesis at the 2475 consumer.  The source artifact is checked for
the exact binary64 numerator/denominator payload before any Lean literal is
copied.
"""

import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ARTIFACT = ROOT / "results/2478_owner_local_curvature_mpfr.json"
OUT = ROOT / "ConnesWeilRH/Dev/C1RouteAOwnerCurvatureTable2481.lean"


def q_literal(payload):
    numerator = int(payload["numerator"])
    denominator = int(payload["denominator"])
    if denominator <= 0 or numerator < 0:
        raise ValueError("cell endpoint is not a nonnegative rational")
    return f"({numerator} : ℚ) / {denominator}"


def emit_chunk(name, payloads):
    lines = [f"def {name} (index : Fin 40) : ℚ :="]
    for index, payload in enumerate(payloads[:-1]):
        lines.append(f"if index.val = {index} then {q_literal(payload)} else")
    lines.append(q_literal(payloads[-1]))
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
    rows = artifact["rows"]
    if artifact["record"] != 2478 or any(row["effective_cells"] != 640 for row in rows):
        raise ValueError("unexpected 2478 artifact shape")
    if [row["sigma"] for row in rows] != [-0.5, 0.5]:
        raise ValueError("unexpected sigma ordering")
    for row in rows:
        payloads = row["cell_upper_bounds"]
        if len(payloads) != 640:
            raise ValueError("unexpected cell count")
        for payload in payloads:
            value = float.fromhex(payload["hex"])
            numerator, denominator = value.as_integer_ratio()
            if payload["numerator"] != str(numerator) or payload["denominator"] != str(denominator):
                raise ValueError("binary64 payload does not round-trip")

    source_hash = hashlib.sha256(artifact_bytes).hexdigest()
    lines = [
        "import ConnesWeilRH.Dev.C1RouteAOwnerL1CoefficientBound2479",
        "",
        "/-!",
        "# 2478 actual-owner curvature cell data",
        "",
        "This file is generated from `results/2478_owner_local_curvature_mpfr.json`.",
        f"Artifact SHA256: `{source_hash}`.",
        "",
        "The two rows correspond to sigma = -1/2 and +1/2.  Each entry is only",
        "an exact rational rendering of the recorded binary64 RNDU endpoint.",
        "This module is data, not a proof of the analytic cell inequality; the",
        "cell inequality remains an explicit premise at the 2475 consumer.",
        "-/",
        "",
        "namespace ConnesWeilRH.Dev",
        "",
        "set_option linter.style.longLine false",
        "set_option maxRecDepth 100000",
        "",
        f"def ownerCurvatureArtifactSha256_2481 : String := \"{source_hash}\"",
        "",
    ]
    lines.append(emit_row("ownerCurvatureMinusQ_2481", rows[0]["cell_upper_bounds"]))
    lines.append("")
    lines.append(emit_row("ownerCurvaturePlusQ_2481", rows[1]["cell_upper_bounds"]))
    lines += [
        "",
        "def ownerCurvatureQ_2481 (side : Fin 2) (index : Fin 640) : ℚ :=",
        "  if side.val = 0 then ownerCurvatureMinusQ_2481 index else",
        "  ownerCurvaturePlusQ_2481 index",
        "",
        "end ConnesWeilRH.Dev",
        "",
    ]
    OUT.write_text("\n".join(lines), encoding="utf-8", newline="\n")
    print({"record": 2481, "artifact_sha256": source_hash,
           "rows": len(rows), "cells_per_row": 640,
           "out": str(OUT)})


if __name__ == "__main__":
    main()
