"""Audit the diagonal-owner inputs before generating record-2628 panels.

This is a pricing and input-consistency gate, not an interval certificate.
It checks the exact phase cancellation and support-radius replay for all
30 diagonal owners, then prices the existing 180-panel enclosure shape
against each diagonal real interval from the 2351 witness.
"""

from fractions import Fraction
import argparse
import hashlib
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

import generate_moment_panel_batch_2622 as panel_batch


def load_inputs():
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text()
    )["owner_capture"]
    witness = json.loads(
        (ROOT / "results/2351_moment_matrix_witness.json").read_text()
    )
    return capture, witness


def audit_diagonal(index, capture, witness):
    width = Fraction(float.fromhex(capture["families_hex"][index][0]))
    modulation = Fraction(float.fromhex(capture["families_hex"][index][1]))
    node_real, node_imag = (
        Fraction(float.fromhex(value))
        for value in capture["nodes_hex"][index]
    )
    radius = width * width
    expected_radius = Fraction(witness["support_radii_exact"][index])
    phase_cancelled = node_imag + modulation == 0
    radius_replayed = radius == expected_radius
    owner = {"radius": radius, "beta": node_real * radius}
    total_charge = sum(
        (panel_batch.panel_data(panel, owner)["integral_charge"]
         for panel in range(180)),
        Fraction(0),
    )
    real_width = (
        Fraction(witness["matrix"][index][index]["real"]["upper_exact"])
        - Fraction(witness["matrix"][index][index]["real"]["lower_exact"])
    )
    return {
        "index": index,
        "phase_cancelled": phase_cancelled,
        "radius_replayed": radius_replayed,
        "charge_exact": str(total_charge),
        "real_width_exact": str(real_width),
        "charge_to_width": float(total_charge / real_width),
    }


def diagonal_payload(index, capture, witness):
    width = Fraction(float.fromhex(capture["families_hex"][index][0]))
    node_real, _ = (
        Fraction(float.fromhex(value))
        for value in capture["nodes_hex"][index]
    )
    radius = width * width
    owner = {"radius": radius, "beta": node_real * radius}
    panels = []
    for panel in range(180):
        data = panel_batch.panel_data(panel, owner)
        panels.append({
            key: ([str(item) for item in value]
                  if isinstance(value, list) else str(value))
            for key, value in data.items()
        })
    return {"owner_index": index, "panels": panels}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--json", action="store_true")
    parser.add_argument("--payload", action="store_true")
    arguments = parser.parse_args()
    capture, witness = load_inputs()
    rows = [audit_diagonal(index, capture, witness) for index in range(30)]
    if not all(row["phase_cancelled"] and row["radius_replayed"] for row in rows):
        raise SystemExit("diagonal phase or radius replay failed")
    max_ratio = max(row["charge_to_width"] for row in rows)
    if max_ratio >= 1 / 100:
        raise SystemExit(f"diagonal charge margin failed: max ratio={max_ratio:.6e}")
    if arguments.payload:
        payload = {
            "record": 2628,
            "owner_count": 30,
            "panel_count": 180,
            "capture_sha256": hashlib.sha256(
                (ROOT / "results/2275_gap_owner_audit.json").read_bytes()
            ).hexdigest(),
            "witness_sha256": hashlib.sha256(
                (ROOT / "results/2351_moment_matrix_witness.json").read_bytes()
            ).hexdigest(),
            "generator_sha256": hashlib.sha256(
                (ROOT / "scripts/generate_moment_panel_batch_2622.py").read_bytes()
            ).hexdigest(),
            "pricing_rows": rows,
            "owners": [diagonal_payload(index, capture, witness)
                       for index in range(30)],
        }
        output_path = ROOT / "results/2628_diagonal_panel_payload.json"
        output_path.write_text(json.dumps(payload, indent=2) + "\n")
        print(output_path)
        return
    if arguments.json:
        print(json.dumps({"rows": rows, "max_charge_to_width": max_ratio}, indent=2))
        return
    print("index phase_cancelled radius_replayed charge/real_width")
    for row in rows:
        print(
            f"{row['index']:02d}    {str(row['phase_cancelled']):5s}"
            f"           {str(row['radius_replayed']):5s}"
            f"          {row['charge_to_width']:.6e}"
        )
    print(f"max_charge_to_width={max_ratio:.6e}")


if __name__ == "__main__":
    main()
