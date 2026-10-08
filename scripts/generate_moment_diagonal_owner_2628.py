"""Generate a sharded record-2628 diagonal-owner panel smoke.

The existing 2622 generator is intentionally owner-0-specific. This wrapper
reuses its exact rational panel construction, then namespaces the generated
Lean symbols and module names for one diagonal owner without changing the
committed owner-0 path.
"""

from fractions import Fraction
import argparse
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH/Dev"
sys.path.insert(0, str(ROOT / "scripts"))

import generate_moment_panel_batch_2622 as panel_batch
import generate_moment_scalar_certificate_2620 as scalar_certificate


def owner_data(index):
    capture = json.loads(
        (ROOT / "results/2275_gap_owner_audit.json").read_text()
    )["owner_capture"]
    witness = json.loads(
        (ROOT / "results/2351_moment_matrix_witness.json").read_text()
    )
    width = Fraction(float.fromhex(capture["families_hex"][index][0]))
    node_real, node_imag = (
        Fraction(float.fromhex(value))
        for value in capture["nodes_hex"][index]
    )
    modulation = Fraction(float.fromhex(capture["families_hex"][index][1]))
    if node_imag + modulation != 0:
        raise ValueError(f"owner {index}: diagonal phase does not cancel")
    radius = width * width
    if radius != Fraction(witness["support_radii_exact"][index]):
        raise ValueError(f"owner {index}: support radius replay failed")
    center = Fraction(9, 200)
    half_width = Fraction(1, 200)
    cut = Fraction(9, 10)
    beta = node_real * radius
    phase = -30 / (1 - center ** 2) + beta * center
    growth = 2 * (abs(beta) + 60 * (abs(center) + half_width) /
                  (1 - (abs(center) + half_width) ** 2) ** 2) * half_width
    edge = -30 / (1 - cut ** 2) + abs(beta)
    return {
        "radius": radius,
        "beta": beta,
        "phase": phase,
        "growth": growth,
        "edge": edge,
        "index": index,
    }


def rename_owner_symbols(source, owner_index):
    suffix = f"K{owner_index:02d}"
    replacements = [
        ("C1RouteAMomentPanelScalars2622Panel", f"C1RouteAMomentPanelScalars2622{suffix}Panel"),
        ("C1RouteAMomentPanelTable2622Panel", f"C1RouteAMomentPanelTable2622{suffix}Panel"),
        ("C1RouteAMomentActualPanel2622Panel", f"C1RouteAMomentActualPanel2622{suffix}Panel"),
        ("C1RouteAMomentPanelBatchAudit2622", f"C1RouteAMomentPanelBatchAudit2622{suffix}"),
        ("C1RouteAMomentScalarOwner2620", f"C1RouteAMomentScalarOwner2620{suffix}"),
        ("2622P", f"2622{suffix}P"),
        ("momentPanelPhase2620", f"momentPanelPhase2620{suffix}"),
        ("momentPanelGrowth2620", f"momentPanelGrowth2620{suffix}"),
        ("momentEdgeArgument2620", f"momentEdgeArgument2620{suffix}"),
        ("momentRadius2620", f"momentRadius2620{suffix}"),
        ("momentBeta2620", f"momentBeta2620{suffix}"),
        ("momentPanelPhase_owner2620", f"momentPanelPhase_owner2620{suffix}"),
        ("momentPanelGrowth_owner2620", f"momentPanelGrowth_owner2620{suffix}"),
        ("momentEdgeArgument_owner2620", f"momentEdgeArgument_owner2620{suffix}"),
        ("momentRadius_owner2620", f"momentRadius_owner2620{suffix}"),
        ("momentBeta_owner2620", f"momentBeta_owner2620{suffix}"),
        ("actualMomentPanel", f"actualMomentPanel{suffix}"),
        ("storedWidth_pos 0", f"storedWidth_pos {owner_index}"),
        ("storedWidth 0", f"storedWidth {owner_index}"),
        ("capturedNodes2584 0", f"capturedNodes2584 {owner_index}"),
    ]
    for old, new in replacements:
        source = source.replace(old, new)
    if owner_index == 4:
        source = source.replace(
            "norm_num [",
            "norm_num [Matrix.cons_val_four, Matrix.cons_val_zero, "
        )
    return source


def generate(owner_index, panels, write):
    owner = owner_data(owner_index)
    sources = {}
    for panel in panels:
        data = panel_batch.panel_data(panel, owner)
        generated = panel_batch.panel_sources(data)
        for filename, source in generated.items():
            sources[rename_owner_symbols(source, owner_index)] = filename

    owner_source = rename_owner_symbols(
        scalar_certificate.owner_source(owner), owner_index
    )
    if write:
        owner_filename = f"C1RouteAMomentScalarOwner2620K{owner_index:02d}.lean"
        (DEV / owner_filename).write_text(owner_source, encoding="utf-8", newline="\n")
        for source, original_filename in sources.items():
            filename = rename_owner_symbols(original_filename, owner_index)
            (DEV / filename).write_text(source, encoding="utf-8", newline="\n")
        print(f"generated owner={owner_index:02d} panels={panels}")
    return sources


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--owner-index", type=int, required=True, choices=range(30))
    parser.add_argument("--panels", default="94")
    parser.add_argument("--write", action="store_true")
    arguments = parser.parse_args()
    panels = [int(value) for value in arguments.panels.split(",")]
    if any(panel < 0 or panel >= 180 for panel in panels):
        raise SystemExit("panel index must lie in [0, 179]")
    generate(arguments.owner_index, panels, arguments.write)


if __name__ == "__main__":
    main()
