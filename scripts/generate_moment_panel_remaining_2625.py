"""Emit the remaining 170 actual-panel modules of the committed 180-panel
partition.

Imports the record-2622 generator unchanged and reuses its parameterized
panel emission for panels 000-089 and 100-179. Panel module names keep the
2622 family tag (the 2617-cell precedent from record 2623), so the only
record-2625-scoped object is the batch audit module and the payload. The
committed record-2622 chain (generator bytes, payload, sources) is not
touched.
"""

import hashlib
import importlib.util
import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEV = ROOT / "ConnesWeilRH/Dev"
AUDIT_MODULE = "C1RouteAMomentPanelBatchAudit2625"
PAYLOAD_PATH = ROOT / "results/2625_moment_panel_remaining_payload.json"
COMMITTED_BATCH = list(range(90, 100))
REMAINING = [index for index in range(180)
             if not 90 <= index <= 99]


def load_batch_generator():
    spec = importlib.util.spec_from_file_location(
        "panel_batch_2622", ROOT / "scripts/generate_moment_panel_batch_2622.py")
    batch = importlib.util.module_from_spec(spec)
    sys.modules["panel_batch_2622"] = batch
    spec.loader.exec_module(batch)
    return batch


def generate(indices, write=True):
    batch = load_batch_generator()
    owner = batch.get_data()
    # Stability canary outside this batch's scope: the committed control
    # panel 094 must keep reproducing the record-2621 payload exactly.
    batch.cross_check_panel94([batch.panel_data(94, owner)])
    panels = [batch.panel_data(index, owner) for index in indices]
    sources = {}
    for index, data in zip(indices, panels):
        sources.update(batch.panel_sources(data))
    sources[AUDIT_MODULE + ".lean"] = batch.audit_source(indices)
    payload = dict(batch.payload_data(indices, panels, owner))
    payload["record"] = 2625
    payload["batch_record"] = 2622
    payload["panel094_canary"] = ("out-of-scope control panel 094 reproduces the "
                                  "committed 2621 payload exactly")
    payload["driver_sha256"] = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    if not write:
        return sources, payload
    for filename, source in sources.items():
        (DEV / filename).write_text(source, encoding="utf-8", newline="\n")
    PAYLOAD_PATH.write_text(json.dumps(payload, indent=2) + "\n",
                            encoding="utf-8", newline="\n")
    for index, data in zip(indices, panels):
        print(f"panel {index:03d}: residual upper ~{float(data['residual_upper']):.6e}, "
              f"integral charge ~{float(data['integral_charge']):.6e}", flush=True)
    return sources, payload


def main():
    generate(REMAINING)


if __name__ == "__main__":
    main()
