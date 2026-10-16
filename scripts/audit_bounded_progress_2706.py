"""Source-only stop/go audit; no numerical, Lean-build, or RH claim."""
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
paths = {
    "consumer": "ConnesWeilRH/Dev/C1RouteACorrectionAnalyticOffDiagCertificate2695.lean",
    "manifest": "ConnesWeilRH/Dev/C1RouteAEntryManifest2664.lean",
    "generic_composition": "ConnesWeilRH/Dev/C1RouteAPanelComposition2662.lean",
}
sources = {key: (ROOT / path).read_text(encoding="utf-8") for key, path in paths.items()}
consumer = sources["consumer"].split(
    "theorem capturedActualCorrectionOwner2584_realizes_of_remaining_offdiag_certificate2695_concrete",
    1,
)[1].split(":= by", 1)[0]
premises = [name for name in ("h_remaining", "hdefect_entry", "hdefect_matrix")
            if re.search(r"\(" + name + r"\s*:", consumer)]
assert len(premises) == 3, "Consumer signature changed; review the audit."
manifest = sources["manifest"].split("\ntheorem ", 1)[0]
pairs = set((int(i), int(j)) for i, j in
            re.findall(r"i = (\d+) ∧ j = (\d+)", manifest))
assert pairs and all(i != j and 0 <= i < 30 and 0 <= j < 30 for i, j in pairs)
assert "(i = 0 ∧ j = 3) ∨ parameterizedOffdiagManifest2664 i j" in sources["consumer"]
known = pairs | {(0, 3)}
payload = {
    "scope": "source signature and wiring audit; not compiled coverage",
    "source_sha256": {paths[k]: hashlib.sha256((ROOT / paths[k]).read_bytes()).hexdigest()
                      for k in paths},
    "wired_offdiagonal_positions": len(known),
    "remaining_positions": 30 * 29 - len(known),
    "remaining_named_premises": premises,
    "existing_generic_composition": paths["generic_composition"],
    "decision": "STOP_UNBOUNDED_ENTRY_AND_AGGREGATE_CAMPAIGN",
    "reason": "Enumerating memberships leaves both defect identities and all later producer obligations open.",
    "restart_gate": "A bounded target with owner, removed premise, consumer, resource budget and stop condition; frozen-family work also requires its named-hypothesis reopening gate.",
    "producer_go": False,
    "rh_claim": False,
}
out = ROOT / "results/2706_bounded_progress_audit.json"
out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
print(json.dumps(payload, indent=2))
