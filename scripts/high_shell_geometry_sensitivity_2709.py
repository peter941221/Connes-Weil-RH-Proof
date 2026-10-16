"""One-pass stored-row arithmetic sensitivity; no new analytic evaluation."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
source = ROOT / "results/2033_gate_tail_pairing.json"
data = json.loads(source.read_text())
d = F(169, 16)
rows = []
for owner in data["owners"]:
    h4 = F(owner["H"]) ** 4
    for row in owner["rows"]:
        if not row["gate_signs"]:
            continue
        n, lam = row["n"], F(row["lambda"])
        assert lam > 0 and d <= h4
        old = F(owner["A0"]) * F(data["q"]) ** (2*n) * (1+h4/lam)**2
        new = old * d/h4 * ((d+lam)/(h4+lam))**2
        assert 0 <= new <= old
        rel = abs(float(old)/row["tau_q"] - 1)
        assert rel < 1e-10, "Old-price convention mismatch"
        rows.append({"gamma": owner["gamma"], "N": owner["N"], "n": n,
                     "old_proxy": float(old), "new_proxy": float(new),
                     "old_replay_relative_difference": rel,
                     "new_proxy_pass": new < 1,
                     "geometric_ratio": float(new/old)})
assert rows, "No registered gate rows found"
out = {"scope": "stored sampled rows; unit proxy only; not complete-owner certification",
       "source_sha256": hashlib.sha256(source.read_bytes()).hexdigest(),
       "rows": rows, "gate_rows": len(rows),
       "proxy_passes": sum(row["new_proxy_pass"] for row in rows),
       "producer_go": False, "family_reopened": False, "rh_claim": False}
(ROOT / "results/2709_high_shell_geometry_sensitivity.json").write_text(
    json.dumps(out, indent=2)+"\n")
print(json.dumps(out, indent=2))
