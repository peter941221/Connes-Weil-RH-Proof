"""2445 independent high-precision containment replay.

This replay does not import the MPFR evaluator. It recomputes each family term
with mpmath at high precision and checks containment in the stored rectangles.
It is still a finite point-box control, not a continuum or quadrature proof.
"""

import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
ARTIFACT = ROOT / "results/2445_routea_family_endpoint_certificate.json"
OUT = ROOT / "results/2445_routea_family_endpoint_independent_replay.json"


def contained(value, interval):
    return mp.mpf(interval["lo"]) <= value <= mp.mpf(interval["hi"])


def lift_stored_position(value):
    return mp.mpf(value)


def validate_artifact_sources(artifact):
    required = {"results/2275_gap_owner_audit.json",
                "scripts/routea_family_endpoint_certificate_2445.py",
                "scripts/routea_mpfr_owner_atom_preflight_2286.py"}
    hashes = artifact["source_sha256"]
    if not required.issubset(hashes):
        raise ValueError("family artifact is missing a required source hash")
    for relative, expected in hashes.items():
        actual = hashlib.sha256((ROOT / relative).read_bytes()).hexdigest()
        if actual != expected:
            raise ValueError(f"family artifact source hash differs: {relative}")
    if artifact["owner"]["capture_sha256"] != hashes["results/2275_gap_owner_audit.json"]:
        raise ValueError("family artifact owner capture hash differs")


def run():
    mp.mp.dps = 80
    capture = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]
    artifact = json.loads(ARTIFACT.read_text(encoding="utf-8"))
    validate_artifact_sources(artifact)
    families = [(mp.mpf(float.fromhex(a)), mp.mpf(float.fromhex(b)))
                for a, b in capture["families_hex"]]
    vectors = {
        "base": [complex(float.fromhex(a), float.fromhex(b)) for a, b in capture["base_hex"]],
        "correction": [complex(float.fromhex(a), float.fromhex(b)) for a, b in capture["corr_hex"]],
    }
    failures = []
    checked = 0
    for row in artifact["rows"]:
        position = lift_stored_position(row["position"])
        for term in row["terms"]:
            index = term["index"]
            width, modulation = families[index]
            coefficient = vectors[row["vector"]][index]
            radius = width * width
            if abs(position) >= radius:
                value = 0j
            else:
                q = 1 - (position / radius) ** 2
                value = (mp.mpc(coefficient.real, coefficient.imag)
                         * mp.exp(-30 / q)
                         * mp.exp(mp.j * modulation * position))
            rectangle = term["rectangle"]
            real_ok = contained(mp.re(value), rectangle["real"])
            imag_ok = contained(mp.im(value), rectangle["imag"])
            checked += 1
            if not (real_ok and imag_ok):
                failures.append({"position": str(position), "vector": row["vector"],
                                 "index": index, "real_ok": real_ok, "imag_ok": imag_ok})
    result = {
        "record": 2445,
        "status": "INDEPENDENT-MPMATH-CONTAINMENT-REPLAY",
        "precision_digits": 80,
        "checked_terms": checked,
        "failure_count": len(failures),
        "failures": failures,
        "position_convention": "exact stored binary64, not decimal-string reconstruction",
        "source_hashes_verified": True,
        "replay_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "artifact_sha256": hashlib.sha256(ARTIFACT.read_bytes()).hexdigest(),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "nonclaims": ["finite point-box control only", "no continuum transfer",
                       "no quadrature enclosure", "no Lean numeric import", "no producer GO"],
    }
    return result


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path, default=OUT)
    args = parser.parse_args()
    result = run()
    args.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"], "checked_terms": result["checked_terms"],
                      "failure_count": result["failure_count"]}))
    if result["failure_count"]:
        raise SystemExit(1)


if __name__ == "__main__":
    main()
