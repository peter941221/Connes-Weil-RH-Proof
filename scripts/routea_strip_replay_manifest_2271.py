"""Refresh the versioned input inventory for the record-2267 reduction replay.

The --refresh flag is deliberately explicit: refreshing hashes accepts a new
input set for review, not a new mathematical certificate.
"""
import argparse
import hashlib
import json
from pathlib import Path

import routea_weighted_zero_sigma_envelope_certified_2267 as strip


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--refresh", action="store_true", required=True)
    args = parser.parse_args()
    if not args.refresh:
        return 1
    files = {}
    for relative in strip.required_inputs():
        content = (strip.ROOT / relative).read_bytes()
        files[relative] = {"sha256": hashlib.sha256(content).hexdigest(),
                           "bytes": len(content)}
    manifest = {
        "schema_version": 1,
        "record": 2271,
        "consumer_record": 2267,
        "parameters": strip.replay_parameters(),
        "files": files,
        "scope": "Exact file binding for artifact-grade reduction replay; "
                 "neither a proof of the analytic bounds nor a Lean certificate.",
    }
    strip.MANIFEST.write_text(json.dumps(manifest, indent=2) + "\n",
                              encoding="utf-8", newline="\n")
    validation = strip.validate_manifest(strip.ROOT, strip.MANIFEST)
    print(json.dumps(validation, indent=2), flush=True)
    return 0 if validation["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
