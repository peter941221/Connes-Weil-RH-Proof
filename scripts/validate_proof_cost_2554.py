"""Read cumulative phase timing without mistaking pure replay for analysis."""
import argparse
import hashlib
import json
from pathlib import Path
import re
from fractions import Fraction as Q

from generate_proof_cost_2554 import ROOT, render
from validate_paired_nodes_2553 import check_node
from validate_boundary_jets_2548 import check as check_payload


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror",type=Path,required=True)
    args = parser.parse_args()
    readings,hashes = {},{}
    for mode in ("Replay","Base","Full"):
        relative = f"ConnesWeilRH/Dev/C1RouteAProfile{mode}2554.lean"
        source = (ROOT/relative).read_text(encoding="utf-8")
        assert source == render(mode)
        normalized = re.sub(r"\bprofile"+mode+r"(\w*)2554\b",lambda m:"pairedN05440Plus"+m[1]+"2553",source)
        if mode == "Replay":
            payload = re.sub(r"\bprofileReplay(\w*)2554\b",lambda m:"edgeN05440Plus"+m[1]+"2548",source)
            check_payload(payload,"N05440Plus",grid_order=(Q(5440),3),sigma=Q(1,2))
        else:
            check_node(normalized,"N05440Plus")
        log_path = args.mirror/f"build-logs/2554_{mode}.log"
        log = log_path.read_text()
        assert "Exit status: 0" in log
        assert not re.search(r"\berror:|declaration uses 'sorry'|warning: .*2554\.lean",log)
        suffix = {"Replay":"Replay","Base":"BaseError","Full":"DerivativeError"}[mode]
        expected = {f"profile{mode}P{i:03d}{suffix}2554" for i in range(30)}
        matches = re.findall(r"'ConnesWeilRH.Dev.([^']+)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {name:[v.strip() for v in ax.split(",") if v.strip()] for name,ax in matches}
        for name in re.findall(r"'ConnesWeilRH.Dev.([^']+)' does not depend on any axioms",log):
            audits[name] = []
        assert set(audits) == expected,(mode,set(audits))
        allowed = ["propext","Classical.choice","Quot.sound"]
        assert all(ax == allowed for ax in audits.values()),audits
        wall = 0.0
        for value in re.search(r"Elapsed .*?: (\S+)",log)[1].split(":"):
            wall = wall*60+float(value)
        readings[mode] = dict(wall_seconds=wall,
            user_seconds=float(re.search(r"User time \(seconds\): ([\d.]+)",log)[1]),
            max_rss_kib=int(re.search(r"Maximum resident set size \(kbytes\): (\d+)",log)[1]),
            audits=audits,log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())
        pending = [relative]
        while pending:
            path = pending.pop()
            if path in hashes:
                continue
            data = (ROOT/path).read_bytes()
            assert data == (args.mirror/path).read_bytes(),path
            hashes[path] = hashlib.sha256(data).hexdigest()
            for line in data.decode("utf-8-sig").splitlines():
                if line.startswith("import "):
                    pending.extend(m.replace(".","/")+".lean" for m in line[7:].split() if m.startswith("ConnesWeilRH"))
    for path in ("lean-toolchain","lake-manifest.json","lakefile.toml"):
        assert (ROOT/path).read_bytes() == (args.mirror/path).read_bytes()
    result = dict(record=2554,status="CUMULATIVE_PHASE_COST_PASS",runs=readings,source_sha256=hashes,
        scope="node5440 sigma+1/2 thirty families; cumulative costs include imports",
        full_grid_certificate=False,exact_coefficient_membership=False,rh_claim=False)
    (ROOT/"results/2554_proof_cost_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print({k:{field:v[field] for field in ("wall_seconds","user_seconds","max_rss_kib")} for k,v in readings.items()},flush=True)


if __name__ == "__main__":
    main()
