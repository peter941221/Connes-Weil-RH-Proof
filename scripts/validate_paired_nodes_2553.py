"""Independent payload, support, axiom and source checks for paired nodes."""
import argparse
import hashlib
import json
from pathlib import Path
import re

from generate_paired_nodes_2553 import ROOT, CASES, render
from validate_boundary_jets_2548 import check
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def


def check_node(source, name):
    grid,sigma = CASES[name]
    normalized = re.sub(r"\bpaired"+name+r"(\w*)2553\b",lambda m:"edge"+name+m[1]+"2548",source)
    sign = "(1/2)" if sigma > 0 else "(-1/2)"
    other = "(-1/2)" if sigma > 0 else "(1/2)"
    assert sign in normalized and other not in normalized
    return check(normalized,name,grid_order=(grid,3),sigma=sigma)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror",type=Path,required=True)
    args = parser.parse_args()
    reports,hashes = [],{}
    for name,(grid,sigma) in CASES.items():
        relative = f"ConnesWeilRH/Dev/C1RouteAPaired{name}2553.lean"
        source = (ROOT/relative).read_text(encoding="utf-8")
        report = check_node(source,name)
        assert source == render(name)[0]
        for index,suffix,replacement in ((report["active"][0],"Factor","(0, 0)"),):
            prefix = f"paired{name}P{index:03d}"
            corrupted = re.sub(r"(def "+prefix+suffix+r"2553\b.*?:=).*?(?=\n\n)",
                               lambda m:m[1]+" "+replacement,source,count=1,flags=re.S)
            assert corrupted != source
            try:
                check_node(corrupted,name)
            except AssertionError:
                pass
            else:
                raise AssertionError("Corrupted factor accepted")
        if report["exterior"]:
            index = report["exterior"][0]
            corrupted = source.replace(f"def paired{name}P{index:03d}Center2553 : RatPair2542 := (0, 0)",
                                       f"def paired{name}P{index:03d}Center2553 : RatPair2542 := (1, 0)")
            assert corrupted != source
            try:
                check_node(corrupted,name)
            except AssertionError:
                pass
            else:
                raise AssertionError("Corrupted exterior center accepted")
        if sigma > 0 and grid in (2700,2701):
            side = "Left" if grid == 2700 else "Right"
            old = (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundary{side}2548.lean").read_text(encoding="utf-8")
            old = re.sub(r":\s*([ℝℚ])",r": \1",old)
            for i in range(30):
                p = f"paired{name}P{i:03d}"
                q = f"edge{side}P{i:03d}"
                for suffix in ("Center","Factor"):
                    assert value(source,p+suffix+"2553") == value(old,q+suffix+"2548")
                assert scalar_def(source,p+"Error2553") == scalar_def(old,q+"Error2548")
        log_path = args.mirror/f"build-logs/2553_{name}.log"
        log = log_path.read_text()
        assert "Exit status: 0" in log
        assert not re.search(r"\berror:|declaration uses 'sorry'|warning: .*2553\.lean",log)
        expected = {f"paired{name}P{i:03d}DerivativeError2553" for i in range(30)}
        expected.add(f"paired{name}Grid2553")
        matches = re.findall(r"'ConnesWeilRH.Dev.([^']+)' depends on axioms:\s*\[([^]]*)\]",log)
        audits = {key:[v.strip() for v in ax.split(",")] for key,ax in matches}
        assert set(audits) == expected
        assert all(ax == ["propext","Classical.choice","Quot.sound"] for ax in audits.values())
        seconds = 0.0
        for part in re.search(r"Elapsed .*?: (\S+)",log)[1].split(":"):
            seconds = seconds*60 + float(part)
        report.update(sigma=str(sigma),wall_seconds=seconds,
            user_seconds=float(re.search(r"User time \(seconds\): ([\d.]+)",log)[1]),
            max_rss_kib=int(re.search(r"Maximum resident set size \(kbytes\): (\d+)",log)[1]),
            source_bytes=len(source.encode()),audits=audits,
            log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())
        reports.append(report)
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
    result = dict(record=2553,status="PAIRED_NODE_PAYLOAD_BUILD_SOURCE_PASS",cases=reports,
        source_sha256=hashes,corrupt_factor_rejections=8,corrupt_exterior_rejections=6,
        accepted_family_matches=60,full_grid_certificate=False,exact_coefficient_membership=False,rh_claim=False)
    (ROOT/"results/2553_paired_node_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print([(r["side"],r["wall_seconds"],r["user_seconds"],r["max_rss_kib"]) for r in reports],flush=True)


if __name__ == "__main__":
    main()
