"""Same-input kernel replay and full support-ladder acceptance."""
import argparse
import hashlib
import json
from pathlib import Path
import re

from generate_kernel_trial_2555 import ROOT, CASES, render, render_node
from validate_boundary_replay_2547 import check
from validate_paired_nodes_2553 import check_node


def reading(path,expected):
    log = path.read_text()
    assert "Exit status: 0" in log
    assert not re.search(r"\berror:|declaration uses 'sorry'|warning: .*2555\.lean",log)
    matches = re.findall(r"'ConnesWeilRH.Dev.([^']+)' depends on axioms:\s*\[([^]]*)\]",log)
    audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
    assert set(audits) == expected
    assert all(ax == ["propext","Classical.choice","Quot.sound"] for ax in audits.values())
    wall = 0.0
    for value in re.search(r"Elapsed .*?: (\S+)",log)[1].split(":"):
        wall = wall*60+float(value)
    return dict(wall_seconds=wall,user_seconds=float(re.search(r"User time \(seconds\): ([\d.]+)",log)[1]),
        max_rss_kib=int(re.search(r"Maximum resident set size \(kbytes\): (\d+)",log)[1]),
        audits=audits,log_sha256=hashlib.sha256(path.read_bytes()).hexdigest())


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror",type=Path,required=True)
    parser.add_argument("--integration-log",type=Path)
    args = parser.parse_args()
    layout = json.loads((ROOT/"results/2555_layout_control.json").read_text())["files"]
    for row in layout:
        data = (ROOT/row["path"]).read_bytes()
        assert hashlib.sha256(data).hexdigest() == row["after_sha256"]
        assert hashlib.sha256(b" ".join(data.split())).hexdigest() == row["tokens_sha256"]
        assert row["tokens_identical"]
    relative = "ConnesWeilRH/Dev/C1RouteAKernelTrial2555.lean"
    source = (ROOT/relative).read_text(encoding="utf-8")
    assert source == render()
    for i,(index,family) in enumerate(((2701,1),(2701,15),(5440,1),(5440,15))):
        prefix = f"kernelTrialC{i:03d}"
        check(source,prefix=prefix,record=2555,family_index=family,grid_indices=(index,),position_name=prefix+"Position2555")
    suffixes = ("BaseError","ThirdError")
    runs = {}
    for mode,prefix,record in (("control","batchPaired",2547),("kernel","kernelTrial",2555)):
        expected = {f"{prefix}C{i:03d}{suffix}{record}" for i in range(4) for suffix in suffixes}
        runs[mode] = reading(args.mirror/f"build-logs/2555_{mode}.log",expected)
    pending = [relative,"ConnesWeilRH/Dev/C1RouteABatchPaired2552.lean"]
    for name in CASES:
        relative = f"ConnesWeilRH/Dev/C1RouteAKernel{name}2555.lean"
        source = (ROOT/relative).read_text(encoding="utf-8")
        assert source == render_node(name)
        normalized = re.sub(r"\bkernel"+name+r"(\w*)2555\b",lambda m:"paired"+name+m[1]+"2553",source)
        check_node(normalized,name)
        expected = {f"kernel{name}P{i:03d}DerivativeError2555" for i in range(30)}|{f"kernel{name}Grid2555"}
        runs[name] = reading(args.mirror/f"build-logs/2555_{name}.log",expected)
        pending.append(relative)
    for name in ("N02701Minus","N05440Plus"):
        for method,prefix,record in (("Paired","paired",2553),("Kernel","kernel",2555)):
            expected = {f"{prefix}{name}P{i:03d}DerivativeError{record}" for i in range(30)}|{f"{prefix}{name}Grid{record}"}
            runs[f"matched_{method}_{name}"] = reading(args.mirror/f"build-logs/2555_matched_{method}_{name}.log",expected)
            pending.append(f"ConnesWeilRH/Dev/C1RouteA{method}{name}{record}.lean")
    if args.integration_log:
        log = args.integration_log.read_text()
        assert re.search(r"^Build completed successfully",log,re.M)
        assert not re.search(r"^error:|declaration uses 'sorry'|warning: .*255[2-5]\.lean",log,re.M)
        pending.append("ConnesWeilRH.lean")
        expected_integration = set()
        for path in (ROOT/"ConnesWeilRH/Dev").glob("C1RouteA*255[2-5].lean"):
            pending.append(path.relative_to(ROOT).as_posix())
            expected_integration.update(re.findall(r"^#print axioms (\S+)",path.read_text(encoding="utf-8"),re.M))
        matches = re.findall(r"'([^']+)' depends on axioms:\s*\[([^]]*)\]",log)
        integrated_audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
        assert expected_integration <= integrated_audits.keys()
        assert all(integrated_audits[name] == ["propext","Classical.choice","Quot.sound"] for name in expected_integration)
    hashes = {}
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
    result = dict(record=2555,status="KERNEL_REPLAY_FULL_NODE_PASS",runs=runs,source_sha256=hashes,
        layout_tokens_verified=len(layout),
        full_grid_certificate=False,exact_coefficient_membership=False,rh_claim=False)
    if args.integration_log:
        result["integration_log_sha256"] = hashlib.sha256(args.integration_log.read_bytes()).hexdigest()
        result["integrated_terminal_audits"] = len(expected_integration)
        result["integration_footer"] = re.findall(r"^Build completed successfully.*$",log,re.M)[-1]
    (ROOT/"results/2555_kernel_trial_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print({k:{f:v[f] for f in ("wall_seconds","user_seconds","max_rss_kib")} for k,v in runs.items()},flush=True)


if __name__ == "__main__":
    main()
