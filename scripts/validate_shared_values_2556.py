"""Independent arithmetic and shared-parent acceptance for endpoint values."""
import argparse
import hashlib
import json
from pathlib import Path
import re

from generate_shared_values_2556 import ROOT, CASES, render
from validate_adaptive_nodes_2542 import check,scalar_def


def normalize(source,name):
    return re.sub(r"\bshared"+name+r"(\w*)2556\b",lambda m:"adaptive"+name+m[1]+"2542",source)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror",type=Path,required=True)
    parser.add_argument("--log",type=Path,required=True)
    args = parser.parse_args()
    reports,pending = [],["ConnesWeilRH.lean"]
    for name,(grid,sigma) in CASES.items():
        index,sign = int(grid),1 if sigma > 0 else -1
        path = f"ConnesWeilRH/Dev/C1RouteAShared{name}2556.lean"
        source = (ROOT/path).read_text(encoding="utf-8")
        assert source == render(name)[0]
        assert "compactExp" not in source and "cbv" not in source and "decide" not in source
        assert source.count("BaseError2555") == 30
        parent = (ROOT/f"ConnesWeilRH/Dev/C1RouteAKernel{name}2555.lean").read_text(encoding="utf-8")
        normalized = normalize(source,name)
        report = check(normalized,index,sign,shared_source=parent)
        corrupted = re.sub(r"(noncomputable def adaptive"+name+r"Upper2542\b.*?:=).*?(?=\n\n)",
                           r"\1 (0 : ℝ)",normalized,count=1,flags=re.S)
        assert corrupted != normalized
        try:
            check(corrupted,index,sign,shared_source=parent)
        except AssertionError:
            pass
        else:
            raise AssertionError("Zero signed upper accepted")
        if index in (5440,10239):
            old = (ROOT/f"ConnesWeilRH/Dev/C1RouteAAdaptive{name}2542.lean").read_text(encoding="utf-8")
        elif sign > 0:
            side = "Left" if index == 2700 else "Right"
            old = (ROOT/f"ConnesWeilRH/Dev/C1RouteABoundaryValue{side}2551.lean").read_text(encoding="utf-8")
        else:
            old = None
        if old is not None:
            assert scalar_def(old,f"adaptive{name}Upper2542") == scalar_def(normalized,f"adaptive{name}Upper2542")
        report.update(zeroed_upper_rejected=True,prior_upper_reproduced=old is not None)
        reports.append(report)
        pending.append(path)
    log = args.log.read_text()
    assert re.search(r"^Build completed successfully",log,re.M)
    assert not re.search(r"^error:|declaration uses 'sorry'|warning: .*2556\.lean",log,re.M)
    expected = {f"shared{name}{suffix}2556" for name in CASES for suffix in ("Signed_le","Physical_le")}
    matches = re.findall(r"'ConnesWeilRH.Dev.([^']+2556)' depends on axioms:\s*\[([^]]*)\]",log)
    audits = {name:[v.strip() for v in ax.split(",")] for name,ax in matches}
    assert set(audits) == expected
    assert all(ax == ["propext","Classical.choice","Quot.sound"] for ax in audits.values())
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
    result = dict(record=2556,status="SHARED_ENDPOINT_VALUE_PASS",cases=reports,audits=audits,
        source_sha256=hashes,build_footer=re.findall(r"^Build completed successfully.*$",log,re.M)[-1],
        build_log_sha256=hashlib.sha256(args.log.read_bytes()).hexdigest(),
        new_exponential_replays=0,full_grid_certificate=False,exact_coefficient_membership=False,rh_claim=False)
    (ROOT/"results/2556_shared_value_readback.json").write_text(json.dumps(result,indent=2)+"\n")
    print("SHARED_ENDPOINT_VALUE_PASS",len(reports),"nodes",len(hashes),"sources",flush=True)


if __name__ == "__main__":
    main()
