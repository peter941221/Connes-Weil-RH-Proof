"""Read actual Lean timing, audit output, payloads and mirror source identity."""
import argparse
import hashlib
import json
import re
from pathlib import Path

from generate_boundary_replay_2547 import ROOT
from validate_boundary_replay_2547 import check
from validate_compact_replay_2542 import value
from validate_adaptive_nodes_2542 import scalar_def


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--mirror", type=Path, required=True)
    args = parser.parse_args()
    results = {}
    hashes = {}
    for mode in ("Baseline", "Paired", "Separate", "BaselineWarm"):
        stem = "Baseline" if mode == "BaselineWarm" else mode
        relative = f"ConnesWeilRH/Dev/C1RouteABatch{stem}2552.lean"
        source = (ROOT / relative).read_text()
        pending = [relative]
        while pending:
            name = pending.pop()
            if name in hashes:
                continue
            data = (ROOT / name).read_bytes()
            assert data == (args.mirror / name).read_bytes(), name
            hashes[name] = hashlib.sha256(data).hexdigest()
            for line in data.decode("utf-8-sig").splitlines():
                if line.startswith("import "):
                    pending.extend(module.replace(".", "/") + ".lean"
                                   for module in line[7:].split() if module.startswith("ConnesWeilRH"))
        log_path = args.mirror / f"build-logs/2552_{mode.lower()}.log"
        log = log_path.read_text()
        assert "Exit status: 0" in log
        assert not re.search(r"\berror:|declaration uses 'sorry'", log)
        matches = re.findall(r"'ConnesWeilRH.Dev.([^']+)' depends on axioms:\s*\[([^]]*)\]", log)
        audits = {name: [v.strip() for v in ax.split(",")] for name, ax in matches}
        if mode in ("Paired", "Separate"):
            expected = {f"batch{mode}C{i:03d}{suffix}2547" for i in range(4)
                        for suffix in ("BaseError", "ThirdError")}
            assert set(audits) == expected
            assert all(ax == ["propext", "Classical.choice", "Quot.sound"] for ax in audits.values())
            for i, (index, family) in enumerate(((2701, 1), (2701, 15), (5440, 1), (5440, 15))):
                prefix = f"batch{mode}C{i:03d}"
                check(source, prefix=prefix, family_index=family, grid_indices=(index,),
                      position_name=prefix+"Position2547")
                if index == 2701:
                    accepted = (ROOT/"ConnesWeilRH/Dev/C1RouteABoundaryRight2548.lean").read_text()
                    accepted = re.sub(r":\s*([ℝℚ])", r": \1", accepted)
                    old_prefix = f"edgeRightP{family:03d}"
                    for suffix in ("Input", "Center", "Factor"):
                        assert value(source, prefix+suffix+"2547") == value(accepted, old_prefix+suffix+"2548")
                    assert scalar_def(source, prefix+"Error2547") == scalar_def(accepted, old_prefix+"Error2548")
                corrupted = re.sub(r"(noncomputable def "+prefix+r"Error2547\b.*?:=).*?(?=\n\n)",
                                   r"\1 (0 : ℝ)", source, count=1, flags=re.S)
                assert corrupted != source
                try:
                    check(corrupted, prefix=prefix, family_index=family, grid_indices=(index,),
                          position_name=prefix+"Position2547")
                except AssertionError:
                    pass
                else:
                    raise AssertionError("Zero error accepted")
        wall = re.search(r"Elapsed .*?: (\S+)", log)[1]
        seconds = 0.0
        for component in wall.split(":"):
            seconds = seconds*60 + float(component)
        results[mode] = dict(wall_seconds=seconds,
            user_seconds=float(re.search(r"User time \(seconds\): ([\d.]+)", log)[1]),
            system_seconds=float(re.search(r"System time \(seconds\): ([\d.]+)", log)[1]),
            max_rss_kib=int(re.search(r"Maximum resident set size \(kbytes\): (\d+)", log)[1]),
            source_bytes=len(source.encode()), audits=audits,
            log_sha256=hashlib.sha256(log_path.read_bytes()).hexdigest())
    for name in ("lean-toolchain", "lake-manifest.json", "lakefile.toml"):
        assert (ROOT/name).read_bytes() == (args.mirror/name).read_bytes()
    result = dict(record=2552, status="MATCHED_BATCH_COST_PASS", runs=results,
                  source_sha256=hashes, scope="four positive-sign order-three family evaluations",
                  accepted_boundary_payload_matches=4, zeroed_error_rejections=8,
                  full_grid_certificate=False, exact_coefficient_membership=False, rh_claim=False)
    (ROOT/"results/2552_batch_cost_readback.json").write_text(json.dumps(result, indent=2)+"\n")
    print(json.dumps(results, indent=2), flush=True)


if __name__ == "__main__":
    main()
