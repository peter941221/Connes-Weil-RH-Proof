"""Compile and audit the actual moment normalization and diagonal imaginary bounds."""
import argparse
from decimal import Decimal, localcontext
from fractions import Fraction
import hashlib
import json
import os
from pathlib import Path
import subprocess

from validate_static_coordinate_bounds_2617 import AXIOMS, parse_successful_log

ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "C1RouteAAnalyticMomentNormalization2618",
    "C1RouteAAnalyticMomentDiagonal2618",
    "C1RouteAAnalyticMomentNormalizationAudit2618",
)
THEOREMS = (
    "momentIntegrand2351_support_subset_Ioc2618",
    "momentEntry2351_eq_intervalIntegral2618",
    "scaledMomentIntegrand2351_eq_normalized2618",
    "momentEntry2351_eq_normalizedIntegral2618",
    "normalizedMomentIntegrand2618_eq_real_of_phase_cancel",
    "momentEntry2351_eq_realIntegral_of_phase_cancel2618",
    "momentEntry2351_im_eq_zero_of_phase_cancel2618",
    "capturedDiagonalPhase2618",
    "actualOwnerMomentMatrix2351_diagonal_im_eq_zero2618",
    "actualOwnerMomentMatrix2351_entry000_im_mem2618",
)


def describe_width(component):
    width = Fraction(component["upper_exact"]) - Fraction(component["lower_exact"])
    if width <= 0:
        raise ValueError("expected a positive witness interval width")
    with localcontext() as context:
        context.prec = 12
        display = str(Decimal(width.numerator) / Decimal(width.denominator))
    return {"width_exact": str(width), "width_decimal": display}


def fingerprint(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def validate(workspace, logs, lean):
    if os.name != "posix":
        raise ValueError("compilation requires Linux and GNU time")
    library = workspace / ".lake/build/lib/lean"
    configured = os.environ.get("LEAN_PATH", "").split(":")
    if not configured[0] or Path(configured[0]).resolve() != library.resolve():
        raise ValueError("LEAN_PATH must begin with the complete workspace project library")
    if any(not Path(path).is_dir() for path in configured):
        raise ValueError("every explicit library root must exist")
    logs.mkdir(parents=True, exist_ok=True)
    environment = dict(os.environ, LC_ALL="C")
    stages = []
    audit_text = None
    for module in MODULES:
        source = ROOT / "ConnesWeilRH/Dev" / f"{module}.lean"
        output = library / "ConnesWeilRH/Dev" / f"{module}.olean"
        source_digest = fingerprint(source)
        print(f"compile {module}", flush=True)
        with (logs / f"{module}.log").open("w", encoding="utf-8") as stream:
            stream.write(f"SOURCE_SHA256={source_digest}\n")
            stream.flush()
            process = subprocess.run([
                "bash", str(ROOT / "scripts/run_resource_aware_task.sh"),
                "--class", "normal", "--workspace", str(workspace), "--",
                "/usr/bin/time", "-v", lean, f"--root={ROOT}",
                "-o", str(output), str(source),
            ], env=environment, stdout=stream, stderr=subprocess.STDOUT)
            if process.returncode != 0 or not output.is_file():
                raise RuntimeError(f"Lean failed for {module}: {process.returncode}")
            if fingerprint(source) != source_digest:
                raise RuntimeError(f"source changed during compilation: {module}")
            object_digest = fingerprint(output)
            stream.write(f"OLEAN_SHA256={object_digest}\n")
        text = (logs / f"{module}.log").read_text()
        metrics = parse_successful_log(text, source_sha256=source_digest,
                                       olean_sha256=object_digest)
        if module == MODULES[-1]:
            audit_text = text
            for theorem in THEOREMS:
                parse_successful_log(text, f"ConnesWeilRH.Dev.{theorem}",
                                     source_digest, object_digest)
        stages.append({"module": module, "source_sha256": source_digest,
                       "olean_sha256": object_digest, "exit_code": 0, **metrics})
    if audit_text is None:
        raise RuntimeError("missing audit stage")
    witness = ROOT / "results/2351_moment_matrix_witness.json"
    entry = json.loads(witness.read_text())["matrix"][0][0]
    return {
        "record": 2618, "scope": "same-owner normalization and diagonal imaginary coordinates",
        "witness_sha256": fingerprint(witness), "audited_axioms": AXIOMS,
        "audited_theorems": list(THEOREMS), "stages": stages,
        "diagonal_imaginary_zero_equalities_verified": 30,
        "imaginary_coordinate_containments_verified": 1,
        "imaginary_coordinate_containment_entries": [[0, 0]],
        "full_analytic_entries_verified": 0,
        "entry_000_widths": {component: describe_width(entry[component])
                             for component in ("real", "imag")},
        "upstream_dependencies": "reused project and Mathlib objects; not rebuilt in this run",
        "lean_toolchain": (ROOT / "lean-toolchain").read_text().strip(),
        "full_static_comparison_verified": False,
        "analytic_interval_soundness": "external_premise_required",
        "actual_coefficient_membership": "not_proved", "producer_go": False, "rh_claim": False,
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--workspace", type=Path, required=True)
    parser.add_argument("--logs", type=Path, required=True)
    parser.add_argument("--lean", default="lean")
    parser.add_argument("--output", type=Path,
                        default=ROOT / "results/2618_analytic_moment_normalization_validation.json")
    arguments = parser.parse_args()
    result = validate(arguments.workspace.resolve(), arguments.logs.resolve(), arguments.lean)
    arguments.output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(f"verified {len(THEOREMS)} theorems, 30 diagonal zero equalities, and entry (0,0) imaginary containment", flush=True)


if __name__ == "__main__":
    main()
