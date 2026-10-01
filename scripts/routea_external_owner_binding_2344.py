"""2344: exact stored-width and rounded endpoint binding checks, not a Lean import."""
import argparse
from fractions import Fraction
import hashlib
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = "results/2275_gap_owner_audit.json"
OWNER = "ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean"
ENDPOINTS = "ConnesWeilRH/Dev/C1RouteAEndpointStrip.lean"
RESULT = "results/2342_direct_ideal_strip.json"


def parse_widths(source):
    match = re.search(r"noncomputable def storedWidth : Fin 30 → ℝ :=\s*!\[(.*?)\]", source, re.S)
    if match is None:
        raise ValueError("storedWidth declaration missing or changed")
    tokens = match.group(1).split(",")
    if len(tokens) != 30:
        raise ValueError("expected exactly 30 stored widths")
    widths = []
    for token in tokens:
        token = token.strip()
        if not re.fullmatch(r"(?:\(\d+\s*/\s*\d+\)|\d+)", token):
            raise ValueError("unsupported width syntax")
        widths.append(Fraction(token.strip("()").replace(" ", "")))
    return widths


def check_widths(source, families):
    widths = parse_widths(source)
    if len(families) != 30 or any(len(row) != 2 for row in families):
        raise ValueError("incomplete captured family rows")
    captured = [Fraction(float.fromhex(row[0])) for row in families]
    if widths != captured:
        raise ValueError("captured widths differ from Lean storedWidth")
    return [{"index": index, "width_exact": str(width), "radius_exact": str(width**2)}
            for index, width in enumerate(widths)]


def check_constants(source, result):
    names = {("base", "m0"): "baseNormUpper2343",
             ("base", "d2"): "baseSecondUpper2343",
             ("correction", "m0"): "correctionNormUpper2343",
             ("correction", "d2"): "correctionSecondUpper2343"}
    rows = result["endpoints"]
    if len(rows) != 2 or {Fraction(row["sigma_exact"]) for row in rows} != {Fraction(-1, 2), Fraction(1, 2)}:
        raise ValueError("missing endpoint rows")
    checks = []
    for (channel, key), name in names.items():
        match = re.search(r"(?:noncomputable )?def " + name + r" : ℝ :=\s*([0-9.]+)\s", source)
        if match is None:
            raise ValueError("unsupported endpoint constant declaration: " + name)
        constant = Fraction(match.group(1))
        upper = max(Fraction(row["channels"][channel][key]["upper_exact"]) for row in rows)
        if upper > constant:
            raise ValueError("Lean endpoint constant rounds inward: " + name)
        checks.append({"name": name, "external_upper_exact": str(upper),
                       "lean_upper_exact": str(constant), "slack_exact": str(constant - upper)})
    return checks


def run():
    source = (ROOT / OWNER).read_text(encoding="utf-8")
    families = json.loads((ROOT / CAPTURE).read_text())["owner_capture"]["families_hex"]
    result = json.loads((ROOT / RESULT).read_text())
    paths = (CAPTURE, OWNER, ENDPOINTS, RESULT, "scripts/routea_direct_ideal_strip_2342.py", __file__)
    return {"record": 2344, "status": "EXACT_WIDTH_AND_ENDPOINT_BINDING_ONLY",
            "widths": check_widths(source, families),
            "constants": check_constants((ROOT / ENDPOINTS).read_text(encoding="utf-8"), result),
            "input_sha256": {str(Path(path).relative_to(ROOT)) if Path(path).is_absolute() else path:
                             hashlib.sha256((ROOT / path).read_bytes()).hexdigest() for path in paths},
            "executed_evaluator_semantics_proved": False,
            "derivative_formula_proved_in_lean": False,
            "ideal_coefficient_realization_imported": False,
            "endpoint_numeric_facts_imported": False,
            "producer_go": False, "rh_claim": False}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", type=Path)
    args = parser.parse_args()
    report = run()
    text = json.dumps(report, indent=2) + "\n"
    if args.output:
        args.output.write_text(text, encoding="utf-8")
    else:
        print(text, end="")
