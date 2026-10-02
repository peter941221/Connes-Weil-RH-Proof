"""Audit the current evaluator's directed-MPFR rounding contract.

This is a source audit only.  It does not assert that the mathematical owner
term lies inside the evaluated rectangle.
"""

from __future__ import annotations

import ast
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SOURCE = ROOT / "scripts/routea_weighted_zero_zero_count_certificate_2242.py"


def sha256(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def require(condition: bool, message: str) -> None:
    if not condition:
        raise AssertionError(message)


def name(node: ast.AST) -> str | None:
    return node.id if isinstance(node, ast.Name) else None


def find_method(tree: ast.Module, cls_name: str, method_name: str) -> ast.FunctionDef:
    classes = [node for node in tree.body
               if isinstance(node, ast.ClassDef) and node.name == cls_name]
    require(len(classes) == 1, f"expected one {cls_name}")
    methods = [node for node in classes[0].body
               if isinstance(node, ast.FunctionDef) and node.name == method_name]
    require(len(methods) == 1, f"expected one {cls_name}.{method_name}")
    return methods[0]


def direct_calls(fn: ast.FunctionDef, target: str) -> list[ast.Call]:
    return [node for node in ast.walk(fn)
            if isinstance(node, ast.Call) and name(node.func) == target]


def rounding_args(calls: list[ast.Call]) -> list[str | None]:
    return [name(call.args[-1]) for call in calls]


def main(output: Path | None = None, record: int = 2435) -> dict:
    text = SOURCE.read_text()
    tree = ast.parse(text, filename=str(SOURCE))
    eval_box = find_method(tree, "Kernel", "eval_box")

    for target in ("MUL", "DIV", "SUB", "ADD"):
        calls = direct_calls(eval_box, target)
        require(calls, f"eval_box has no {target} calls")
        require(set(rounding_args(calls)) <= {"RNDD", "RNDU"},
                f"{target} has a non-directed rounding argument")

    for target in ("EXP", "SIN", "COS"):
        calls = direct_calls(eval_box, target)
        require(calls, f"eval_box has no {target} calls")
        require(set(rounding_args(calls)) <= {"RNDD", "RNDU"},
                f"{target} has a non-directed rounding argument")

    text_checks = {
        "mpfr_lower_conversion": "acc[0].get_d(RNDD)",
        "mpfr_upper_conversion": "acc[1].get_d(RNDU)",
        "mpfr_imag_lower_conversion": "acc[2].get_d(RNDD)",
        "mpfr_imag_upper_conversion": "acc[3].get_d(RNDU)",
        "public_lower_nextafter": "np.nextafter(lo_r, -np.inf)",
        "public_upper_nextafter": "np.nextafter(hi_r, np.inf)",
    }
    for label, fragment in text_checks.items():
        require(fragment in text, f"missing {label}")

    result = {
        "record": record,
        "status": "MPFR_ROUNDING_CONTRACT_AUDIT_PASS",
        "source_sha256": sha256(SOURCE),
        "directed_arithmetic_calls": {
            target: len(direct_calls(eval_box, target))
            for target in ("MUL", "DIV", "SUB", "ADD", "EXP", "SIN", "COS")
        },
        "all_arithmetic_rounding_args_directed": True,
        "public_binary64_outward_steps_present": True,
        "pointwise_mathematical_term_dominance_proved": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = output or (ROOT / f"results/{record}_mpfr_rounding_contract_audit.json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
