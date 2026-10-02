"""Lock the algebraic shape used by the Route A interval kernel.

This is a source-structure audit, not a numerical enclosure proof.  It keeps
the Lean rectangle lemmas aligned with the actual `iprod`/`ciprod` code.
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


def direct_calls(fn: ast.FunctionDef, target: str) -> list[ast.Call]:
    return [
        node.value
        for node in fn.body
        if isinstance(node, ast.Expr)
        and isinstance(node.value, ast.Call)
        and name(node.value.func) == target
    ]


def find_function(tree: ast.Module, target: str) -> ast.FunctionDef:
    matches = [node for node in tree.body
               if isinstance(node, ast.FunctionDef) and node.name == target]
    require(len(matches) == 1, f"expected one {target} definition")
    return matches[0]


def main(output: Path | None = None, record: int = 2432) -> dict:
    text = SOURCE.read_text()
    tree = ast.parse(text, filename=str(SOURCE))
    iprod = find_function(tree, "iprod")
    ciprod = find_function(tree, "ciprod")

    iprod_muls = direct_calls(iprod, "MUL")
    require(len(iprod_muls) == 8, "iprod must have eight directed products")
    require([name(call.args[3]) for call in iprod_muls[:4]] ==
            ["RNDD"] * 4, "iprod lower products changed")
    require([name(call.args[3]) for call in iprod_muls[4:]] ==
            ["RNDU"] * 4, "iprod upper products changed")
    require(len(direct_calls(iprod, "imin")) == 3,
            "iprod lower hull must consume four corners")
    require(len(direct_calls(iprod, "imax")) == 3,
            "iprod upper hull must consume four corners")

    require(len(direct_calls(ciprod, "iprod")) == 4,
            "ciprod must contain four real products")
    subs = direct_calls(ciprod, "SUB")
    adds = direct_calls(ciprod, "ADD")
    require(len(subs) == 2 and len(adds) == 2,
            "ciprod must have two differences and two sums")
    require([name(call.args[3]) for call in subs] == ["RNDD", "RNDU"],
            "ciprod subtraction rounding changed")
    require([name(call.args[3]) for call in adds] == ["RNDD", "RNDU"],
            "ciprod addition rounding changed")

    result = {
        "record": record,
        "status": "INTERVAL_KERNEL_SHAPE_AUDIT_PASS",
        "source_sha256": sha256(SOURCE),
        "iprod_directed_products": 8,
        "iprod_lower_hull_steps": 3,
        "iprod_upper_hull_steps": 3,
        "ciprod_real_products": 4,
        "ciprod_subtractions": 2,
        "ciprod_additions": 2,
        "pointwise_mathematical_term_dominance_proved": False,
        "lean_numeric_imported": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = output or (ROOT / f"results/{record}_interval_kernel_shape_audit.json")
    output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps(result, indent=2, sort_keys=True))
    return result


if __name__ == "__main__":
    main()
