"""Check full 2338 coefficient intervals against the 2570 Lean boxes."""

from fractions import Fraction
import ast
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
REPAIR = ROOT / "results/2338_exact_interpolation_repair.json"
BOXES = ROOT / "ConnesWeilRH/Dev/C1RouteACorrectionCoefficientBoxes2570.lean"


def rational_expr(text: str) -> Fraction:
    expression = re.sub(r"\s+", "", text).replace("^", "**")
    tree = ast.parse(expression, mode="eval")

    def evaluate(node):
        if isinstance(node, ast.Constant) and isinstance(node.value, int):
            return Fraction(node.value)
        if isinstance(node, ast.UnaryOp) and isinstance(node.op, (ast.UAdd, ast.USub)):
            value = evaluate(node.operand)
            return value if isinstance(node.op, ast.UAdd) else -value
        if isinstance(node, ast.BinOp) and isinstance(node.op, (ast.Add, ast.Sub, ast.Mult, ast.Pow)):
            left = evaluate(node.left)
            right = evaluate(node.right)
            if isinstance(node.op, ast.Add):
                return left + right
            if isinstance(node.op, ast.Sub):
                return left - right
            if isinstance(node.op, ast.Mult):
                return left * right
            if right.denominator != 1 or right < 0:
                raise ValueError("non-integral or negative exponent")
            return left ** right.numerator
        raise ValueError(f"unsupported expression: {ast.dump(node)}")

    return evaluate(tree.body)


def strip_outer_parens(text: str) -> str:
    text = text.strip()
    while text.startswith("(") and text.endswith(")"):
        depth = 0
        closes_at = None
        for index, char in enumerate(text):
            if char == "(":
                depth += 1
            elif char == ")":
                depth -= 1
                if depth == 0:
                    closes_at = index
                    break
        if closes_at != len(text) - 1:
            break
        text = text[1:-1].strip()
    return text


def parse_boxes(text: str):
    fields = {}
    field_names = ("reLo", "reHi", "imLo", "imHi")
    for field in field_names:
        pattern = re.compile(
            rf"{field} :=(.*?)(?=\n\s+(?:reLo|reHi|imLo|imHi) :=|\n\s+\}}|\n\s+\|)",
            re.S,
        )
        matches = pattern.findall(text)
        if len(matches) != 30:
            raise AssertionError(f"expected 30 {field} literals, found {len(matches)}")
        values = []
        for raw in matches:
            left, right = raw.split(": ℝ", 1)
            left = left.strip()
            numerator = strip_outer_parens(left[1:] if left.startswith("(") else left)
            denominator = strip_outer_parens(right.split("/", 1)[1].strip().rstrip("}").strip())
            values.append(rational_expr(numerator) / rational_expr(denominator))
        fields[field] = values
    return [
        {field: fields[field][index] for field in fields}
        for index in range(30)
    ]

def main():
    repair = json.loads(REPAIR.read_text(encoding="utf-8"))
    rows = repair["coefficient_rows"]
    boxes = parse_boxes(BOXES.read_text(encoding="utf-8"))
    failures = []
    margins = []
    for row, box in zip(rows, boxes):
        coefficient = row["ideal_correction_coefficient"]
        interval = {
            "reLo": Fraction(coefficient["real"]["lower_exact"]),
            "reHi": Fraction(coefficient["real"]["upper_exact"]),
            "imLo": Fraction(coefficient["imag"]["lower_exact"]),
            "imHi": Fraction(coefficient["imag"]["upper_exact"]),
        }
        for lower, upper in (("reLo", "reHi"), ("imLo", "imHi")):
            if not (box[lower] <= interval[lower] and interval[upper] <= box[upper]):
                failures.append({"index": row["index"], "component": lower[:2]})
            margins.extend((interval[lower] - box[lower], box[upper] - interval[upper]))
    result = {
        "record": 2585,
        "status": "FULL_INTERVAL_BOX_CONTAINMENT_PASS" if not failures else "FULL_INTERVAL_BOX_CONTAINMENT_FAIL",
        "rows_checked": len(rows),
        "coordinates_checked": 2 * len(rows),
        "failures": failures,
        "minimum_outward_margin": str(min(margins)),
        "repair_source": str(REPAIR.relative_to(ROOT)),
        "box_source": str(BOXES.relative_to(ROOT)),
        "lean_membership_theorem": False,
        "owner_transfer_to_live_consumer": False,
        "producer_go": False,
        "rh_claim": False,
    }
    output = ROOT / "results/2585_full_interval_box_containment.json"
    output.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(result, indent=2))
    if failures:
        raise AssertionError(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
