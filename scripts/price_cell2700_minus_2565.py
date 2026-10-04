"""Price the sigma=-1/2 three-piece summand at production cell 2700.

Extracts the certified per-family bound leaves of the 2558 batch modules
(left/right norm uppers, fourth uppers), bridges the L2 coefficient norms of
the 2338 base boxes to their L1 sums, and evaluates the exact rational
three-piece summand of the 2562 decomposition with the 2565 minus first-jet
upper and the 2556 minus endpoint values. Emits the closed cell-bound
numerator used by the Lean assembly module.
"""
from fractions import Fraction as Q
from math import ceil
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def exact_expression(expression):
    import ast
    node = ast.parse(re.sub(r":\s*ℝ", "", expression).replace("^", "**").strip(),
                     mode="eval").body
    def evaluate(term):
        if isinstance(term, ast.Constant) and type(term.value) is int:
            return Q(term.value)
        if isinstance(term, ast.UnaryOp) and isinstance(term.op, ast.USub):
            return -evaluate(term.operand)
        if isinstance(term, ast.BinOp):
            left, right = evaluate(term.left), evaluate(term.right)
            if isinstance(term.op, ast.Add):
                return left + right
            if isinstance(term.op, ast.Sub):
                return left - right
            if isinstance(term.op, ast.Mult):
                return left * right
            if isinstance(term.op, ast.Div):
                return left / right
            if isinstance(term.op, ast.Pow) and right.denominator == 1:
                return left ** right.numerator
        raise ValueError("unsupported generated rational expression")
    return evaluate(node)


def scalar_defs(source, pattern):
    out = {}
    for match in re.finditer(r"noncomputable def (" + pattern + r") : ℝ :=\s*(.*?)(?=\n\n)",
                             source, re.S):
        out[match.group(1)] = exact_expression(match.group(2).replace("\n", " "))
    return out


def main():
    r = Q(65536001, 10 ** 7)
    step = 2 * r / 10240
    half = step / 2
    left = (-r + 2700 * step)
    right = (-r + 2701 * step)
    assert left == Q(-7929856121, 2560000000)
    assert right == Q(-158531586419, 51200000000)

    left_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusLeftBounds2558.lean").read_text()
    right_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusRightBounds2558.lean").read_text()
    fourth_src = (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusFourth2558.lean").read_text()
    vals = {}
    vals.update(scalar_defs(left_src, r"batchC02700MinusLeftP\d{3}NormUpper2558"))
    vals.update(scalar_defs(right_src, r"batchC02700MinusRightP\d{3}NormUpper2558"))
    vals.update(scalar_defs(fourth_src, r"batchC02700MinusFourthP\d{3}Upper2558"))
    assert len(vals) == 90, len(vals)

    rows = json.loads(
        (ROOT / "results/2338_exact_interpolation_repair.json").read_text())["coefficient_rows"]
    third_agg = Q(0)
    for i, row in enumerate(rows):
        box = row["ideal_base_coefficient"]
        l1 = sum(abs((Q(box[p]["lower_exact"]) + Q(box[p]["upper_exact"])) / 2)
                 for p in ("real", "imag"))
        t = max(vals[f"batchC02700MinusLeftP{i:03d}NormUpper2558"],
                vals[f"batchC02700MinusRightP{i:03d}NormUpper2558"]) \
            + vals[f"batchC02700MinusFourthP{i:03d}Upper2558"] * half
        third_agg += (l1 + Q(1, 10 ** 30)) * t

    mid_upper = Q(377443, 10 ** 8)
    curvature = mid_upper + third_agg * half
    jet1 = Q(1283, 20000000)
    n0l = Q(19793, 10 ** 10)
    n0r = Q(9637, 5 * 10 ** 9)
    sigma = Q(-1, 2)
    pieces = (step * curvature,
              2 * abs(sigma) * (step * (jet1 + curvature * half)),
              sigma ** 2 * (half * (n0l + n0r) + curvature * (step ** 3 / 12)))
    total = sum(pieces)
    scale = 10 ** 12
    bound = Q(ceil(total * scale), scale)
    assert bound >= total
    result = dict(
        record=2565, scope="sigma=-1/2 cell2700 three-piece pricing; external exact arithmetic",
        third_aggregate_l1=str(third_agg), third_aggregate_display=float(third_agg),
        curvature_upper=str(curvature), curvature_display=float(curvature),
        midpoint_jet2_upper=str(mid_upper), first_jet_upper=str(jet1),
        endpoint_left=str(n0l), endpoint_right=str(n0r),
        pieces_display=[float(v) for v in pieces],
        piece_sum_display=float(total), cell_bound=str(bound),
        headroom_ratio=float(bound / total),
        left_source_sha256=hashlib.sha256(
            (ROOT / "ConnesWeilRH/Dev/C1RouteABatchC02700MinusLeftBounds2558.lean").read_bytes()).hexdigest(),
        rh_claim=False, full_grid_certificate=False)
    (ROOT / "results/2565_cell2700_minus_pricing.json").write_text(
        json.dumps(result, indent=2) + "\n")
    print("CELL2700_MINUS_PRICING third_agg", float(third_agg), "curvature", float(curvature),
          "sum", float(total), "bound", bound, "headroom", float(bound / total), flush=True)


if __name__ == "__main__":
    main()
