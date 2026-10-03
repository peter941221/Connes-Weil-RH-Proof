"""Exact rounded-Horner/squaring witnesses for the first positive grid node."""
import argparse
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"
NODE = Q(65536001, 51200000000)
ROUND = Q(1, 2**99)


def integer(value):
    if value < 0:
        return f"(-{integer(-value)})"
    high, low = divmod(value, 10**40)
    if not high:
        return str(value)
    return f"({integer(high)} * 10^40\n        + {low})"


def add(a, b):
    return a[0]+b[0], a[1]+b[1]


def mul(a, b):
    return a[0]*b[0]-a[1]*b[1], a[0]*b[1]+a[1]*b[0]


def scale(a, q):
    return a[0]*q, a[1]*q


def rounded(a):
    return tuple(Q((q*2**100).numerator//(q*2**100).denominator, 2**100) for q in a)


def up(q):
    q *= 2**140
    return Q(-((-q.numerator)//q.denominator), 2**140)


def real(q):
    q = Q(q)
    if q.denominator == 1:
        return f"({integer(q.numerator)} : ℝ)"
    return f"(({integer(q.numerator)} : ℝ) /\n        {integer(q.denominator)})"


def pair(z):
    return f"⟨{real(z[0])},\n    {real(z[1])}⟩"


def witness(index):
    data = json.loads(CAPTURE.read_text(encoding="utf-8"))["owner_capture"]["families_hex"]
    width, theta = (Q.from_float(float.fromhex(s)) for s in data[index])
    radius = width**2
    assert abs(NODE) < radius
    exponent = (NODE/2 - 30/(1-(NODE/radius)**2), theta*NODE)
    z = scale(exponent, Q(1, 64))
    assert abs(z[0])+abs(z[1]) <= 1
    horner = [(Q(1), Q(0))]
    for k in range(19, 0, -1):
        exact = add((Q(1), Q(0)), mul(scale(z, Q(1, k)), horner[-1]))
        p = rounded(exact)
        assert sum(abs(a-b) for a,b in zip(exact,p)) <= ROUND
        horner.append(p)
    squares = [horner[-1]]
    errors = [Q(1, 10**18)+19*ROUND]
    magnitudes = []
    for _ in range(6):
        magnitude = sum(abs(x) for x in squares[-1])
        exact = mul(squares[-1], squares[-1])
        center = rounded(exact)
        assert sum(abs(a-b) for a,b in zip(exact,center)) <= ROUND
        errors.append(up(errors[-1]*(2*magnitude+errors[-1])+ROUND))
        magnitudes.append(magnitude)
        squares.append(center)
    return z, horner, squares, errors, magnitudes


def render(index):
    z, horner, squares, errors, magnitudes = witness(index)
    tag = f"P{index:03d}"
    zname, hname, sname, ename = (f"node{kind}{tag}2541" for kind in ("Z", "H", "S", "E"))
    lines = ["import ConnesWeilRH.Dev.C1RouteAComplexExpBall2541", "",
             "/-! Generated exact arithmetic witness for sigma=1/2 and node 5121/10240.",
             "Source: results/2275_gap_owner_audit.json",
             "SHA256: " + hashlib.sha256(CAPTURE.read_bytes()).hexdigest(), "-/", "",
             "namespace ConnesWeilRH.Dev", "",
             f"noncomputable def {zname} : ℂ :=", f"  {pair(z)}", ""]
    for name, values in ((hname, horner), (sname, squares)):
        lines.append(f"noncomputable def {name} : ℕ → ℂ")
        for n, value in enumerate(values):
            lines.extend([f"  | {n} =>", f"    {pair(value)}"])
        lines.extend(["  | _ => 0", ""])
    lines.append(f"noncomputable def {ename} : ℕ → ℝ")
    lines.extend(f"  | {n} => {real(e)}" for n,e in enumerate(errors))
    lines.extend(["  | _ => 0", "", f"theorem nodeExp{tag}_error2541 :",
                  f"    ‖Complex.exp ((2 : ℂ)^6 * {zname}) - {sname} 6‖ ≤ {ename} 6 := by",
                  f"  have hz : ‖{zname}‖ ≤ 1 := by",
                  "    apply complex_norm_le_l1_2541", f"    norm_num [{zname}]",
                  f"  have h0 : ‖expHorner2541 {zname} 0 - {hname} 0‖ ≤ (0 : ℝ) := by",
                  "    change ‖(1 : ℂ) - 1‖ ≤ 0",
                  "    norm_num"])
    for n in range(19):
        lines.extend([
            f"  have h{n+1} : ‖expHorner2541 {zname} {n+1} - {hname} {n+1}‖ ≤",
            f"      {real((n+1)*ROUND)} := by",
            f"    have h := horner_ball_step2541 {zname} ({hname} {n}) ({hname} {n+1}) {n}",
            f"      {real(n*ROUND)} {real(ROUND)} (by norm_num) hz h{n}",
            "      (by",
            "        apply complex_norm_le_l1_2541",
            f"        norm_num [{zname}, {hname}, Complex.mul_re, Complex.mul_im])",
            "    exact h.trans (by norm_num)"])
    lines.extend([
        f"  have s0 : ‖Complex.exp ((2 : ℂ)^0 * {zname}) - {sname} 0‖ ≤ {ename} 0 := by",
        f"    have h := exp_ball_of_horner2541 {zname} ({hname} 19) {real(19*ROUND)} hz h19",
        f"    convert h using 1 <;> norm_num [{hname}, {sname}, {ename}]"])
    for k in range(6):
        lines.extend([
            f"  have s{k+1} : ‖Complex.exp ((2 : ℂ)^{k+1} * {zname}) - {sname} {k+1}‖ ≤",
            f"      {ename} {k+1} := by",
            f"    have h := exp_scaled_square_ball2541 {zname} ({sname} {k}) ({sname} {k+1}) {k}",
            f"      ({ename} {k}) {real(magnitudes[k])} {real(ROUND)} s{k}",
            "      (by",
            "        apply complex_norm_le_l1_2541",
            f"        norm_num [{sname}])",
            "      (by",
            "        apply complex_norm_le_l1_2541",
            f"        norm_num [{sname}, pow_two, Complex.mul_re, Complex.mul_im])",
            f"    exact h.trans (by norm_num [{ename}])"])
    lines.extend(["  exact s6", "", "end ConnesWeilRH.Dev", ""])
    return "\n".join(lines)


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--families", type=int, choices=range(1,31), default=1)
    parser.add_argument("--check", action="store_true")
    args = parser.parse_args()
    for index in range(args.families):
        path = ROOT/f"ConnesWeilRH/Dev/C1RouteAExpNode2541P{index:03d}.lean"
        expected = render(index)
        if args.check:
            assert path.read_text(encoding="utf-8") == expected
        else:
            path.write_text(expected, encoding="utf-8", newline="\n")
        print(index, "final error", float(witness(index)[3][-1]), flush=True)


if __name__ == "__main__":
    main()
