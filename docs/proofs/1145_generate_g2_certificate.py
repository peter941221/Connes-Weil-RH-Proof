"""1145 - emit the kernel-checked grounding block and the replacement proof
for the 1139 checkpoint `q28_certificate_Q` (Dev/
C1ConcreteClassMomentCertificate.lean).  Sole input: the module itself;
sole effect: (i) insert the BEGIN/END-1145-GENERATED region (the layer-0
bridge, all 35 literal layer tables, and their period-1 grounding
theorems) before the checkpoint, (ii) replace the `native_decide` proof
body with the layered-grounding proof.  Rerunning is idempotent and
byte-stable (deterministic Fractions).  Pure stdlib.  RH NOT claimed.

Kernel facts this emission relies on (measured, v4.30, RED-2..RED-6):
* `List.range` / `List.map` / `if` over closed Nat reduce (simp-viable at
  666 entries with raised maxRecDepth, no Rat arithmetic involved).
* `Rat` arithmetic does NOT reduce in the kernel (gcd is well-founded):
  every closure with rational arithmetic must be simp + norm_num, whose
  proof terms carry only structural Nat-level checks.
* denominators equal to 1 are emitted as bare numerals so the layer-0
  grounding stays a plain rfl.
* The grounding theorems expose exactly ONE syntactic occurrence of the
  previous cached layer (via `show` + delta/zeta) and inline the previous
  table ONCE with `rw`.  Rewriting inside the un-reduced map would inline
  the table at every (k, i) pair - 13320 copies - which is the RED-5
  `simp` step explosion.
* `norm_num [table, ...]` does NOT delta-unfold a plain table constant;
  the tables must go through an explicit `simp only [table, ...]` step
  (measured RED-6 scratch: the final `literals = table` goal stays open
  otherwise)."""
import math
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
TARGET = os.path.join(HERE, "..", "..", "ConnesWeilRH", "Dev",
                      "C1ConcreteClassMomentCertificate.lean")

TC = [Fraction((-2) ** i, 35 ** i) / Fraction(math.factorial(i))
      for i in range(20)]


def conv_layer(prev):
    return [sum((prev[k - i] * TC[i] for i in range(20) if i <= k), Fraction(0))
            for k in range(666)]


LAYERS = {0: [Fraction(1) if k == 0 else Fraction(0) for k in range(666)]}
for _n in range(1, 36):
    LAYERS[_n] = conv_layer(LAYERS[_n - 1])

GROUND = list(range(1, 36))

# ---------------------------------------------------------------------------
# exact endpoint/moment tables (mirror of the module's recursions, computed
# with Fractions).  endpointAQ/endpointBQ recurse on `k + 2`, whose equation
# lemma does NOT match closed Nat literals under simp (measured RED-6: no
# progress); the emission therefore bridges through `n + 1 + 1`-arity step
# theorems and per-index value theorems chained bottom-up.
R = Fraction(97, 100)

endpointA = [Fraction(0)] * 666
endpointA[0] = 2 * R
endpointB = [Fraction(0)] * 666
endpointB[1] = Fraction(1)
for _j in range(2, 666):
    _m = _j - 2
    _c = Fraction(2 * _m + 1, 2 * (_m + 1))
    _env = R / (Fraction(_m + 1) * (1 - R * R) ** (_m + 1))
    endpointA[_j] = _env + _c * endpointA[_j - 1]
    endpointB[_j] = _c * endpointB[_j - 1]

momentA = [Fraction(0)] * 666
momentA[0] = 2 * R ** 3 / 3
momentB = [Fraction(0)] * 666
for _j in range(1, 666):
    momentA[_j] = endpointA[_j] - endpointA[_j - 1]
    momentB[_j] = endpointB[_j] - endpointB[_j - 1]


def step_theorem(fn_name, step_name, rhs):
    return (f"private theorem {step_name} (n : ℕ) :\n"
            f"    {fn_name} (n + 1 + 1) = {rhs} := by\n"
            f"  rw [{fn_name}]\n\n")


PER_INDEX_STEPS = (
    step_theorem("endpointAQ", "endpointAQ_step",
                 "rationalRadiusQ /\n"
                 "        (((n : ℚ) + 1) * (1 - rationalRadiusQ ^ 2) ^ (n + 1)) +\n"
                 "      ((2 * (n : ℚ) + 1) / (2 * ((n : ℚ) + 1))) *\n"
                 "        endpointAQ (n + 1)")
    + step_theorem("endpointBQ", "endpointBQ_step",
                   "((2 * (n : ℚ) + 1) / (2 * ((n : ℚ) + 1))) *\n"
                   "        endpointBQ (n + 1)")
    + step_theorem("momentAQ", "momentAQ_step",
                   "endpointAQ (n + 1) - endpointAQ n")
    + step_theorem("momentBQ", "momentBQ_step",
                   "endpointBQ (n + 1) - endpointBQ n")
)


def per_index_theorems():
    parts = ["-- per-index value theorems: `k + 2` equation lemmas do not match\n",
             "-- closed Nat literals under simp, so each index is grounded\n",
             "-- through the step theorem with an explicit `n + 1 + 1` bridge.\n\n"]
    parts.append(PER_INDEX_STEPS)
    fams = [("endpointAQ", "endpointA", endpointA, "rationalRadiusQ"),
            ("endpointBQ", "endpointB", endpointB, "rationalRadiusQ"),
            ("momentAQ", "momentA", momentA, ""),
            ("momentBQ", "momentB", momentB, "")]
    for fn_name, short, vals, extra in fams:
        for j in range(666):
            v = rat_lit(vals[j])
            if j == 0:
                base_lemmas = fn_name
                if short in ("endpointA", "momentA"):
                    base_lemmas += ", rationalRadiusQ"
                parts.append(f"private theorem {short}_at_0 : {fn_name} 0 =\n"
                             f"    {v} := by\n"
                             f"  norm_num (config := {{ maxSteps := 20000000 }})\n"
                             f"    [{base_lemmas}]\n\n")
                continue
            if j == 1 and short.startswith("endpoint"):
                parts.append(f"private theorem {short}_at_1 : {fn_name} 1 =\n"
                             f"    {v} := by\n  rfl\n\n")
                continue
            if j == 1:
                src = short[-1].upper()
                parts.append(f"private theorem {short}_at_1 : {fn_name} 1 =\n"
                             f"    {v} := by\n"
                             f"  show {fn_name} (0 + 1) = _\n"
                             f"  rw [{short}_step]\n"
                             f"  rw [endpoint{src}_at_1, endpoint{src}_at_0]\n"
                             f"  norm_num (config := {{ maxSteps := 20000000 }})\n\n")
                continue
            if short.startswith("endpoint"):
                bridge = (f"  show {fn_name} ({j - 2} + 1 + 1) = _\n"
                          f"  rw [{short}_step]\n"
                          f"  rw [{short}_at_{j - 1}]\n")
            else:
                src = short[-1].upper()  # endpointA / endpointB source family
                bridge = (f"  show {fn_name} ({j - 1} + 1) = _\n"
                          f"  rw [{short}_step]\n"
                          f"  rw [endpoint{src}_at_{j}, endpoint{src}_at_{j - 1}]\n")
            tail = ("  norm_num (config := { maxSteps := 20000000 })\n"
                    if not extra else
                    "  norm_num (config := { maxSteps := 20000000 })\n"
                    f"    [{extra}]\n")
            parts.append(f"private theorem {short}_at_{j} : {fn_name} {j} =\n"
                         f"    {v} := by\n" + bridge + tail + "\n")
    return "".join(parts)


def rat_lit(v):
    if v.denominator == 1:
        return str(v.numerator)
    sign = "-" if v < 0 else ""
    return f"({sign}{abs(v.numerator)} / {abs(v.denominator)})"


def list_def(name, values):
    body = ",\n    ".join(rat_lit(v) for v in values)
    return (f"-- 1145 generated: exact value of layer {name.split('_')[-1]} "
            f"of the cached convolution (no semantic content).\n"
            f"private def {name} : List ℚ :=\n"
            f"  [{body}]\n")


def ground_theorem(n):
    base = n - 1
    inner_base = ("zeroPowerCoefficientListQ" if base == 0
                  else f"powerCoefficientListQ {base}")
    rewrite = ("groundLayer_eq_0" if base == 0 else f"groundLayer_eq_{base}")
    lam = ("(List.range 666).map fun k => ∑ i ∈ Finset.range 20, "
           f"if i ≤ k then listCoeffQ ({inner_base}) (k - i) * "
           "taylorCoefficientQ i else 0")
    stmt = (f"private theorem groundLayer_eq_{n} :\n"
            f"    powerCoefficientListQ {n} = groundLayer_{n} := by\n"
            f"  show ({lam}) = groundLayer_{n}\n"
            f"  rw [{rewrite}]\n"
            f"  simp only [range_666_lit, groundLayer_{base}, groundLayer_{n}]\n"
            f"  norm_num (config := {{ maxSteps := 20000000 }})\n"
            f"    [listCoeffQ, taylorCoefficientQ, Finset.sum_range_succ,\n"
            f"    Finset.sum_empty, List.getD_cons_zero, List.getD_cons_succ,\n"
            f"    List.map_cons, List.map_nil]\n")
    return stmt


def generated_block():
    range_lit = ", ".join(str(i) for i in range(666))
    parts = ["-- BEGIN 1145 GENERATED (docs/proofs/1145_generate_g2_certificate.py;\n",
             "-- rerunning the generator reproduces this region byte-for-byte).\n",
             "section GroundingLayers1145\n",
             "set_option linter.style.longLine false\n",
             "set_option linter.style.maxHeartbeats false\n",
             "set_option maxRecDepth 1000000\n",
             "-- reason: kernel-checked 666-entry rational list evaluation\n",
             "set_option maxHeartbeats 2000000000\n",
             "-- reason: kernel-checked 666-entry rational list evaluation\n\n",
             "-- the index list, literalized once so List.map iota-reduces\n",
             f"private theorem range_666_lit : (List.range 666 : List Nat) =\n"
             f"    [{range_lit}] := by\n  decide\n\n",
             list_def("groundLayer_0", LAYERS[0]),
             "private theorem groundLayer_eq_0 :\n"
             "    zeroPowerCoefficientListQ = groundLayer_0 := by\n  rfl\n\n"]
    for n in GROUND:
        parts.append(list_def(f"groundLayer_{n}", LAYERS[n]))
        parts.append(ground_theorem(n))
        parts.append("\n")
    parts.append(per_index_theorems())
    parts.append("end GroundingLayers1145\n")
    parts.append("-- END 1145 GENERATED\n")
    return "".join(parts)


def proof_body():
    names = ["comparisonDataQ", "h35", "groundLayer_35", "listCoeffQ",
             "Finset.sum_range_succ", "Finset.sum_empty",
             "List.getD_cons_zero", "List.getD_cons_succ"]
    for short in ("endpointA", "endpointB", "momentA", "momentB"):
        names.extend(f"{short}_at_{j}" for j in range(666))
    lines = []
    cur = "  simp (config := { maxSteps := 20000000 }) only ["
    for nm in names:
        if len(cur) + len(nm) + 2 > 96:
            lines.append(cur.rstrip())
            cur = "    "
        cur += nm + ", "
    lines.append(cur.rstrip(", ") + "]")
    lines.append("  norm_num (config := { maxSteps := 20000000 })")
    return "  have h35 := groundLayer_eq_35\n" + "\n".join(lines) + "\n"

ANCHOR = ("set_option maxRecDepth 1000000 in\n"
          "set_option maxHeartbeats 2000000000 in")
OLD_BODY = "  native_decide"

# previously emitted checkpoint-proof variants (idempotent regeneration)
OLD_PROOF_BODIES = [
    # RED-5 variant (even-layer grounding, simp-only closure)
    "  have h35 := groundLayer_eq_35\n"
    "  simp only [comparisonDataQ, h35, listCoeffQ, Finset.sum_range_succ,\n"
    "    Finset.sum_empty, List.getD_cons_zero, List.getD_cons_succ,\n"
    "    endpointAQ, endpointBQ, momentAQ, momentBQ, taylorCoefficientQ]\n"
    "  norm_num",
    # RED-4 variant (norm_num with explicit lemma list)
    "  have h35 := groundLayer_eq_35\n"
    "  simp only [comparisonDataQ, h35, listCoeffQ, Finset.sum_range_succ,\n"
    "    Finset.sum_empty]\n"
    "  norm_num [endpointAQ, endpointBQ, momentAQ, momentBQ, taylorCoefficientQ,\n"
    "    rationalRadiusQ, groundLayer_35]",
    # RED-6 v1 variant (endpoint unfolding by name; dead: the k+2 equation
    # lemma does not match closed Nat literals)
    "  have h35 := groundLayer_eq_35\n"
    "  simp (config := { maxSteps := 20000000 }) only [comparisonDataQ, h35,\n"
    "    groundLayer_35, listCoeffQ, Finset.sum_range_succ, Finset.sum_empty,\n"
    "    List.getD_cons_zero, List.getD_cons_succ, endpointAQ, endpointBQ,\n"
    "    momentAQ, momentBQ, taylorCoefficientQ]\n"
    "  norm_num (config := { maxSteps := 20000000 })",
]


def strip_previous(text):
    begin = "-- BEGIN 1145 GENERATED"
    end = "-- END 1145 GENERATED"
    if begin in text:
        a = text.index(begin)
        b = text.index(end) + len(end)
        if text[b:b + 1] == "\n":
            b += 1
        text = text[:a] + text[b:]
    return text


def splice(text):
    text = strip_previous(text)
    for old in OLD_PROOF_BODIES:
        if old in text:
            text = text.replace(old, OLD_BODY)
    assert text.count(ANCHOR) == 1, "checkpoint anchor not unique"
    text = text.replace(ANCHOR, generated_block() + ANCHOR)
    body = proof_body()
    if body not in text:
        assert text.count(OLD_BODY) == 1, "native_decide body not unique"
        text = text.replace(OLD_BODY, body)
    return text


def main():
    with open(TARGET, "r", encoding="utf-8") as f:
        text = f.read()
    out = splice(text)
    with open(TARGET, "w", encoding="utf-8", newline="\n") as f:
        f.write(out)
    print("spliced; file bytes:", len(out))


if __name__ == "__main__":
    main()
