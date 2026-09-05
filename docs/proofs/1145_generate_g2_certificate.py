"""1145 - emit the kernel-checked grounding machinery for the 1139
checkpoint `q28_certificate_Q` (RED-8 five-module layout).

Files owned by this generator (all byte-stable, deterministic Fractions):

  ConnesWeilRH/Dev/C1ConcreteClassMomentGroundingA.lean
      index-list literal + layer tables 0..17 + groundings 1..17
  ConnesWeilRH/Dev/C1ConcreteClassMomentGroundingB.lean
      layer tables + groundings 18..35
  ConnesWeilRH/Dev/C1ConcreteClassMomentGroundingC.lean
      per-index endpoint/moment values + prefix sums + the four
      comparison_a0/b0/a2/b2_eq consumption theorems
  ConnesWeilRH/Dev/C1ConcreteClassMomentCertificate.lean
      only the checkpoint proof is touched (mark-based restore)

C1ConcreteClassMomentBase.lean holds the moved verbatim def block (created
once by the RED-8 surgery; this generator asserts it exists).  The three
grounding modules each stay under the ~36 GB single-process environment
wall that killed RED-6/RED-7 (swap thrash, ~4e7 major faults): peak
memory per build process is capped by splitting the environment mass.

Kernel facts (measured, v4.30, RED-2..RED-7):
* `List.range` / `List.map` / `if` over closed Nat reduce (simp-viable).
* `Rat` arithmetic does NOT kernel-reduce: closure is simp + norm_num.
* the grounding theorems expose exactly ONE syntactic occurrence of the
  previous cached layer (`show` + delta/zeta) and inline the previous
  table ONCE with `rw` (RED-5 lesson: rewriting inside the unreduced map
  inlines the table at every (k, i) pair - 13320 copies).
* `norm_num [table, ...]` does NOT delta-unfold a plain table constant;
  tables go through an explicit `simp only [table, ...]` step.
* the `k + 2` equation lemmas of endpointAQ/endpointBQ do NOT match
  closed Nat literals under simp; values are grounded through `n + 1 + 1`
  step theorems and per-index bridges.
* shifted indices (`f (n + x)`) are not literalized by simp simprocs
  (RED-6 lesson); the RED-7 prefix-sum functions keep every index direct.
"""
import math
import os
from fractions import Fraction

HERE = os.path.dirname(os.path.abspath(__file__))
DEV = os.path.join(HERE, "..", "..", "ConnesWeilRH", "Dev")
TARGET_CERT = os.path.join(DEV, "C1ConcreteClassMomentCertificate.lean")
TARGET_A = os.path.join(DEV, "C1ConcreteClassMomentGroundingA.lean")
TARGET_B = os.path.join(DEV, "C1ConcreteClassMomentGroundingB.lean")
TARGET_C = os.path.join(DEV, "C1ConcreteClassMomentGroundingC.lean")
TARGET_BASE = os.path.join(DEV, "C1ConcreteClassMomentBase.lean")

# ---------------------------------------------------------------------------
# exact layer values
TC = [Fraction((-2) ** i, 35 ** i) / Fraction(math.factorial(i))
      for i in range(20)]


def conv_layer(prev):
    return [sum((prev[k - i] * TC[i] for i in range(20) if i <= k), Fraction(0))
            for k in range(666)]


LAYERS = {0: [Fraction(1) if k == 0 else Fraction(0) for k in range(666)]}
for _n in range(1, 36):
    LAYERS[_n] = conv_layer(LAYERS[_n - 1])

# ---------------------------------------------------------------------------
# exact endpoint/moment tables (mirror of the module's recursions)
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

# ---------------------------------------------------------------------------
# exact prefix sums over the layer-35 coefficients
COEFF = LAYERS[35]
TERMS = {"endpointA": endpointA, "endpointB": endpointB,
         "momentA": momentA, "momentB": momentB}
PREFIX = {}
for _k, _tv in TERMS.items():
    _p = [Fraction(0)] * 667
    for _j in range(1, 667):
        _p[_j] = _p[_j - 1] + COEFF[_j - 1] * _tv[_j - 1]
    PREFIX[_k] = _p


def rat_lit(v):
    if v.denominator == 1:
        return str(v.numerator)
    sign = "-" if v < 0 else ""
    return f"({sign}{abs(v.numerator)} / {abs(v.denominator)})"


def list_def(name, values):
    body = ",\n    ".join(rat_lit(v) for v in values)
    return (f"-- 1145 generated: exact value of layer {name.split('_')[-1]} "
            f"of the cached convolution (no semantic content).\n"
            f"def {name} : List ℚ :=\n"
            f"  [{body}]\n")


def ground_theorem(n):
    base = n - 1
    inner_base = ("zeroPowerCoefficientListQ" if base == 0
                  else f"powerCoefficientListQ {base}")
    rewrite = ("groundLayer_eq_0" if base == 0 else f"groundLayer_eq_{base}")
    lam = ("(List.range 666).map fun k => ∑ i ∈ Finset.range 20, "
           f"if i ≤ k then listCoeffQ ({inner_base}) (k - i) * "
           "taylorCoefficientQ i else 0")
    return (f"theorem groundLayer_eq_{n} :\n"
            f"    powerCoefficientListQ {n} = groundLayer_{n} := by\n"
            f"  show ({lam}) = groundLayer_{n}\n"
            f"  rw [{rewrite}]\n"
            f"  simp only [range_666_lit, groundLayer_{base}, groundLayer_{n}]\n"
            f"  norm_num (config := {{ maxSteps := 20000000 }})\n"
            f"    [listCoeffQ, taylorCoefficientQ, Finset.sum_range_succ,\n"
            f"    Finset.sum_empty, List.getD_cons_zero, List.getD_cons_succ,\n"
            f"    List.map_cons, List.map_nil]\n")


OPT_BLOCK = ("set_option linter.style.longLine false\n"
             "set_option linter.style.maxHeartbeats false\n"
             "set_option maxRecDepth 1000000\n"
             "-- reason: kernel-checked 666-entry rational list evaluation\n"
             "set_option maxHeartbeats 2000000000\n"
             "-- reason: kernel-checked 666-entry rational list evaluation\n")

LICENSE = ("/-\n"
           "Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.\n"
           "Released under the Apache 2.0 license as described in the file LICENSE.\n"
           "-/\n\n")


def module_scaffold(ns, imports, doc):
    return (LICENSE + "\n".join(imports) + "\n\n/-!\n" + doc + "\n-/\n\n"
            + f"namespace ConnesWeilRH\nnamespace Source\nnamespace {ns}\n\n"
            + "open scoped BigOperators\n\n")


MODULE_END = "\nend\nend {ns}\nend Source\nend ConnesWeilRH\n"


def grounding_a():
    body = [OPT_BLOCK, "\n",
            "-- the index list, literalized once so List.map iota-reduces\n",
            "theorem range_666_lit : (List.range 666 : List Nat) =\n"
            "    [" + ", ".join(str(i) for i in range(666)) + "] := by\n"
            "  decide\n\n",
            list_def("groundLayer_0", LAYERS[0]),
            "theorem groundLayer_eq_0 :\n"
            "    zeroPowerCoefficientListQ = groundLayer_0 := by\n  rfl\n\n"]
    for n in range(1, 18):
        body.append(list_def(f"groundLayer_{n}", LAYERS[n]))
        body.append(ground_theorem(n))
        body.append("\n")
    doc = ("# Record 1145 (RED-8): grounding layers 1-17\n\n"
           "Literal tables for the cached convolution's low layers and their\n"
           "kernel-checked grounding theorems.  Each grounding exposes ONE\n"
           "syntactic occurrence of the previous layer and inlines its table\n"
           "once.  Generated by docs/proofs/1145_generate_g2_certificate.py;\n"
           "rerunning reproduces this file byte-for-byte.  RH NOT claimed.")
    return (module_scaffold("C1ConcreteClassMomentCertificate",
                            ["import ConnesWeilRH.Dev.C1ConcreteClassMomentBase"],
                            doc)
            + "section GroundingLayersA\n" + "".join(body) + "end GroundingLayersA\n"
            + MODULE_END.format(ns="C1ConcreteClassMomentCertificate"))


def grounding_b():
    body = [OPT_BLOCK, "\n"]
    for n in range(18, 36):
        body.append(list_def(f"groundLayer_{n}", LAYERS[n]))
        body.append(ground_theorem(n))
        body.append("\n")
    doc = ("# Record 1145 (RED-8): grounding layers 18-35\n\n"
           "High layers of the cached convolution; groundLayer_eq_35 is the\n"
           "consumption root for the prefix sums.  Generated by\n"
           "docs/proofs/1145_generate_g2_certificate.py; rerunning reproduces\n"
           "this file byte-for-byte.  RH NOT claimed.")
    return (module_scaffold("C1ConcreteClassMomentCertificate",
                            ["import ConnesWeilRH.Dev.C1ConcreteClassMomentBase",
                             "import ConnesWeilRH.Dev.C1ConcreteClassMomentGroundingA"],
                            doc)
            + "section GroundingLayersB\n" + "".join(body) + "end GroundingLayersB\n"
            + MODULE_END.format(ns="C1ConcreteClassMomentCertificate"))


def step_theorem(fn_name, step_name, rhs):
    return (f"theorem {step_name} (n : ℕ) :\n"
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
    fams = (("endpointA", "endpointAQ", endpointA, "rationalRadiusQ"),
            ("endpointB", "endpointBQ", endpointB, "rationalRadiusQ"),
            ("momentA", "momentAQ", momentA, ""),
            ("momentB", "momentBQ", momentB, ""))
    for short, fn_name, vals, extra in fams:
        for j in range(666):
            v = rat_lit(vals[j])
            if j == 0:
                base_lemmas = fn_name
                if extra:
                    base_lemmas += ", " + extra
                parts.append(f"theorem {short}_at_0 : {fn_name} 0 =\n"
                             f"    {v} := by\n"
                             f"  norm_num (config := {{ maxSteps := 20000000 }})\n"
                             f"    [{base_lemmas}]\n\n")
                continue
            if j == 1 and short.startswith("endpoint"):
                parts.append(f"theorem {short}_at_1 : {fn_name} 1 =\n"
                             f"    {v} := by\n  rfl\n\n")
                continue
            if j == 1:
                src = short[-1].upper()
                parts.append(f"theorem {short}_at_1 : {fn_name} 1 =\n"
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
                src = short[-1].upper()
                bridge = (f"  show {fn_name} ({j - 1} + 1) = _\n"
                          f"  rw [{short}_step]\n"
                          f"  rw [endpoint{src}_at_{j}, endpoint{src}_at_{j - 1}]\n")
            tail = ("  norm_num (config := { maxSteps := 20000000 })\n"
                    if not extra else
                    "  norm_num (config := { maxSteps := 20000000 })\n"
                    f"    [{extra}]\n")
            parts.append(f"theorem {short}_at_{j} : {fn_name} {j} =\n"
                         f"    {v} := by\n" + bridge + tail + "\n")
    return "".join(parts)


def prefix_machinery():
    parts = ["-- RED-7 prefix-sum machinery: one tiny declaration per step;\n",
             "-- no shifted indices, no mega-tactic.\n\n"]
    fams = (("endpointA", "endpointAQ", "a0"), ("endpointB", "endpointBQ", "b0"),
            ("momentA", "momentAQ", "a2"), ("momentB", "momentBQ", "b2"))
    for short, fn, cmp_name in fams:
        pre = f"sum{short}pref"
        term = f"listCoeffQ (powerCoefficientListQ 35) k * {fn} k"
        parts.append(f"def {pre} : ℕ → ℚ\n"
                     f"  | 0 => 0\n"
                     f"  | j + 1 =>\n"
                     f"      {pre} j + {term.replace('k', 'j')}\n\n")
        parts.append(f"theorem {pre}_eq (j : ℕ) :\n"
                     f"    (∑ k ∈ Finset.range j, {term}) = {pre} j := by\n"
                     f"  induction j with\n"
                     f"  | zero => simp [{pre}]\n"
                     f"  | succ n ih =>\n"
                     f"      rw [Finset.sum_range_succ, ih]\n"
                     f"      rfl\n\n")
        vals = PREFIX[short]
        parts.append(f"theorem {pre}_at_0 : {pre} 0 = 0 := by rfl\n\n")
        for j in range(1, 667):
            parts.append(f"theorem {pre}_at_{j} : {pre} {j} =\n"
                         f"    {rat_lit(vals[j])} := by\n"
                         f"  show {pre} ({j - 1} + 1) = _\n"
                         f"  rw [{pre}, {pre}_at_{j - 1}]\n"
                         f"  simp only [groundLayer_eq_35, groundLayer_35,\n"
                         f"    listCoeffQ, List.getD_cons_zero,\n"
                         f"    List.getD_cons_succ, {short}_at_{j - 1}]\n"
                         f"  norm_num (config := {{ maxSteps := 20000000 }})\n\n")
        cmp_lit = rat_lit(vals[666])
        parts.append(f"theorem comparison_{cmp_name}_eq :\n"
                     f"    (∑ k ∈ Finset.range 666, {term}) = {cmp_lit} := by\n"
                     f"  rw [{pre}_eq, {pre}_at_666]\n\n")
    return "".join(parts)


def grounding_c():
    doc = ("# Record 1145 (RED-8): per-index values, prefix sums, comparisons\n\n"
           "The endpoint/moment recursions are grounded per index (their\n"
           "`k + 2` equation lemmas do not match closed Nat literals), the\n"
           "four comparison sums are grounded as prefix-sum functions (one\n"
           "tiny declaration per step - no mega-tactic), and the consumption\n"
           "theorems comparison_a0/b0/a2/b2_eq feed the 1139 checkpoint.\n"
           "Generated by docs/proofs/1145_generate_g2_certificate.py; the\n"
           "file is byte-stable.  RH NOT claimed.")
    return (module_scaffold("C1ConcreteClassMomentCertificate",
                            ["import ConnesWeilRH.Dev.C1ConcreteClassMomentBase",
                             "import ConnesWeilRH.Dev.C1ConcreteClassMomentGroundingB"],
                            doc)
            + OPT_BLOCK + "\n"
            + per_index_theorems() + prefix_machinery()
            + MODULE_END.format(ns="C1ConcreteClassMomentCertificate"))


def proof_body():
    return ("  simp only [comparisonDataQ]\n"
            "  rw [comparison_a0_eq, comparison_b0_eq, comparison_a2_eq,\n"
            "    comparison_b2_eq]\n"
            "  norm_num (config := { maxSteps := 20000000 })\n")


ANCHOR = ("set_option maxRecDepth 1000000 in\n"
          "set_option maxHeartbeats 2000000000 in")
OLD_BODY = "  native_decide"


def splice_certificate(text):
    # structural restore of ANY previously generated checkpoint body: it
    # starts at the h35 have-line (RED-5/6) or at the comparisonDataQ simp
    # (RED-7+), and ends at the trailing norm_num line.
    for mark, endmark in (("  have h35 := groundLayer_eq_35\n",
                           "  norm_num (config := { maxSteps := 20000000 })\n"),
                          ("  simp only [comparisonDataQ]\n",
                           "  norm_num (config := { maxSteps := 20000000 })\n")):
        if mark in text:
            start = text.index(mark)
            end = text.index(endmark, start) + len(endmark)
            text = text[:start] + OLD_BODY + "\n" + text[end:]
            break
    for old in [
        "  have h35 := groundLayer_eq_35\n"
        "  simp only [comparisonDataQ, h35, listCoeffQ, Finset.sum_range_succ,\n"
        "    Finset.sum_empty, List.getD_cons_zero, List.getD_cons_succ,\n"
        "    endpointAQ, endpointBQ, momentAQ, momentBQ, taylorCoefficientQ]\n"
        "  norm_num",
        "  have h35 := groundLayer_eq_35\n"
        "  simp only [comparisonDataQ, h35, listCoeffQ, Finset.sum_range_succ,\n"
        "    Finset.sum_empty]\n"
        "  norm_num [endpointAQ, endpointBQ, momentAQ, momentBQ, taylorCoefficientQ,\n"
        "    rationalRadiusQ, groundLayer_35]",
    ]:
        if old in text:
            text = text.replace(old, OLD_BODY)
    assert text.count(OLD_BODY) == 1, "checkpoint proof slot not unique"
    return text.replace(OLD_BODY, proof_body())


def write_stable(path, content):
    old = None
    if os.path.exists(path):
        with open(path, "r", encoding="utf-8") as f:
            old = f.read()
    with open(path, "w", encoding="utf-8", newline="\n") as f:
        f.write(content)
    return old == content


def main():
    # sanity (prereg section 3): the five checkpoint conjuncts must hold on
    # the exact prefix-sum values BEFORE any splicing or building.
    a0 = PREFIX["endpointA"][666]
    b0 = PREFIX["endpointB"][666]
    a2 = PREFIX["momentA"][666]
    b2 = PREFIX["momentB"][666]
    log_lo = Fraction(41845914400698788, 10 ** 16)
    log_hi = Fraction(41845914400698789, 10 ** 16)
    central = 2 * R * (70 * (Fraction(21) / (Fraction(math.factorial(20)) * 20)))
    tail = Fraction(1, 10 ** 16)
    m0 = Fraction(2397466416982805, 18014398509481984)
    m2 = Fraction(8817094793947821, 576460752303423488)
    assert m0 - Fraction(1, 10 ** 15) + central <= a0 + b0 * log_hi
    assert a0 + b0 * log_lo + central + 2 * tail <= m0 + Fraction(1, 10 ** 15)
    assert m2 - Fraction(1, 10 ** 15) + central <= a2 + b2 * log_hi
    assert a2 + b2 * log_lo + central + 2 * tail <= m2 + Fraction(1, 10 ** 15)
    assert b0 < 0 and b2 < 0
    assert os.path.exists(TARGET_BASE), "Base module missing (RED-8 surgery not run)"
    with open(TARGET_CERT, "r", encoding="utf-8") as f:
        cert = f.read()
    changed = [write_stable(TARGET_A, grounding_a()),
               write_stable(TARGET_B, grounding_b()),
               write_stable(TARGET_C, grounding_c())]
    new_cert = splice_certificate(cert)
    changed.append(new_cert == cert)
    with open(TARGET_CERT, "w", encoding="utf-8", newline="\n") as f:
        f.write(new_cert)
    print("spliced; A/B/C changed:", changed[:3], "| cert unchanged:", changed[3])
    print("a0 ~", float(a0), " b0 ~", float(b0), " a2 ~", float(a2),
          " b2 ~", float(b2))


if __name__ == "__main__":
    main()
