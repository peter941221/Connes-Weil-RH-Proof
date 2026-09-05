"""1145 - emit the kernel-checked grounding machinery for the 1139
checkpoint `q28_certificate_Q` (RED-9 integer lifting).

Files owned by this generator (all byte-stable, deterministic):

  ConnesWeilRH/Dev/C1ConcreteClassMomentGroundingA.lean
      zCoeff + zLayerList defs, integer tables zTable_0..17, rfl
      groundings 1..17, range_666_lit
  ConnesWeilRH/Dev/C1ConcreteClassMomentGroundingB.lean
      integer tables zTable_18..35 + rfl groundings 18..35
  ConnesWeilRH/Dev/C1ConcreteClassMomentGroundingC.lean
      bigQ + factorial-exactness + the symbolic Rat bridge
      listCoeff_eq_zDiv + per-index endpoint/moment values + prefix
      sums (coeff fed through the bridge) + the four
      comparison_a0/b0/a2/b2_eq consumption theorems
  ConnesWeilRH/Dev/C1ConcreteClassMomentCertificate.lean
      only the checkpoint proof is touched (mark-based restore)

C1ConcreteClassMomentBase.lean holds the moved verbatim def block (created
once by the RED-8 surgery; this generator asserts it exists).

WHY integer lifting (prereg addendum 5): three memory walls (RED-6/7/8d)
isolated the mass as Rat gcd-normalization PROOF TERMS - 666 entries x
20 products x layers, split-invariant, 34.5 GB for layers 0-17 alone.
Nat/Int literal arithmetic IS kernel-reducible (GMP-backed), so every
layer grounding closes by `rfl` after the established show-bridge +
single `rw` inlines the previous LITERAL table: near-zero proof mass,
seconds of evaluation.  The only Rat content is the fully symbolic
bridge theorem listCoeff_eq_zDiv, over Q = 35^19 * 19!:

    listCoeffQ (powerCoefficientListQ m) k
      = (getD (zLayerList m) k 0 : Rat) / Q^m

Kernel facts (measured, v4.30, RED-2..RED-8):
* `List.range` / `List.map` / `if` over closed Nat reduce.
* Nat/Int literal arithmetic and List.getD on literal lists reduce in
  the kernel; `rfl` closes the 666-entry integer list equalities.
* `Rat` arithmetic does NOT kernel-reduce: the Rat sums still close by
  simp + norm_num, one tiny declaration per prefix step (RED-7 design).
* the grounding theorems expose exactly ONE syntactic occurrence of the
  previous cached layer (`show` + delta/zeta) and inline the previous
  table ONCE with `rw` (RED-5 lesson).
* the `k + 2` equation lemmas of endpointAQ/endpointBQ do NOT match
  closed Nat literals under simp; values are grounded through `n + 1 + 1`
  step theorems and per-index bridges.
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
# exact layer values (Fraction) and their integer lift over Q = 35^19 * 19!
TC = [Fraction((-2) ** i, 35 ** i) / Fraction(math.factorial(i))
      for i in range(20)]


def conv_layer(prev):
    return [sum((prev[k - i] * TC[i] for i in range(20) if i <= k), Fraction(0))
            for k in range(666)]


LAYERS = {0: [Fraction(1) if k == 0 else 0 for k in range(666)]}
for _n in range(1, 36):
    LAYERS[_n] = conv_layer(LAYERS[_n - 1])

Q = 35 ** 19 * math.factorial(19)
ZC = [(-2) ** i * 35 ** (19 - i) * (math.factorial(19) // math.factorial(i))
      for i in range(20)]

ZLAYERS = {0: [1 if k == 0 else 0 for k in range(666)]}
_QPOW = {0: 1}
for _n in range(1, 36):
    _prev = ZLAYERS[_n - 1]
    ZLAYERS[_n] = [sum((_prev[k - i] * ZC[i] for i in range(20) if i <= k), 0)
                   for k in range(666)]
    _QPOW[_n] = _QPOW[_n - 1] * Q

# lifting cross-check: layer n (k) == Z(n, k) / Q^n for EVERY entry
for _n in range(36):
    for _k in range(666):
        assert Fraction(ZLAYERS[_n][_k], _QPOW[_n]) == LAYERS[_n][_k], (_n, _k)

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


def int_lit(v):
    return str(v)


def zlist_def(name, values):
    body = ",\n    ".join(int_lit(v) for v in values)
    n = name.split("_")[-1]
    return (f"-- 1145 generated: Z({n}, k) = layer {n} (k) * Q^{n} of the\n"
            f"-- cached convolution, Q = 35^19 * 19! (no semantic content).\n"
            f"def {name} : List ℤ :=\n"
            f"  [{body}]\n")


def ground_theorem(n):
    base = n - 1
    lam = ("(List.range 666).map fun k => ∑ i ∈ Finset.range 20, "
           "if i ≤ k then List.getD (zLayerList "
           f"{base}) (k - i) 0 * zCoeff i else 0")
    return (f"theorem zGround_eq_{n} :\n"
            f"    zLayerList {n} = zTable_{n} := by\n"
            f"  show ({lam}) = zTable_{n}\n"
            f"  rw [zGround_eq_{base}]\n"
            f"  rfl\n\n")


OPT_BLOCK = ("set_option linter.style.longLine false\n"
             "set_option linter.style.setOption false\n"
             "set_option maxRecDepth 1000000\n"
             "set_option maxHeartbeats 2000000000\n\n")

LICENSE = ("/-\n"
           "Copyright (c) 2026 ConnesWeilRH contributors. All rights reserved.\n"
           "Released under the Apache 2.0 license as described in the file LICENSE.\n"
           "-/\n\n")


def module_scaffold(ns, imports, doc):
    return (LICENSE + "\n".join(imports) + "\n\n/-!\n" + doc + "\n-/\n\n"
            + f"namespace ConnesWeilRH\nnamespace Source\nnamespace {ns}\n\n"
            + "open scoped BigOperators\n\n")


MODULE_END = "\nend {ns}\nend Source\nend ConnesWeilRH\n"


def grounding_a():
    body = [OPT_BLOCK, "\n",
            "-- the index list, literalized once so List.map iota-reduces\n",
            "theorem range_666_lit : (List.range 666 : List Nat) =\n"
            "    [" + ", ".join(str(i) for i in range(666)) + "] := by\n"
            "  decide\n\n",
            "-- the integer lift of the Taylor coefficients over\n",
            "-- Q = 35^19 * 19!:  taylorCoefficientQ i = zCoeff i / Q.\n",
            "def zCoeff (i : ℕ) : ℤ :=\n"
            "  (-2 : ℤ) ^ i * (35 : ℤ) ^ (19 - i) *\n"
            "    ((Nat.factorial 19 / i.factorial : ℕ) : ℤ)\n\n",
            "-- the same convolution as powerCoefficientListQ, in integers:\n",
            "-- layer m (k) * Q^m.  Only its PER-LAYER literal values are\n",
            "-- ever forced (one step at a time via the groundings below).\n",
            "def zLayerList : ℕ → List ℤ\n"
            "  | 0 => (List.range 666).map fun k => if k = 0 then 1 else 0\n"
            "  | m + 1 =>\n"
            "      (List.range 666).map fun k => ∑ i ∈ Finset.range 20,\n"
            "        if i ≤ k then List.getD (zLayerList m) (k - i) 0 *\n"
            "          zCoeff i else 0\n\n"]
    body.append(zlist_def("zTable_0", ZLAYERS[0]))
    body.append("theorem zGround_eq_0 :\n"
                "    zLayerList 0 = zTable_0 := by\n  rfl\n\n")
    for n in range(1, 18):
        body.append(zlist_def(f"zTable_{n}", ZLAYERS[n]))
        body.append(ground_theorem(n))
    doc = ("# Record 1145 (RED-9): integer grounding layers 0-17\n\n"
           "The integer lift of the cached convolution: zCoeff, zLayerList,\n"
           "literal tables Z(n, k) = layer n (k) * Q^n for n ≤ 17, and their\n"
           "kernel-checked groundings (closed by `rfl`: Nat/Int literal\n"
           "arithmetic is GMP-backed and kernel-reducible, unlike Rat).\n"
           "Generated by docs/proofs/1145_generate_g2_certificate.py;\n"
           "rerunning reproduces this file byte-for-byte.  RH NOT claimed.")
    return (module_scaffold("C1ConcreteClassMomentCertificate",
                            ["import ConnesWeilRH.Dev.C1ConcreteClassMomentBase"],
                            doc)
            + "section GroundingLayersA\n" + "".join(body) + "end GroundingLayersA\n"
            + MODULE_END.format(ns="C1ConcreteClassMomentCertificate"))


def grounding_b():
    body = [OPT_BLOCK, "\n"]
    for n in range(18, 36):
        body.append(zlist_def(f"zTable_{n}", ZLAYERS[n]))
        body.append(ground_theorem(n))
    doc = ("# Record 1145 (RED-9): integer grounding layers 18-35\n\n"
           "High layers of the integer lift; zGround_eq_35 is the\n"
           "consumption root for the Rat bridge and the prefix sums.\n"
           "Generated by docs/proofs/1145_generate_g2_certificate.py;\n"
           "rerunning reproduces this file byte-for-byte.  RH NOT claimed.")
    return (module_scaffold("C1ConcreteClassMomentCertificate",
                            ["import ConnesWeilRH.Dev.C1ConcreteClassMomentBase",
                             "import ConnesWeilRH.Dev.C1ConcreteClassMomentGroundingA"],
                            doc)
            + "section GroundingLayersB\n" + "".join(body) + "end GroundingLayersB\n"
            + MODULE_END.format(ns="C1ConcreteClassMomentCertificate"))


BRIDGE_MACHINERY = (
    "-- RED-9 bridge: the frozen Rat definition equals the integer lift\n"
    "-- divided by Q^m.  Fully symbolic (no bignum content).\n\n"
    "def bigQ : ℕ := 35 ^ 19 * Nat.factorial 19\n\n"
    "theorem bigQ_pos : 0 < bigQ :=\n"
    "  Nat.mul_pos (by positivity) (Nat.factorial_pos 19)\n\n"
    "theorem taylorCoefficientQ_mul_bigQ_eq_zCoeff (i : ℕ) (hi : i < 20) :\n"
    "    taylorCoefficientQ i * (bigQ : ℚ) = (zCoeff i : ℚ) := by\n"
    "  have hdvd : i.factorial ∣ Nat.factorial 19 :=\n"
    "    Nat.factorial_dvd_factorial (by omega)\n"
    "  have hcastdiv : ((Nat.factorial 19 / i.factorial : ℕ) : ℚ)\n"
    "      = (Nat.factorial 19 : ℚ) / (i.factorial : ℚ) :=\n"
    "    Nat.cast_div hdvd (by positivity)\n"
    "  have hpow : (35 : ℚ) ^ i * (35 : ℚ) ^ (19 - i) = (35 : ℚ) ^ 19 := by\n"
    "    rw [← pow_add]\n"
    "    congr 1\n"
    "    omega\n"
    "  have hQ : (bigQ : ℚ) = (35 : ℚ) ^ 19 * (Nat.factorial 19 : ℚ) := by\n"
    "    unfold bigQ\n"
    "    norm_num [Nat.factorial]\n"
    "  rw [taylorCoefficientQ, if_pos hi]\n"
    "  unfold bigQ\n"
    "  simp only [zCoeff]\n"
    "  rw [show (-(2 / 35 : ℚ)) = (-2 : ℚ) / 35 by norm_num, div_pow]\n"
    "  simp only [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_natCast]\n"
    "  rw [hcastdiv]\n"
    "  field_simp [Nat.cast_pos.mpr i.factorial_pos]\n"
    "  norm_num only [Nat.cast_mul, Nat.cast_pow]\n"
    "  calc\n"
    "    (-2 : ℚ) ^ i * 26447672832002022437587219218750000000000000000 =\n"
    "        (-2 : ℚ) ^ i * ((35 : ℚ) ^ 19 * (Nat.factorial 19 : ℚ)) := by norm_num\n"
    "    _ = (-2 : ℚ) ^ i * ((35 : ℚ) ^ i * 35 ^ (19 - i)) *\n"
    "        (Nat.factorial 19 : ℚ) := by rw [hpow]; ring\n"
    "    _ = _ := by ring\n\n"
    "theorem getD_range_map_lt {α : Type*} [Inhabited α] (f : ℕ → α) (k : ℕ)\n"
    "    (hk : k < 666) (z : α) :\n"
    "    List.getD ((List.range 666).map f) k z = f k := by\n"
    "  rw [List.getD_eq_getElem _ _]\n"
    "  · rw [List.getElem_map]\n"
    "    simp\n"
    "  · simp [hk]\n\n"
    "theorem listCoeff_eq_zDiv (m k : ℕ) (hk : k < 666) :\n"
    "    listCoeffQ (powerCoefficientListQ m) k\n"
    "      = ((List.getD (zLayerList m) k 0 : ℤ) : ℚ) / (bigQ : ℚ) ^ m := by\n"
    "  induction m generalizing k with\n"
    "  | zero =>\n"
    "      rw [powerCoefficientListQ, zLayerList, zeroPowerCoefficientListQ]\n"
    "      rw [listCoeff_range_map _ k hk, getD_range_map_lt _ k hk]\n"
    "      by_cases h0 : k = 0\n"
    "      · rw [if_pos h0, if_pos h0]\n"
    "        norm_num\n"
    "      · rw [if_neg h0, if_neg h0]\n"
    "        norm_num\n"
    "  | succ m ih =>\n"
    "      change powerCoefficientQ (m + 1) k = _\n"
    "      rw [powerCoefficientQ_succ m k hk, zLayerList,\n"
    "        getD_range_map_lt _ k hk]\n"
    "      push_cast\n"
    "      calc\n"
    "        (∑ i ∈ Finset.range 20, if i ≤ k then powerCoefficientQ m (k - i) * taylorCoefficientQ i else 0) =\n"
    "            ∑ i ∈ Finset.range 20, (if i ≤ k then ((zLayerList m).getD (k - i) 0 : ℚ) * (zCoeff i : ℚ) else 0) / (bigQ : ℚ) ^ (m + 1) := by\n"
    "          apply Finset.sum_congr rfl\n"
    "          intro i hi\n"
    "          by_cases hik : i ≤ k\n"
    "          · have hi20 : i < 20 := Finset.mem_range.mp hi\n"
    "            rw [if_pos hik, if_pos hik, powerCoefficientQ,\n"
    "              ih (k - i) (by omega)]\n"
    "            have hQ0 : (bigQ : ℚ) ≠ 0 :=\n"
    "              Nat.cast_ne_zero.mpr (Nat.ne_of_gt bigQ_pos)\n"
    "            have htc : taylorCoefficientQ i = (zCoeff i : ℚ) / (bigQ : ℚ) := by\n"
    "              apply (eq_div_iff hQ0).2\n"
    "              simpa [mul_comm] using\n"
    "                (taylorCoefficientQ_mul_bigQ_eq_zCoeff i (by omega))\n"
    "            rw [htc]\n"
    "            field_simp [pow_succ, hQ0]\n"
    "            rw [pow_succ]\n"
    "            ring\n"
    "          · simp only [if_neg hik, zero_mul, zero_div]\n"
    "        _ = _ := by rw [Finset.sum_div]\n"
    "\n")


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
                   "endpointAQ (n + 1 + 1) - endpointAQ (n + 1)")
    + step_theorem("momentBQ", "momentBQ_step",
                   "endpointBQ (n + 1 + 1) - endpointBQ (n + 1)")
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
                             f"  norm_num (config := {{ maxSteps := 2000000000 }})\n"
                             f"    [{base_lemmas}]\n\n")
                continue
            if j == 1 and short.startswith("endpoint"):
                parts.append(f"theorem {short}_at_1 : {fn_name} 1 =\n"
                             f"    {v} := by\n  rfl\n\n")
                continue
            if j == 1:
                parts.append(f"theorem {short}_at_1 : {fn_name} 1 =\n"
                             f"    {v} := by\n"
                          f"  norm_num (config := {{ maxSteps := 2000000000 }})\n"
                             f"    [{fn_name}]\n\n")
                continue
            if short.startswith("endpoint"):
                bridge = (f"  show {fn_name} ({j - 2} + 1 + 1) = _\n"
                          f"  rw [{fn_name}_step]\n"
                          f"  rw [{short}_at_{j - 1}]\n")
            else:
                src = short[-1].upper()
                bridge = (f"  show {fn_name} ({j - 2} + 1 + 1) = _\n"
                          f"  rw [{fn_name}_step]\n"
                          f"  rw [endpoint{src}_at_{j}, endpoint{src}_at_{j - 1}]\n")
            tail = ("  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num\n"
                    if not extra else
                    "  norm_num (config := { maxSteps := 2000000000 }) <;> field_simp <;> norm_num\n"
                    f"    [{extra}]\n")
            parts.append(f"theorem {short}_at_{j} : {fn_name} {j} =\n"
                         f"    {v} := by\n" + bridge + tail + "\n")
    return "".join(parts)


def prefix_machinery():
    parts = ["-- RED-7 prefix-sum machinery: one tiny declaration per step;\n",
             "-- no shifted indices, no mega-tactic.  RED-9: the cached\n",
             "-- coefficient enters through the symbolic Rat bridge, then the\n",
             "-- literal integer table is inlined ONCE via zGround_eq_35.\n\n"]
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
                         f"  rw [listCoeff_eq_zDiv 35 ({j - 1}) (by omega)]\n"
                         f"  simp only [zGround_eq_35, bigQ, listCoeffQ,\n"
                         f"    List.getD_cons_zero, List.getD_cons_succ,\n"
                         f"    {short}_at_{j - 1}]\n"
                         f"  norm_num (config := {{ maxSteps := 2000000000 }})\n\n")
        cmp_lit = rat_lit(vals[666])
        parts.append(f"theorem comparison_{cmp_name}_eq :\n"
                     f"    (∑ k ∈ Finset.range 666, {term}) = {cmp_lit} := by\n"
                     f"  rw [{pre}_eq, {pre}_at_666]\n\n")
    return "".join(parts)


def grounding_c():
    doc = ("# Record 1145 (RED-9): bridge, per-index values, prefix sums\n\n"
           "The symbolic Rat bridge listCoeff_eq_zDiv connects the frozen\n"
           "Rat definition to the integer lift over Q = 35^19 * 19!; the\n"
           "endpoint/moment recursions are grounded per index (their\n"
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
            + BRIDGE_MACHINERY + per_index_theorems() + prefix_machinery()
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
