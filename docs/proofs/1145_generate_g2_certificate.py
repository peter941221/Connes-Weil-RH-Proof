"""1145 - emit the kernel-checked grounding block and the replacement proof
for the 1139 checkpoint `q28_certificate_Q` (Dev/
C1ConcreteClassMomentCertificate.lean).  Sole input: the module itself;
sole effect: (i) insert the BEGIN/END-1145-GENERATED region (the layer-0
bridge, eighteen even-layer + top-layer literal tables, and their grounding
theorems) before the checkpoint, (ii) replace the `native_decide` proof
body with the layered-grounding proof.  Rerunning is idempotent and
byte-stable (deterministic Fractions).  Pure stdlib.  RH NOT claimed.

Kernel facts this emission relies on (measured, v4.30):
* `List.range` / `List.map` / `if` over closed Nat reduce in the kernel
  (rfl-viable at 666 entries with raised maxRecDepth, no Rat arithmetic).
* `Rat` arithmetic does NOT reduce in the kernel (gcd is well-founded):
  every closure with rational arithmetic must be simp + norm_num, whose
  proof terms carry only structural Nat-level checks.
* denominators equal to 1 are emitted as bare numerals so the layer-0
  grounding stays a plain rfl."""
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

GROUND = [n for n in range(2, 36, 2)] + [35]


def rat_lit(v):
    if v.denominator == 1:
        return str(v.numerator)
    sign = "-" if v < 0 else ""
    return f"({sign}{abs(v.numerator)} / {abs(v.denominator)})"


def list_def(name, values):
    body = ",\n    ".join(rat_lit(v) for v in values)
    return (f"-- 1145 generated: exact value of layer {name.split('_')[-1]} "
            f"of the cached convolution (no semantic content).\n"
            f"set_option maxHeartbeats 2000000000 in\n"
            f"-- reason: literal rational table elaboration (generated data)\n"
            f"private def {name} : List ℚ :=\n"
            f"  [{body}]\n")


def ground_theorem(n):
    base = n - 2
    inner_base = ("zeroPowerCoefficientListQ" if base == 0
                  else f"powerCoefficientListQ {base}")
    rewrite = ("groundLayer_eq_0" if base == 0 else f"groundLayer_eq_{base}")
    inner = ("(List.range 666).map fun k' => ∑ i' ∈ Finset.range 20, "
             f"if i' ≤ k' then listCoeffQ ({inner_base}) (k' - i') * "
             "taylorCoefficientQ i' else 0")
    lam = ("(List.range 666).map fun k => ∑ i ∈ Finset.range 20, "
           "if i ≤ k then listCoeffQ prev (k - i) * taylorCoefficientQ i "
           "else 0")
    stmt = (f"set_option maxRecDepth 1000000 in\n"
            f"set_option maxHeartbeats 2000000000 in\n"
            f"-- reason: kernel-checked 666-entry rational list evaluation\n"
            f"private theorem groundLayer_eq_{n} :\n"
            f"    powerCoefficientListQ {n} = groundLayer_{n} := by\n"
            f"  show let prev := ({inner});\n"
            f"    ({lam}) = groundLayer_{n}\n"
            f"  simp only [{rewrite}]\n"
            f"  norm_num [listCoeffQ, taylorCoefficientQ, "
            f"Finset.sum_range_succ, Finset.sum_empty,\n"
            f"    List.getD_cons_zero, List.getD_cons_succ]\n")
    return stmt


def generated_block():
    parts = ["-- BEGIN 1145 GENERATED (docs/proofs/1145_generate_g2_certificate.py;\n",
             "-- rerunning the generator reproduces this region byte-for-byte).\n",
             "section GroundingLayers1145\n",
             "set_option linter.style.longLine false\n",
             "set_option linter.style.maxHeartbeats false\n\n",
             list_def("groundLayer_0", LAYERS[0]),
             "set_option maxRecDepth 1000000 in\n"
             "set_option maxHeartbeats 2000000000 in\n"
             "-- reason: kernel-checked 666-entry rational list evaluation\n"
             "private theorem groundLayer_eq_0 :\n"
             "    zeroPowerCoefficientListQ = groundLayer_0 := by\n  rfl\n\n"]
    for n in GROUND:
        parts.append(list_def(f"groundLayer_{n}", LAYERS[n]))
        parts.append(ground_theorem(n))
        parts.append("\n")
    parts.append("end GroundingLayers1145\n")
    parts.append("-- END 1145 GENERATED\n")
    return "".join(parts)


PROOF_BODY = """  have h35 := groundLayer_eq_35
  simp only [comparisonDataQ, h35, listCoeffQ, Finset.sum_range_succ,
    Finset.sum_empty, List.getD_cons_zero, List.getD_cons_succ,
    endpointAQ, endpointBQ, momentAQ, momentBQ, taylorCoefficientQ]
  norm_num"""

ANCHOR = ("set_option maxRecDepth 1000000 in\n"
          "set_option maxHeartbeats 2000000000 in")
OLD_BODY = "  native_decide"


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
    assert text.count(ANCHOR) == 1, "checkpoint anchor not unique"
    text = text.replace(ANCHOR, generated_block() + ANCHOR)
    if PROOF_BODY not in text:
        assert text.count(OLD_BODY) == 1, "native_decide body not unique"
        text = text.replace(OLD_BODY, PROOF_BODY)
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
