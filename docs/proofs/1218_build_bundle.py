"""1218 - build the class (2,8) certificate bundle for the consumption-
chain regeneration (prereg 1218_consumption_chain_regen_preregistration.md,
committed a51aa58 BEFORE this run; law 42).

Output 1218_cert_q28.json = the committed 1112 class-(2,8) bundle with
M_lo/M_hi replaced by the record-1217 dyadic boxes of the TRUE gate
matrix (mixed parity exact "0").  G side / R_mid / U_outward / A_R are
byte-identical to 1112 (falsifier F1 asserts every field).

Falsifier F1: any mismatch -> exit 3, nothing written.
"""
import json
import os
import sys
from fractions import Fraction as F

HERE = os.path.dirname(os.path.abspath(__file__))
C1112 = os.path.join(HERE, "1112_cert.json")
C1217 = os.path.join(HERE, "1217_m_boxes_cert.json")
OUT = os.path.join(HERE, "1218_cert_q28.json")

src = json.load(open(C1112))
true_boxes = json.load(open(C1217))
classes = [c for c in src["classes"] if c["A_R"] == 2.0]
assert len(classes) == 1, f"expected exactly one (2,8) class, got {len(classes)}"
ce = dict(classes[0])

wc = true_boxes["whitened_check"]
if wc.get("pass") is not True:
    print(f"F1: 1217 whitened_check.pass = {wc.get('pass')!r} (must be True)")
    sys.exit(3)

ent = true_boxes["entries"]
K = 8
M_lo = [[""] * K for _ in range(K)]
M_hi = [[""] * K for _ in range(K)]
worst_same = F(0)
worst_mixed = F(0)
for i in range(K):
    for j in range(K):
        e = ent[f"{i},{j}"]
        lo, hi = F(e["lo"]), F(e["hi"])
        if lo > hi:
            print(f"F1: 1217 box ({i},{j}) inverted: lo {lo} > hi {hi}")
            sys.exit(3)
        if (i + j) % 2:                      # mixed parity (prereg sec. 7):
            # consistency only; the bundle emits EXACT [0, 0] mirroring
            # the committed C1GateMatrixBoxData / D1 ownership
            if not (lo <= 0 <= hi):
                print(f"F1: mixed box ({i},{j}) does not contain 0: "
                      f"[{lo}, {hi}]")
                sys.exit(3)
            if abs(F(e["mid"])) > F(e["budget"]):
                print(f"F1: mixed mid ({i},{j}) exceeds own budget: "
                      f"{float(abs(F(e['mid']))):.3e}")
                sys.exit(3)
            worst_mixed = max(worst_mixed, abs(F(e["mid"])))
            M_lo[i][j] = "0"
            M_hi[i][j] = "0"
        else:
            worst_same = max(worst_same, hi - lo)
            M_lo[i][j] = str(lo)
            M_hi[i][j] = str(hi)

# F1: G side / R_mid / U_outward byte-equal to the committed 1112 bundle
orig = classes[0]
for key in ("G_lo", "G_hi", "R_mid", "U_outward"):
    if ce[key] != orig[key]:
        print(f"F1: field {key} mutated - must be byte-identical to 1112")
        sys.exit(3)

print(f"F1 PASS: 1217 whitened_check pass=True, "
      f"worst same-parity width {float(worst_same):.3e}, "
      f"mixed |mid| {float(worst_mixed):.3e} (exact-zero boxes emitted)")
print(f"G/R/U byte-identical to 1112 class (2,8); "
      f"U_outward[1] = {ce['U_outward'][1]}")

ce["M_lo"] = M_lo
ce["M_hi"] = M_hi
ce["verdict"] = "PASS 1218 (M side = record-1217 true gate boxes)"

bundle = dict(record="1218-bundle",
              prereg="1218_consumption_chain_regen_preregistration.md",
              m_side_source="1217_m_boxes_cert.json",
              g_side_source="1112_cert.json",
              classes=[ce])
with open(OUT, "w") as f:
    json.dump(bundle, f, indent=1)
print(f"WROTE {OUT}")
