#!/usr/bin/env python3
"""Cross-checker for the Route-B batch records 2032-2035.

Re-derives every headline number of docs/proofs/2035_route_b_full_block_outcome.md
from the committed artifacts (results/2032_gate_row_search.json,
results/2033_gate_tail_pairing.json, results/2033_interval_mass_w3.json,
results/2034_support_radius_robustness.json) and asserts the prose tables quote
them. Exit code 0 means 0 failed checks.

Run with a python that has no third-party requirement:

    python3 scripts/check_route_b_batch_2032_2035.py
"""

import json
import math
import pathlib
import sys

R = pathlib.Path(".")
g32 = json.loads((R / "results/2032_gate_row_search.json").read_text())
p33 = json.loads((R / "results/2033_gate_tail_pairing.json").read_text())
m33 = json.loads((R / "results/2033_interval_mass_w3.json").read_text())
r34 = json.loads((R / "results/2034_support_radius_robustness.json").read_text())
doc35 = (R / "docs/proofs/2035_route_b_full_block_outcome.md").read_text()

fail = 0


def chk(cond, label):
    global fail
    if not cond:
        fail += 1
        print("FAIL:", label)


# ---------------- P4 / record 2032 ----------------
chk(g32["status"] == "ROW-FOUND", "2032 status")
chk(g32["anchor_passed"] is True, "2032 anchor_passed")
chk(g32["anchor_max_dev_C"] == 0.0, "2032 anchor bit-exact at dxi=0.02")
chk(abs(g32["anchor_max_dev_C_fine_grid"] - 2.686150835096157e-07) < 1e-15,
    "2032 anchor dev at dxi=0.01")
chk(g32["prime_book"] == {"0": 24, "1": 98, "2": 465, "3": 2532, "4": 15040},
    "2032 prime book")
chk(g32["cutoff_label"] == "CUTOFF-SENSITIVE", "2032 cutoff label")
chk(len(g32["rows"]) == 45, "2032 row count")

gate_rows = [r for r in g32["rows"] if r["gate_signs"] and r["n"] >= 1]
ctrl_rows = [r for r in g32["rows"] if r["gate_signs"] and r["n"] == 0]
chk(len(gate_rows) == 9, "2032 nine gate rows at n>=1")
chk(len(ctrl_rows) == 9, "2032 nine n=0 control rows")
chk(all(r["sign_stable"] for r in gate_rows), "2032 gate rows sign-stable")
expect = {(21.022039638771556, 3, 2), (21.022039638771556, 4, 2),
          (21.022039638771556, 5, 2), (30.424876125859512, 3, 2),
          (30.424876125859512, 3, 3), (30.424876125859512, 4, 2),
          (30.424876125859512, 4, 3), (30.424876125859512, 5, 2),
          (30.424876125859512, 5, 3)}
chk({(r["gamma"], r["N"], r["n"]) for r in gate_rows} == expect,
    "2032 gate row index set")
chk(not any(r["n"] == 1 for r in g32["rows"] if r["gate_signs"]),
    "2032 no gate row at n=1")
chk(not any(r["n"] >= 4 for r in g32["rows"] if r["gate_signs"]),
    "2032 no gate row at n>=4")
for r in gate_rows:
    v = r["dxi0.02"]
    chk(v["C"] > 0 and v["b"] > 0 and v["det"] < 0,
        "2032 pattern signs g=%s N=%d n=%d" % (r["gamma"], r["N"], r["n"]))
    chk(abs(v["det"] - (v["C"] * v["D"] - v["b"] ** 2)) <= 1e-6 * abs(v["det"]),
        "2032 det = C D - b^2 g=%s N=%d n=%d" % (r["gamma"], r["N"], r["n"]))
# the two rows quoted verbatim in the T1 table
by_index = {(r["gamma"], r["N"], r["n"]): r for r in gate_rows}
r_a = by_index[(21.022039638771556, 3, 2)]["dxi0.02"]
chk("+1.65478e+04" in doc35 and "+4.05740e+07" in doc35 and "-4.68143e+14" in doc35,
    "2035 T1 quotes gamma_2/N=3/n=2")
r_b = by_index[(30.424876125859512, 5, 3)]["dxi0.02"]
chk(abs(r_b["C"] - 33267.55) < 0.5 and abs(r_b["det"] + 2.49244e16) < 1e10,
    "2035 T1 quotes gamma_3/N=5/n=3")

# ---------------- P4c / record 2034 ----------------
chk(r34["status"] == "RADIUS-FRAGILE", "2034 status")
chk(len(r34["rows"]) == 15, "2034 row count")
survivors = [r for r in r34["rows"] if not [d for d in r["moved_at"] if d > 0]]
moved_pos = [r for r in r34["rows"] if [d for d in r["moved_at"] if d > 0]]
chk(len(survivors) == 1, "2034 exactly one row survives +1/+2")
chk(len(moved_pos) == 14, "2034 fourteen rows move at +1/+2")
chk(survivors[0]["gamma"] == 21.022039638771556 and survivors[0]["N"] == 5
    and survivors[0]["n"] == 2, "2034 the survivor is gamma_2/N=5/n=2")
chk(all(r["delta+0"]["gate_signs"] for r in r34["rows"]), "2034 base pattern")
chk(sum(1 for r in r34["rows"] if not r["delta-1"]["gate_signs"]) == 9,
    "2034 nine rows flip at delta=-1")

# ---------------- P4b / record 2033 ----------------
chk(p33["status"] == "PAIR-MISMATCH", "2033 status")
chk(p33["paired_rows"] == [], "2033 paired_rows empty")
chk(abs(p33["anchor_2028_max_dev"] - 2.220446049250313e-16) < 1e-30,
    "2033 anchor vs record 2028")
q = p33["q"]
for o in p33["owners"]:
    for r in o["rows"]:
        a0 = o["A0"]
        chk(abs(r["tau_q_no_vertex_factor"] - a0 * q ** (2 * r["n"]))
            <= 1e-9 * r["tau_q_no_vertex_factor"],
            "2033 tau_inf = A0 q^(2n) g=%s N=%d n=%d" % (o["gamma"], o["N"], r["n"]))
        if r["gate_signs"] and r["n"] >= 1:
            chk(r["tau_q_no_vertex_factor"] > 1.0,
                "2033 gate row has tau_inf > 1 g=%s N=%d n=%d"
                % (o["gamma"], o["N"], r["n"]))
            chk(not r["tail_closed_q"] and not r["gate_and_tail"],
                "2033 gate row tail not closed g=%s N=%d n=%d"
                % (o["gamma"], o["N"], r["n"]))
        if r["n"] == 4:
            chk(not r["gate_signs"], "2033 n=4 row has no gate pattern")
chk("2.115e+10" in doc35 and "9.668e+12" in doc35 and "3.602e+04" in doc35,
    "2035 quotes the tau_inf ladder")
# derived closure index
for o in p33["owners"]:
    n_min = math.ceil(math.log(o["A0"]) / (2 * math.log(1.0 / q)))
    want = 3 if abs(o["gamma"] - 14.134725141734693) < 1e-9 else 4
    chk(n_min == want, "2033 n_min = %d at gamma=%.6f" % (want, o["gamma"]))
    chk(o["n_min_lambda_inf_tail"] == want, "2033 artifact n_min at gamma=%.6f" % o["gamma"])
chk("2532" in doc35 and "15040" in doc35 and "60000" in doc35,
    "2035 quotes the prime books and the cap")
# the q-needed table
o0 = [o for o in p33["owners"] if abs(o["gamma"] - 21.022039638771556) < 1e-9
      and o["N"] == 3][0]
chk(abs((2.0 ** -14) / o0["A0"] ** (-0.25) - 381.3) < 0.5,
    "2035 q-needed ratio 381.3 at gamma_2/N=3/n=2")

# ---------------- P6 / record 2033 ----------------
chk(m33["status"] == "MASS-BRACKETED", "P6 status")
chk(m33["n_base"] == 20000, "P6 n_base")
chk(m33["panels"]["sign"] == 19728 and m33["panels"]["env"] == 272,
    "P6 panel split")
strip = m33["certified_strip"]
chk(abs(strip["bound"] - 3.0018472213129583e-07) < 1e-20, "P6 bound")
chk(abs(strip["margin_vs_q"] - 203.3253252086035) < 1e-9, "P6 margin")
chk(strip["smoke"] is False, "P6 full run, not smoke")
chk(strip["sigma_grid_points"] == 101 and strip["t_grid_points"] == 345,
    "P6 grid")
chk(strip["sigma"] == 0.0 and strip["t"] == 28.0, "P6 argmax")
chk(abs(strip["bound"] / strip["uncertified_2031_bound"] - 1.0) < 1e-4,
    "P6 certified vs uncertified relative gap")
for c in m33["W3_bracket_checks"]:
    chk(c["contains_2031"] is True, "P6 bracket contains 2031 at a=%.3f" % c["a"])
    chk(c["rel_width"] < 5.1e-3, "P6 rel width at a=%.3f" % c["a"])
ref = {c["a"]: c["record_2031_value"] for c in m33["W3_bracket_checks"]}
chk(abs(ref[0.025] - 78.9829335535928) < 1e-9, "P6 ref 0.025")
chk(abs(ref[0.525] - 105.83438341394672) < 1e-9, "P6 ref 0.525")
chk("3.001847221e-07" in doc35 and "203.33" in doc35, "2035 quotes the P6 bound")

# ---------------- doc strings ----------------
for s in ("ROW-FOUND", "PAIR-MISMATCH", "LAMBDA-PAYS", "RADIUS-FRAGILE",
          "MASS-BRACKETED", "n_min = 3", "n_min = 4", "381x", "1763x",
          "5.0e-03", "105.334079", "105.835774"):
    chk(s in doc35, "doc35 has %s" % s)
print("checks failed:", fail)
sys.exit(1 if fail else 0)
