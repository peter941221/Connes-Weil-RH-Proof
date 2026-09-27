#!/usr/bin/env python3
"""Cross-checker for the Route-B batch records 2028-2031.

Re-derives every headline number of docs/proofs/2029, 2030 and 2031 from the
committed artifacts (results/2028_coupling_scan.json,
results/2030_determinant_margin.json, results/2031_sharp_q_ladder.json) and
asserts the prose tables quote them. Exit code 0 means 0 failed checks.

Run with a python that has no third-party requirement:

    python3 scripts/check_route_b_batch_2028_2031.py
"""

import json
import math
import pathlib
import sys
R = pathlib.Path(".")
scan = json.loads((R/"results/2028_coupling_scan.json").read_text())
c1981 = json.loads((R/"results/1981_powered_seed_underapprox.json").read_text())
m2030 = json.loads((R/"results/2030_determinant_margin.json").read_text())
m2031 = json.loads((R/"results/2031_sharp_q_ladder.json").read_text())
doc29 = (R/"docs/proofs/2029_coupling_scan_outcome.md").read_text()
doc30 = (R/"docs/proofs/2030_determinant_certification_margin.md").read_text()
doc31 = (R/"docs/proofs/2031_sharp_q_ladder_outcome.md").read_text()

fail = 0
def chk(cond, label):
    global fail
    if not cond:
        fail += 1
        print("FAIL:", label)

conv = {r["n"]: r for r in scan["refinement"] if abs(r["dxi"]-0.002) < 1e-12}
def fmt(x):
    return "%.10e" % x
# 2029 erratum table rows
cases = [(0,"C",2372.283545851358,2372.2617326e0),(1,"C",-5174.028192052667,-5126.7476046e0),
         (2,"C",-21286.53324145657,-23475.484817e0),(3,"C",-7410.351527503077,-145219.47349e0),
         (4,"C",3000119.3333906233,-501735.56258e0)]
for n,f,a,b in cases:
    chk(abs(c1981["rows"][n][f]-a)/abs(a) < 1e-12, "1981 %d %s value"%(n,f))
    chk(abs(conv[n][f]-b)/abs(b) < 1e-6, "converged %d %s value"%(n,f))
# P_n and routes
Pn = {r["n"]: r["prime_power_count"] for r in scan["structural"] if r["prime_power_count"]}
chk(Pn[0]==24 and Pn[1]==98 and Pn[2]==465 and Pn[3]==2532 and Pn[4]==15040 and Pn[5]==93371 and Pn[6]==595877, "P_n values")
chk(all(str(v) in doc29 for v in (24,98,465,2532,15040,93371,595877)), "P_n in doc")
# tail proxies
tp = {r["n"]: r["tail_proxy_L_over_lambda_sq"] for r in scan["trend"] if "tail_proxy_L_over_lambda_sq" in r}
chk(abs(tp[0]-2.1447633577852578e28)/tp[0] < 1e-12, "proxy n=0")
chk(abs(tp[5]-6.374215e23)/tp[5] < 1e-3, "proxy n=5")
factor = (tp[5]/tp[0])**(1/5)
steps = math.log(tp[0])/math.log(1/factor)
chk(abs(steps-31.29) < 0.1, "n_needed 31.3 (got %.2f)"%steps)
chk("31" in doc29, "n_needed in doc")
# 2030 eps values
rows30 = {r["n"]: r for r in m2030["rows"]}
chk(abs(rows30[4]["frame_0"]["eps_det_upper_zero"]-9.0252e-2) < 5e-6, "2030 eps n=4")
chk(abs(rows30[2]["frame_0"]["eps_det_upper_zero"]-3.8198e-3) < 5e-8, "2030 eps n=2")
chk(abs(rows30[0]["frame_vertex"]["eps_det_upper_zero"]-(math.sqrt(2)-1)) < 1e-9, "2030 vertex sqrt2-1")
chk(not rows30[1]["frame_0"]["C0_positive"] and not rows30[1]["frame_0"]["b0_positive"], "2030 sign n=1")
# 2031 bounds
lb = {r["k"]: r for r in m2031["ladder_bounds"]}
chk(abs(lb[3]["bound"]-3.00164105722696e-07)/lb[3]["bound"] < 1e-12, "2031 k=3 bound")
chk(abs(lb[3]["margin_vs_q"]-203.339)/203.339 < 1e-3, "2031 k=3 margin")
chk(lb[3]["t"]==28.0 and lb[3]["sigma"]==0.0, "2031 k=3 argmax")
chk(lb[4]["bound"] > m2031["q"] > 0, "2031 k=4 fails")
crude = {r["k"]: r for r in m2031["crude_mass_bounds_1982_style"]}
chk(abs(crude[3]["bound"]-5.918919e-05)/5.918919e-05 < 1e-5, "2031 crude k=3")
chk(abs(crude[3]["margin_vs_q"]-1.0312) < 1e-3, "2031 crude margin")
chk(m2031["seed0_exact"] == 59049.0, "seed0")
chk(abs(float(m2031["S_seed_exact_samples"]["0.00"])-3.0) < 1e-12, "S_seed(0)=3")
# docs contain the headline strings
for s in ("3.0016e-07","2.03e+02","1.03e+00","5.918919e-05","203.34","8.387290e+07"):
    chk(s in doc31, "doc31 has %s"%s)
for s in ("9.0252e-02","3.8198e-03","0.4142","1.16e-5"):
    chk(s in doc30, "doc30 has %s"%s)
print("checks failed:", fail)
sys.exit(1 if fail else 0)
