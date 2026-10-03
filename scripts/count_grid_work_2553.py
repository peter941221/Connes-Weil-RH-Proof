"""Exact support counts for pricing endpoint reuse before grid replication."""
from fractions import Fraction as Q
import json

from generate_complex_exp_node_2541 import ROOT, CAPTURE
from routea_exp_schedule_probe_2542 import R, STEP


def main():
    raw = json.loads(CAPTURE.read_text())["owner_capture"]["families_hex"]
    rows = []
    for i,values in enumerate(raw):
        radius = Q.from_float(float.fromhex(values[0]))**2
        counts = {}
        for label,offset,last in (("endpoints",Q(0),10240),("midpoints",Q(1,2),10239)):
            lower,upper = (R-radius)/STEP-offset,(R+radius)/STEP-offset
            first = max(0,lower.numerator//lower.denominator+1)
            final = min(last,-((-upper.numerator)//upper.denominator)-1)
            count = max(0,final-first+1)
            # Independently count using exact scaled integer inequalities.
            a = R-radius-offset*STEP
            b = R+radius-offset*STEP
            independent = sum(a.numerator*STEP.denominator < j*STEP.numerator*a.denominator
                and j*STEP.numerator*b.denominator < b.numerator*STEP.denominator
                for j in range(last+1))
            assert count == independent
            counts[label] = count
        rows.append(dict(family=i,**counts))
    totals = {key:2*sum(row[key] for row in rows) for key in ("endpoints","midpoints")}
    result = dict(record=2553,families=rows,both_sign_active_counts=totals,
        shared_exponential_evaluations=sum(totals.values()),
        scope="shared order0/order3 endpoint exponential; separate order2 midpoint exponential",
        excludes="fourth-envelope exponentials, scalar bounds, signed sums, integral assembly, owner membership",
        independently_enumerated=True,full_grid_certificate=False)
    (ROOT/"results/2553_grid_work_count.json").write_text(json.dumps(result,indent=2)+"\n")
    print(totals,"shared total",result["shared_exponential_evaluations"],flush=True)


if __name__ == "__main__":
    main()
