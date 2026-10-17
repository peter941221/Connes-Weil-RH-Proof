"""Bounded refinement decision probe for corrected 2743; diagnostic only."""
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import mpmath as mp
from fraction_jet_replay_control_2743 import run, lift

ROOT = Path(__file__).resolve().parents[1]

def main():
    mp.mp.dps = 100
    a, b = F(2049,8192), F(8394751,33554432)
    f = lambda x: 1/(1+mp.exp(-(1/(1-x)-1/x)))
    rows = []
    for pieces in (1,2,4,8):
        charges = {4:F(0),7:F(0)}
        max_width = {4:F(0),7:F(0)}
        contained = True
        for i in range(pieces):
            left = a+(b-a)*i/pieces
            right = a+(b-a)*(i+1)/pieces
            jet = run(left,right)
            for k in (4,7):
                box = jet[k]
                charges[k] += (right-left)*max(abs(box.l),abs(box.h))
                max_width[k] = max(max_width[k],box.h-box.l)
                for x in (left,(left+right)/2,right):
                    contained &= lift(box.l) <= mp.diff(f,lift(x),k) <= lift(box.h)
        rows.append({'pieces':pieces,'sampled_containment':bool(contained),
                     'upper_integral_diagnostic':{str(k):float(v) for k,v in charges.items()},
                     'max_width':{str(k):float(v) for k,v in max_width.items()}})
    checks = {'all_samples_contained':all(r['sampled_containment'] for r in rows),
              'width_contracts':all(rows[i+1]['max_width'][str(k)] < rows[i]['max_width'][str(k)] for i in range(3) for k in (4,7)),
              'charge_decreases':all(rows[i+1]['upper_integral_diagnostic'][str(k)] < rows[i]['upper_integral_diagnostic'][str(k)] for i in range(3) for k in (4,7))}
    out = {'record':2745,'status':'PASS' if all(checks.values()) else 'FAIL','checks':checks,'rows':rows,
           'parent_sha256':hashlib.sha256((ROOT/'scripts/fraction_jet_replay_control_2743.py').read_bytes()).hexdigest(),
           'scope':'One representative cell only. Refinement viability, not global integral certification.',
           'nonclaims':['No Lean replay','No D4/D7 certificate','No pins or RH']}
    (ROOT/'results/2745_jet_refinement_probe.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
    return 0 if all(checks.values()) else 1

if __name__ == '__main__':
    raise SystemExit(main())
