"""Reject the three historical 2743 faults against independent derivatives."""
import inspect
import json
from fractions import Fraction as F
from pathlib import Path
import mpmath as mp
import fraction_jet_replay_control_2743 as parent

ROOT = Path(__file__).resolve().parents[1]

def main():
    mp.mp.dps = 100
    source = inspect.getsource(parent.run)
    replacements = {
        'collapsed_coordinate_cells': [('I(a,b)', 'I(a)'), ('I(1-b,1-a)', 'I(1-b)')],
        'reversed_phase_endpoints': [
            ('taylor(-p[0].l/m)+tail(-p[0].l/m)', 'taylor(-p[0].h/m)+tail(-p[0].h/m)'),
            ('taylor(-p[0].h/m)-tail(-p[0].h/m)', 'taylor(-p[0].l/m)-tail(-p[0].l/m)')],
        'wrong_exponential_binomial': [('scale(comb(n-1,j))', 'scale(comb(n,j+1))')],
    }
    a, b = F(2049,8192), F(8394751,33554432)
    f = lambda x: 1/(1+mp.exp(-(1/(1-x)-1/x)))
    references = {(x,n):mp.diff(f,parent.lift(x),n)
                  for x in (a,(a+b)/2,b) for n in range(8)}
    def failures(run):
        jet = run(a,b)
        return [{'x':str(x),'order':n} for (x,n),v in references.items()
                if not parent.lift(jet[n].l) <= v <= parent.lift(jet[n].h)]
    baseline = failures(parent.run)
    rows = {}
    for name, edits in replacements.items():
        mutated = source
        for before,after in edits:
            assert mutated.count(before) == 1, (name,before)
            mutated = mutated.replace(before,after)
        namespace = dict(vars(parent))
        exec(compile(mutated, '<historical-fault-control>', 'exec'), namespace)
        try:
            missed = failures(namespace['run'])
        except ValueError as error:
            if str(error) != 'Reversed interval endpoints':
                raise
            missed = [{'invariant':str(error)}]
        rows[name] = {'rejected':bool(missed),'failed_samples':len(missed),
                      'first_failure':missed[0] if missed else None}
    checks = {'baseline_passes':not baseline,
              'all_historical_faults_rejected':all(r['rejected'] for r in rows.values())}
    out = {'record':2746,'checks':checks,'mutations':rows,
           'status':'PASS' if all(checks.values()) else 'FAIL',
           'scope':'Diagnostic regression guards; not a continuum or Lean certificate.'}
    (ROOT/'results/2746_jet_fault_controls.json').write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps(out,indent=2))
    return 0 if all(checks.values()) else 1

if __name__ == '__main__':
    raise SystemExit(main())
