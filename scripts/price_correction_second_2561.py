"""External whole-cell enclosure for exp(sigma*x) c''(x); no Lean claim."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from math import comb
from pathlib import Path
import time

from flint import acb, arb, ctx
import routea_owner_whole_cell_2535 as base

ROOT = Path(__file__).resolve().parents[1]
PIN = F('666472.585392')


def polynomials():
    result = [{0: 1}]
    for k in range(6):
        nxt = {}
        for p, c in result[-1].items():
            for power, value in ((p+1, (4*k-60)*c), (p+3, -4*k*c)):
                nxt[power] = nxt.get(power, 0)+value
            if p:
                for shift, factor in ((-1, 1), (1, -2), (3, 1)):
                    nxt[p+shift] = nxt.get(p+shift, 0)+p*c*factor
        result.append({p: c for p, c in nxt.items() if c})
    assert result[:5] == base.POLYS
    return result


POLYS = polynomials()


def load_families():
    families = base.load_families()
    rows = json.loads(base.REPAIR.read_text())['coefficient_rows']
    for f, row in zip(families, rows):
        box = row['ideal_correction_coefficient']
        bounds = [tuple(F(box[p][s]) for s in ('lower_exact', 'upper_exact'))
                  for p in ('real', 'imag')]
        assert all(lo <= hi for lo, hi in bounds)
        mids = [base.lift((lo+hi)/2) for lo, hi in bounds]
        halves = [base.lift((hi-lo)/2) for lo, hi in bounds]
        f['center'] = acb(*mids)
        f['error'] = base.upper((halves[0]**2+halves[1]**2).sqrt())
        f['scale'] = base.upper(abs(f['center'])+f['error'])
    return families


def jets(f, coordinate, sigma, order=3):
    if abs(coordinate) >= f['r']:
        return [acb(0) for _ in range(order+1)]
    x, s = base.lift(coordinate), base.lift(sigma)
    u = x/f['radius']
    q = 1-u*u
    assert q > 0
    e = acb(-30/q+s*x, f['theta']*x).exp()
    bump = [sum((c*u**p for p, c in POLYS[k].items()), arb(0)) /
            (f['radius']**k*q**(2*k)) for k in range(order+3)]
    lam = acb(0, f['theta'])
    raw = [sum((comb(k,j)*lam**(k-j)*bump[j] for j in range(k+1)), acb(0))
           for k in range(order+3)]
    return [e*sum((comb(k,j)*s**(k-j)*raw[j+2] for j in range(k+1)), acb(0))
            for k in range(order+1)]


def envelope(f, a, b, sigma):
    near = F(0) if a <= 0 <= b else min(abs(a), abs(b))
    if near >= f['r']:
        return arb(0)
    far = min(max(abs(a), abs(b)), f['r'])
    u, v = base.lift(near/f['r']), base.lift(far/f['r'])
    t = 1/(1-u*u)
    decay = (-30*t).exp()
    theta, s = abs(f['theta']), abs(base.lift(sigma))
    raw = []
    for k in range(7):
        raw.append(sum((comb(k,j)*theta**(k-j)*
            sum((abs(c)*v**p for p,c in POLYS[j].items()), arb(0))*
            decay*t**(2*j)/f['radius']**j for j in range(k+1)), arb(0)))
    weight = base.lift(max(sigma*a, sigma*b)).exp()
    return base.upper(weight*sum((comb(4,j)*s**(4-j)*raw[j+2] for j in range(5)), arb(0)))


def point(families, x, sigma):
    value, error, thirds = acb(0), arb(0), []
    for f in families:
        jet = jets(f, x, sigma)
        value += f['center']*jet[0]
        error += f['error']*abs(jet[0])
        thirds.append(base.upper(abs(jet[3])))
    return base.upper(abs(value)+error), thirds


def run(cells, sign):
    families = load_families()
    sigma, step = F(sign,2), 2*base.RADIUS/cells
    h = base.lift(step)
    left, thirds = point(families, -base.RADIUS, sigma)
    node_sum, remainder_sum = F(0), F(0)
    for index in range(cells):
        a, b = -base.RADIUS+index*step, -base.RADIUS+(index+1)*step
        right, next_thirds = point(families,b,sigma)
        center, error, third = acb(0), arb(0), arb(0)
        for f, l, r in zip(families, thirds, next_thirds):
            j2 = jets(f,(a+b)/2,sigma,2)[2]
            center += f['center']*j2
            error += f['error']*abs(j2)
            third += f['scale']*(max(l,r)+h/2*envelope(f,a,b,sigma))
        curvature = base.upper(abs(center)+error+h/2*third)
        node_sum += base.exact_upper(h/2*(left+right))
        remainder_sum += base.exact_upper(h**3/12*curvature)
        left, thirds = right, next_thirds
        if (index+1)%2048 == 0:
            print('CORRECTION', cells, sign, index+1, flush=True)
    total = node_sum+remainder_sum
    return dict(cells=cells, sign=sign, node=str(node_sum), remainder=str(remainder_sum),
                total=str(total), margin=str(PIN-total), fits_pin=total<=PIN,
                display=dict(node=float(node_sum), remainder=float(remainder_sum),
                             total=float(total), margin=float(PIN-total)))


if __name__ == '__main__':
    parser = argparse.ArgumentParser()
    parser.add_argument('--cells', type=int, default=10240)
    parser.add_argument('--precision', type=int, default=192)
    args = parser.parse_args()
    assert args.cells > 0 and args.precision >= 128
    ctx.prec = args.precision
    started = time.monotonic()
    rows = [run(args.cells, sign) for sign in (-1,1)]
    paths = [Path(__file__), Path(base.__file__), base.REPAIR, base.CAPTURE]
    result = dict(record=2561, status='EXTERNAL_CORRECTION_SECOND_ENCLOSURE',
                  precision=args.precision, rows=rows, pin=str(PIN),
                  source_sha256={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in paths},
                  elapsed_seconds=time.monotonic()-started, lean_certificate=False,
                  exact_coefficient_membership=False, producer_go=False, rh_claim=False)
    path = ROOT/f'results/2561_correction_second_{args.cells}.json'
    path.write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps([r['display'] for r in rows]),flush=True)
