"""2665 M1 leg 3: hmargin (2249 L1 detector value) on the repaired coefficients.

Preregistration:
  consumer : same as the window leg -- healthy selected detector producer
             margin (2109 known-prefix ledger consumed margin_lo from 2249).
  owner    : the 2249 discrete owner (gamma 39.25244858548658, delta 0.445,
             4001-point grid) with base/corr swapped to the 2338 ideal pair
             (float64 realization of the exact balls), cast charged
             explicitly: per point, |L| <= B + eps*Lambda (triangle), so the
             exact multiplicative perturbation is
             (B+b)^2 (C+c)^2 - B^2 C^2 with b = eps*Lambda_b, c = eps*Lambda_c
             -- no truncation, sound by construction.
  premise  : "the 2249 margin survives the repair" -- unverified; q is a
             SIGNED cancellation sum, so no monotone screen is valid and the
             value itself must be re-measured (lane law).
  decision : control arm must reproduce the committed 2249 q (same-run law).
             Treatment margin_lo (with cast perturbation inside the value
             enclosure) minus the 2109 ledger charge
             (tail_2248 * 21/62 + known_error_2109) must stay > 0 => premise
             removed at measurement grade. Otherwise => named no-go
             L1-MARGIN-REPAIR-FAIL.
  order check: the 2338 coefficient_rows are indexed against the CAPTURE
             family order; injection into the 2249 rig is positional only
             after the control arm's solved base/corr match the capture's
             stored hex arrays bitwise (order-faithfulness evidence).
  output   : results/2665_l1_margin_repair.json; the committed
             results/2249_l1_enclosure.json is never opened for writing.
"""
import hashlib
import json
import math
import sys
import time
from fractions import Fraction
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

import routea_weighted_zero_l1_enclosure_2249 as r2249  # noqa: E402
import routea_direct_functional_difference_screen_2295 as direct2295  # noqa: E402

REPAIR = ROOT / 'results/2338_exact_interpolation_repair.json'
COMMITTED = ROOT / 'results/2249_l1_enclosure.json'


def eps_cast_exact(rows):
    worst = Fraction(0)
    for row in rows:
        for channel in ('ideal_base_coefficient',
                        'ideal_correction_coefficient'):
            for component in ('real', 'imag'):
                slot = row[channel][component]
                mid = (Fraction(slot['lower_exact'])
                       + Fraction(slot['upper_exact'])) / 2
                if mid == 0:
                    continue
                worst = max(worst,
                            abs(Fraction(float(mid)) - mid) / abs(mid))
    return worst


def coefficient_mid_floats(rows):
    base, corr = [], []
    for row in rows:
        for target, channel in ((base, 'ideal_base_coefficient'),
                                (corr, 'ideal_correction_coefficient')):
            parts = {}
            for component in ('real', 'imag'):
                slot = row[channel][component]
                mid = (Fraction(slot['lower_exact'])
                       + Fraction(slot['upper_exact'])) / 2
                parts[component] = float(mid)
            target.append(complex(parts['real'], parts['imag']))
    return np.asarray(base, complex), np.asarray(corr, complex)


def weight_grid(fam):
    xw_cache = {}
    xw_list = []
    for pair in fam:
        if float(pair[0]) not in xw_cache:
            xw_cache[float(pair[0])] = r2249.phi_weights_cached(pair[0])
        xw_list.append(xw_cache[float(pair[0])])
    return xw_list


def chain(base, corr, fam, nodes, values, rho, eps, t_start):
    """The 2249 main() numeric chain, verbatim order, injected coefficients."""
    t0 = t_start
    grid = np.arange(-r2249.XMAX, r2249.XMAX + r2249.STEP / 2, r2249.STEP)
    npts = grid.shape[0]
    nfam = len(fam)
    xw_list = weight_grid(fam)
    ref_x, ref_w = r2249.r59.phi_weights(fam[0][0], panels=6, m=r2249.M)
    gl_identity_ok = (np.array_equal(ref_x, xw_list[0][0])
                      and np.array_equal(ref_w, xw_list[0][1]))
    tables = []
    for j, (a, th) in enumerate(fam):
        X, f, ef = r2249.phi_terms(a, xw_list[j])
        tables.append((a, th, X, f, ef))
    vre = np.zeros((nfam, npts))
    evre = np.zeros((nfam, npts))
    vim = np.zeros((nfam, npts))
    evim = np.zeros((nfam, npts))
    for j, (a, th, X, f, ef) in enumerate(tables):
        for lo in range(0, npts, r2249.CHUNK):
            hi = min(lo + r2249.CHUNK, npts)
            r0, er0, i0, ei0 = r2249.laplace_rows(a, th, X, f, ef,
                                                  grid[lo:hi])
            vre[j, lo:hi] = r0
            evre[j, lo:hi] = er0
            vim[j, lo:hi] = i0
            evim[j, lo:hi] = ei0
    print('  family tables done %.1fs' % (time.time() - t0), flush=True)
    lre, elre, lim, elim = r2249.dot30(vre, evre, vim, evim, base)
    cre, ecre, cim, ecim = r2249.dot30(vre, evre, vim, evim, corr)
    hb, ehb = r2249.sq_abs(lre, elre, lim, elim)
    hc, ehc = r2249.sq_abs(cre, ecre, cim, ecim)
    support = 2 * max(pair[0] for pair in fam)
    primes = r2249.r59.rig.prime_powers_up_to(math.exp(support))
    kern, ekern = r2249.kernel_full(grid, primes)
    p, ep = r2249.p_instrumented(grid, r2249.r80.counterpart_nodes(rho))
    p2, ep2 = r2249.m2(p, ep, p, ep)
    g, eg = r2249.m2(kern, ekern, p2, ep2)
    g, eg = r2249.m2(g, eg, hb, ehb)
    g, eg = r2249.m2(g, eg, hc, ehc)
    w = np.full(npts, 1.0 / 50.0)
    if npts > 1:
        w[0] = 1.0 / 100.0
        w[-1] = 1.0 / 100.0
    # cast perturbation: |L_exact| <= |L_run| + (eps/(1-eps))*Lambda
    # pointwise (triangle with |c_exact| <= |c_run|/(1-eps)), so the exact
    # multiplicative value perturbation is
    # (B+b)^2 (C+c)^2 - B^2 C^2, b = (eps/(1-eps))*Lambda_b, c likewise.
    abs_v = np.sqrt(vre ** 2 + vim ** 2)
    inflate = eps / (1.0 - eps) if eps < 1 else float('inf')
    b_cast = inflate * (np.abs(base) @ abs_v)
    c_cast = inflate * (np.abs(corr) @ abs_v)
    rb = np.sqrt(hb) + b_cast
    rc = np.sqrt(hc) + c_cast
    delta_g = rb * rb * rc * rc - hb * hc
    # triangle charge: delta_g >= 0 pointwise but the KERNEL is signed, so
    # the sound value-perturbation bound sums |kern*p2|*delta_g.
    delta_q_cast = float(np.sum(w * np.abs(kern * p2) * delta_g)) \
        if eps > 0 else 0.0
    terms = [float(w[i] * g[i]) for i in range(npts)]
    q = math.fsum(terms)
    e_pts = [float(w[i] * eg[i]) for i in range(npts)]
    e_pts_round = r2249.U * math.fsum([abs(e_pts[i]) for i in range(npts)])
    e_prod = r2249.U * math.fsum([abs(t) for t in terms])
    e_sum = math.fsum(e_pts) + e_pts_round + e_prod + r2249.U * abs(q)
    e_total = r2249.INFLATE * e_sum
    # cast enters the value enclosure: q_exact in [q - d, q + d]
    margin_lo = -(q + e_total + delta_q_cast)
    margin_hi = -(q - e_total - delta_q_cast)
    vp = r2249.r80.family_values(fam, r2249.K, 0.5 - 2j * np.pi * grid,
                                 xw_list)
    lbp = base @ vp
    lcp = corr @ vp
    pp = np.real(r2249.r59.P_from_nodes(grid,
                                        r2249.r80.counterpart_nodes(rho)))
    kp = r2249.r59.rig.sigma_vec(2.0 * np.pi * grid)
    for number, weight in primes:
        kp = kp + 2 * weight / math.sqrt(number) * np.cos(
            2 * np.pi * grid * math.log(number))
    gp = kp * pp * pp * np.abs(lbp) ** 2 * np.abs(lcp) ** 2
    q_plain = float(np.trapezoid(gp, grid))
    return {'q': q, 'e_total': e_total, 'delta_q_cast': delta_q_cast,
            'margin_lo': margin_lo, 'margin_hi': margin_hi,
            'gl_identity_ok': gl_identity_ok, 'npts': int(npts),
            'base_md5': hashlib.md5(np.ascontiguousarray(base).tobytes())
            .hexdigest(),
            'corr_md5': hashlib.md5(np.ascontiguousarray(corr).tobytes())
            .hexdigest(),
            'q_plain': q_plain,
            'cancel_factor': math.fsum([abs(t) for t in terms]) / abs(q)}


def main():
    started = time.time()
    rows = json.loads(REPAIR.read_text())['coefficient_rows']
    eps = float(eps_cast_exact(rows))
    base_rep, corr_rep = coefficient_mid_floats(rows)
    print('eps_cast =', eps, flush=True)

    # ---- control arm (the rig's own solve, captured owner) ----
    t0 = time.time()
    rho, nodes, values, fam = r2249.build()
    xw_list = weight_grid(fam)
    a_mat = r2249.r80.family_values(fam, r2249.K,
                                    np.asarray(nodes, complex), xw_list).T
    base_cap = np.linalg.solve(a_mat, np.ones(len(nodes), complex))
    corr_cap = np.linalg.solve(a_mat, np.asarray(values, complex))

    # order-faithfulness: the rig's own solve vs the capture hex arrays
    _, _, base_hex, corr_hex = direct2295.filon.load_owner()
    order_base_ok = bool(np.array_equal(base_cap,
                                        np.asarray(base_hex, complex)))
    order_corr_ok = bool(np.array_equal(corr_cap,
                                        np.asarray(corr_hex, complex)))
    print('order_base_ok', order_base_ok, 'order_corr_ok', order_corr_ok,
          flush=True)

    print('control arm...', flush=True)
    control = chain(base_cap, corr_cap, fam, nodes, values, rho, 0.0, t0)
    committed = json.loads(COMMITTED.read_text())['diagnostics']
    q_drift = abs(control['q'] - committed['q'])
    print('control q =', repr(control['q']), ' committed =',
          repr(committed['q']), ' |drift| =', q_drift, flush=True)

    # ---- treatment arm (repaired coefficients) ----
    print('treatment arm...', flush=True)
    treatment = chain(base_rep, corr_rep, fam, nodes, values, rho, eps, t0)
    print('treatment q =', repr(treatment['q']), flush=True)

    # ledger verdict (mirror 2249 diag channels)
    tail_2248 = 4894093747.764274
    known_2109 = 74601530.30234718
    charge_import = tail_2248 * (21.0 / 62.0) + known_2109
    charge_uncond = tail_2248 * (26.0 / 62.0) + known_2109
    verdict_import = treatment['margin_lo'] - charge_import
    verdict_uncond = treatment['margin_lo'] - charge_uncond
    survives = verdict_import > 0 and verdict_uncond > 0

    artifact = {
        'record': 2665,
        'leg': 'l1_margin',
        'status': 'L1-MARGIN-SURVIVES-REPAIR' if survives
        else 'L1-MARGIN-REPAIR-FAIL',
        'order_faithful_to_capture': {'base': order_base_ok,
                                      'corr': order_corr_ok},
        'eps_cast': eps,
        'control': control,
        'control_q_drift_vs_committed': q_drift,
        'treatment': treatment,
        'committed_q': committed['q'],
        'committed_margin_lo': committed['margin_lo_certified'],
        'charge_import': charge_import,
        'charge_uncond': charge_uncond,
        'verdict_import': verdict_import,
        'verdict_uncond': verdict_uncond,
        'timing_sec': time.time() - started,
        'producer_go': False,
        'rh_claim': False,
        'provenance': {
            'repair': 'results/2338_exact_interpolation_repair.json',
            'committed': 'results/2249_l1_enclosure.json',
            'rig': 'scripts/routea_weighted_zero_l1_enclosure_2249.py',
        },
    }
    out = ROOT / 'results/2665_l1_margin_repair.json'
    out.write_text(json.dumps(artifact, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: artifact[k] for k in (
        'status', 'order_faithful_to_capture', 'control_q_drift_vs_committed',
        'committed_margin_lo', 'treatment_margin_lo' if False else 'verdict_import',
        'verdict_uncond', 'timing_sec')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
