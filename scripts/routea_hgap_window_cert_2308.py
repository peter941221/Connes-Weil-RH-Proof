"""2308 -- certified continuous window weight enclosure for the hgap finite-window half.

The 2295-2302 window lane measured the finite-window charge

    charge = int_{|xi| <= 40} |kernel(xi)| |ann(xi)|^2 T(xi) dxi

with *sampled* float64 weights at cell centres (proxies 0.0405x - 0.0494x
of the 1e7 hgap budget, screen grade).  2302's registered next obligation:
a continuous kernel/annihilator weight bound on the same cells, retaining
all 41136 prime powers and signed cancellations before bounding variation,
followed by a directed summation.

This instrument discharges the weight side of that obligation:

- per dyadic cell [c-d, c+d], sup_cell |kernel| is enclosed by a centre
  Taylor polynomial (degree K = 4) of the *convention* kernel -- the 2280
  frozen float64 parameterization
      kernel(xi) = sigma(2 pi xi) + 2 sum_n w_n cos(2 pi log(n) xi),
      n over the 41136 prime powers <= 492475, w_n = log(p)/sqrt(n) --
  with interval coefficients carrying a certified float64 execution budget,
  plus a Lagrange remainder bounded by the certified S-moment ladder (every
  one of the 41136 signed terms enters each moment BEFORE the triangle
  bound: the 2291 grouping law one level deeper);
- sup_cell |ann|^2 is the interval product form of the four frozen nodes
  (argument and node casts covered by a 4u relative widening);
- the cell charge h * supW * T_cell is summed in mpmath.iv, where T_cell
  is the 2302 perturbation majorant (inherited at its recorded execution
  model grade).

Verdict target: WINDOW-WEIGHT-CERTIFIED at mixed grade -- the weight factor
is interval-certified; the transform-side perturbation majorant and the
object difference radii are inherited from the 2297/2301/2302 chain at
their declared standard-arithmetic/BLAS rounding model.  No hgap
certificate, no producer GO, no RH claim.
"""
import json
import math
import os
import time
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np

import routea_regenerated_carrier_evaluator_2301 as evaluator
import routea_local_frequency_taylor_screen_2302 as window2302

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/2308_window_weight_certified.json'
STEP_OUT = ROOT / 'results/2308_window_weight_step_den{denom}.json'
BUDGET = 1.0e7
TAYLOR_DEGREE = 4
TWO_PI_FLOAT = 2.0 * math.pi               # the 2280 convention constant
UNIT = mp.mpf(2) ** -53                    # float64 unit roundoff

# ---------------------------------------------------------------------------
# sigma(u) = log pi - Re psi(1/4 - i u/2) as an interval routine.
# Verbatim from routea_interval_kernel_2043.sigma_arch_iv (Stirling shift 8,
# six Bernoulli terms, analytic remainder (1/12) 8.25^-14 <= 3.97e-15) with
# one tightening: the Bernoulli coefficients are rebuilt INSIDE the interval
# context from exact integer ratios (the 2043 copies were built from 15-dps
# scalars) and the remainder enters as an interval upper.  u is an iv.mpf
# interval; the result encloses sigma(u) for every u in it.
# ---------------------------------------------------------------------------


def build_bernoulli_iv():
    numerators = [1, -1, 1, -1, 1, -691]
    denominators = [12, 120, 252, 240, 132, 32760]
    return [mp.iv.mpf(n)/mp.iv.mpf(d) for n, d in zip(numerators, denominators)]


def sigma_arch_iv(u, bernoulli_iv, rem_hi):
    iv = mp.iv
    x = iv.mpf(8)
    x += iv.mpf(1)/iv.mpf(4)                 # Re w = 8.25 (exact)
    y = u / 2
    y2 = y * y
    m2 = x * x + y2                          # |w|^2 >= 8.25^2 > 0
    two = iv.mpf(2)
    re_psi = iv.log(m2) / two - x / (two * m2)
    w2_re = x * x - y2
    w2_im = two * x * y
    pw_re, pw_im = w2_re, w2_im
    for c in bernoulli_iv:
        pw2 = pw_re * pw_re + pw_im * pw_im
        re_psi = re_psi - (pw_re / pw2) * c
        nre = pw_re * w2_re - pw_im * w2_im
        nim = pw_re * w2_im + pw_im * w2_re
        pw_re, pw_im = nre, nim
    xq = iv.mpf(1)/iv.mpf(4)
    for j in range(8):
        xj = xq + iv.mpf(j)
        re_psi = re_psi - xj / (xj * xj + y2)
    logpi = iv.log(iv.pi)
    rem = iv.mpf([0, rem_hi])
    sig = logpi - (re_psi + rem)
    return iv.mpf([mp.mpf(sig.a), mp.mpf(sig.b)])


def sigma_remainder_upper():
    with mp.workdps(60):
        rem = (mp.mpf(1)/mp.mpf(12))/mp.power(mp.mpf('8.25'), 14)
        return float(mp.mpf(rem) * (1 + mp.mpf('1e-30'))) + 1e-25


def arch_derivative_bound(order):
    """sup_u |sigma^(order)(u)| <= 2^-order order! 4^(order+1) (1+2*4^-(order+1)).

    |psi^(j)(z)| = j! |sum (z+n)^-(j+1)| <= j! sum (n+1/4)^-(j+1) for
    Re z = 1/4; sum_{n>=0} (n+1/4)^-(j+1) = 4^(j+1) sum (4n+1)^-(j+1)
    <= 4^(j+1) (1 + 4^-(j+1) zeta(j+1)) <= 4^(j+1) (1 + 2*4^-(j+1)).
    """
    iv = mp.iv
    two = iv.mpf(2)
    four = iv.mpf(4)
    value = (two ** (-order)) * iv.mpf(math.factorial(order)) * (four ** (order+1))
    value = value * (iv.mpf(1) + two * (four ** (-(order+1))))
    return value


def arch_coefficient_bound(order):
    """|d^order/dxi^order sigma(2 pi xi)| <= (2 pi)^order * arch_derivative_bound."""
    return (mp.iv.mpf(TWO_PI_FLOAT) ** order) * arch_derivative_bound(order)


# ---------------------------------------------------------------------------
# prime-power book and the certified S-moment ladder
# ---------------------------------------------------------------------------


def prime_book(source):
    _, families, _, _ = source.load_owner()
    support = 2.0 * max(width * width for width, _ in families)
    primes = source.rig.prime_powers_up_to(math.exp(support))
    numbers = np.asarray([n for n, _ in primes], dtype=np.int64)
    lam = np.asarray([w for _, w in primes], dtype=float)
    logn = np.asarray([math.log(int(n)) for n in numbers], dtype=float)
    weights = lam / np.sqrt(numbers.astype(float))
    phi = TWO_PI_FLOAT * logn
    cutoff = int(math.floor(math.exp(support)))
    if numbers.size != 41136 or cutoff != 492475 or int(numbers[-1]) > cutoff:
        raise ValueError('prime-power book changed')
    if not np.array_equal(np.diff(numbers) > 0, np.ones(numbers.size-1, bool)):
        raise ValueError('prime-power book not sorted-distinct')
    return {'support': support, 'cutoff': cutoff, 'numbers': numbers, 'lam': lam,
            'logn': logn, 'weights': weights, 'phi': phi}


def moment_ladder(book, degree):
    """A_j = sum 2 w phi^j, B_j = sum 2 w phi^j log n, in interval arithmetic.

    All 41136 signed terms accumulate BEFORE any triangle/norm step: the
    factors 2 w, phi and log n enter as exact-real products of float64
    values (mpmath.iv point products of two 53-bit values are exact in 266
    bits), so each A_j/B_j encloses the exact-real moment of the frozen
    float64 parameterization; the conversion to the true Weil parameters is
    carried by the (6j+40)u budget terms below.
    """
    iv = mp.iv
    two = iv.mpf(2)
    two_pi = iv.mpf(TWO_PI_FLOAT)
    A = [iv.mpf(0) for _ in range(degree+2)]
    B = [iv.mpf(0) for _ in range(degree+1)]
    numbers, lam, logn = book['numbers'], book['lam'], book['logn']
    for index in range(numbers.size):
        w2 = two * (iv.mpf(float(lam[index])) / iv.sqrt(iv.mpf(int(numbers[index]))))
        phi = two_pi * iv.mpf(float(logn[index]))
        logn_iv = iv.mpf(float(logn[index]))
        power = iv.mpf(1)
        for j in range(degree+2):
            A[j] += w2 * power
            if j <= degree:
                B[j] += w2 * power * logn_iv
            power *= phi
    return A, B


def coefficient_error_budget(moments, cell_abs, degree):
    """Certified float64 execution budget for the center derivative estimates.

    est_j = fl64 sum_n (2 w phi^j) * [cos, -sin, -cos, sin](theta_n(c)) aims
    at f^(j)(c) of the true Weil kernel.  Sources, relative to sum 2 w phi^j:
      parameters: w cast 1u, phi chain (2 pi cast + log cast + product) 6j u,
      libm cos/sin 1u, product chain (j+2)u, pairwise summation 20u
      -> (6j+24)u <= (6j+40)u;  the theta argument error chain is
      u*(4 pi |c| log n + 3 |theta|) <= u*10 pi |c| log n
      -> 40 |c| u B_j;  plus 2u absolute.
    """
    iv = mp.iv
    A, B = moments
    unit = iv.mpf(UNIT)
    budgets = []
    for j in range(degree+1):
        value = unit * ((6*j + 40) * A[j] + 40 * cell_abs * B[j] + iv.mpf(2))
        budgets.append(value)
    return budgets


# ---------------------------------------------------------------------------
# certified weight side on one dyadic grid
# ---------------------------------------------------------------------------


def certified_weight_side(centers, cell_radius, book, moments, chunk=128):
    """Per-cell certified sup |kernel| and sup |ann|^2 (floats, upper bounds)."""
    iv = mp.iv
    degree = TAYLOR_DEGREE
    count = len(centers)
    bernoulli_iv = build_bernoulli_iv()
    rem_hi = sigma_remainder_upper()
    arch = [arch_coefficient_bound(j) for j in range(degree+1)]
    arch_rem = arch_derivative_bound(degree+1) * \
        (iv.mpf(TWO_PI_FLOAT) ** (degree+1))
    A, B = moments
    factor_cast = iv.mpf(1) + (6*degree+30) * iv.mpf(UNIT)   # true-parameter cast
    delta = iv.mpf(Fraction(cell_radius * 2).numerator) / \
        iv.mpf(Fraction(cell_radius * 2).denominator) / 2      # exact h/2
    remainder = (delta ** (degree+1)) / math.factorial(degree+1) * \
        (A[degree+1] * factor_cast + arch_rem)
    rem_float = nextafter_hi(float(remainder.b))
    inv_fact = [mp.mpf(1)/mp.mpf(math.factorial(j)) for j in range(degree+1)]
    w2phi = [2.0 * book['weights'] * (book['phi'] ** j) for j in range(degree+1)]
    cos_of = (1, 0, 1, 0)          # cos, sin, cos, sin for j mod 4
    sign_of = (1, -1, -1, 1)       # f^(j) = sign * sum 2 w phi^j trig(theta)
    estimates = np.empty((count, degree+1))
    for start in range(0, count, chunk):
        stop = min(start+chunk, count)
        theta = book['phi'][None, :] * centers[start:stop, None]
        cos_t = np.cos(theta)
        sin_t = np.sin(theta)
        for j in range(degree+1):
            trig = cos_t if cos_of[j % 4] else sin_t
            estimates[start:stop, j] = sign_of[j % 4] * np.sum(
                w2phi[j][None, :] * trig, axis=1)
        del theta, cos_t, sin_t
    kernel_sup = np.empty(count)
    ann_sup = np.empty(count)
    delta_fl = cell_radius
    for index in range(count):
        center = float(centers[index])
        cell_abs = iv.mpf(abs(center))
        budgets = coefficient_error_budget(moments, cell_abs, degree)
        coefficients = []
        # j = 0: certified sigma at the (cast-widened) true argument
        u_point = TWO_PI_FLOAT * center
        u_inc = 4 * UNIT * abs(u_point) + 1e-30
        u_iv = iv.mpf([u_point - u_inc, u_point + u_inc])
        sigma0 = sigma_arch_iv(u_iv, bernoulli_iv, rem_hi)
        err0 = float(budgets[0].b)
        e0 = float(estimates[index, 0])
        coefficients.append(iv.mpf(tight_interval(e0, err0)) + sigma0)
        for j in range(1, degree+1):
            err = float(budgets[j].b) + float(arch[j].b)
            ej = float(estimates[index, j])
            coefficients.append(iv.mpf(tight_interval(ej, err)))
        delta_iv = iv.mpf([-delta_fl, delta_fl])
        accumulate = coefficients[degree] * inv_fact[degree]
        for j in range(degree-1, -1, -1):
            accumulate = accumulate * delta_iv + coefficients[j] * inv_fact[j]
        poly_sup = max(abs(float(accumulate.a)), abs(float(accumulate.b)))
        kernel_sup[index] = nextafter_hi(poly_sup + rem_float)
        # annihilator: four frozen nodes, cast-widened, product form
        x_inc = delta_fl + 4 * UNIT * abs(center)
        x_iv = iv.mpf([center - x_inc, center + x_inc])
        acc_re = iv.mpf(1)
        acc_im = iv.mpf(0)
        for node_re, node_im in ((0.445, 39.25244858548658),
                                 (-0.445, 39.25244858548658),
                                 (0.445, -39.25244858548658),
                                 (-0.445, -39.25244858548658)):
            re_slack = 4 * UNIT * abs(node_re)
            im_slack = 4 * UNIT * abs(node_im)
            fre = iv.mpf([node_re - re_slack, node_re + re_slack])
            fim = iv.mpf([node_im - im_slack, node_im + im_slack]) + \
                iv.mpf(TWO_PI_FLOAT) * x_iv
            nre = acc_re * fre - acc_im * fim
            nim = acc_re * fim + acc_im * fre
            acc_re, acc_im = nre, nim
        ann_sq = acc_re * acc_re + acc_im * acc_im
        ann_sup[index] = nextafter_hi(float(ann_sq.b))
    return {'kernel_sup': kernel_sup, 'ann_sup': ann_sup,
            'remainder_upper': rem_float,
            'A_upper': [float(a.b) for a in A],
            'B_upper': [float(b.b) for b in B]}


def nextafter_hi(value):
    return float(np.nextafter(value, np.inf))


def tight_interval(center, radius):
    """Float interval [center-radius, center+radius] inflated one ulp outward.

    The two float64 subtractions/additions and the rounding of a certified
    `radius` upper can each shrink an endpoint by up to half an ulp; one
    outward nextafter per side covers the full deficit.
    """
    return [float(np.nextafter(center - radius, -np.inf)),
            float(np.nextafter(center + radius, np.inf))]


# ---------------------------------------------------------------------------
# one grid: T-side (inherited model), float crosscheck, directed assembly
# ---------------------------------------------------------------------------


def grid_inputs():
    source = window2302.read_source()
    platform = evaluator.platform_contract()
    carrier = evaluator.bridge.refined.remainder.carrier
    capture, families, base, correction = carrier.SOURCE.load_owner()
    model, totals, _ = evaluator.prepare(families, base, correction)
    pi_value = evaluator.midpoint_extended(mp.iv.pi)
    series = window2302.generalized_series(6 + window2302.TAYLOR_ORDER)
    table = window2302.derivative_polynomials(model, window2302.TAYLOR_ORDER)
    errors, support, constants = window2302.derivative_error_bounds(
        model, totals, pi_value, window2302.TAYLOR_ORDER)
    owner = evaluator.bridge.refined.remainder.jets.repaired
    object_radii = {
        channel: sum((mp.iv.mpf(source['charges'][channel][slot]['upper'])
                      for slot in ('coefficient', 'geometry')), mp.iv.mpf(0))
        + mp.iv.mpf(json.loads(
            evaluator.bridge.refined.OUT.read_text(encoding='utf-8'))
            ['refined_reading'][channel + '_radius']['upper'])
        for channel in totals}
    half = max(width * width for width, _ in families)
    return {'source': source, 'platform': platform, 'carrier': carrier,
            'families': families, 'capture': capture, 'model': model,
            'totals': totals, 'pi_value': pi_value, 'series': series,
            'table': table, 'errors': errors, 'support': support,
            'object_radii': object_radii, 'owner': owner, 'half': half}


def run_grid(denom, inputs, book, moments):
    mp.mp.dps = mp.iv.dps = 80
    owner = inputs['owner']
    render = evaluator.bridge.refined.remainder.propagation.interval_text
    step = 1.0 / denom
    count = round(80 / step)
    centers = -40.0 + (np.arange(count) + 0.5) * step
    for center in centers:
        index = (float(center) + 40.0) * denom - 0.5
        if index != round(index) or Fraction.from_float(float(center)) != \
                Fraction(-40) + Fraction(2*round(index) + 1, 2*denom):
            raise ValueError('center not dyadic')
    radius, gap = window2302.coverage_radius(step, centers)
    if float(owner.upper(gap)) != 0.0:
        raise ValueError('dyadic grid has midpoint gap')
    started = time.time()
    remainder = window2302.taylor_remainders(
        inputs['totals'], inputs['support'], radius, window2302.TAYLOR_ORDER)
    jets = window2302.evaluate_derivatives(
        inputs['model'], centers, inputs['pi_value'], inputs['series'],
        inputs['table'])
    suprema = window2302.cell_suprema(jets, inputs['errors'], remainder, radius)
    del jets
    base_radius = nextafter_hi(float(owner.upper(inputs['object_radii']['base'])))
    corr_radius = nextafter_hi(float(owner.upper(inputs['object_radii']['corr'])))
    terms = evaluator.bridge.refined.propagation.error_terms(
        suprema[:, 0], suprema[:, 1], base_radius, corr_radius)
    t_sum = terms[0] + terms[1] + terms[2]
    transform_sec = time.time() - started
    weight = certified_weight_side(centers, step/2, book, moments)
    kernel_fl, prime_count = inputs['carrier'].SOURCE.prime_kernel(
        centers, 2.0 * inputs['half'])
    if prime_count != 41136:
        raise ValueError('incomplete kernel')
    ann_fl = np.abs(inputs['carrier'].SOURCE.annihilator(centers)) ** 2
    proxy_same = float(np.sum(np.abs(kernel_fl) * ann_fl * t_sum) * step)
    ratio_kernel = weight['kernel_sup'] / np.maximum(np.abs(kernel_fl), 1e-300)
    ratio_ann = weight['ann_sup'] / np.maximum(ann_fl, 1e-300)
    # directed assembly in mpmath.iv
    iv = mp.iv
    h_iv = iv.mpf(1) / iv.mpf(denom)
    charge = iv.mpf(0)
    for index in range(count):
        cell = h_iv * iv.mpf(weight['kernel_sup'][index]) * \
            iv.mpf(weight['ann_sup'][index]) * iv.mpf(float(t_sum[index]))
        charge += cell
    if float(charge.a) <= 0 or float(charge.b) < float(charge.a):
        raise ValueError('charge interval inadmissible')
    row = {
        'step_denom': denom, 'step': step, 'cell_count': count,
        'coverage_radius': render(radius),
        'midpoint_coordinate_gap': render(gap),
        'taylor_degree': TAYLOR_DEGREE,
        'prime_power_count': prime_count, 'prime_limit': int(book['cutoff']),
        'support': 2.0 * inputs['half'],
        'charge_render': render(charge),
        'charge_lo': float(charge.a), 'charge_hi': float(charge.b),
        'charge_hi_float': nextafter_hi(float(charge.b)),
        'cert_over_budget': float(charge.b) / BUDGET,
        'sampled_weight_proxy_same_grid': proxy_same,
        'cert_over_proxy_same_grid': float(charge.b) / proxy_same,
        'cert_over_proxy_same_grid_lb': float(charge.a) / proxy_same,
        'kernel_sup_over_center_mean': float(np.mean(ratio_kernel)),
        'kernel_sup_over_center_max': float(np.max(ratio_kernel)),
        'ann_sup_over_center_mean': float(np.mean(ratio_ann)),
        'ann_sup_over_center_max': float(np.max(ratio_ann)),
        'kernel_taylor_remainder_upper': weight['remainder_upper'],
        'A_upper': weight['A_upper'], 'B_upper': weight['B_upper'],
        't_sum_max': float(np.max(t_sum)), 't_sum_mean': float(np.mean(t_sum)),
        'max_cell_sup_base': float(np.max(suprema[:, 0])),
        'max_cell_sup_corr': float(np.max(suprema[:, 1])),
        'base_radius': render(mp.iv.mpf(base_radius)),
        'corr_radius': render(mp.iv.mpf(corr_radius)),
        'timing_sec': {'transform': transform_sec,
                       'total': time.time() - started},
    }
    return row


# ---------------------------------------------------------------------------
# modes
# ---------------------------------------------------------------------------


def mode_constants(book, moments):
    mp.mp.dps = mp.iv.dps = 80
    A, B = moments
    bernoulli_iv = build_bernoulli_iv()
    rem_hi = sigma_remainder_upper()
    anchors = []
    for u_float in (0.0, TWO_PI_FLOAT * 20.0, -TWO_PI_FLOAT * 20.0):
        got = sigma_arch_iv(mp.iv.mpf([u_float, u_float]), bernoulli_iv, rem_hi)
        reference = float(inputs_book_rig().sigma_vec(np.asarray([u_float]))[0])
        anchors.append({'u': u_float, 'sigma_lo': float(got.a),
                        'sigma_hi': float(got.b), 'sigma_float': reference,
                        'contains': float(got.a) <= reference <= float(got.b)})
    payload = {'record': 2308, 'mode': 'constants',
               'prime_power_count': int(book['numbers'].size),
               'prime_limit': int(book['cutoff']),
               'S_moment_upper_A': [float(a.b) for a in A],
               'S_moment_upper_B': [float(b.b) for b in B],
               'budget_units_U': float(UNIT),
               'err_j_at_c40': [float((coefficient_error_budget(
                   moments, mp.iv.mpf(40), TAYLOR_DEGREE)[j]).b)
                   for j in range(TAYLOR_DEGREE+1)],
               'arch_coefficient_bounds': [float(arch_coefficient_bound(j).b)
                                           for j in range(TAYLOR_DEGREE+1)],
               'sigma_anchors': anchors}
    print(json.dumps(payload, indent=2), flush=True)


def inputs_book_rig():
    carrier = evaluator.bridge.refined.remainder.carrier
    return carrier.SOURCE.rig


def mode_reduce():
    rows = []
    for denom in (64, 128, 256):
        path = Path(str(STEP_OUT).format(denom=denom))
        if path.is_file():
            rows.append(json.loads(path.read_text(encoding='utf-8')))
    if not rows:
        raise SystemExit('no step artifacts')
    rows.sort(key=lambda row: row['step_denom'])
    best = rows[-1]
    source = json.loads(
        (ROOT / 'results/2302_local_frequency_taylor_screen.json')
        .read_text(encoding='utf-8'))
    finest_proxy_2302 = min(row['sampled_weight_proxy_charge']
                            for row in source['rows'])
    payload = {
        'record': 2308, 'status': 'WINDOW-WEIGHT-CERTIFIED',
        'grade': 'weight-side interval-certified; transform-side majorant and '
                 'object difference radii inherited from the 2297/2301/2302 '
                 'chain at its declared standard-arithmetic/BLAS model',
        'weight_certificate': True, 'certificate': False, 'hgap_closed': False,
        'budget': BUDGET, 'taylor_degree': TAYLOR_DEGREE,
        'interval': {'lib': 'mpmath.iv', 'dps': 80},
        'rows': [{'step_denom': row['step_denom'], 'cell_count': row['cell_count'],
                  'charge_hi': row['charge_hi'],
                  'charge_hi_float': row['charge_hi_float'],
                  'cert_over_budget': row['cert_over_budget'],
                  'sampled_weight_proxy_same_grid':
                      row['sampled_weight_proxy_same_grid'],
                  'cert_over_proxy_same_grid': row['cert_over_proxy_same_grid'],
                  'kernel_sup_over_center_mean': row['kernel_sup_over_center_mean'],
                  'ann_sup_over_center_mean': row['ann_sup_over_center_mean'],
                  'kernel_taylor_remainder_upper':
                      row['kernel_taylor_remainder_upper']} for row in rows],
        'best': {'step_denom': best['step_denom'], 'charge_hi': best['charge_hi'],
                 'cert_over_budget': best['cert_over_budget'],
                 'cert_over_proxy_same_grid': best['cert_over_proxy_same_grid']},
        'cross_record': {
            '2302_finest_sampled_proxy': finest_proxy_2302,
            'cert_over_2302_finest_proxy':
                best['charge_hi'] / finest_proxy_2302},
        'scope': 'continuous certified weight enclosure sup_cell |kernel| '
                 '|ann|^2 on dyadic cells via centre Taylor (degree 4) of the '
                 'frozen 2280 kernel convention with all 41136 prime powers '
                 'and signed cancellations, certified S-moment budgets, iv '
                 'annihilator product form, and an mpmath.iv directed cell '
                 'summation of h * supW * T_cell; T_cell (cell transform '
                 'suprema, derivative execution bounds, object difference '
                 'radii) is inherited from 2297/2301/2302 at its recorded '
                 'model grade; no hgap certificate',
        'nonclaims': [
            'the transform-side perturbation majorant and the object difference '
            'radii are inherited at the 2301/2302 declared rounding-model grade; '
            'only the weight factor is interval-certified',
            'the certified kernel bounds the true Weil kernel through the frozen '
            '2280 float64 parameterization with certified cast budgets; libm '
            'cos/sin and numpy pairwise summation enter inside those budgets as '
            'declared substrate trust',
            'sigma_arch_iv is the 2043 routine with iv-rebuilt Bernoulli '
            'coefficients (tightened); its analytic remainder is a bound, not a '
            'proof of the Stirling expansion',
            'finite window |xi| <= 40 only; the infinite tail is 2307 and is not '
            're-touched',
            'no hgap certificate, no producer GO, no RH claim'],
        'provenance': {
            'script': 'scripts/routea_hgap_window_cert_2308.py',
            'predecessor': 'results/2302_local_frequency_taylor_screen.json',
            'owner_capture': 'results/2275_gap_owner_audit.json',
        },
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'status': payload['status'],
                      'best': payload['best'],
                      'cross_record': payload['cross_record']}), flush=True)


def mode_selftest():
    import unittest
    mp.mp.dps = mp.iv.dps = 80
    source = window2302.read_source()
    carrier = evaluator.bridge.refined.remainder.carrier
    capture, families, base, correction = carrier.SOURCE.load_owner()
    book = prime_book(carrier.SOURCE)
    moments = moment_ladder(book, TAYLOR_DEGREE)
    A, B = moments
    iv = mp.iv

    class WindowWeightControls(unittest.TestCase):
        def test_book(self):
            self.assertEqual(book['numbers'].size, 41136)
            self.assertEqual(int(book['cutoff']), 492475)
            self.assertLessEqual(int(book['numbers'][-1]), int(book['cutoff']))
            for index in (0, 1, 2, 41135):
                n = int(book['numbers'][index])
                self.assertAlmostEqual(float(book['logn'][index]),
                                       math.log(n), delta=1e-14 * abs(math.log(n)))
            self.assertAlmostEqual(2.0 * max(w*w for w, _ in families),
                                   13.1072, delta=1e-12)

        def test_moment_ladder_encloses_floats(self):
            self.assertGreaterEqual(float(A[0].a), 0.0)
            float_a = 2.0 * float(np.sum(book['weights']))
            self.assertLessEqual(float_a, float(A[0].b) * (1 + 1e-12))
            self.assertGreaterEqual(float_a, float(A[0].a) * (1 - 1e-12))
            for j in (1, 4, 5):
                value = 2.0 * float(np.sum(book['weights'] * book['phi']**j))
                self.assertLessEqual(value, float(A[j].b) * (1 + 1e-12))
                self.assertGreaterEqual(value, float(A[j].a) * (1 - 1e-12))

        def test_budgets_dominate_dps100_reference(self):
            # two real cells, true-parameter dps-100 reference of the prime sum
            with mp.workdps(100):
                for center in (0.00390625 - 40 + 0.5*0.0078125, 19.99609375):
                    center_mp = mp.mpf(repr(center))
                    totals = {2: mp.mpf(0), 4: mp.mpf(0)}
                    for index in range(book['numbers'].size):
                        n = int(book['numbers'][index])
                        p = smallest_prime_factor(n)
                        logn_mp = mp.log(n)
                        phi_mp = 2 * mp.pi * logn_mp
                        common = 2 * (mp.log(p)/mp.sqrt(n)) * \
                            mp.cos(phi_mp*center_mp)
                        totals[2] -= common * phi_mp**2   # f'' = -sum 2w phi^2 cos
                        totals[4] += common * phi_mp**4   # f'''' = +sum 2w phi^4 cos
                    for power in (2, 4):
                        estimate = float(np.sum(
                            (2.0 * book['weights'] * book['phi']**power) *
                            ((-1)**(power//2)) *
                            np.cos(book['phi']*center)))
                        err = float(coefficient_error_budget(
                            moments, iv.mpf(abs(center)), TAYLOR_DEGREE
                            )[power].b)
                        self.assertLessEqual(abs(estimate - float(totals[power])),
                                             err * (1 + 1e-9),
                                             f'c={center} j={power}')

        def test_polynomial_dominates_grid(self):
            for center in (-39.99609375, 0.00390625, 19.99609375):
                half = 0.00390625
                side = certified_weight_side(np.asarray([center]), half, book,
                                             moments)
                bound = float(side['kernel_sup'][0])
                deltas = np.linspace(-half, half, 33)
                grid = np.abs(prime_eval(book, center + deltas) +
                              carrier.SOURCE.rig.sigma_vec(
                                  TWO_PI_FLOAT * (center + deltas)))
                self.assertLessEqual(float(np.max(grid)), bound * (1 + 1e-12))

        def test_ann_sup_dominates_grid(self):
            for center in (-39.99609375, 0.00390625, 19.99609375):
                half = 0.00390625
                side = certified_weight_side(np.asarray([center]), half, book,
                                             moments)
                bound = float(side['ann_sup'][0])
                deltas = np.linspace(-half, half, 33)
                grid = np.abs(carrier.SOURCE.annihilator(center + deltas))**2
                self.assertLessEqual(float(np.max(grid)), bound * (1 + 1e-12))
                self.assertGreaterEqual(bound, float(np.max(grid)) * 0.999)

        def test_convention_replication(self):
            centers = np.asarray([-39.99609375, 0.00390625, 19.99609375])
            mine = prime_eval(book, centers) + \
                carrier.SOURCE.rig.sigma_vec(TWO_PI_FLOAT * centers)
            theirs, count = carrier.SOURCE.prime_kernel(
                centers, 2.0 * max(w*w for w, _ in families))
            self.assertEqual(count, 41136)
            for a, b in zip(mine, theirs):
                self.assertLessEqual(abs(a - b), 1e-11 * max(abs(b), 1.0))

        def test_sigma_anchor(self):
            bernoulli_iv = build_bernoulli_iv()
            rem_hi = sigma_remainder_upper()
            for u_float in (0.0, 12.0, -251.3):
                got = sigma_arch_iv(iv.mpf([u_float, u_float]), bernoulli_iv,
                                    rem_hi)
                ref = float(carrier.SOURCE.rig.sigma_vec(
                    np.asarray([u_float]))[0])
                self.assertLessEqual(abs(ref - float(got.a)), 1e-9)
                self.assertLessEqual(abs(ref - float(got.b)), 1e-9)

        def test_arch_bounds(self):
            # crude finite-difference sanity of |sigma'| <= arch_derivative_bound(1)
            bound = float(arch_derivative_bound(1).b)
            self.assertGreater(bound, 8.0)
            self.assertLess(bound, 20.0)
            for u_float in (-40.0, 0.0, 40.0):
                step = 1e-4
                got = abs((float(carrier.SOURCE.rig.sigma_vec(
                    np.asarray([u_float+step]))[0]) -
                    float(carrier.SOURCE.rig.sigma_vec(
                        np.asarray([u_float-step]))[0])) / (2*step))
                self.assertLessEqual(got, bound)

        def test_end_to_end_mini_grid(self):
            inputs = grid_inputs()
            row = run_grid(32, inputs, book, moments)
            self.assertGreaterEqual(row['cert_over_proxy_same_grid'], 0.999)
            self.assertLess(row['cert_over_proxy_same_grid'], 12.0)
            self.assertGreater(row['cert_over_proxy_same_grid_lb'], 0.999)
            self.assertEqual(row['cell_count'], 2560)

    return unittest.TextTestRunner(verbosity=2).run(
        unittest.defaultTestLoader.loadTestsFromTestCase(WindowWeightControls))


def smallest_prime_factor(n):
    if n % 2 == 0:
        return 2
    d = 3
    while d * d <= n:
        if n % d == 0:
            return d
        d += 2
    return n


def prime_eval(book, xi):
    xi = np.asarray(xi, dtype=float)
    total = np.zeros_like(xi)
    for lo in range(0, book['numbers'].size, 256):
        hi = min(lo+256, book['numbers'].size)
        total += 2.0 * np.sum(
            book['weights'][lo:hi, None] *
            np.cos(book['phi'][lo:hi, None] * xi[None, :]), axis=0)
    return total


def main():
    mode = os.environ.get('MODE', 'step')
    mp.mp.dps = mp.iv.dps = 80
    if mode == 'reduce':
        mode_reduce()
        return
    if mode == 'selftest':
        result = mode_selftest()
        raise SystemExit(0 if result.wasSuccessful() else 1)
    carrier = evaluator.bridge.refined.remainder.carrier
    book = prime_book(carrier.SOURCE)
    started = time.time()
    moments = moment_ladder(book, TAYLOR_DEGREE)
    print(json.dumps({'moment_ladder_sec': time.time()-started,
                      'A0_upper': float(moments[0][0].b),
                      'A5_upper': float(moments[0][5].b)}), flush=True)
    if mode == 'constants':
        mode_constants(book, moments)
        return
    inputs = grid_inputs()
    denom = int(os.environ.get('STEP_DENOM', '128'))
    row = run_grid(denom, inputs, book, moments)
    path = Path(str(STEP_OUT).format(denom=denom))
    path.write_text(json.dumps(row, indent=2, allow_nan=False) + '\n',
                    encoding='utf-8')
    print(json.dumps(row), flush=True)


if __name__ == '__main__':
    main()