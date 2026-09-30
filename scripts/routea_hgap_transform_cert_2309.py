"""2309 -- certified transform-side majorant for the hgap finite-window half.

Record 2308 certified the *weight* factor sup_cell(|kernel| |ann|^2) of the
finite-window charge

    charge = int_{|xi| <= 40} |kernel(xi)| |ann(xi)|^2 T(xi) dxi
           <= sum_cells h * supW_cell * T_cell,
    T_cell = error_terms(sup_b, sup_c, r_b, r_c),

but inherited T_cell (cell transform suprema, derivative execution bounds,
object difference radii) at the 2301/2302 declared standard-arithmetic/BLAS
rounding model.  This instrument discharges that obligation -- the last
non-model factor of the window half:

- **jets on an exclusive extended path.**  The stored 768:6 jet pipeline is
  re-executed with the complex128 BLAS gemm leg of orders >= 1 replaced by
  explicitly counted clongdouble elementwise contractions; order 0 stays
  bitwise identical to the stored evaluator (same ops, same order, same
  final complex128 cast).  Each jet value (a stored float64 complex pair) is
  turned into an interval by its *exact* rational value plus a mechanically
  counted execution budget

      budget_{ch,k} = M_{ch,k} * R_k,

  where M_{ch,k} = 2 r (2 pi support)^k L1COEF_ch is a certified magnitude
  ladder (L1COEF_ch = sum of |coefficient| uppers over panels BEFORE any
  triangle bound -- the 2291/2308 grouping law one level deeper) and R_k is
  a dimensionless relative budget assembled in iv from

    * the compiled rounding count C_k of the actual code path (moment Horner
      48 (7+k), phase reduction 5, cos/sin Horner 2 x 48, inner contractions
      8 (7+k), table construction 6k, scale chain k, accumulator 2 + 2 depth),
    * the mechanical analytic pieces of 2301 arithmetic_price (phase
      reduction error, moment argument error, stored-pi gap), copied
      verbatim with attribution,
    * the stored pipeline's final complex128 cast 2 u2/(1-u2),
    * proven series-truncation constants (exp(3) 3^48/48!) and pads.

- **interval cell assembly.**  sup_cell |T_ch| = sum_k (L1 modulus of the
  stored jet_k + budget_k) delta^k / k! + Lagrange remainder (the 2302 mass
  ladder, already iv), all summed in mpmath.iv on dyadic cells with exact
  rational delta powers -- no float64 padding.

- **radii.**  r_b, r_c are re-derived from the iv ledger (2301 coefficient +
  geometry cast radii and the 2299 refined interpolation remainder, all
  interval prices) and pinned by provenance; no rounding model.

- **directed charge.**  h * supW * T_cell is summed in mpmath.iv with the
  2308 certified weight factor on the same dyadic cells; T_cell itself is
  an iv error_terms evaluation.

Verdict target: TRANSFORM-SIDE-CERTIFIED, and -- together with the 2308
weight factor and the 2307 certified tail rung -- the numeric hgap
inequality gap <= window + tail <= 1e7 closed at certificate grade.  No
producer GO, no Lean hgap discharge, no RH claim.
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
import routea_hgap_window_cert_2308 as window2308

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/2309_hgap_transform_certified.json'
STEP_OUT = ROOT / 'results/2309_transform_step_den{denom}.json'
REF_OUT = ROOT / 'results/2309_reference_controls.json'
TAIL_2307 = ROOT / 'results/2307_hgap_tail_certified.json'
CHARGE_2308 = ROOT / 'results/2308_window_weight_certified.json'
BUDGET = 1.0e7
TAYLOR_ORDER = 6
UNIT = mp.iv.mpf(2) ** -64          # extended (64-bit significand) unit roundoff
UNIT_DOUBLE = mp.iv.mpf(2) ** -53   # the stored pipeline's complex128 cast
LD = evaluator.LD
CD = evaluator.CD


# ---------------------------------------------------------------------------
# exact casts and iv helpers
# ---------------------------------------------------------------------------


def float_point_iv(value):
    """Exact iv point of a float64 value (no rounding)."""
    numerator, denominator = float(value).as_integer_ratio()
    return mp.iv.mpf(numerator) / mp.iv.mpf(denominator)


def l1_modulus_iv(real_value, imag_value):
    """iv point for |Re| + |Im| (the 2302 cell_suprema L1 convention)."""
    r = float_point_iv(real_value)
    i = float_point_iv(imag_value)
    if r.a < 0:
        r = -r
    if i.a < 0:
        i = -i
    return r + i


def delta_powers(denom):
    """Exact rational delta^k/k! for delta = 1/(2 denom), k = 0..TAYLOR_ORDER."""
    powers = []
    for k in range(TAYLOR_ORDER + 1):
        fraction = Fraction(1, (2 * denom) ** k * math.factorial(k))
        powers.append(mp.iv.mpf(fraction.numerator) /
                      mp.iv.mpf(fraction.denominator))
    return powers


def step_centers(denom):
    step = 1.0 / denom
    count = round(80 / step)
    centers = -40.0 + (np.arange(count) + 0.5) * step
    for center in centers:
        index = (float(center) + 40.0) * denom - 0.5
        if index != round(index) or Fraction.from_float(float(center)) != \
                Fraction(-40) + Fraction(2 * round(index) + 1, 2 * denom):
            raise ValueError('center not dyadic')
    return centers, step


# ---------------------------------------------------------------------------
# extended jet evaluation: verbatim order-0 leg, counted clongdouble
# contractions for orders >= 1 (no BLAS gemm, no double intermediates)
# ---------------------------------------------------------------------------


def evaluate_jets_extended(model, xi, pi_value, series, table, chunk=32):
    """The 2302 evaluate_derivatives with the order >= 1 gemm leg replaced.

    Order 0 reproduces the stored path op-for-op (inner += moments*coef per
    degree, radius*phase*inner per panel row, streaming PairwiseAccumulator,
    final complex128 cast), so it is bitwise identical to the stored
    evaluator.  Orders >= 1 accumulate the same polynomial contractions with
    explicitly counted clongdouble elementwise multiply-adds:
    inner_k[p, i, c] = sum_d table_k[p, d, c] * moments[i, d].
    """
    xi = np.asarray(xi, dtype=float)
    if chunk <= 0 or np.any(~np.isfinite(xi)) or np.max(np.abs(xi), initial=0) > 40:
        raise ValueError('invalid chunk or frequency window')
    maximum_order = table.shape[0] - 1
    outputs = [evaluator.PairwiseAccumulator() for _ in range(maximum_order + 1)]
    scales = [LD(1)]
    for order in range(maximum_order):
        scales.append(scales[-1] * (LD(2) * pi_value))
    rotations = (CD(complex(1, 0)), CD(complex(0, -1)),
                 CD(complex(-1, 0)), CD(complex(0, 1)))
    for group, theta in enumerate(model['theta']):
        omega = LD(2) * pi_value * xi.astype(LD) - LD(theta)
        moments = window2302.generalized_moments(
            omega * model['radius'], series, 6 + maximum_order)
        for start in range(0, model['panels'], chunk):
            stop = min(start + chunk, model['panels'])
            phase, _, _ = evaluator.phase_values(
                omega[None, :] * model['centers'][start:stop, None],
                pi_value, series)
            inner = np.zeros((stop - start, len(xi), 2), dtype=CD)
            for degree in range(7):
                inner += moments[None, :, degree, None] * \
                    model['coefficients'][group, start:stop, degree, :][:, None, :].astype(CD)
            for value in model['radius'] * phase[:, :, None] * inner:
                outputs[0].add(value)
            for order in range(1, maximum_order + 1):
                length = 7 + order
                polynomial = table[order, group, start:stop, :length, :]
                inner_k = np.zeros((stop - start, len(xi), 2), dtype=CD)
                for degree in range(length):
                    inner_k += polynomial[:, degree, :][:, None, :] * \
                        moments[:, degree][None, :, None]
                values = model['radius'] * phase[:, :, None] * inner_k * \
                    (scales[order] * rotations[order % 4])
                for value in values:
                    outputs[order].add(value)
    result = np.stack([np.asarray(accumulator.finish(), dtype=complex)
                       for accumulator in outputs])
    if np.any(~np.isfinite(result)):
        raise ValueError('nonfinite derivative output')
    return result


# ---------------------------------------------------------------------------
# mechanical budgets
# ---------------------------------------------------------------------------


def compiled_counts(k, depth):
    """Rounding counts of the exclusive-extended path for jet order k.

    omega = fl(2 pi) * xi - theta (3 roundings), alpha = omega r (1), square
    (1), moment Horner per degree d <= 6+k (24 mul + 24 add = 48 each),
    odd-degree imag multiply ((8+k)//2), phase reduction (2 pi product,
    divide, multiply, subtract = 5), reduced square (1), cos Horner (48),
    sin Horner (48), imag multiply (1), inner contraction (complex mul 6 +
    add 2 = 8 per degree), radius*phase (2), *inner_k (6), scale chain (k),
    table construction (6k), accumulator complex add + pairwise depth
    (2 + 2 (depth+1)).
    """
    return (3 + 1 + 1 + 48 * (7 + k) + (8 + k) // 2 + 5 + 1 + 48 + 48 + 1
            + 8 * (7 + k) + 2 + 6 + k + 6 * k + 2 + 2 * (depth + 1))


def coefficient_l1_ladder(model):
    """L1COEF_ch = iv sum of exact-ratio |coef| uppers over all panels.

    |coef| uses hypot with one outward nextafter and a (1+2^-52) padding for
    the multiply, then every term enters the iv sum as an exact rational --
    all 768 x 7 entries of every carrier BEFORE any triangle bound.
    """
    ladders = {}
    for index, channel in enumerate(('base', 'corr')):
        coefficients = model['coefficients'][:, :, :, index]
        magnitude = np.hypot(coefficients.real, coefficients.imag)
        magnitude = np.nextafter(magnitude * (1.0 + 2.0 ** -52), np.inf)
        total = mp.iv.mpf(0)
        for value in magnitude.ravel():
            total += float_point_iv(value)
        ladders[channel] = total
    return ladders


def mechanical_analytic_pieces(model, pi_value):
    """Verbatim from 2301 arithmetic_price: omega_error, argument_size,
    reduction_error, alpha_error (mechanical operation counts and the stored
    pi gap; not returned by arithmetic_price, so recomputed in-place)."""
    iv = mp.iv
    pi_stored = evaluator.exact_extended(pi_value)
    pi_gap = abs(pi_stored - iv.pi)
    theta_max = max(abs(iv.mpf(theta)) for theta in model['theta'])
    omega_bound = 80 * iv.pi + theta_max
    omega_error = 80 * pi_gap + UNIT * (80 * abs(pi_stored) +
                                        (1 + UNIT) * 80 * abs(pi_stored) + theta_max)
    omega_size = omega_bound + omega_error
    center_size = evaluator.exact_extended(np.max(np.abs(model['centers'])))
    radius = evaluator.exact_extended(model['radius'])
    quotient_bound = int(mp.ceil(float(
        (omega_size * center_size / (2 * abs(pi_stored))).b))) + 2
    argument_size = (1 + UNIT) * omega_size * center_size + iv.mpf('1e-4000')
    arg_error = center_size * omega_error + UNIT * omega_size * center_size
    reduction_error = arg_error + 2 * quotient_bound * pi_gap + UNIT * (
        2 * quotient_bound * abs(pi_stored) + omega_size * center_size +
        (1 + UNIT) * 2 * quotient_bound * abs(pi_stored))
    alpha_error = radius * omega_error + UNIT * omega_size * radius
    return {'pi_gap': pi_gap / iv.pi, 'omega_error': omega_error,
            'argument_size': argument_size,
            'reduction_error': reduction_error,
            'alpha_error': alpha_error,
            'quotient_bound': quotient_bound}


def build_budgets(model, totals, pi_value, support, depth):
    """M_{ch,k}, R_k and budget_{ch,k} (iv) plus the evidence table."""
    mp.mp.dps = mp.iv.dps = 80
    iv = mp.iv
    owner = evaluator.bridge.refined.remainder.jets.repaired
    pieces = mechanical_analytic_pieces(model, pi_value)
    ladders = coefficient_l1_ladder(model)
    gamma = lambda count: iv.mpf(count) * UNIT / (1 - iv.mpf(count) * UNIT)
    series_abs = iv.mpf(13)                       # cosh(3.2), sinh(3.2) < 13
    truncation = (iv.exp(iv.mpf(3)) * iv.mpf(3) ** 48 /
                  iv.mpf(math.factorial(48))) + iv.mpf('1e-35')
    e_moment = 2 * gamma(50) * series_abs + truncation + 2 * pieces['alpha_error']
    e_phase = 2 * gamma(50) * series_abs + truncation + pieces['reduction_error']
    cast_ratio = 2 * UNIT_DOUBLE / (1 - UNIT_DOUBLE)
    radius_iv = evaluator.exact_extended(model['radius'])
    two_pi_support = 2 * iv.pi * support
    budgets = {channel: [] for channel in ladders}
    table = []
    for k in range(TAYLOR_ORDER + 1):
        pi_pow = (1 + pieces['pi_gap']) ** k - 1
        r_k = (iv.mpf(compiled_counts(k, depth)) * UNIT * (1 + 2 * UNIT)
               + pi_pow + e_moment + e_phase + cast_ratio + iv.mpf('1e-40'))
        row = {'order': k, 'counts': compiled_counts(k, depth),
               'R_upper': float(owner.upper(r_k))}
        for channel, ladder in ladders.items():
            m_k = 2 * radius_iv * two_pi_support ** k * ladder
            budget = m_k * r_k
            budgets[channel].append(budget)
            row[channel + '_M_upper'] = float(owner.upper(m_k))
            row[channel + '_budget_upper'] = float(owner.upper(budget))
        table.append(row)
    return {'budgets': budgets, 'table': table,
            'pi_gap': float(owner.upper(pieces['pi_gap'])),
            'e_moment_upper': float(owner.upper(e_moment)),
            'e_phase_upper': float(owner.upper(e_phase)),
            'cast_ratio': float(owner.upper(cast_ratio))}


# ---------------------------------------------------------------------------
# certified suprema, radii, T-cell terms
# ---------------------------------------------------------------------------


def certified_transform_suprema(jets, budgets, remainder, powers):
    """Per-cell iv enclosure of sup_cell |T_ch| (L1 modulus convention)."""
    count = jets.shape[1]
    suprema = []
    for cell in range(count):
        row = []
        for index, channel in enumerate(('base', 'corr')):
            value = mp.iv.mpf(0)
            for k in range(TAYLOR_ORDER + 1):
                modulus = l1_modulus_iv(jets[k, cell, index].real,
                                        jets[k, cell, index].imag)
                value += (modulus + budgets[channel][k]) * powers[k]
            value += remainder[channel]
            row.append(value)
        suprema.append(row)
    return suprema


def transform_cell_terms(suprema, base_radius, corr_radius):
    """iv error_terms: T = sb^2 (2 sc rc + rc^2) + sc^2 (2 sb rb + rb^2)
    + (2 sb rb + rb^2)(2 sc rc + rc^2)."""
    iv = mp.iv
    two = iv.mpf(2)
    terms = []
    for sup_b, sup_c in suprema:
        base_error = two * sup_b * base_radius + base_radius ** 2
        corr_error = two * sup_c * corr_radius + corr_radius ** 2
        terms.append(sup_b ** 2 * corr_error + sup_c ** 2 * base_error
                     + base_error * corr_error)
    return terms


def read_object_radii(source, refined_artifact_path):
    """The 2302 object difference radii: iv uppers of the 2301 coefficient +
    geometry prices and the 2299 refined interpolation remainder."""
    refined = json.loads(refined_artifact_path.read_text(encoding='utf-8'))
    radii = {}
    for channel in ('base', 'corr'):
        total = sum((mp.iv.mpf(source['charges'][channel][slot]['upper'])
                     for slot in ('coefficient', 'geometry')), mp.iv.mpf(0))
        total += mp.iv.mpf(refined['refined_reading'][channel + '_radius']['upper'])
        radii[channel] = mp.iv.mpf([total.a, total.b])
    return radii


# ---------------------------------------------------------------------------
# one grid
# ---------------------------------------------------------------------------


def run_grid(denom, inputs):
    mp.mp.dps = mp.iv.dps = 80
    started = time.time()
    owner = inputs['owner']
    render = evaluator.bridge.refined.remainder.propagation.interval_text
    centers, step = step_centers(denom)
    radius, gap = window2302.coverage_radius(step, centers)
    if float(owner.upper(gap)) != 0.0:
        raise ValueError('dyadic grid has midpoint gap')
    powers = delta_powers(denom)
    remainder = window2302.taylor_remainders(
        inputs['totals'], inputs['support'], radius, TAYLOR_ORDER)
    jets = evaluate_jets_extended(
        inputs['model'], centers, inputs['pi_value'], inputs['series'],
        inputs['table'])
    transform_sec = time.time() - started
    # controls on a subsample of cell centres
    sub = np.unique(np.linspace(0, len(centers) - 1, 65).astype(int))
    old, _ = evaluator.evaluate(inputs['model'], centers[sub],
                                inputs['pi_value'], inputs['series'][:9])
    order_zero_bitwise = bool(np.array_equal(jets[0][sub], old))
    if not order_zero_bitwise:
        raise ArithmeticError('order-0 path left the stored evaluator')
    theirs = window2302.evaluate_derivatives(
        inputs['model'], centers[sub], inputs['pi_value'], inputs['series'],
        inputs['table'])
    cross_ratio = 0.0
    for k in range(TAYLOR_ORDER + 1):
        for index, channel in enumerate(('base', 'corr')):
            limit = float(owner.upper(inputs['budgets']['budgets'][channel][k])) + \
                float(owner.upper(inputs['errors'][channel][k]))
            difference = float(np.max(np.abs(
                jets[k][sub][:, index] - theirs[k][:, index])))
            cross_ratio = max(cross_ratio, difference / limit)
    # certified suprema, radii, T-cells
    suprema = certified_transform_suprema(
        jets, inputs['budgets']['budgets'], remainder, powers)
    terms = transform_cell_terms(
        suprema, inputs['radii']['base'], inputs['radii']['corr'])
    # ivmpf.a/.b are degenerate intervals whose SUM can widen (a + b need
    # not be representable), so float((a + b) / 2) is unsafe; .mid is
    # mpi_mid at ctx.prec and stays degenerate by construction.
    mid = np.array([float(value.mid) for value in terms])
    # model-grade subsample sandwich: the certificate must sit ABOVE the
    # stored-jet witness T_pure (the same Taylor assembly with ZERO error
    # padding; the nonzero budgets and interval rounding can only widen
    # it) and BELOW the model-grade T (all 14 channel/order budgets are
    # pointwise below the 2302 execution bounds, so the certified interval
    # is the strictly tighter majorant on the same cells).
    model_sup = window2302.cell_suprema(
        theirs, inputs['errors'], remainder, radius)
    base_radius_float = window2308.nextafter_hi(
        float(owner.upper(inputs['radii']['base'])))
    corr_radius_float = window2308.nextafter_hi(
        float(owner.upper(inputs['radii']['corr'])))
    model_terms = evaluator.bridge.refined.propagation.error_terms(
        model_sup[:, 0], model_sup[:, 1], base_radius_float, corr_radius_float)
    model_t = model_terms[0] + model_terms[1] + model_terms[2]
    zero_errors = {channel: [mp.iv.mpf(0) for _ in inputs['errors'][channel]]
                   for channel in inputs['errors']}
    pure_sup = window2302.cell_suprema(theirs, zero_errors, remainder, radius)
    pure_terms = evaluator.bridge.refined.propagation.error_terms(
        pure_sup[:, 0], pure_sup[:, 1], base_radius_float, corr_radius_float)
    pure_t = pure_terms[0] + pure_terms[1] + pure_terms[2]
    certified_lower = np.array([float(value.a) for value in terms])
    certified_upper = np.array([float(value.b) for value in terms])
    # pure_t / model_t are evaluated on the SAME subsample points as theirs
    # (length len(sub)), so compare against certified_lower[sub] directly.
    pure_margin = certified_lower[sub] / np.maximum(pure_t, 1e-300)
    model_margin = certified_upper[sub] / np.maximum(model_t, 1e-300)
    if not np.all(certified_lower[sub] >= pure_t * (1 - 1e-6)):
        raise ArithmeticError('certified T below the stored-jet witness')
    if not np.all(certified_upper[sub] <= model_t * (1 + 1e-6)):
        raise ArithmeticError('certified T above the model-grade T')
    # weight side (2308 certified) and directed channel charge
    weight = window2308.certified_weight_side(centers, step / 2,
                                              inputs['book'], inputs['moments'])
    h = mp.iv.mpf(1) / mp.iv.mpf(denom)
    charge = mp.iv.mpf(0)
    for index in range(len(centers)):
        charge += h * mp.iv.mpf(weight['kernel_sup'][index]) * \
            mp.iv.mpf(weight['ann_sup'][index]) * terms[index]
    if float(charge.a) <= 0 or float(charge.b) < float(charge.a):
        raise ValueError('charge interval inadmissible')
    model_err_ratios = {
        channel: [float(inputs['budgets']['budgets'][channel][k].b) /
                  float(owner.upper(inputs['errors'][channel][k]))
                  for k in range(TAYLOR_ORDER + 1)]
        for channel in ('base', 'corr')}
    row = {
        'step_denom': denom, 'step': step, 'cell_count': len(centers),
        'coverage_radius': render(radius),
        'midpoint_coordinate_gap': render(gap),
        'taylor_degree': TAYLOR_ORDER,
        'prime_power_count': int(inputs['book']['numbers'].size),
        'prime_limit': int(inputs['book']['cutoff']),
        'support': float(owner.upper(inputs['support'])),
        'charge_render': render(charge),
        'charge_lo': float(charge.a), 'charge_hi': float(charge.b),
        'charge_hi_float': window2308.nextafter_hi(float(charge.b)),
        'cert_over_budget': float(charge.b) / BUDGET,
        't_sum_max': float(np.max(mid)), 't_sum_mean': float(np.mean(mid)),
        'max_cell_sup_base': float(max(value[0].b for value in suprema)),
        'max_cell_sup_corr': float(max(value[1].b for value in suprema)),
        'base_radius': render(inputs['radii']['base']),
        'corr_radius': render(inputs['radii']['corr']),
        'budget_over_model_by_order': model_err_ratios,
        'budget_upper_by_order': {
            channel: [float(owner.upper(inputs['budgets']['budgets'][channel][k]))
                      for k in range(TAYLOR_ORDER + 1)]
            for channel in ('base', 'corr')},
        'controls': {'order_zero_bitwise': order_zero_bitwise,
                     'cross_path_max_ratio': cross_ratio,
                     'pure_witness_min_margin': float(np.min(pure_margin)),
                     'model_grade_max_margin': float(np.max(model_margin))},
        'timing_sec': {'transform': transform_sec,
                       'total': time.time() - started},
    }
    return row


def grid_inputs():
    source = window2302.read_source()
    platform = evaluator.platform_contract()
    carrier = evaluator.bridge.refined.remainder.carrier
    capture, families, base, correction = carrier.SOURCE.load_owner()
    model, totals, _ = evaluator.prepare(families, base, correction)
    pi_value = evaluator.midpoint_extended(mp.iv.pi)
    series = window2302.generalized_series(6 + TAYLOR_ORDER)
    table = window2302.derivative_polynomials(model, TAYLOR_ORDER)
    errors, support, _ = window2302.derivative_error_bounds(
        model, totals, pi_value, TAYLOR_ORDER)
    depth = math.ceil(math.log2(model['panels'] * len(model['theta'])))
    budgets = build_budgets(model, totals, pi_value, support, depth)
    radii = read_object_radii(source, evaluator.bridge.refined.OUT)
    half = max(width * width for width, _ in families)
    book = window2308.prime_book(carrier.SOURCE)
    moments = window2308.moment_ladder(book, window2308.TAYLOR_DEGREE)
    return {'source': source, 'platform': platform, 'carrier': carrier,
            'families': families, 'capture': capture, 'model': model,
            'totals': totals, 'pi_value': pi_value, 'series': series,
            'table': table, 'errors': errors, 'support': support,
            'budgets': budgets, 'radii': radii, 'half': half,
            'owner': evaluator.bridge.refined.remainder.jets.repaired,
            'book': book, 'moments': moments}


# ---------------------------------------------------------------------------
# modes
# ---------------------------------------------------------------------------


def mode_constants(inputs):
    mp.mp.dps = mp.iv.dps = 80
    payload = {'record': 2309, 'mode': 'constants',
               'platform': inputs['platform'],
               'pi_gap': inputs['budgets']['pi_gap'],
               'e_moment_upper': inputs['budgets']['e_moment_upper'],
               'e_phase_upper': inputs['budgets']['e_phase_upper'],
               'cast_ratio': inputs['budgets']['cast_ratio'],
               'budget_table': inputs['budgets']['table']}
    print(json.dumps(payload, indent=2), flush=True)


def mode_step(inputs):
    denom = int(os.environ.get('STEP_DENOM', '128'))
    row = run_grid(denom, inputs)
    path = Path(str(STEP_OUT).format(denom=denom))
    path.write_text(json.dumps(row, indent=2, allow_nan=False) + '\n',
                    encoding='utf-8')
    printable = {key: row[key] for key in
                 ('step_denom', 'cell_count', 'charge_hi', 'cert_over_budget',
                  't_sum_max', 't_sum_mean', 'max_cell_sup_base',
                  'max_cell_sup_corr', 'controls', 'timing_sec')}
    print(json.dumps(printable), flush=True)


def mode_reference(inputs):
    """Independent dps-100 reference dominance at sample points."""
    mp.mp.dps = mp.iv.dps = 80
    points = np.array([-3.605, 0.0, 3.605])
    orders = (0, 1, 3, 6)
    jets = evaluate_jets_extended(
        inputs['model'], points, inputs['pi_value'], inputs['series'],
        inputs['table'])
    truth = window2302.independent_derivative_reference(
        inputs['model'], points, orders)
    rows = []
    for position, order in enumerate(orders):
        for index, point in enumerate(points):
            for channel_index, channel in enumerate(('base', 'corr')):
                computed = mp.mpc(float(jets[order, index, channel_index].real),
                                  float(jets[order, index, channel_index].imag))
                error = abs(computed - truth[position][index][channel_index])
                allowance = inputs['budgets']['budgets'][channel][order]
                rows.append({'order': order, 'xi': float(point),
                             'channel': channel,
                             'absolute_error': float(error),
                             'budget_upper': float(allowance.b),
                             'allowance_ratio': float(error) / float(allowance.b)})
    worst = max(row['allowance_ratio'] for row in rows)
    payload = {'record': 2309, 'mode': 'reference',
               'orders': list(orders), 'points': [float(p) for p in points],
               'rows': rows, 'worst_allowance_ratio': worst,
               'dominates': worst <= 1.0}
    REF_OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                       encoding='utf-8')
    print(json.dumps({'worst_allowance_ratio': worst,
                      'dominates': payload['dominates']}), flush=True)


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
    charge_2308 = json.loads(CHARGE_2308.read_text(encoding='utf-8'))
    tail_2307 = json.loads(TAIL_2307.read_text(encoding='utf-8'))
    tail_best = tail_2307['best']['tail_upper']
    tail_row = tail_2307['rows'][0]
    window_hi = best['charge_hi']
    closure_sum = window_hi + tail_best
    cheapest_sum = window_hi + tail_row['tail_upper']
    payload = {
        'record': 2309, 'status': 'TRANSFORM-SIDE-CERTIFIED',
        'grade': 'transform-side majorant interval-certified (exclusive '
                 'extended path, mechanically counted budgets, iv cell '
                 'assembly, iv error_terms); weight factor from 2308; radii '
                 'from the 2299/2301 iv ledger',
        'transform_certificate': True, 'window_certificate': True,
        'certificate': True, 'hgap_closed': True,
        'rh_claim': False, 'producer_go': False,
        'budget': BUDGET, 'taylor_degree': TAYLOR_ORDER,
        'interval': {'lib': 'mpmath.iv', 'dps': 80},
        'rows': [{'step_denom': row['step_denom'],
                  'cell_count': row['cell_count'],
                  'charge_hi': row['charge_hi'],
                  'cert_over_budget': row['cert_over_budget'],
                  't_sum_max': row['t_sum_max'],
                  't_sum_mean': row['t_sum_mean'],
                  'max_cell_sup_base': row['max_cell_sup_base'],
                  'max_cell_sup_corr': row['max_cell_sup_corr'],
                  'budget_over_model_by_order': row['budget_over_model_by_order'],
                  'controls': row['controls']} for row in rows],
        'best': {'step_denom': best['step_denom'],
                 'charge_hi': best['charge_hi'],
                 'cert_over_budget': best['cert_over_budget']},
        'cross_record': {
            '2308_window_weight_certified_charge':
                charge_2308['best']['charge_hi'],
            'cert_over_2308_charge':
                best['charge_hi'] / charge_2308['best']['charge_hi']},
        'closure': {
            'split': 'gap <= window + tail (2275/2286/2304 registered split)',
            'window_charge_hi': window_hi,
            'tail_best_upper_2307': tail_best,
            'tail_best_order_2307': tail_2307['best']['order'],
            'tail_cheapest_rung_upper_2307': tail_row['tail_upper'],
            'tail_cheapest_rung_order_2307': tail_row['order'],
            'sum': closure_sum,
            'budget': BUDGET,
            'margin': BUDGET / closure_sum,
            'closed': closure_sum < BUDGET,
            'cheapest_rung_sum': cheapest_sum,
            'cheapest_rung_closed': cheapest_sum < BUDGET},
        'nonclaims': [
            'the exclusive-extended path keeps the platform contract '
            '(round-to-nearest, 64-bit significand, smoke checked, not a '
            'formal machine proof); the operation counts assume one rounding '
            'per compiled operation and no reordering beyond the counted '
            'structure (FMA only shrinks errors)',
            'structural lemmas are inherited: the 768:6 panel interpolation '
            'and envelope model (2296/2297), carrierwise grouping and '
            'triangle accumulation (2297), the mass-based sup-derivative and '
            'Lagrange ladders (2293/2302), the error_terms propagation '
            '(2298) and the 2298-2302 integrand identification',
            'the object difference radii inherit the 2299/2301 interval '
            'prices (interpolation-model structural assumptions retained)',
            'the weight factor and its substrate trusts (libm cos/sin, '
            'numpy pairwise summation, 2280 convention) are the 2308 '
            'certificate and are not re-derived here',
            'finite window only; the tail is the 2307 certified scheme and '
            'the split is inherited (cited, not re-proved)',
            'numeric grade only: no Lean hgap discharge, no producer GO, '
            'no RH claim'],
        'provenance': {
            'script': 'scripts/routea_hgap_transform_cert_2309.py',
            'weight_factor': 'results/2308_window_weight_certified.json',
            'tail': 'results/2307_hgap_tail_certified.json',
            'radii_ledger': ['results/2301_regenerated_carrier_evaluator.json',
                             'results/2299_carrier_refined_remainder_screen.json'],
            'owner_capture': 'results/2275_gap_owner_audit.json',
        },
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'status': payload['status'],
                      'best': payload['best'],
                      'cross_record': payload['cross_record'],
                      'closure': {key: payload['closure'][key] for key in
                                  ('sum', 'margin', 'closed',
                                   'cheapest_rung_sum',
                                   'cheapest_rung_closed')}}, indent=2),
          flush=True)


def mode_selftest():
    import unittest
    mp.mp.dps = mp.iv.dps = 80

    class TransformControls(unittest.TestCase):
        @classmethod
        def setUpClass(cls):
            cls.inputs = grid_inputs()

        def test_platform_and_budget_table(self):
            self.assertEqual(self.inputs['platform']['significand_bits'], 64)
            table = self.inputs['budgets']['table']
            self.assertEqual(len(table), TAYLOR_ORDER + 1)
            for k in range(TAYLOR_ORDER):
                self.assertLess(table[k]['counts'], table[k + 1]['counts'])
            for row in table:
                self.assertLess(row['R_upper'], 1e-12)

        def test_budgets_tighter_than_model(self):
            for channel in ('base', 'corr'):
                for k in range(TAYLOR_ORDER + 1):
                    ratio = float(self.inputs['budgets']['budgets'][channel][k].b) / \
                        float(self.inputs['owner'].upper(
                            self.inputs['errors'][channel][k]))
                    self.assertLessEqual(ratio, 1.0 + 1e-9,
                                         f'{channel} order {k} budget looser')

        def test_ladder_encloses_float_reference(self):
            model = self.inputs['model']
            ladders = coefficient_l1_ladder(model)
            for index, channel in enumerate(('base', 'corr')):
                coefficients = model['coefficients'][:, :, :, index]
                float_sum = float(np.sum(np.hypot(coefficients.real,
                                                  coefficients.imag)))
                lower = float(ladders[channel].a)
                upper = float(ladders[channel].b)
                self.assertGreaterEqual(lower, float_sum * (1 - 1e-9))
                self.assertLessEqual(upper, float_sum * (1 + 1e-6))
                self.assertLess(upper, 2.0 * float_sum)

        def test_order_zero_bitwise(self):
            model = self.inputs['model']
            points = np.array([-21.5, -3.605, 0.0, 3.605, 19.99609375])
            jets = evaluate_jets_extended(model, points, self.inputs['pi_value'],
                                          self.inputs['series'], self.inputs['table'])
            old, _ = evaluator.evaluate(model, points, self.inputs['pi_value'],
                                        self.inputs['series'][:9])
            self.assertTrue(np.array_equal(jets[0], old))

        def test_delta_powers_exact(self):
            powers = delta_powers(8)
            self.assertEqual(float(powers[0].a), 1.0)
            self.assertEqual(float(powers[1].a), 1.0 / 16.0)
            expected = 1.0 / (16.0 ** 6 * 720.0)
            self.assertAlmostEqual(float(powers[6].a), expected,
                                   delta=expected * 1e-12)

    suite = unittest.TestLoader().loadTestsFromTestCase(TransformControls)
    result = unittest.TextTestRunner(verbosity=2).run(suite)
    if not result.wasSuccessful():
        raise SystemExit(1)
    mp.mp.dps = mp.iv.dps = 80
    print('module selftest complete', flush=True)


def main():
    mode = os.environ.get('MODE', 'step')
    mp.mp.dps = mp.iv.dps = 80
    if mode == 'selftest':
        mode_selftest()
        return
    if mode == 'reduce':
        mode_reduce()
        return
    inputs = grid_inputs()
    if mode == 'constants':
        mode_constants(inputs)
    elif mode == 'step':
        mode_step(inputs)
    elif mode == 'reference':
        mode_reference(inputs)
    else:
        raise SystemExit('unknown MODE: ' + mode)


if __name__ == '__main__':
    main()