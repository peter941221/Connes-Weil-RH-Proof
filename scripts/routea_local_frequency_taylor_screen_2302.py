"""Local real-frequency Taylor magnitude bounds for the captured 768:6 owner.

Derivative execution bounds remain a declared rounding model. Kernel weights
and final integration are sampled; no continuous integral certificate is made.
"""
import hashlib
import json
import math
from fractions import Fraction
from pathlib import Path

import mpmath as mp
import numpy as np

import routea_regenerated_carrier_evaluator_2301 as evaluator

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/2302_local_frequency_taylor_screen.json'
TAYLOR_ORDER = 6


def generalized_series(maximum_degree):
    prefix, _ = evaluator.series_coefficients()
    rows = list(prefix[:2])
    owner = evaluator.bridge.refined.remainder.jets.repaired
    unit = mp.iv.mpf(2)**-64
    for degree in range(maximum_degree+1):
        parity = degree % 2
        exact = [mp.iv.mpf(2*(-1)**index)/((degree+2*index+parity+1)*math.factorial(2*index+parity))
                 for index in range(evaluator.SERIES_TERMS//2)]
        cast = [evaluator.midpoint_extended(value) for value in exact]
        for value, stored in zip(exact, cast):
            if owner.upper(abs(evaluator.exact_extended(stored)-value)/abs(value)) > owner.lower(2*unit):
                raise ValueError('generalized moment coefficient cast failed')
        rows.append(np.array(cast, dtype=evaluator.LD))
    if any(not np.array_equal(first, second) for first, second in zip(rows[:9], prefix)):
        raise ValueError('2301 moment prefix changed')
    return rows


def generalized_moments(alpha, coefficients, maximum_degree):
    if np.max(np.abs(alpha), initial=evaluator.LD(0)) > evaluator.LD(3):
        raise ValueError('moment argument outside [-3,3]')
    square = alpha*alpha
    output = np.zeros((len(alpha), maximum_degree+1), dtype=evaluator.CD)
    for degree in range(maximum_degree+1):
        value = evaluator.horner(square, coefficients[degree+2])
        if degree % 2:
            output[:, degree].imag = -alpha*value
        else:
            output[:, degree].real = value
    return output


def derivative_polynomials(model, maximum_order):
    table = np.zeros((maximum_order+1, len(model['theta']), model['panels'], 7+maximum_order, 2), dtype=evaluator.CD)
    table[0, :, :, :7, :] = model['coefficients'].astype(evaluator.CD)
    centers = model['centers'][None, :, None, None]
    for order in range(1, maximum_order+1):
        length = 7+order
        table[order, :, :, :length-1, :] = centers*table[order-1, :, :, :length-1, :]
        table[order, :, :, 1:length, :] += model['radius']*table[order-1, :, :, :length-1, :]
    return table


def evaluate_derivatives(model, xi, pi_value, series, table, chunk=32):
    xi = np.asarray(xi, dtype=float)
    if chunk <= 0 or np.any(~np.isfinite(xi)) or np.max(np.abs(xi), initial=0) > 40:
        raise ValueError('invalid chunk or frequency window')
    maximum_order = table.shape[0]-1
    outputs = [evaluator.PairwiseAccumulator() for _ in range(maximum_order+1)]
    scales = [evaluator.LD(1)]
    for order in range(maximum_order):
        scales.append(scales[-1]*(evaluator.LD(2)*pi_value))
    for group, theta in enumerate(model['theta']):
        omega = evaluator.LD(2)*pi_value*xi.astype(evaluator.LD)-evaluator.LD(theta)
        moments = generalized_moments(omega*model['radius'], series, 6+maximum_order)
        for start in range(0, model['panels'], chunk):
            stop = min(start+chunk, model['panels'])
            phase, _, _ = evaluator.phase_values(omega[None, :]*model['centers'][start:stop, None], pi_value, series)
            inner = np.zeros((stop-start, len(xi), 2), dtype=evaluator.CD)
            for degree in range(7):
                inner += moments[None, :, degree, None]*model['coefficients'][group, start:stop, degree, :][:, None, :].astype(evaluator.CD)
            for value in model['radius']*phase[:, :, None]*inner:
                outputs[0].add(value)
            for order in range(1, maximum_order+1):
                length = 7+order
                polynomial = table[order, group, start:stop, :length, :].astype(complex)
                matrix = polynomial.transpose(1, 0, 2).reshape(length, (stop-start)*2)
                inner64 = (moments[:, :length].astype(complex) @ matrix).reshape(len(xi), stop-start, 2).transpose(1, 0, 2)
                rotation = (1, -1j, -1, 1j)[order % 4]
                values = float(model['radius'])*phase.astype(complex)[:, :, None]*inner64*(float(scales[order])*rotation)
                for value in values:
                    outputs[order].add(value)
    result = np.stack([np.asarray(accumulator.finish(), dtype=complex) for accumulator in outputs])
    if np.any(~np.isfinite(result)):
        raise ValueError('nonfinite derivative output')
    return result


def derivative_error_bounds(model, totals, pi_value, maximum_order):
    owner = evaluator.bridge.refined.remainder.jets.repaired
    _, constants = evaluator.arithmetic_price(model, totals, pi_value)
    phase = mp.iv.mpf(constants['phase_error']['upper'])
    moment = mp.iv.mpf(constants['moment_relative_error']['upper'])
    unit_extended = mp.iv.mpf(2)**-64
    unit_double = mp.iv.mpf(2)**-53
    gamma = lambda count, unit: count*unit/(1-count*unit)
    support = evaluator.exact_extended(np.max(np.abs(model['centers'])))+evaluator.exact_extended(model['radius'])
    depth = math.ceil(math.log2(model['panels']*len(model['theta'])))
    pi_gap = abs(evaluator.exact_extended(pi_value)-mp.iv.pi)/mp.iv.pi
    result = {channel: [] for channel in totals}
    for order in range(maximum_order+1):
        unit = unit_extended if order == 0 else unit_double
        construction = gamma(8*order, unit_extended)
        prefactor = (1+pi_gap)**order*(1+gamma(order, unit_extended))-1
        magnitude = (1+phase)*(1+moment)*(1+construction)*(1+prefactor)
        operation = magnitude-1+gamma(96+16*order, unit)*magnitude
        pairwise = mp.iv.sqrt(2)*gamma(depth, unit)*(1+gamma(96+16*order, unit))*magnitude
        final = mp.iv.sqrt(2)*unit_double/(1-unit_double)*(1+operation+pairwise) if order == 0 else mp.iv.mpf(0)
        for channel, values in totals.items():
            mass = values['mass']*(2*mp.iv.pi*support)**order
            if owner.upper(mass) >= mp.mpf('1e80'):
                raise ValueError('derivative magnitude leaves the admitted underflow/overflow class')
            result[channel].append(mass*(operation+pairwise+final)+mp.iv.mpf('1e-200'))
    return result, support, constants


def coverage_radius(step, centers):
    rational_step = Fraction(str(step))
    count = len(centers)
    if rational_step*count != 80:
        raise ValueError('cells do not cover the full window')
    maximum = max(abs(Fraction.from_float(float(center))-(-40+rational_step*Fraction(2*index+1, 2)))
                  for index, center in enumerate(centers))
    gap = mp.iv.mpf(maximum.numerator)/maximum.denominator
    return mp.iv.mpf(str(step))/2+gap, gap


def taylor_remainders(totals, support, radius, order):
    factor = (2*mp.iv.pi*support*radius)**(order+1)/math.factorial(order+1)
    return {channel: values['mass']*factor for channel, values in totals.items()}


def cell_suprema(jets, errors, remainder, radius):
    owner = evaluator.bridge.refined.remainder.jets.repaired
    delta = np.nextafter(float(owner.upper(radius)), np.inf)
    suprema = np.zeros((jets.shape[1], 2))
    for channel_index, channel in enumerate(errors):
        for order in range(jets.shape[0]):
            error = np.nextafter(float(owner.upper(errors[channel][order])), np.inf)
            safe_size = np.abs(jets[order, :, channel_index].real)+np.abs(jets[order, :, channel_index].imag)+error
            suprema[:, channel_index] += safe_size*delta**order/math.factorial(order)
        suprema[:, channel_index] += np.nextafter(float(owner.upper(remainder[channel])), np.inf)
    return np.nextafter(suprema*(1+64*np.finfo(float).eps)+1e-200, np.inf)


def independent_derivative_reference(model, points, orders):
    mp.mp.dps = 100
    owner = evaluator.bridge.refined.remainder.jets.repaired
    radius = owner.lower(evaluator.exact_extended(model['radius']))
    maximum = max(orders)
    result = [[[mp.mpc(0) for _ in range(2)] for _ in points] for _ in orders]
    for group, theta in enumerate(model['theta']):
        omega = [2*mp.pi*mp.mpf(float(point))-mp.mpf(theta) for point in points]
        moments = [[mp.quad(lambda coordinate: coordinate**degree*mp.exp(-1j*frequency*radius*coordinate), [-1, 0, 1])
                    for degree in range(7+maximum)] for frequency in omega]
        for panel in range(model['panels']):
            center = owner.lower(evaluator.exact_extended(model['centers'][panel]))
            phases = [mp.exp(-1j*frequency*center) for frequency in omega]
            for channel in range(2):
                polynomial = [mp.mpc(float(value.real), float(value.imag)) for value in model['coefficients'][group, panel, :, channel]]
                for order in range(maximum+1):
                    if order in orders:
                        position = orders.index(order)
                        for index, phase in enumerate(phases):
                            value = sum((coefficient*moments[index][degree] for degree, coefficient in enumerate(polynomial)), mp.mpc(0))
                            result[position][index][channel] += radius*phase*value*((-2j*mp.pi)**order)
                    if order < maximum:
                        following = [mp.mpc(0) for _ in range(len(polynomial)+1)]
                        for degree, coefficient in enumerate(polynomial):
                            following[degree] += center*coefficient
                            following[degree+1] += radius*coefficient
                        polynomial = following
    return result


def read_source():
    source = json.loads(evaluator.OUT.read_text(encoding='utf-8'))
    for path, expected in source['source_sha256'].items():
        if hashlib.sha256((ROOT/path).read_bytes()).hexdigest() != expected:
            raise ValueError('2301 provenance mismatch: '+path)
    if source['certificate'] or source['hgap_closed'] or source['panels'] != 768:
        raise ValueError('2301 profile/scope mismatch')
    return source


def main():
    mp.mp.dps = mp.iv.dps = 80
    source = read_source()
    platform = evaluator.platform_contract()
    carrier = evaluator.bridge.refined.remainder.carrier
    capture, families, base, correction = carrier.SOURCE.load_owner()
    model, totals, _ = evaluator.prepare(families, base, correction)
    if hashlib.sha256(model['coefficients'].tobytes()).hexdigest() != source['coefficient_table_sha256']:
        raise ValueError('regenerated table differs from 2301')
    pi_value = evaluator.midpoint_extended(mp.iv.pi)
    series = generalized_series(6+TAYLOR_ORDER)
    table = derivative_polynomials(model, TAYLOR_ORDER)
    errors, support, constants = derivative_error_bounds(model, totals, pi_value, TAYLOR_ORDER)
    owner = evaluator.bridge.refined.remainder.jets.repaired
    render = evaluator.bridge.refined.remainder.propagation.interval_text
    object_radii = {channel: sum((mp.iv.mpf(source['charges'][channel][slot]['upper'])
                                 for slot in ('coefficient', 'geometry')), mp.iv.mpf(0))
                    +mp.iv.mpf(json.loads(evaluator.bridge.refined.OUT.read_text(encoding='utf-8'))['refined_reading'][channel+'_radius']['upper'])
                    for channel in totals}
    print(json.dumps({'support_half': render(support), 'derivative_error_bounds': {
        channel: [render(value) for value in values] for channel, values in errors.items()}}), flush=True)
    points = np.array([-3.605, 0.0, 3.605])
    orders = (0, 1, 3, 6)
    values = evaluate_derivatives(model, points, pi_value, series, table)
    old, _ = evaluator.evaluate(model, points, pi_value, series[:9])
    if not np.array_equal(values[0], old):
        raise ArithmeticError('2301 order-zero execution changed')
    truth = independent_derivative_reference(model, points, orders)
    controls = []
    for position, order in enumerate(orders):
        for index, point in enumerate(points):
            for channel_index, channel in enumerate(totals):
                computed = mp.mpc(float(values[order, index, channel_index].real), float(values[order, index, channel_index].imag))
                error = abs(computed-truth[position][index][channel_index])
                allowance = owner.lower(errors[channel][order])
                if error > allowance:
                    raise ArithmeticError('independent derivative exceeded its own execution allowance')
                controls.append({'order': order, 'xi': float(point), 'channel': channel,
                                 'absolute_error': float(error), 'allowance_ratio': float(error/allowance)})
    print(json.dumps({'order_zero_bitwise_control': True,
                      'max_derivative_allowance_ratio': max(row['allowance_ratio'] for row in controls)}), flush=True)
    rows = []
    for step in (0.02, 0.01, 0.005):
        count = round(80/step)
        centers = -40+(np.arange(count)+0.5)*step
        radius, gap = coverage_radius(step, centers)
        remainder = taylor_remainders(totals, support, radius, TAYLOR_ORDER)
        jets = evaluate_derivatives(model, centers, pi_value, series, table)
        suprema = cell_suprema(jets, errors, remainder, radius)
        kernel, prime_count = carrier.SOURCE.prime_kernel(centers, 2*max(width*width for width, _ in families))
        if prime_count != 41136:
            raise ValueError('incomplete kernel')
        weight = np.abs(kernel)*np.abs(carrier.SOURCE.annihilator(centers))**2
        base_radius = np.nextafter(float(owner.upper(object_radii['base'])), np.inf)
        corr_radius = np.nextafter(float(owner.upper(object_radii['corr'])), np.inf)
        terms = evaluator.bridge.refined.propagation.error_terms(suprema[:, 0], suprema[:, 1], base_radius, corr_radius)
        proxy = float(np.sum(weight*sum(terms))*step)
        rows.append({'xi_step': step, 'cell_count': count, 'prime_power_count': prime_count,
                     'coverage_radius': render(radius), 'midpoint_coordinate_gap': render(gap),
                     'taylor_remainder': {channel: render(value) for channel, value in remainder.items()},
                     'max_cell_sup_base': float(np.max(suprema[:, 0])),
                     'max_cell_sup_corr': float(np.max(suprema[:, 1])),
                     'cell_suprema_sha256': hashlib.sha256(suprema.tobytes()).hexdigest(),
                     'sampled_weight_proxy_charge': proxy, 'sampled_weight_proxy_budget_ratio': proxy/1e7})
        print(json.dumps(rows[-1]), flush=True)
    result = {'record': 2302, 'status': 'LOCAL-FREQUENCY-TAYLOR-MAGNITUDE-MODEL',
              'certificate': False, 'hgap_closed': False, 'platform': platform,
              'owner': source['owner'], 'taylor_order': TAYLOR_ORDER,
              'moment_terms': evaluator.SERIES_TERMS,
              'support_half': render(support), 'mass': {channel: render(value['mass']) for channel, value in totals.items()},
              'object_difference_radii': {channel: render(value) for channel, value in object_radii.items()},
              'derivative_execution_bounds': {channel: [render(value) for value in values] for channel, values in errors.items()},
              'order_zero_bitwise_control': True, 'independent_controls': controls, 'rows': rows,
              'source_sha256': {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (evaluator.OUT, evaluator.bridge.refined.OUT, evaluator.bridge.OUT,
                                             carrier.SOURCE.CAPTURE, Path(evaluator.__file__), Path(__file__))},
              'nonclaims': ['derivative and cell magnitude bounds use a declared standard arithmetic and BLAS rounding model',
                            'full complex carrier sums precede all cell magnitude norms; L1 complex norms are conservative',
                            'continuous transform cell coverage does not enclose the continuous kernel or polynomial weight',
                            'proxy charges still use sampled weights and unpriced outer arithmetic',
                            'no continuous functional integral, infinite tail, actual selected-owner bridge, hgap or RH claim']}
    OUT.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
