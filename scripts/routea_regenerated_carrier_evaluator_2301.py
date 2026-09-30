"""Regenerated 768:6 evaluator with explicitly priced extended arithmetic.

Uses real Horner series, integer phase reduction and streaming pairwise sums.
The rounding-model budget is not a continuous integral or RH certificate.
"""
import hashlib
import json
import math
from pathlib import Path

import mpmath as mp
import numpy as np

import routea_carrier_coefficient_bridge_price_2300 as bridge

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/2301_regenerated_carrier_evaluator.json'
LD = np.longdouble
CD = np.clongdouble
SERIES_TERMS = 48


def exact_extended(value):
    numerator, denominator = LD(value).as_integer_ratio()
    return mp.iv.mpf(numerator)/mp.iv.mpf(denominator)


def midpoint_extended(value):
    owner = bridge.refined.remainder.jets.repaired
    return LD(str((owner.lower(value)+owner.upper(value))/2))


def platform_contract():
    info = np.finfo(LD)
    if info.nmant != 63 or info.maxexp != 16384 or info.minexp != -16382:
        raise ValueError('requires the tested 64-bit-significand extended format')
    if LD(1)+LD(2)**-64 != LD(1) or LD(1)+LD(2)**-63 == LD(1):
        raise ValueError('round-to-nearest smoke contract failed')
    return {'numpy_version': np.__version__, 'significand_bits': 64,
            'maxexp': int(info.maxexp), 'minexp': int(info.minexp),
            'rounding_model': 'round-to-nearest arithmetic; smoke checked, not a formal machine proof'}


def series_coefficients():
    coefficient_rows = []
    exact_rows = []
    for parity in (0, 1):
        exact_rows.append([mp.iv.mpf((-1)**index)/math.factorial(2*index+parity)
                           for index in range(SERIES_TERMS//2)])
    for degree in range(7):
        parity = degree % 2
        exact_rows.append([mp.iv.mpf(2*(-1)**index)/((degree+2*index+parity+1)*math.factorial(2*index+parity))
                           for index in range(SERIES_TERMS//2)])
    owner = bridge.refined.remainder.jets.repaired
    unit = mp.iv.mpf(2)**-64
    maximum = mp.mpf(0)
    for row in exact_rows:
        converted = [midpoint_extended(value) for value in row]
        for value, cast in zip(row, converted):
            relative = owner.upper(abs(exact_extended(cast)-value)/abs(value))
            maximum = max(maximum, relative)
            if relative > owner.lower(2*unit):
                raise ValueError('series coefficient conversion allowance failed')
        coefficient_rows.append(np.array(converted, dtype=LD))
    return coefficient_rows, float(maximum)


def horner(square, coefficients):
    output = np.full_like(square, coefficients[-1], dtype=LD)
    for coefficient in coefficients[-2::-1]:
        output = output*square+coefficient
    return output


def phase_values(arguments, pi_value, coefficients):
    quotient = np.rint(arguments/(LD(2)*pi_value))
    reduced = arguments-quotient*(LD(2)*pi_value)
    if np.max(np.abs(reduced), initial=LD(0)) > LD('3.2'):
        raise ValueError('phase reduction left the priced domain')
    square = reduced*reduced
    output = horner(square, coefficients[0]).astype(CD)
    output.imag = -reduced*horner(square, coefficients[1])
    return output, float(np.max(np.abs(reduced), initial=LD(0))), float(np.max(np.abs(quotient), initial=LD(0)))


def moment_values(alpha, coefficients):
    if np.max(np.abs(alpha), initial=LD(0)) > LD(3):
        raise ValueError('moments left the priced domain')
    square = alpha*alpha
    output = np.zeros((len(alpha), 7), dtype=CD)
    for degree in range(7):
        value = horner(square, coefficients[degree+2])
        if degree % 2:
            output[:, degree].imag = -alpha*value
        else:
            output[:, degree].real = value
    return output


class PairwiseAccumulator:
    def __init__(self):
        self.levels = []
        self.count = 0

    def add(self, value):
        level = 0
        self.count += 1
        while level < len(self.levels) and self.levels[level] is not None:
            value = self.levels[level]+value
            self.levels[level] = None
            level += 1
        if level == len(self.levels):
            self.levels.append(value)
        else:
            self.levels[level] = value

    def finish(self):
        result = None
        for value in self.levels:
            if value is not None:
                result = value if result is None else result+value
        if result is None:
            raise ValueError('empty accumulator')
        return result


def prepare(families, base, correction, panels=768):
    carrier = bridge.refined.remainder.carrier
    half = max(mp.iv.mpf(width)**2 for width, _ in families)
    radius = half/panels
    radius_value = midpoint_extended(radius)
    center_values = np.array([midpoint_extended(-half+2*radius*(mp.iv.mpf(panel)+mp.iv.mpf('0.5')))
                              for panel in range(panels)], dtype=LD)
    matrix = bridge.interpolation_matrix()
    groups = carrier.carrier_groups(families)
    channels = (bridge.refined.remainder.channel_coefficients(families, base),
                bridge.refined.remainder.channel_coefficients(families, correction))
    coefficients = np.zeros((len(groups), panels, 7, 2), dtype=complex)
    totals = {channel: {slot: mp.iv.mpf(0) for slot in ('coefficient', 'geometry', 'mass')}
              for channel in ('base', 'corr')}
    upper = bridge.refined.remainder.jets.repaired.upper
    rows = []
    for panel in range(panels):
        center = -half+2*radius*(mp.iv.mpf(panel)+mp.iv.mpf('0.5'))
        cache = {}
        for width in sorted(set(width for width, _ in families)):
            samples = [bridge.envelope_interval(center+radius*bridge.exact_cosine(node), width) for node in range(7)]
            cache[width] = [sum((matrix[degree][node]*samples[node] for node in range(7)), mp.iv.mpf(0))
                            for degree in range(7)]
        panel_totals = {channel: {slot: mp.iv.mpf(0) for slot in totals[channel]} for channel in totals}
        for group, (theta, _) in enumerate(groups):
            for channel_index, channel in enumerate(totals):
                _, by_width = channels[channel_index][group]
                ideal = [sum((coefficient*cache[width][degree] for width, coefficient in by_width.items()), mp.iv.mpc(0))
                         for degree in range(7)]
                cast = bridge.regenerated_coefficients(ideal)
                coefficients[group, panel, :, channel_index] = cast
                panel_totals[channel]['coefficient'] += bridge.coefficient_radius(ideal, cast, radius)
                magnitudes = [abs(mp.iv.mpc(float(value.real), float(value.imag))) for value in cast]
                size = sum(magnitudes, mp.iv.mpf(0))
                radius_gap = abs(exact_extended(radius_value)-radius)
                center_gap = abs(exact_extended(center_values[panel])-center)
                frequency_bound = 80*mp.iv.pi+abs(mp.iv.mpf(theta))
                phase_gap = mp.iv.mpf(min(mp.mpf(2), upper(frequency_bound*(center_gap+radius_gap))))
                panel_totals[channel]['geometry'] += (2*radius_gap+2*radius*phase_gap)*size
                panel_totals[channel]['mass'] += exact_extended(radius_value)*sum(
                    (mp.iv.mpf(2)/(degree+1)*magnitude for degree, magnitude in enumerate(magnitudes)), mp.iv.mpf(0))
        rows.append({'panel': panel, **{channel: {slot: bridge.refined.remainder.propagation.interval_text(value)
                                               for slot, value in charges.items()} for channel, charges in panel_totals.items()}})
        for channel in totals:
            for slot in totals[channel]:
                totals[channel][slot] += panel_totals[channel][slot]
    model = {'families': families, 'theta': [theta for theta, _ in groups], 'panels': panels,
             'half': half, 'radius': radius_value, 'centers': center_values, 'coefficients': coefficients}
    return model, totals, rows


def evaluate(model, xi, pi_value, coefficients, chunk=16):
    if chunk <= 0:
        raise ValueError('chunk size must be positive')
    xi = np.asarray(xi, dtype=float)
    if np.any(~np.isfinite(xi)) or np.max(np.abs(xi), initial=0) > 40:
        raise ValueError('frequency input leaves [-40,40]')
    accumulator = PairwiseAccumulator()
    reading = {'max_alpha': 0.0, 'max_reduced_phase': 0.0, 'max_phase_integer': 0.0}
    for group, theta in enumerate(model['theta']):
        omega = LD(2)*pi_value*xi.astype(LD)-LD(theta)
        alpha = omega*model['radius']
        moments = moment_values(alpha, coefficients)
        reading['max_alpha'] = max(reading['max_alpha'], float(np.max(np.abs(alpha), initial=LD(0))))
        for start in range(0, model['panels'], chunk):
            stop = min(start+chunk, model['panels'])
            arguments = omega[None, :]*model['centers'][start:stop, None]
            phase, maximum, quotient = phase_values(arguments, pi_value, coefficients)
            reading['max_reduced_phase'] = max(reading['max_reduced_phase'], maximum)
            reading['max_phase_integer'] = max(reading['max_phase_integer'], quotient)
            inner = np.zeros((stop-start, len(xi), 2), dtype=CD)
            for degree in range(7):
                inner += moments[None, :, degree, None]*model['coefficients'][group, start:stop, degree, :][:, None, :].astype(CD)
            values = model['radius']*phase[:, :, None]*inner
            for value in values:
                accumulator.add(value)
    output = np.asarray(accumulator.finish(), dtype=complex)
    if np.any(~np.isfinite(output)):
        raise ValueError('nonfinite evaluator output')
    reading['term_count'] = accumulator.count
    reading['pairwise_depth'] = math.ceil(math.log2(accumulator.count))
    return output, reading


def arithmetic_price(model, totals, pi_value):
    owner = bridge.refined.remainder.jets.repaired
    unit = mp.iv.mpf(2)**-64
    gamma = lambda count: count*unit/(1-count*unit)
    pi_stored = exact_extended(pi_value)
    pi_gap = abs(pi_stored-mp.iv.pi)
    theta_max = max(abs(mp.iv.mpf(theta)) for theta in model['theta'])
    omega_bound = 80*mp.iv.pi+theta_max
    omega_error = 80*pi_gap+unit*(80*abs(pi_stored)+(1+unit)*80*abs(pi_stored)+theta_max)
    omega_size = omega_bound+omega_error
    center_size = exact_extended(np.max(np.abs(model['centers'])))
    radius = exact_extended(model['radius'])
    analytic_alpha_bound = omega_size*radius
    if owner.upper(analytic_alpha_bound) > 3:
        raise ValueError('full-window moment range exceeds the priced series domain')
    quotient_bound = int(mp.ceil(owner.upper(omega_size*center_size/(2*abs(pi_stored)))))+2
    argument_size = (1+unit)*omega_size*center_size+mp.iv.mpf('1e-4000')
    if owner.upper((1+unit)*argument_size/(2*abs(pi_stored))+mp.iv.mpf('0.5')) > quotient_bound:
        raise ValueError('phase quotient bound is insufficient for the full window')
    analytic_phase_bound = abs(pi_stored)+2*unit*argument_size+unit*(2+unit)*2*quotient_bound*abs(pi_stored)+mp.iv.mpf('1e-3990')
    if owner.upper(analytic_phase_bound) > mp.mpf('3.2'):
        raise ValueError('full-window reduced phase range exceeds the priced series domain')
    arg_error = center_size*omega_error+unit*omega_size*center_size
    reduction_error = arg_error+2*quotient_bound*pi_gap+unit*(
        2*quotient_bound*abs(pi_stored)+omega_size*center_size+(1+unit)*2*quotient_bound*abs(pi_stored))
    alpha_error = radius*omega_error+unit*omega_size*radius
    phase_limit = mp.iv.mpf('3.2')
    moment_limit = mp.iv.mpf(3)
    path_count = 4*SERIES_TERMS+16
    phase_series = 2*gamma(path_count)*mp.iv.exp(phase_limit)+mp.iv.exp(phase_limit)*phase_limit**SERIES_TERMS/math.factorial(SERIES_TERMS)
    moment_series = 2*gamma(path_count)*mp.iv.exp(moment_limit)+mp.iv.exp(moment_limit)*moment_limit**SERIES_TERMS/math.factorial(SERIES_TERMS)
    underflow = mp.iv.mpf('1e-4000')
    phase_error = phase_series+reduction_error+4000*underflow
    moment_error = moment_series+alpha_error+4000*underflow
    magnitude = (1+phase_error)*(1+moment_error)
    operation_ratio = phase_error+moment_error+phase_error*moment_error+gamma(96)*magnitude
    depth = math.ceil(math.log2(model['panels']*len(model['theta'])))
    sum_ratio = mp.iv.sqrt(2)*gamma(depth)*(1+gamma(96))*magnitude
    final_cast_ratio = mp.iv.sqrt(2)*(mp.iv.mpf(2)**-53)/(1-mp.iv.mpf(2)**-53)*(1+operation_ratio+sum_ratio)
    charges = {channel: {'execution': value['mass']*operation_ratio+4000*underflow,
                         'pairwise_sum': value['mass']*sum_ratio+4000*underflow,
                         'final_cast': value['mass']*final_cast_ratio+mp.iv.mpf('2e-300')}
               for channel, value in totals.items()}
    constants = {'phase_integer_bound': quotient_bound, 'pairwise_depth': depth, 'series_terms': SERIES_TERMS,
                 'analytic_alpha_bound': bridge.refined.remainder.propagation.interval_text(analytic_alpha_bound),
                 'analytic_reduced_phase_bound': bridge.refined.remainder.propagation.interval_text(analytic_phase_bound),
                 'series_path_operations': path_count, 'post_chain_operations': 96,
                 **{name: bridge.refined.remainder.propagation.interval_text(value) for name, value in
                    (('omega_error', omega_error), ('phase_error', phase_error),
                     ('moment_relative_error', moment_error), ('operation_ratio', operation_ratio),
                     ('sum_ratio', sum_ratio), ('final_cast_ratio', final_cast_ratio))}}
    return charges, constants


def independent_reference(model, xi):
    mp.mp.dps = 100
    converted_radius = exact_extended(model['radius'])
    owner = bridge.refined.remainder.jets.repaired
    radius = owner.lower(converted_radius)
    output = []
    for frequency in xi:
        channel_sum = [mp.mpc(0), mp.mpc(0)]
        for group, theta in enumerate(model['theta']):
            omega = 2*mp.pi*mp.mpf(float(frequency))-mp.mpf(theta)
            alpha = omega*radius
            moments = [mp.quad(lambda coordinate: coordinate**degree*mp.exp(-1j*alpha*coordinate), [-1, 0, 1])
                       for degree in range(7)]
            for panel, center_value in enumerate(model['centers']):
                center = owner.lower(exact_extended(center_value))
                phase = mp.exp(-1j*omega*center)
                for channel in range(2):
                    polynomial = sum((mp.mpc(float(value.real), float(value.imag))*moments[degree]
                                      for degree, value in enumerate(model['coefficients'][group, panel, :, channel])), mp.mpc(0))
                    channel_sum[channel] += radius*phase*polynomial
        output.append(channel_sum)
    return output


def main():
    mp.mp.dps = mp.iv.dps = 80
    platform = platform_contract()
    source = bridge.read_refined_source()
    previous = json.loads(bridge.OUT.read_text(encoding='utf-8'))
    for name, expected in previous['source_sha256'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != expected:
            raise ValueError('2300 provenance mismatch: '+name)
    carrier = bridge.refined.remainder.carrier
    capture, families, base, correction = carrier.SOURCE.load_owner()
    model, totals, panel_rows = prepare(families, base, correction)
    coefficient_control = {}
    for channel in totals:
        actual = bridge.refined.remainder.propagation.interval_text(totals[channel]['coefficient'])
        expected = previous['reading']['totals'][channel]['regenerated_coefficient_radius']
        if actual != expected:
            raise ArithmeticError('2300 regenerated coefficient control failed: '+channel)
        coefficient_control[channel] = True
    pi_value = midpoint_extended(mp.iv.pi)
    series, coefficient_relative = series_coefficients()
    charges, constants = arithmetic_price(model, totals, pi_value)
    combined = {}
    for channel in totals:
        combined[channel] = mp.iv.mpf(source['refined_reading'][channel+'_radius']['upper'])+totals[channel]['coefficient']+totals[channel]['geometry']+sum(charges[channel].values(), mp.iv.mpf(0))
    readings = {channel: {**{slot: bridge.refined.remainder.propagation.interval_text(value) for slot, value in totals[channel].items()},
                          **{slot: bridge.refined.remainder.propagation.interval_text(value) for slot, value in charges[channel].items()},
                          'combined_radius': bridge.refined.remainder.propagation.interval_text(combined[channel])} for channel in totals}
    print(json.dumps({'platform': platform, 'charges': readings, 'coefficient_control': coefficient_control}), flush=True)
    anchor_xi = np.array([-40.0, -3.605, 0.0, 3.605, 40.0])
    anchor, anchor_engine = evaluate(model, anchor_xi, pi_value, series)
    truth = independent_reference(model, anchor_xi)
    controls = []
    owner = bridge.refined.remainder.jets.repaired
    for index, frequency in enumerate(anchor_xi):
        for channel_index, channel in enumerate(totals):
            error = abs(mp.mpc(float(anchor[index, channel_index].real), float(anchor[index, channel_index].imag))-truth[index][channel_index])
            allowance = owner.lower(sum(charges[channel].values(), mp.iv.mpf(0)))
            if error > allowance:
                raise ArithmeticError('independent full-polynomial reference exceeded execution allowance')
            controls.append({'xi': float(frequency), 'channel': channel, 'absolute_error': float(error),
                             'execution_allowance': float(allowance), 'allowance_ratio': float(error/allowance)})
    print(json.dumps({'max_anchor_allowance_ratio': max(row['allowance_ratio'] for row in controls)}), flush=True)
    rows = []
    for step in (0.02, 0.01, 0.005):
        xi = np.arange(-round(40/step), round(40/step)+1)*step
        output, engine = evaluate(model, xi, pi_value, series)
        if engine['max_phase_integer'] > constants['phase_integer_bound']:
            raise ValueError('runtime phase integer exceeds the priced bound')
        kernel, count = carrier.SOURCE.prime_kernel(xi, 2*max(width*width for width, _ in families))
        if count != 41136:
            raise ValueError('incomplete kernel')
        base_radius = np.nextafter(float(owner.upper(combined['base'])), np.inf)
        corr_radius = np.nextafter(float(owner.upper(combined['corr'])), np.inf)
        value = bridge.refined.integrate_profile(xi, output, kernel, base_radius, corr_radius)
        row = {'xi_step': step, 'prime_power_count': count, 'engine': engine, 'reading': value,
               'sampled_budget_ratio': value['sampled_majorant_charge']/1e7}
        rows.append(row)
        print(json.dumps(row), flush=True)
    result = {'record': 2301, 'status': 'REGENERATED-CARRIER-EXECUTION-MODEL-PRICE',
              'certificate': False, 'hgap_closed': False, 'platform': platform,
              'owner': source['owner'], 'panels': 768, 'degree': 6,
              'coefficient_table_sha256': hashlib.sha256(model['coefficients'].tobytes()).hexdigest(),
              'coefficient_control': coefficient_control, 'series_coefficient_max_relative_error': coefficient_relative,
              'charges': readings, 'constants': constants, 'panel_rows': panel_rows,
              'independent_controls': controls, 'anchor_engine': anchor_engine, 'rows': rows,
              'sampled_majorant_pass_all_grids': all(row['sampled_budget_ratio'] <= 1 for row in rows),
              'source_sha256': {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (bridge.OUT, bridge.refined.OUT, carrier.SOURCE.CAPTURE,
                                             Path(bridge.__file__), Path(bridge.refined.__file__), Path(carrier.__file__),
                                             Path(carrier.SOURCE.__file__), Path(__file__))},
              'nonclaims': ['execution charge is a declared round-to-nearest model with operation-count assumptions, not a machine proof',
                            'independent numerical controls are not universal rounding proofs',
                            'kernel, annihilator, functional products and final trapezoid arithmetic remain outside the transform bridge',
                            'sampled full-window pricing does not certify continuous integration',
                            'no infinite-tail certificate, actual selected-owner bridge, hgap supplier or RH claim']}
    OUT.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
