"""Price stored polynomial coefficients and panel geometry against ideal 768:6.

The finite-window bridge deliberately excludes moment/phase execution error.
"""
import hashlib
import json
from pathlib import Path

import mpmath as mp
import numpy as np

import routea_carrier_refined_remainder_screen_2299 as refined

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/2300_carrier_coefficient_bridge_price.json'
CHEBYSHEV_POWERS = ((1,), (0, 1), (-1, 0, 2), (0, -3, 0, 4),
                    (1, 0, -8, 0, 8), (0, 5, 0, -20, 0, 16),
                    (-1, 0, 18, 0, -48, 0, 32))


def exact_cosine(index):
    half_root = mp.iv.sqrt(3)/2
    clock = (mp.iv.mpf(1), half_root, mp.iv.mpf('0.5'), mp.iv.mpf(0),
             mp.iv.mpf('-0.5'), -half_root, mp.iv.mpf(-1), -half_root,
             mp.iv.mpf('-0.5'), mp.iv.mpf(0), mp.iv.mpf('0.5'), half_root)
    return clock[index % 12]


def interpolation_matrix():
    matrix = [[mp.iv.mpf(0) for _ in range(7)] for _ in range(7)]
    for order, powers in enumerate(CHEBYSHEV_POWERS):
        for node in range(7):
            scale = mp.iv.mpf(1)/3
            if order in (0, 6):
                scale /= 2
            if node in (0, 6):
                scale /= 2
            for degree, value in enumerate(powers):
                matrix[degree][node] += value*scale*exact_cosine(order*node)
    return matrix


def envelope_interval(coordinate, width):
    radius = mp.iv.mpf(width)**2
    quotient = 1-coordinate**2/radius**2
    upper = refined.remainder.jets.repaired.upper
    lower = refined.remainder.jets.repaired.lower
    if upper(quotient) <= 0:
        return mp.iv.mpf(0)
    exponent_upper = -30/mp.iv.mpf(upper(quotient))+mp.iv.mpf(upper(coordinate))/2
    if upper(exponent_upper) < -1000:
        return mp.iv.mpf([0, upper(mp.iv.exp(-1000))])
    if lower(quotient) <= 0:
        return mp.iv.mpf([0, upper(mp.iv.exp(exponent_upper))])
    return mp.iv.exp(-30/quotient+coordinate/2)


def coefficient_radius(coefficients, candidate, radius):
    upper = refined.remainder.jets.repaired.modulus_upper
    return radius*sum((mp.iv.mpf(2)/(degree+1)*mp.iv.mpf(upper(
        mp.iv.mpc(float(candidate[degree].real), float(candidate[degree].imag))-value))
        for degree, value in enumerate(coefficients)), mp.iv.mpf(0))


def regenerated_coefficients(coefficients):
    owner = refined.remainder.jets.repaired
    return np.array([complex(float((owner.lower(value.real)+owner.upper(value.real))/2),
                             float((owner.lower(value.imag)+owner.upper(value.imag))/2))
                     for value in coefficients])


def price_coefficients(families, base, correction, panels):
    carrier = refined.remainder.carrier
    upper = refined.remainder.jets.repaired.upper
    half = max(mp.iv.mpf(width)**2 for width, _ in families)
    length = 2*half/panels
    float_half = max(width*width for width, _ in families)
    float_edges = np.linspace(-float_half, float_half, panels+1)
    float_nodes = np.cos(np.pi*np.arange(7)/6)
    matrix = interpolation_matrix()
    channels = refined.remainder.channel_coefficients(families, base), refined.remainder.channel_coefficients(families, correction)
    coefficients = np.column_stack((base, correction))
    slots = ('stored_coefficient_radius', 'stored_geometry_radius', 'regenerated_coefficient_radius')
    totals = {channel: {slot: mp.iv.mpf(0) for slot in slots} for channel in ('base', 'corr')}
    rows = []
    widths = sorted(set(width for width, _ in families))
    for panel in range(panels):
        radius = length/2
        center = -half+length*(mp.iv.mpf(panel)+mp.iv.mpf('0.5'))
        left, right = float_edges[panel:panel+2]
        float_center = (left+right)/2
        float_radius = (right-left)/2
        cache = {}
        for width in widths:
            samples = [envelope_interval(center+radius*exact_cosine(node), width) for node in range(7)]
            cache[width] = [sum((matrix[degree][node]*samples[node] for node in range(7)), mp.iv.mpf(0))
                            for degree in range(7)]
        panel_totals = {channel: {slot: mp.iv.mpf(0) for slot in slots} for channel in totals}
        for group, (theta, indices) in enumerate(carrier.carrier_groups(families)):
            envelopes = carrier.envelope_values(float_center+float_radius*float_nodes, families, coefficients, indices)
            for channel_index, channel in enumerate(totals):
                _, by_width = channels[channel_index][group]
                ideal = [sum((coefficient*cache[width][degree] for width, coefficient in by_width.items()), mp.iv.mpc(0))
                         for degree in range(7)]
                stored_short = np.polynomial.chebyshev.cheb2poly(np.polynomial.chebyshev.chebfit(
                    float_nodes, envelopes[:, channel_index], 6))
                stored = np.zeros(7, dtype=complex)
                stored[:len(stored_short)] = stored_short
                regenerated = regenerated_coefficients(ideal)
                panel_totals[channel]['stored_coefficient_radius'] += coefficient_radius(ideal, stored, radius)
                panel_totals[channel]['regenerated_coefficient_radius'] += coefficient_radius(ideal, regenerated, radius)
                magnitude = sum((abs(mp.iv.mpc(float(value.real), float(value.imag))) for value in stored), mp.iv.mpf(0))
                radius_gap = abs(mp.iv.mpf(float(float_radius))-radius)
                center_gap = abs(mp.iv.mpf(float(float_center))-center)
                frequency_bound = 80*mp.iv.pi+abs(mp.iv.mpf(theta))
                phase_gap = mp.iv.mpf(min(mp.mpf(2), upper(frequency_bound*(center_gap+radius_gap))))
                panel_totals[channel]['stored_geometry_radius'] += (2*radius_gap+2*radius*phase_gap)*magnitude
        row = {'panel': panel}
        for channel in totals:
            row[channel] = {}
            for slot in slots:
                totals[channel][slot] += panel_totals[channel][slot]
                row[channel][slot] = refined.remainder.propagation.interval_text(panel_totals[channel][slot])
        rows.append(row)
    return {'panels': panels, 'degree': 6, 'rows': rows,
            'totals': {channel: {slot: refined.remainder.propagation.interval_text(value)
                                for slot, value in charges.items()} for channel, charges in totals.items()}}, totals


def read_refined_source():
    source = json.loads(refined.OUT.read_text(encoding='utf-8'))
    for path, expected in source['source_sha256'].items():
        if hashlib.sha256((ROOT/path).read_bytes()).hexdigest() != expected:
            raise ValueError('2299 provenance mismatch: '+path)
    reading = source['refined_reading']
    if reading['panels'] != 768 or reading['degree'] != 6:
        raise ValueError('2300 bridge requires the named 768:6 profile')
    if source['certificate'] or source['hgap_closed']:
        raise ValueError('2299 diagnostic scope mismatch')
    return source


def main():
    mp.mp.dps = mp.iv.dps = 80
    source = read_refined_source()
    capture, families, base, correction = refined.remainder.carrier.SOURCE.load_owner()
    reading, totals = price_coefficients(families, base, correction, source['refined_reading']['panels'])
    print(json.dumps(reading['totals']), flush=True)
    radii = {}
    for variant in ('stored_polynomial', 'regenerated_coefficients_ideal_geometry'):
        radii[variant] = {}
        for channel in totals:
            charge = mp.iv.mpf(source['refined_reading'][channel+'_radius']['upper'])
            if variant == 'stored_polynomial':
                charge += totals[channel]['stored_coefficient_radius']+totals[channel]['stored_geometry_radius']
            else:
                charge += totals[channel]['regenerated_coefficient_radius']
            radii[variant][channel] = np.nextafter(float(refined.remainder.jets.repaired.upper(charge)), np.inf)
    rows = []
    for step in (0.02, 0.01, 0.005):
        half_points = round(40/step)
        xi = np.arange(-half_points, half_points+1)*step
        candidate = refined.remainder.carrier.separated_transform(xi, families, np.column_stack((base, correction)), 768, 6)
        kernel, count = refined.remainder.carrier.SOURCE.prime_kernel(xi, 2*max(width*width for width, _ in families))
        if count != 41136:
            raise ValueError('incomplete kernel')
        for variant, radius in radii.items():
            diagnostic = refined.integrate_profile(xi, candidate, kernel, radius['base'], radius['corr'])
            rows.append({'xi_step': step, 'variant': variant, 'reading': diagnostic,
                         'sampled_budget_ratio': diagnostic['sampled_majorant_charge']/1e7})
            print(json.dumps(rows[-1]), flush=True)
    result = {'record': 2300, 'status': 'CARRIER-COEFFICIENT-AND-GEOMETRY-BRIDGE-PRICE',
              'certificate': False, 'hgap_closed': False, 'owner': source['owner'],
              'reading': reading, 'combined_partial_radii': radii, 'rows': rows,
              'source_sha256': {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (refined.OUT, refined.remainder.carrier.SOURCE.CAPTURE,
                                             Path(refined.__file__), Path(refined.remainder.__file__),
                                             Path(refined.remainder.carrier.__file__), Path(__file__))},
              'nonclaims': ['stored geometry and coefficient bounds price exact integration of those polynomials only',
                            'moment and phase floating execution and accumulation are not included',
                            'regenerated coefficient variant uses ideal geometry, not an implemented complete evaluator',
                            'both variant prices use sampled old-candidate magnitudes, not a certified alternate magnitude envelope',
                            'sampled trapezoids do not certify continuous integration',
                            'no infinite tail, actual selected-owner readback, hgap supplier or RH claim']}
    OUT.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
