"""Full-window sizing of the 2297 interpolation-only error majorant.

All readings are sampled diagnostics, not continuous integral certificates.
"""
import argparse
import hashlib
import json
import math
from pathlib import Path

import numpy as np

import routea_carrier_separated_functional_screen_2296 as carrier
import routea_carrier_envelope_remainder_price_2297 as remainder

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/2298_carrier_full_window_propagation_screen.json'


def error_terms(base_size, corr_size, base_radius, corr_radius):
    if any(np.any(np.asarray(value) < 0) for value in
           (base_size, corr_size, base_radius, corr_radius)):
        raise ValueError('sizes and radii must be nonnegative')
    base_error = 2*base_size*base_radius + base_radius**2
    corr_error = 2*corr_size*corr_radius + corr_radius**2
    return (base_size**2*corr_error, corr_size**2*base_error, base_error*corr_error)


def read_radii():
    artifact = json.loads(remainder.OUT.read_text(encoding='utf-8'))
    for name, expected in artifact['source_sha256'].items():
        if hashlib.sha256((ROOT/name).read_bytes()).hexdigest() != expected:
            raise ValueError('2297 source provenance mismatch: '+name)
    if artifact['certificate'] or artifact['hgap_closed']:
        raise ValueError('2297 diagnostic scope mismatch')
    reading = artifact['reading']
    if reading['panels'] != 192 or reading['degree'] != 6:
        raise ValueError('2297 profile must match 192:6 candidate')
    return (np.nextafter(float(reading['base_radius']['upper']), np.inf),
            np.nextafter(float(reading['corr_radius']['upper']), np.inf))


def run(step, base_radius, corr_radius):
    if not np.isfinite(step) or step <= 0:
        raise ValueError('step must be finite and positive')
    half_points = round(40/step)
    if not math.isclose(half_points*step, 40, rel_tol=1e-12, abs_tol=1e-12):
        raise ValueError('positive step must divide the finite window')
    xi = np.arange(-half_points, half_points+1)*step
    capture, families, base, correction = carrier.SOURCE.load_owner()
    candidate = carrier.separated_transform(xi, families, np.column_stack((base, correction)), 192, 6)
    kernel, count = carrier.SOURCE.prime_kernel(xi, 2*max(width*width for width, _ in families))
    if count != 41136:
        raise ValueError('incomplete kernel')
    weight = np.abs(kernel)*np.abs(carrier.SOURCE.annihilator(xi))**2
    terms = error_terms(np.abs(candidate[:, 0]), np.abs(candidate[:, 1]), base_radius, corr_radius)
    charges = [float(np.trapezoid(weight*term, xi)) for term in terms]
    total_density = weight*sum(terms)
    total = float(np.trapezoid(total_density, xi))
    candidate_integral = float(np.trapezoid(carrier.direct.functional(
        xi, candidate[:, 0], candidate[:, 1], kernel), xi))
    prior_artifact = json.loads(carrier.OUT.read_text(encoding='utf-8'))
    prior = next(row for row in prior_artifact['rows'] if row['xi_step'] == step
                 and row['panels'] == 192 and row['degree'] == 6 and row['reference_order'] == 512)
    movement = abs(candidate_integral-prior['candidate_signed_integral'])/max(abs(prior['candidate_signed_integral']), 1)
    if movement > 1e-12:
        raise ArithmeticError('2296 same-candidate control failed')
    peak = int(np.argmax(total_density))
    return {'xi_step': step, 'xi_points': len(xi), 'prime_power_count': count,
            'base_md5': capture['owner_capture']['base_md5'],
            'corr_md5': capture['owner_capture']['corr_md5'],
            'base_squared_corr_error_charge': charges[0],
            'corr_squared_base_error_charge': charges[1], 'cross_error_charge': charges[2],
            'sampled_majorant_charge': total, 'sampled_budget_ratio': total/1e7,
            'peak_xi': float(xi[peak]), 'peak_density': float(total_density[peak]),
            'same_candidate_signed_integral': candidate_integral,
            'same_candidate_relative_movement': movement,
            'prior_sampled_absolute_difference': prior['direct_absolute_difference']}


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--steps', default='0.02,0.01,0.005')
    parser.add_argument('--output', type=Path, default=OUT)
    args = parser.parse_args()
    steps = [float(value) for value in args.steps.split(',')]
    if not steps or any(not np.isfinite(value) or value <= 0 for value in steps):
        parser.error('steps must be finite positive values')
    base_radius, corr_radius = read_radii()
    rows = [run(step, base_radius, corr_radius) for step in steps]
    result = {'record': 2298, 'status': 'CARRIER-FULL-WINDOW-PROPAGATION-SCREEN',
              'certificate': False, 'hgap_closed': False, 'window': [-40, 40],
              'base_radius': base_radius, 'corr_radius': corr_radius,
              'diagnostic_budget': 10000000, 'rows': rows,
              'sampled_majorant_pass_all_grids': all(row['sampled_budget_ratio'] <= 1 for row in rows),
              'source_sha256': {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (remainder.OUT, carrier.OUT, carrier.SOURCE.CAPTURE,
                                             Path(carrier.SOURCE.__file__), Path(carrier.direct.__file__),
                                             Path(carrier.__file__), Path(remainder.__file__), Path(__file__))},
              'nonclaims': ['radii price ideal interpolation only, not the stored evaluator arithmetic',
                            'sampled magnitudes and trapezoids are not continuous enclosures',
                            'majorant size is not a lower bound on actual error',
                            'grid agreement is a reproducibility control, not an integral certificate',
                            'no infinite-tail estimate, selected-owner bridge, hgap supplier or RH claim']}
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n', encoding='utf-8')
    for row in rows:
        print(json.dumps(row), flush=True)


if __name__ == '__main__':
    main()
