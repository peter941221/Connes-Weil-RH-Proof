"""Reprice the named 768:6 profile with a same-run 192:6 control.

The diagnostic keeps the captured owner and the full finite-window kernel.
"""
import argparse
import hashlib
import json
from pathlib import Path

import mpmath as mp
import numpy as np

import routea_carrier_envelope_remainder_price_2297 as remainder
import routea_carrier_full_window_propagation_screen_2298 as propagation

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/2299_carrier_refined_remainder_screen.json'


def upward_radius(reading, channel):
    return np.nextafter(float(reading[channel+'_radius']['upper']), np.inf)


def integrate_profile(xi, candidate, kernel, base_radius, corr_radius):
    weight = np.abs(kernel)*np.abs(remainder.carrier.SOURCE.annihilator(xi))**2
    terms = propagation.error_terms(np.abs(candidate[:, 0]), np.abs(candidate[:, 1]), base_radius, corr_radius)
    charges = [float(np.trapezoid(weight*term, xi)) for term in terms]
    return {'sampled_majorant_charge': float(np.trapezoid(weight*sum(terms), xi)),
            'channel_charges': charges,
            'sampled_signed_integral': float(np.trapezoid(remainder.carrier.direct.functional(
                xi, candidate[:, 0], candidate[:, 1], kernel), xi))}


def run_grids(families, base, correction, baseline, refined, steps):
    prior = json.loads(propagation.OUT.read_text(encoding='utf-8'))
    coefficients = np.column_stack((base, correction))
    rows = []
    for step in steps:
        half_points = round(40/step)
        if not np.isfinite(step) or step <= 0 or not np.isclose(half_points*step, 40):
            raise ValueError('positive finite step must divide window')
        xi = np.arange(-half_points, half_points+1)*step
        kernel, count = remainder.carrier.SOURCE.prime_kernel(xi, 2*max(width*width for width, _ in families))
        if count != 41136:
            raise ValueError('incomplete kernel')
        old_candidate = remainder.carrier.separated_transform(xi, families, coefficients, 192, 6)
        new_candidate = remainder.carrier.separated_transform(xi, families, coefficients, refined['panels'], 6)
        old = integrate_profile(xi, old_candidate, kernel, upward_radius(baseline, 'base'), upward_radius(baseline, 'corr'))
        new = integrate_profile(xi, new_candidate, kernel, upward_radius(refined, 'base'), upward_radius(refined, 'corr'))
        anchor = next(row for row in prior['rows'] if row['xi_step'] == step)
        control = abs(old['sampled_majorant_charge']-anchor['sampled_majorant_charge'])/anchor['sampled_majorant_charge']
        if control > 1e-12:
            raise ArithmeticError('2298 baseline reproduction failed')
        difference = remainder.carrier.direct.functional(xi, new_candidate[:, 0], new_candidate[:, 1], kernel)-remainder.carrier.direct.functional(
            xi, old_candidate[:, 0], old_candidate[:, 1], kernel)
        rows.append({'xi_step': step, 'xi_points': len(xi), 'prime_power_count': count,
                     'baseline': old, 'refined': new, 'baseline_relative_movement': control,
                     'refined_budget_ratio': new['sampled_majorant_charge']/1e7,
                     'price_gain': old['sampled_majorant_charge']/new['sampled_majorant_charge'],
                     'candidate_difference_signed': float(np.trapezoid(difference, xi)),
                     'candidate_difference_absolute': float(np.trapezoid(np.abs(difference), xi))})
        print(json.dumps(rows[-1]), flush=True)
    return rows


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--panels', type=int, default=768)
    parser.add_argument('--subcells', type=int, default=2)
    parser.add_argument('--output', type=Path, default=OUT)
    args = parser.parse_args()
    if args.panels <= 0 or args.subcells <= 0:
        parser.error('panel and subcell counts must be positive')
    mp.mp.dps = mp.iv.dps = 70
    propagation.read_radii()
    capture, families, base, correction = remainder.carrier.SOURCE.load_owner()
    baseline, _ = remainder.price(families, base, correction, 192, 2)
    prior = json.loads(remainder.OUT.read_text(encoding='utf-8'))['reading']
    if baseline != prior:
        raise ArithmeticError('2297 same-run panel-ledger reproduction failed')
    print(json.dumps({'baseline_panel_ledger_bitwise': True}), flush=True)
    refined, _ = remainder.price(families, base, correction, args.panels, args.subcells)
    print(json.dumps({key: refined[key] for key in ('panels', 'base_radius', 'corr_radius')}), flush=True)
    rows = run_grids(families, base, correction, baseline, refined, (0.02, 0.01, 0.005))
    result = {'record': 2299, 'status': 'CARRIER-REFINED-REMAINDER-SCREEN',
              'certificate': False, 'hgap_closed': False, 'baseline_panel_ledger_bitwise': True,
              'owner': {'family_count': len(families), 'base_md5': capture['owner_capture']['base_md5'],
                        'corr_md5': capture['owner_capture']['corr_md5']},
              'baseline_reading': baseline, 'refined_reading': refined, 'rows': rows,
              'sampled_majorant_pass_all_grids': all(row['refined_budget_ratio'] <= 1 for row in rows),
              'source_sha256': {path.relative_to(ROOT).as_posix(): hashlib.sha256(path.read_bytes()).hexdigest()
                                for path in (remainder.OUT, propagation.OUT, remainder.carrier.SOURCE.CAPTURE,
                                             Path(remainder.__file__), Path(propagation.__file__),
                                             Path(remainder.carrier.__file__), Path(remainder.jets.__file__),
                                             Path(remainder.propagation.__file__), Path(__file__))},
              'nonclaims': ['uniform radii price ideal polynomial interpolation, not stored arithmetic',
                            'sampled majorant and grid agreement are not continuous integral certificates',
                            'no infinite-tail certificate or actual selected-owner readback',
                            'no hgap supplier, producer GO or RH claim']}
    args.output.write_text(json.dumps(result, indent=2, allow_nan=False)+'\n', encoding='utf-8')


if __name__ == '__main__':
    main()
