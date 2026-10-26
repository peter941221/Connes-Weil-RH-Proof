#!/usr/bin/env python3
"""Signed omitted-prime band on the exact stored row-B powered-seed model.

The outputs are model diagnostics on finite frequency quadrature. They do
not certify the continuum gate or the uncomputed prime-power range.
"""

from fractions import Fraction
import hashlib
import json
import math
from pathlib import Path
import resource
import sys
import time

import numpy as np

import fourpoint_actual_owner_1980 as owner_engine
import fourpoint_coupling_scan_2028 as prime_engine
import fourpoint_diagonal_sign_1918 as arch_engine
import fourpoint_owner_density_1959 as orbit_engine
import fourpoint_powered_seed_1981 as seed_engine

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/3119_routeb_prime_cut_probe.json'
SOURCES = [
    'scripts/routeb_prime_cut_probe_3119.py',
    'scripts/fourpoint_actual_owner_1980.py',
    'scripts/fourpoint_coupling_scan_2028.py',
    'scripts/fourpoint_diagonal_sign_1918.py',
    'scripts/fourpoint_owner_density_1959.py',
    'scripts/fourpoint_powered_seed_1981.py',
    'results/2722f_rowB_capture_data.json', 'results/2032_gate_row_search.json',
]


def digest(rel):
    return hashlib.sha256((ROOT / rel).read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def decode(values):
    return [complex(float(Fraction(a)), float(Fraction(b))) for a, b in values]


def main():
    if sys.platform != 'linux':
        raise RuntimeError('run in the Linux verification environment')
    started = time.monotonic()
    OUT.write_text(json.dumps({'record': 3119, 'status': 'RUNNING'})+'\n', encoding='utf-8')
    provenance = {rel: digest(rel) for rel in SOURCES}
    capture = json.loads((ROOT / SOURCES[-2]).read_text())
    rho = decode([capture['rho']])[0]
    nodes, targets, values = [decode(capture[k]) for k in ('owner', 'targets', 'values')]
    assert len(nodes) == 56 and len(targets) == 8
    assert [nodes[i] for i in capture['target_owner_index']] == targets
    assert values == [owner_engine.target_value(rho, z) for z in nodes]
    records = json.loads((ROOT / SOURCES[-1]).read_text())
    legacy = next(r for r in records['rows'] if r['gamma'] == rho.imag and r['N'] == 5 and r['n'] == 3)
    vals, logs = prime_engine.fast_prime_powers_up_to(math.exp(12))
    cut = vals <= math.floor(math.exp(10))
    band = ~cut
    assert np.any(cut) and np.any(band)
    cases = [(0.02, 300), (0.01, 300), (0.01, 1200)]
    rows = []
    controls = {'capture_identity': True, 'nonempty_omitted_band': True,
                'independent_prime_generator_control': prime_engine.validation_block()['all_identical']}
    for dxi, order in cases:
        xi = np.arange(-25.0, 25.0 + 0.5 * dxi, dxi)
        transform = seed_engine.make_powered_seed(order=order)
        seed0 = complex(transform(np.array([0j]))[0])
        W = prime_engine.build_density(xi, transform, seed0, nodes, targets, values, 3)
        P = np.real(orbit_engine.P_from_nodes(xi, [z - 0.5 for z in targets[:4]]))
        fs = (W, P * W, P * P * W)
        sig = arch_engine.sigma_vec(2 * math.pi * xi)
        arch = np.array([float(np.trapezoid(sig * f, xi)) for f in fs])
        kcut = prime_engine.direct_prime_channel(xi, vals[cut], logs[cut])
        kband = prime_engine.direct_prime_channel(xi, vals[band], logs[band])
        pcut = np.array([float(np.trapezoid(kcut * f, xi)) for f in fs])
        pband = np.array([float(np.trapezoid(kband * f, xi)) for f in fs])
        coefficients = np.array([24.0 ** 2, -48.0, 1.0])
        legacy_gate = float(coefficients @ (arch + pcut))
        signed_band = float(coefficients @ pband)
        direct_band = float(np.trapezoid(kband * (P - 24) ** 2 * W, xi))
        direct_cut = float(np.trapezoid((sig + kcut) * (P - 24) ** 2 * W, xi))
        scale = max(1.0, abs(direct_band), abs(signed_band))
        controls[f'band_polarization_{dxi}_{order}'] = abs(direct_band - signed_band) <= 2e-12 * scale
        controls[f'cut_polarization_{dxi}_{order}'] = abs(direct_cut - legacy_gate) <= 2e-12 * max(1.0, abs(direct_cut))
        if order == 300:
            ref = legacy[f'dxi{dxi:g}']
            got = arch + pcut
            controls[f'legacy_bitwise_{dxi}'] = got.tolist() == [ref['C'], ref['b'], ref['D']]
        rows.append({'dxi': dxi, 'seed_order': order, 'C_cut': float(arch[0]+pcut[0]),
                     'cut_coefficients_C_b_D': (arch+pcut).tolist(),
                     'band_coefficients_C_b_D': pband.tolist(),
                     'gate_cut_lambda24': legacy_gate, 'signed_band_lambda24': signed_band,
                     'gate_through_log12_lambda24': legacy_gate + signed_band,
                     'signed_band_over_abs_old_gate': signed_band / abs(legacy_gate),
                     'direct_band_lambda24': direct_band})
        print(f'dxi={dxi} order={order} old={legacy_gate:.9e} band={signed_band:.9e} new={legacy_gate+signed_band:.9e}', flush=True)
    controls['source_unchanged'] = provenance == {rel: digest(rel) for rel in SOURCES}
    controls['finite_output'] = all(math.isfinite(v) for r in rows for v in r.values() if isinstance(v, float))
    reference = rows[-1]['signed_band_lambda24']
    stability = [abs(r['signed_band_lambda24']-reference)/max(1.0,abs(reference)) for r in rows]
    controls['grid_and_rule_stable'] = max(stability) < 1e-5
    controls['empty_band_exact_zero'] = bool(np.array_equal(
        prime_engine.direct_prime_channel(np.array([-1.0,0.0,1.0]), vals[:0], logs[:0]), np.zeros(3)))
    elapsed = time.monotonic()-started
    rss_bytes = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
    controls['resource_budget'] = elapsed < 600 and rss_bytes <= 2*1024**3
    report = {'record': 3119, 'status': 'MODEL-DIAGNOSTIC' if all(controls.values()) else 'CONTROL-FAIL',
              'owner': 'Exact stored 2722F nodes/values, powered seed, n=3, lambda=24',
              'rho_exact': [str(Fraction(rho.real)), str(Fraction(rho.imag))],
              'n': 3, 'lambda': 24, 'node_count': len(nodes),
              'prime_log_cut': 10, 'prime_log_end': 12,
              'cut_prime_power_count': int(np.sum(cut)), 'band_prime_power_count': int(np.sum(band)),
              'frequency_window': [-25, 25], 'controls': controls, 'rows': rows,
              'relative_band_stability': stability,
              'decision': ('OMITTED-BAND-EXCEEDS-OLD-MARGIN' if abs(reference)>abs(rows[-1]['gate_cut_lambda24'])
                           else 'OMITTED-BAND-WITHIN-OLD-MARGIN') if all(controls.values()) else 'NO-VERDICT',
              'elapsed_seconds': elapsed, 'max_rss_bytes': rss_bytes,
              'hash_convention': 'SHA-256 with CRLF normalized to LF', 'provenance': provenance,
              'scope': 'Signed finite-frequency quadrature diagnostics only; no continuum readback, '
                       'full prime coverage, zero-set assertion or RH proof.'}
    OUT.write_text(json.dumps(report, indent=2)+'\n', encoding='utf-8')
    print(json.dumps({'status': report['status'], 'controls': controls}, indent=2))
    return 0 if all(controls.values()) else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as exc:
        OUT.write_text(json.dumps({'record': 3119, 'status': 'CONTROL-FAIL',
                                   'failure_type': type(exc).__name__})+'\n', encoding='utf-8')
        print(f'probe failed: {exc}', file=sys.stderr)
        sys.exit(1)
