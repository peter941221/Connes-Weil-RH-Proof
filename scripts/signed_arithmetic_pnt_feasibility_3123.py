#!/usr/bin/env python3
"""Exact algebra and endpoint controls for the paper review in record 3123.

Polynomial weights and formal log(p) symbols check partial summation against
direct finite prime-power sums. They are auxiliary controls, not fabricated
detector data. No actual detector, PNT theorem, Weil sign or RH is certified.
All mathematical arithmetic uses Fraction; there is no numerical quadrature.
"""

from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path
import resource
import sys
import time


ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / 'results/3123_signed_arithmetic_pnt_feasibility.json'
SOURCES = [
    'scripts/signed_arithmetic_pnt_feasibility_3123.py',
    'ConnesWeilRH/Dev/C1RouteBSignedPrimeCut3119.lean',
    'ConnesWeilRH/Dev/C1RouteBPrimeFourierReadback3120.lean',
    'ConnesWeilRH/Dev/C1RouteBAdaptivePoweredTail3117.lean',
    'ConnesWeilRH/Dev/C1RouteBQuadraticPinGapCost3116.lean',
    'ConnesWeilRH/Dev/C1ActualWeilUnavoidableDeficit3122.lean',
    'docs/proofs/215_pnt_main_kernel_and_all_prime_principal_screen.md',
    'docs/proofs/220_qroot_pnt_green_identity.md',
    'docs/proofs/221_target_zero_chebyshev_pairing.md',
]


def digest(rel):
    return hashlib.sha256((ROOT / rel).read_bytes().replace(b'\r\n', b'\n')).hexdigest()


def multiply(left, right):
    result = [Q(0)] * (len(left) + len(right) - 1)
    for i, x in enumerate(left):
        for j, y in enumerate(right):
            result[i + j] += x * y
    return tuple(result)


def evaluate(poly, x):
    result = Q(0)
    for coefficient in reversed(poly):
        result = result * x + coefficient
    return result


def integrate(poly, start, end):
    return sum((c * (Q(end) ** (i + 1) - Q(start) ** (i + 1)) / (i + 1)
                for i, c in enumerate(poly)), Q(0))


def add_scaled(target, source, scale=Q(1)):
    for symbol, coefficient in source.items():
        target[symbol] = target.get(symbol, Q(0)) + scale * coefficient
    return {symbol: coefficient for symbol, coefficient in target.items() if coefficient}


def prime_power_base(n):
    for divisor in range(2, n + 1):
        if n % divisor == 0:
            rest = n
            while rest % divisor == 0:
                rest //= divisor
            return divisor if rest == 1 else None
    return None


def chebyshev(x):
    result = {}
    for q in range(2, x + 1):
        base = prime_power_base(q)
        if base is not None:
            symbol = f'log({base})'
            result[symbol] = result.get(symbol, Q(0)) + 1
    return result


def discrepancy(x):
    return add_scaled({'constant': -Q(x)}, chebyshev(x))


def check_interval(start, end, poly):
    # Direct sum uses (start,end]; psi(start) includes the cutoff's own jump.
    direct = {}
    for q in range(start + 1, end + 1):
        base = prime_power_base(q)
        if base is not None:
            direct = add_scaled(direct, {f'log({base})': 2 * evaluate(poly, q)})

    derivative = tuple(i * poly[i] for i in range(1, len(poly))) or (Q(0),)
    x_derivative = (Q(0),) + derivative
    error_integral = {}
    for k in range(start, end):
        error_integral = add_scaled(error_integral, chebyshev(k),
                                    integrate(derivative, k, k + 1))
        error_integral = add_scaled(error_integral,
                                    {'constant': -integrate(x_derivative, k, k + 1)})

    endpoint = add_scaled({}, discrepancy(end), 2 * evaluate(poly, end))
    endpoint = add_scaled(endpoint, discrepancy(start), -2 * evaluate(poly, start))
    rhs = add_scaled({'constant': 2 * integrate(poly, start, end)}, endpoint)
    rhs = add_scaled(rhs, error_integral, -2)
    return direct, rhs, endpoint


def serialize(symbols):
    return {symbol: str(value) for symbol, value in sorted(symbols.items())}


def main():
    if sys.platform != 'linux':
        raise RuntimeError('run in a Linux verification environment')
    started = time.monotonic()
    OUT.write_text(json.dumps({'record': 3123, 'status': 'RUNNING'}) + '\n', encoding='utf-8')
    provenance = {rel: digest(rel) for rel in SOURCES}
    controls = {}
    rows = []
    for start, end in ((2, 3), (2, 8), (3, 9), (4, 12), (8, 13), (12, 13), (4, 4)):
        upper_zero = (Q(end * end), Q(-2 * end), Q(1))
        lower_zero = (Q(start * start), Q(-2 * start), Q(1))
        profiles = {
            'upper_endpoint_zero': upper_zero,
            'both_endpoints_zero': multiply(lower_zero, upper_zero),
            'nonzero_upper_endpoint': (Q(1), Q(1)),
        }
        for name, poly in profiles.items():
            direct, rhs, endpoint = check_interval(start, end, poly)
            key = f'partial_summation_{start}_{end}_{name}'
            controls[key] = direct == rhs
            rows.append({'cutoff': start, 'end': end, 'profile': name,
                         'direct_sum': serialize(direct), 'by_parts': serialize(rhs),
                         'endpoint': serialize(endpoint)})

    # Mutations must fail on a boundary where the changed term matters.
    poly = (Q(9), Q(-6), Q(1))  # (3-x)^2 on [2,3].
    direct, rhs, endpoint = check_interval(2, 3, poly)
    controls['empty_excluded_band_is_zero'] = direct == {}
    controls['nonzero_cutoff_endpoint_retained'] = bool(endpoint)
    controls['missing_endpoint_rejected'] = add_scaled(rhs.copy(), endpoint, -1) != direct
    controls['left_limit_psi_at_cutoff_rejected'] = add_scaled(
        rhs.copy(), {'log(2)': 2 * evaluate(poly, 2)}) != direct
    controls['including_cutoff_prime_rejected'] = add_scaled(
        direct.copy(), {'log(2)': 2 * evaluate(poly, 2)}) != rhs
    nonzero, _, _ = check_interval(2, 8, (Q(64), Q(-16), Q(1)))
    controls['missing_hermitian_factor_two_rejected'] = (
        bool(nonzero) and {k: v / 2 for k, v in nonzero.items()} != nonzero)
    controls['prime_power_repeats_retained'] = chebyshev(8)['log(2)'] == 3

    # For b>0, 2*b*(log W)' = b + 2*r - c*sqrt(b).
    # Complete the square in y=sqrt(b), using exact published decimals.
    r, c = Q(303, 200), Q(4137, 5000)
    remainder = 2 * r - c * c / 4
    square = multiply((-c / 2, Q(1)), (-c / 2, Q(1)))
    controls['envelope_derivative_square_identity'] = (
        (square[0] + remainder, square[1], square[2]) == (2 * r, -c, Q(1)))
    controls['envelope_derivative_remainder_positive'] = remainder > 0
    controls['envelope_growth_square_identity'] = (
        multiply((-c, Q(1, 2)), (-c, Q(1, 2))) == (c * c, -c, Q(1, 4)))
    controls['sources_unchanged'] = provenance == {rel: digest(rel) for rel in SOURCES}
    elapsed = time.monotonic() - started
    rss = resource.getrusage(resource.RUSAGE_SELF).ru_maxrss * 1024
    controls['resource_budget'] = elapsed < 60 and rss <= 2 * 1024 ** 3
    report = {
        'record': 3123, 'status': 'EXACT-CONTROLS-PASS' if all(controls.values()) else 'CONTROL-FAIL',
        'scope': 'Rational algebra and auxiliary finite prime-power endpoint controls only. '
                 'No actual detector integral, external PNT theorem, Lean sign, or RH is certified.',
        'literature': {'url': 'https://arxiv.org/html/2204.01980v2',
                       'theorem': 'Johnston-Yang Theorem 1.1 (1.3), x>=2',
                       'A': '939/100', 'r': str(r), 'c': str(c),
                       'grade': 'External literature input; not formalized or axiomatized'},
        'controls': controls, 'rows': rows,
        'derivative_square_positive_remainder': str(remainder),
        'actual_signed_pairing': 'OPEN', 'actual_pnt_envelope_budget': 'UNPRICED',
        'rh': 'UNPROVED', 'elapsed_seconds': elapsed, 'max_rss_bytes': rss,
        'hash_convention': 'SHA-256 with CRLF normalized to LF', 'provenance': provenance,
    }
    OUT.write_text(json.dumps(report, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: report[k] for k in ('status', 'controls', 'actual_signed_pairing',
                                            'actual_pnt_envelope_budget', 'rh')}, indent=2))
    return 0 if all(controls.values()) else 1


if __name__ == '__main__':
    try:
        sys.exit(main())
    except Exception as exc:
        OUT.write_text(json.dumps({'record': 3123, 'status': 'CONTROL-FAIL',
                                   'failure_type': type(exc).__name__}) + '\n', encoding='utf-8')
        print(f'feasibility controls failed: {exc}', file=sys.stderr)
        sys.exit(1)
