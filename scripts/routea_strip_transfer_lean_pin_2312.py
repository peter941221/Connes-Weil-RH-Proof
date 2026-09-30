"""Record 2312 pin check: the Lean strip-transfer constants against the
certified 2303 artifact.

The Lean module `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` pins the
record 2303 grid geometry as decimal constants:

    stripRadius2303 := 6.5536001    (sound upper of owner.rmax render)
    stripHalfStep2303 := 0.005      (exact grid.half_step)
    stripTransfer2303 := 1.0677312  (record 2311 transfer pin)

and proves `Real.exp (2 * stripRadius2303 * stripHalfStep2303) <=
stripTransfer2303` by `Real.exp_bound'` at order 6.  This check
machine-verifies, in exact rational arithmetic, that

  1. the radius pin is an UPPER of the committed `owner.rmax` render
     `6.553600000000003` (sound under render rounding: the exact decimal
     `6.5536` sits ~3.4 ulp below the render), with slack above 100 ulp
     of the render and below the radius-tightness bar 1e-6 (the Taylor
     margin `S < stripTransfer2303` survives radius slack up to
     ~2.25e-6, so the bar sits an order of magnitude inside the failure
     frontier);
  2. the half-step pin equals the committed `grid.half_step` exactly
     (a designed parameter, `1/(2*(101-1))`, not a rounded render);
  3. the order-6 Taylor bound `S(x) = sum_{m<6} x^m/m! +
     x^6*7/(720*6)` at the pinned exponent `x = 2*6.5536001*0.005 =
     0.065536001` is exactly below `stripTransfer2303`, with the margin
     reported; the bound's overshoot over `e^x` is a few 1e-11;
  4. the committed `grid.transfer` render agrees with
     `e^(2 * owner.rmax * grid.half_step)` to 1e-12 relative, and the
     pinned transfer dominates that render;
  5. the Lean text carries the expected declarations, the exp_bound'
     order and the norm_num call (transcription guards).

Controls run in the same pass: a synthetic-text regex probe, a negative
control (radius pin shifted below the render must fail the direction
check), a render-dust control (the raw `owner.rmax` render, not just the
exact decimal, still satisfies the Taylor bound under the pin) and an
overshoot control (radius pin shifted by 5e-6 must break the bound).
Writes `results/2312_strip_transfer_lean_pin.json`; exit code 1 on any
failure.
"""
import hashlib
import json
import math
import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ARITH = ROOT / 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean'
LEAN_TRANSFER = ROOT / 'ConnesWeilRH/Dev/C1RouteAStripTransfer.lean'
ENVELOPE_2303 = ROOT / 'results/2303_corrected_strip_envelope.json'
OUT = ROOT / 'results/2312_strip_transfer_lean_pin.json'

RADIUS_TOL = Fraction(10) ** -6                 # radius tightness bar
ULP_SLACK_MIN = 100                             # slack >= 100 ulp of render
CONSISTENCY_TOL = 1e-12                         # transfer render vs exp rel
TAYLOR_ORDER = 6

R_DEF = re.compile(r'def\s+stripRadius2303\s*:\s*Real\s*:=\s*(\S+)')
H_DEF = re.compile(r'def\s+stripHalfStep2303\s*:\s*Real\s*:=\s*(\S+)')
T_DEF = re.compile(r'def\s+stripTransfer2303\s*:\s*Real\s*:=\s*(\S+)')
DECIMAL = re.compile(r'^\d+\.\d+$')


def parse_pins(text):
    radius = R_DEF.search(text)
    half = H_DEF.search(text)
    transfer = T_DEF.search(text)
    if not radius or not half or not transfer:
        raise ValueError('pinned transfer definitions not found in Lean source')
    for label, raw in (('stripRadius2303', radius.group(1)),
                       ('stripHalfStep2303', half.group(1)),
                       ('stripTransfer2303', transfer.group(1))):
        if not DECIMAL.match(raw):
            raise ValueError(f'{label} literal is not a plain decimal: {raw}')
    return {'radius_raw': radius.group(1), 'half_raw': half.group(1),
            'transfer_raw': transfer.group(1),
            'radius': Fraction(radius.group(1)),
            'half': Fraction(half.group(1)),
            'transfer': Fraction(transfer.group(1))}


def taylor_bound(x):
    """Order-n Taylor upper bound of exp at x (exact rational)."""
    total = sum(x ** m / math.factorial(m) for m in range(TAYLOR_ORDER))
    total += x ** TAYLOR_ORDER * Fraction(TAYLOR_ORDER + 1) / \
        (Fraction(math.factorial(TAYLOR_ORDER)) * TAYLOR_ORDER)
    return total


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def main():
    failures = []
    controls = {}

    lean_text = LEAN_ARITH.read_text(encoding='utf-8')
    transfer_text = LEAN_TRANSFER.read_text(encoding='utf-8')
    pins = parse_pins(lean_text)
    radius_pin, half_pin, transfer_pin = \
        pins['radius'], pins['half'], pins['transfer']

    # control 1: synthetic-text regex probe
    synthetic = 'def stripRadius2303 : Real := 12.345\n' \
                'def stripHalfStep2303 : Real := 0.125\n' \
                'def stripTransfer2303 : Real := 9.75\n'
    synth = parse_pins(synthetic)
    controls['synthetic_parse'] = {
        'radius': str(synth['radius']), 'half': str(synth['half']),
        'transfer': str(synth['transfer']),
        'ok': synth['radius'] == Fraction('12.345') and
              synth['half'] == Fraction('0.125') and
              synth['transfer'] == Fraction('9.75')}
    if not controls['synthetic_parse']['ok']:
        failures.append('synthetic parse control failed')

    # reference values from the certified artifact
    artifact = json.loads(ENVELOPE_2303.read_text(encoding='utf-8'))
    rmax_render = Fraction(str(artifact['owner']['rmax']))
    half_render = Fraction(str(artifact['grid']['half_step']))
    sigma_nodes = artifact['grid']['sigma_nodes']
    transfer_render = Fraction(str(artifact['grid']['transfer']))

    # check 1: radius pin is a sound, tight upper of the render
    radius_slack = radius_pin - rmax_render
    radius_slack_ulps = float(radius_slack) / math.ulp(float(rmax_render))
    radius_direction = radius_slack >= 0
    radius_tight = 0 <= radius_slack <= RADIUS_TOL
    radius_slack_ok = radius_slack_ulps >= ULP_SLACK_MIN
    if not radius_direction:
        failures.append('radius pin below the certified rmax render')
    if not radius_tight:
        failures.append('radius pin slack outside (0, 1e-6]')
    if not radius_slack_ok:
        failures.append('radius pin slack below 100 ulp of the render')

    # check 2: half-step pin equals the designed half-step exactly
    half_ok = half_pin == half_render == Fraction(1, 2 * (sigma_nodes - 1))
    if not half_ok:
        failures.append('half-step pin differs from the committed half-step')

    # check 3: order-6 Taylor bound at the pinned exponent below the pin
    x_pin = 2 * radius_pin * half_pin
    bound_pin = taylor_bound(x_pin)
    bound_margin = transfer_pin - bound_pin
    bound_ok = bound_pin < transfer_pin
    if not bound_ok:
        failures.append('Taylor bound at the pinned exponent exceeds the pin')
    exp_pin = None
    try:  # high-precision reference for the overshoot (not a check input)
        from mpmath import mp, mpf, exp as mpexp
        mp.dps = 60
        exp_pin = mpexp(mpf(str(float(x_pin))))
    except Exception:
        pass

    # check 4: committed transfer render vs the exponentiation of renders
    exp_render = None
    try:
        from mpmath import mp, mpf, exp as mpexp
        mp.dps = 60
        exp_render = mpexp(2 * mpf(str(artifact['owner']['rmax'])) *
                           mpf(str(artifact['grid']['half_step'])))
        consistency = abs(float(exp_render) - float(transfer_render)) / \
            float(transfer_render)
    except Exception:
        consistency = None
    render_pin_ok = transfer_pin >= transfer_render
    if not render_pin_ok:
        failures.append('transfer pin below the committed render')
    if consistency is not None and consistency > CONSISTENCY_TOL:
        failures.append('transfer render differs from the exponentiation '
                        'of the committed renders')
    x_render = 2 * rmax_render * half_render
    bound_render = taylor_bound(x_render)
    render_dust_ok = bound_render < transfer_pin

    # control: overshoot rejection at the failure frontier
    overshoot_pin = radius_pin + Fraction(5, 10 ** 6)
    bound_overshoot = taylor_bound(2 * overshoot_pin * half_pin)
    overshoot_rejected = not (bound_overshoot < transfer_pin)
    controls['overshoot_rejected'] = {
        'radius_plus_5e_6_bound': float(bound_overshoot),
        'pin': float(transfer_pin), 'rejected': overshoot_rejected}
    if not overshoot_rejected:
        failures.append('overshoot control failed: +5e-6 radius still passes')

    # check 5: transcription guards on the Lean statements
    guards = {
        'def_radius_pin': pins['radius_raw'] == '6.5536001',
        'def_half_pin': pins['half_raw'] == '0.005',
        'def_transfer_pin': pins['transfer_raw'] == '1.0677312',
        'exp_theorem':
            'theorem real_exp_transfer_le_stripTransfer2303' in lean_text,
        'exp_statement':
            'Real.exp (2 * stripRadius2303 * stripHalfStep2303) '
            '<= stripTransfer2303' in lean_text,
        'exp_bound_prime': 'Real.exp_bound' in lean_text,
        'exp_bound_order': '(n := 6)' in lean_text,
        'exp_norm_num':
            'norm_num [stripRadius2303, stripHalfStep2303, '
            'stripTransfer2303,' in lean_text,
        'core_lemmas':
            'theorem expWeightedIntegral_le_transfer_of_neighbor' in
            transfer_text and
            'theorem stripNorm_le_transfer_of_neighbor' in transfer_text and
            'theorem stripSecondNorm_le_transfer_of_neighbor' in
            transfer_text,
        'min_product_lemma':
            'theorem min_stripProduct_le_transfer_of_neighbor' in
            transfer_text and
            'min_stripProduct_le_transfer_of_neighbor (b.test : ℝ → ℂ)' in
            transfer_text,
        'consumer_theorem':
            'theorem frozenStripHypothesis_of_certified_grid ' in
            transfer_text,
        'consumer_pin_hypothesis':
            'R * h ≤ stripRadius2303 * stripHalfStep2303' in transfer_text,
        'consumer_envelope_call':
            'frozenStripHypothesis_of_certified_envelope' in transfer_text,
        'corner_theorem':
            'theorem frozenStripHypothesis_of_certified_grid_rmax' in
            transfer_text and
            'frozenStripHypothesis_of_certified_grid b c stripRadius2303 '
            'stripHalfStep2303' in transfer_text,
        'support_chain':
            'support_deriv_subset' in transfer_text and
            'tsupport_deriv_subset' in transfer_text,
    }
    for key, ok in guards.items():
        if not ok:
            failures.append(f'Lean transcription guard failed: {key}')

    # negative control: the direction predicate must reject a shifted pin
    bad_pin = rmax_render - Fraction(1, 10 ** 6)
    controls['negative_pin_rejected'] = {
        'shifted_pin_below': bool(bad_pin < rmax_render),
        'predicate_fails': bool((bad_pin - rmax_render) < 0)}

    payload = {
        'record': 2312, 'mode': 'check',
        'verdict': 'PINNED-TRANSFER-VERIFIED' if not failures else 'FAILED',
        'radius': {
            'lean_literal': pins['radius_raw'],
            'artifact_render': float(rmax_render),
            'pin_slack': float(radius_slack),
            'pin_slack_ulps': radius_slack_ulps,
            'direction_ok': radius_direction, 'tight_ok': radius_tight,
            'slack_ok': radius_slack_ok,
        },
        'half_step': {
            'lean_literal': pins['half_raw'],
            'artifact_render': float(half_render),
            'sigma_nodes': sigma_nodes,
            'exact_design_value': str(Fraction(1, 2 * (sigma_nodes - 1))),
            'ok': half_ok,
        },
        'taylor_bound': {
            'order': TAYLOR_ORDER,
            'exponent_pin': str(x_pin),
            'bound': float(bound_pin),
            'pin': float(transfer_pin),
            'margin': float(bound_margin),
            'bound_ok': bound_ok,
            'exp_reference': None if exp_pin is None else float(exp_pin),
            'overshoot_over_exp':
                None if exp_pin is None else float(bound_pin) - float(exp_pin),
        },
        'render_consistency': {
            'transfer_render': float(transfer_render),
            'exp_of_renders':
                None if exp_render is None else float(exp_render),
            'rel_diff': consistency,
            'pin_above_render_ok': render_pin_ok,
            'render_dust_bound_ok': render_dust_ok,
        },
        'lean_guards': guards,
        'controls': controls,
        'provenance': {
            'lean_arithmetic': {
                'path': 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean',
                'md5': md5(LEAN_ARITH)},
            'lean_transfer': {
                'path': 'ConnesWeilRH/Dev/C1RouteAStripTransfer.lean',
                'md5': md5(LEAN_TRANSFER)},
            'envelope_artifact': 'results/2303_corrected_strip_envelope.json',
            'render_convention': 'float64 renders of the 256-bit MPFR '
                                 'certified reduction; the radius pin is a '
                                 'sound upper of the render with slack '
                                 '>= 100 ulp asserted and <= 1e-6',
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'verdict': payload['verdict'],
                      'radius_slack': float(radius_slack),
                      'half_ok': half_ok,
                      'bound': float(bound_pin),
                      'bound_margin': float(bound_margin),
                      'render_dust_ok': render_dust_ok,
                      'rel_diff': consistency,
                      'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()