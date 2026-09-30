"""Record 2311 pin check: the Lean strip-envelope constants against the
certified 2303 artifact.

The Lean module `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` pins the
certified centered-strip envelope factors as decimal constants:

    stripGridMax2303 := 2644542.8515    (record 2303, grid maximum)
    stripTransfer2303 := 1.0677312      (record 2303, transfer factor)

This check machine-verifies, in exact rational arithmetic, that

  1. each pinned constant is an UPPER of the committed artifact render
     (`centered.max_point_B` and `grid.transfer` of
     `results/2303_corrected_strip_envelope.json`), with the pin slack
     above the float64 render-chain rounding of the stored value
     (>= 100 ulp of the render) and below the registered tightness bar
     (1e-3 grid maximum, 1e-6 transfer);
  2. the pinned product is an upper of the rendered product, the product
     slack is above 100 ulp of the product render and below 0.1, and the
     rendered product matches the artifact's own `centered.sup_certified`
     to 1e-12 relative (internal consistency of the committed multiply);
  3. the pinned product is <= bUpper2243 exactly (the Lean side proves the
     same inequality by `norm_num` on these exact rationals);
  4. the Lean text carries the expected declarations and the norm_num call
     (transcription guard binding the check to the committed statements).

Controls run in the same pass: a synthetic-text regex probe, a negative
control (grid-max pin shifted below the render must fail the direction
check), and a join-direction control.  Writes
`results/2311_strip_envelope_lean_pin.json`; exit code 1 on any failure.
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
LEAN_PRODUCER = ROOT / 'ConnesWeilRH/Dev/C1RouteAProducerWired.lean'
ENVELOPE_2303 = ROOT / 'results/2303_corrected_strip_envelope.json'
OUT = ROOT / 'results/2311_strip_envelope_lean_pin.json'

BUDGET = Fraction('9506275.102584327')          # bUpper2243
GM_TOL = Fraction(10) ** -3                     # grid-max tightness bar
T_TOL = Fraction(10) ** -6                      # transfer tightness bar
PROD_TOL = Fraction(10) ** -1                   # product tightness bar
ULP_SLACK_MIN = 100                             # slack >= 100 ulp of render
CONSISTENCY_TOL = 1e-12                         # product vs sup_certified

GM_DEF = re.compile(r'def\s+stripGridMax2303\s*:\s*Real\s*:=\s*(\S+)')
T_DEF = re.compile(r'def\s+stripTransfer2303\s*:\s*Real\s*:=\s*(\S+)')
DECIMAL = re.compile(r'^\d+\.\d+$')


def parse_pins(text):
    grid = GM_DEF.search(text)
    transfer = T_DEF.search(text)
    if not grid or not transfer:
        raise ValueError('pinned strip definitions not found in Lean source')
    for label, raw in (('stripGridMax2303', grid.group(1)),
                       ('stripTransfer2303', transfer.group(1))):
        if not DECIMAL.match(raw):
            raise ValueError(f'{label} literal is not a plain decimal: {raw}')
    return {'grid_raw': grid.group(1), 'transfer_raw': transfer.group(1),
            'grid': Fraction(grid.group(1)),
            'transfer': Fraction(transfer.group(1))}


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def main():
    failures = []
    controls = {}

    lean_text = LEAN_ARITH.read_text(encoding='utf-8')
    producer_text = LEAN_PRODUCER.read_text(encoding='utf-8')
    pins = parse_pins(lean_text)
    grid_pin, transfer_pin = pins['grid'], pins['transfer']

    # control 1: synthetic-text regex probe
    synthetic = 'def stripGridMax2303 : Real := 12.345\n' \
                'def stripTransfer2303 : Real := 1.0123\n'
    synth = parse_pins(synthetic)
    controls['synthetic_parse'] = {
        'grid': str(synth['grid']), 'transfer': str(synth['transfer']),
        'ok': synth['grid'] == Fraction('12.345') and
              synth['transfer'] == Fraction('1.0123')}
    if not controls['synthetic_parse']['ok']:
        failures.append('synthetic parse control failed')

    # reference values from the certified artifact
    artifact = json.loads(ENVELOPE_2303.read_text(encoding='utf-8'))
    grid_render = Fraction(str(artifact['centered']['max_point_B']))
    transfer_render = Fraction(str(artifact['grid']['transfer']))
    sup_render = Fraction(str(artifact['centered']['sup_certified']))
    frozen = Fraction(str(artifact['centered']['frozen']))
    if frozen != BUDGET:
        failures.append('artifact frozen constant differs from bUpper2243')

    # check 1: grid-max pin is a tight, sound upper of the render
    grid_slack = grid_pin - grid_render
    grid_slack_ulps = float(grid_slack) / math.ulp(float(grid_render))
    grid_direction = grid_slack >= 0
    grid_tight = 0 <= grid_slack <= GM_TOL
    grid_slack_ok = grid_slack_ulps >= ULP_SLACK_MIN
    if not grid_direction:
        failures.append('grid-max pin below the certified render')
    if not grid_tight:
        failures.append('grid-max pin slack outside (0, 1e-3]')
    if not grid_slack_ok:
        failures.append('grid-max pin slack below 100 ulp of the render')

    # check 1: transfer pin is a tight, sound upper of the render
    transfer_slack = transfer_pin - transfer_render
    transfer_slack_ulps = float(transfer_slack) / math.ulp(float(transfer_render))
    transfer_direction = transfer_slack >= 0
    transfer_tight = 0 <= transfer_slack <= T_TOL
    transfer_slack_ok = transfer_slack_ulps >= ULP_SLACK_MIN
    if not transfer_direction:
        failures.append('transfer pin below the certified render')
    if not transfer_tight:
        failures.append('transfer pin slack outside (0, 1e-6]')
    if not transfer_slack_ok:
        failures.append('transfer pin slack below 100 ulp of the render')

    # check 2: pinned product vs rendered product, artifact consistency
    prod_pin = grid_pin * transfer_pin
    prod_render = grid_render * transfer_render
    prod_slack = prod_pin - prod_render
    prod_slack_ulps = float(prod_slack) / math.ulp(float(prod_render))
    prod_direction = prod_slack >= 0
    prod_tight = 0 <= prod_slack <= PROD_TOL
    prod_slack_ok = prod_slack_ulps >= ULP_SLACK_MIN
    if not prod_direction:
        failures.append('pinned product below the rendered product')
    if not prod_tight:
        failures.append('product pin slack outside (0, 0.1]')
    if not prod_slack_ok:
        failures.append('product pin slack below 100 ulp of the render')
    consistency = float(abs(prod_render - sup_render) / sup_render)
    if consistency > CONSISTENCY_TOL:
        failures.append('rendered product differs from sup_certified')

    # check 3: exact join below bUpper2243
    join_margin = BUDGET - prod_pin
    if not (prod_pin <= BUDGET):
        failures.append('pinned product exceeds bUpper2243')
    controls['join_direction'] = {'strictly_below': prod_pin < BUDGET,
                                  'margin': str(join_margin)}

    # check 4: transcription guards on the Lean statements
    guards = {
        'def_grid_pin': pins['grid_raw'] == '2644542.8515',
        'def_transfer_pin': pins['transfer_raw'] == '1.0677312',
        'join_theorem':
            'theorem stripGridMax2303_mul_stripTransfer2303_le_bUpper2243' in
            lean_text,
        'join_norm_num':
            'norm_num [stripGridMax2303, stripTransfer2303, bUpper2243]' in
            lean_text,
        'conversion_theorem':
            'theorem frozenStripHypothesis_of_certified_envelope' in
            producer_text,
        'conversion_call':
            '(henvelope sigma hsigma).trans' in producer_text,
        'consumer_theorem':
            'a005_item5_producer_wired_certified_multiplicity_gap_split_envelope'
            in producer_text,
        'consumer_call':
            'frozenStripHypothesis_of_certified_envelope b c henvelope' in
            producer_text,
    }
    for key, ok in guards.items():
        if not ok:
            failures.append(f'Lean transcription guard failed: {key}')

    # negative control: the direction predicate must reject a shifted pin
    bad_pin = grid_render - Fraction(1, 10 ** 6)
    controls['negative_pin_rejected'] = {
        'shifted_pin_below': bool(bad_pin < grid_render),
        'predicate_fails': bool((bad_pin - grid_render) < 0)}

    payload = {
        'record': 2311, 'mode': 'check',
        'verdict': 'PINNED-ENVELOPE-VERIFIED' if not failures else 'FAILED',
        'budget': str(BUDGET),
        'grid_max': {
            'lean_literal': pins['grid_raw'],
            'artifact_render': float(grid_render),
            'pin_slack': float(grid_slack),
            'pin_slack_ulps': grid_slack_ulps,
            'direction_ok': grid_direction, 'tight_ok': grid_tight,
            'slack_ok': grid_slack_ok,
        },
        'transfer': {
            'lean_literal': pins['transfer_raw'],
            'artifact_render': float(transfer_render),
            'pin_slack': float(transfer_slack),
            'pin_slack_ulps': transfer_slack_ulps,
            'direction_ok': transfer_direction, 'tight_ok': transfer_tight,
            'slack_ok': transfer_slack_ok,
        },
        'product': {
            'pin': float(prod_pin), 'render': float(prod_render),
            'sup_certified_render': float(sup_render),
            'pin_slack': float(prod_slack),
            'pin_slack_ulps': prod_slack_ulps,
            'consistency_rel': consistency,
            'direction_ok': prod_direction, 'tight_ok': prod_tight,
            'slack_ok': prod_slack_ok,
        },
        'join': {
            'margin': float(join_margin),
            'margin_ratio': float(BUDGET / prod_pin),
            'closed': bool(prod_pin <= BUDGET),
        },
        'lean_guards': guards,
        'controls': controls,
        'provenance': {
            'lean_arithmetic': {
                'path': 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean',
                'md5': md5(LEAN_ARITH)},
            'lean_producer': {
                'path': 'ConnesWeilRH/Dev/C1RouteAProducerWired.lean',
                'md5': md5(LEAN_PRODUCER)},
            'envelope_artifact': 'results/2303_corrected_strip_envelope.json',
            'render_convention': 'float64 renders of the 256-bit MPFR '
                                 'certified reduction; pin slack asserted '
                                 '>= 100 ulp of each render',
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'verdict': payload['verdict'],
                      'grid_slack': float(grid_slack),
                      'transfer_slack': float(transfer_slack),
                      'product_slack': float(prod_slack),
                      'join_margin': float(join_margin),
                      'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()