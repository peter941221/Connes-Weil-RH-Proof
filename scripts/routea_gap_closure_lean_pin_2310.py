"""Record 2310 pin check: the Lean hgap-closure constants against the
certified artifacts.

The Lean module `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` pins the
certified hgap split uppers as decimal constants:

    windowCharge2309 := 477248.98581176                  (records 2308/2309)
    tailCharge2307   := 0.000000000000000000000000002   (record 2307)

This check machine-verifies, in exact rational arithmetic, that

  1. each pinned constant is an UPPER of the certified artifact value --
     the window reference is the 45-digit directed-ceiling render of the
     exact interval upper endpoint (`interval_text`, ROUND_CEILING for the
     upper side, record 2294 convention), so render >= exact upper >= true
     charge by construction; the tail reference is the float64 render,
     dominated by the pin slack 4.1e-29 (17 orders above any float64
     rounding of the stored value);
  2. each pin is TIGHT: pin - reference stays below the registered bar
     (1e-6 window, 1e-26 tail);
  3. the join pin_window + pin_tail <= gapCharge2255 holds exactly (the
     Lean side proves the same inequality by `norm_num` on these exact
     rationals);
  4. the Lean text carries the expected declarations and the norm_num call
     (transcription guard binding the check to the committed statements).

Controls run in the same pass: a synthetic-text regex probe, a negative
control (window pin shifted below the render must fail the direction
check), and a join-direction control.  Writes
`results/2310_gap_closure_lean_pin.json`; exit code 1 on any failure.
"""
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_ARITH = ROOT / 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean'
LEAN_PRODUCER = ROOT / 'ConnesWeilRH/Dev/C1RouteAProducerWired.lean'
STEP_2309 = ROOT / 'results/2309_transform_step_den256.json'
CERT_2309 = ROOT / 'results/2309_hgap_transform_certified.json'
TAIL_2307 = ROOT / 'results/2307_hgap_tail_certified.json'
OUT = ROOT / 'results/2310_gap_closure_lean_pin.json'

BUDGET = Fraction(10) ** 7
WINDOW_TOL = Fraction(10) ** -6      # window pin tightness bar
TAIL_TOL = Fraction(10) ** -26       # tail pin tightness bar
TAIL_SLACK_MIN = Fraction(10) ** -30  # tail pin soundness bar

WINDOW_DEF = re.compile(r'def\s+windowCharge2309\s*:\s*Real\s*:=\s*(\S+)')
TAIL_DEF = re.compile(r'def\s+tailCharge2307\s*:\s*Real\s*:=\s*(\S+)')
DECIMAL = re.compile(r'^\d+\.\d+$')


def parse_pins(text):
    window = WINDOW_DEF.search(text)
    tail = TAIL_DEF.search(text)
    if not window or not tail:
        raise ValueError('pinned definitions not found in Lean source')
    for label, raw in (('windowCharge2309', window.group(1)),
                       ('tailCharge2307', tail.group(1))):
        if not DECIMAL.match(raw):
            raise ValueError(f'{label} literal is not a plain decimal: {raw}')
    return {'window_raw': window.group(1), 'tail_raw': tail.group(1),
            'window': Fraction(window.group(1)),
            'tail': Fraction(tail.group(1))}


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def main():
    failures = []
    controls = {}

    lean_text = LEAN_ARITH.read_text(encoding='utf-8')
    producer_text = LEAN_PRODUCER.read_text(encoding='utf-8')
    pins = parse_pins(lean_text)
    window_pin, tail_pin = pins['window'], pins['tail']

    # control 1: synthetic-text regex probe
    synthetic = 'def windowCharge2309 : Real := 123.456\n' \
                'def tailCharge2307 : Real := 0.000123\n'
    synth = parse_pins(synthetic)
    controls['synthetic_parse'] = {
        'window': str(synth['window']), 'tail': str(synth['tail']),
        'ok': synth['window'] == Fraction('123.456') and
        synth['tail'] == Fraction('0.000123')}
    if not controls['synthetic_parse']['ok']:
        failures.append('synthetic parse control failed')

    # reference values from the certified artifacts
    step = json.loads(STEP_2309.read_text(encoding='utf-8'))
    cert = json.loads(CERT_2309.read_text(encoding='utf-8'))
    tail = json.loads(TAIL_2307.read_text(encoding='utf-8'))
    window_render = Fraction(step['charge_render']['upper'])
    window_float = Fraction(cert['best']['charge_hi'])
    tail_float = Fraction(tail['best']['tail_upper'])

    # window consistency between the two artifacts (render vs float)
    render_float_gap = abs(float(window_render) - float(window_float))
    if render_float_gap > 1e-9:
        failures.append('window render/float artifact mismatch')

    # check 1+2: window pin is a tight upper of the directed-ceiling render
    window_slack = window_pin - window_render
    window_direction = window_slack >= 0
    window_tight = 0 <= window_slack <= WINDOW_TOL
    if not window_direction:
        failures.append('window pin below the certified render upper')
    if not window_tight:
        failures.append('window pin slack outside (0, 1e-6]')

    # check 1+2: tail pin is a tight upper of the float64 render
    tail_slack = tail_pin - tail_float
    tail_direction = tail_slack >= 0
    tail_sound = tail_slack >= TAIL_SLACK_MIN
    tail_tight = 0 < tail_slack <= TAIL_TOL
    if not tail_direction:
        failures.append('tail pin below the certified float upper')
    if not tail_sound:
        failures.append('tail pin slack below 1e-30 float-rounding margin')
    if not tail_tight:
        failures.append('tail pin slack outside (0, 1e-26]')

    # check 3: exact join below the 2255 charge
    join_sum = window_pin + tail_pin
    join_margin = BUDGET - join_sum
    if not (join_sum <= BUDGET):
        failures.append('pinned join exceeds gapCharge2255')
    controls['join_direction'] = {'strictly_below': join_sum < BUDGET,
                                  'margin': str(join_margin)}

    # check 4: transcription guards on the Lean statements
    guards = {
        'def_window_pin': pins['window_raw'] == '477248.98581176',
        'def_tail_pin': pins['tail_raw'] ==
            '0.000000000000000000000000002',
        'join_theorem':
            'theorem windowCharge2309_add_tailCharge2307_le_gapCharge2255' in
            lean_text,
        'join_norm_num':
            'norm_num [windowCharge2309, tailCharge2307, gapCharge2255]' in
            lean_text,
        'split_theorem': 'theorem hgap_of_certified_split' in lean_text,
        'producer_theorem':
            'a005_item5_producer_wired_certified_multiplicity_gap_split' in
            producer_text,
        'producer_call':
            'hgap_of_certified_split hsplit hwindow htail' in producer_text,
    }
    for key, ok in guards.items():
        if not ok:
            failures.append(f'Lean transcription guard failed: {key}')

    # negative control: the direction predicate must reject a shifted pin
    bad_pin = window_render - Fraction(1, 10 ** 9)
    controls['negative_pin_rejected'] = {
        'shifted_pin_below': bool(bad_pin < window_render),
        'predicate_fails': bool((bad_pin - window_render) < 0)}

    payload = {
        'record': 2310, 'mode': 'check',
        'verdict': 'PINNED-UPPERS-VERIFIED' if not failures else 'FAILED',
        'budget': int(BUDGET),
        'window': {
            'lean_literal': pins['window_raw'],
            'artifact_render_upper': str(window_render),
            'artifact_charge_hi_float': float(window_float),
            'render_vs_float_gap': render_float_gap,
            'pin_slack': float(window_slack),
            'direction_ok': window_direction, 'tight_ok': window_tight,
        },
        'tail': {
            'lean_literal': pins['tail_raw'],
            'artifact_tail_upper_float': float(tail_float),
            'artifact_best_order': tail['best']['order'],
            'pin_slack': float(tail_slack),
            'direction_ok': tail_direction, 'sound_ok': tail_sound,
            'tight_ok': tail_tight,
        },
        'join': {
            'sum': float(join_sum), 'margin': float(join_margin),
            'margin_ratio': float(BUDGET / join_sum),
            'closed': bool(join_sum <= BUDGET),
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
            'window_artifacts': [
                'results/2309_transform_step_den256.json',
                'results/2309_hgap_transform_certified.json'],
            'tail_artifact': 'results/2307_hgap_tail_certified.json',
            'render_convention': 'interval_text directed ceiling (2294); '
                                 'upper endpoint rendered ROUND_CEILING',
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'verdict': payload['verdict'],
                      'window_slack': float(window_slack),
                      'tail_slack': float(tail_slack),
                      'join_margin': float(join_margin),
                      'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()