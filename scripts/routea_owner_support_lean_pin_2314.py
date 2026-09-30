"""Record 2314 pin check: the Lean owner support radius against the
committed owner capture and the strip pins.

The Lean module `ConnesWeilRH/Dev/C1RouteAOwnerSupport.lean` proves that
the corrected width-a^2 owner `correctedPhysical` — the record 2276
family sum over the 30 captured families — has `tsupport` inside
`[-stripRadius2303, stripRadius2303]` for arbitrary coefficient and
modulation vectors, via the exact chain

    bump support  ->  term support  ->  sum support  ->  tsupport
    ->  squared-width bound  a_j^2 <= a_4^2  ->  a_4^2 <= 6.5536001.

This check machine-verifies, in exact rational arithmetic, that

  1. the 30 width literals in the Lean source `C1RouteAOwnerScaleAudit.
     Lean` equal the record 2275 owner capture's family widths
     (`Fraction.from_float (float.fromhex ...)`, bit-exact), and that
     family 4 is the unique strictly largest width, so `a_4^2` is the
     exact owner support radius;
  2. the exact radius `a_4^2` equals the record 2276 artifact's
     `corrected_max_radius_exact`, and its float64 render equals both the
     committed `owner.rmax` in the record 2303 envelope artifact and the
     literal `6.553600000000003` — i.e. the pinned radius used in Lean is
     exactly the radius the record 2303 certification measured;
  3. the pin `stripRadius2303 = 6.5536001` dominates `a_4^2` with exact
     rational slack (recorded in ulps of the pin), and that a decimal pin
     `6.5536` would strictly exclude the true radius;
  4. the record 2312/2313 files are byte-frozen across records (md5
     continuity), and the audit module is frozen since record 2276
     (sha256 continuity against the 2276 price artifact input hashes);
  5. the Lean text carries the expected declarations and proof steps
     (transcription guards), and the probe covers all 12 declarations.

Controls run in the same pass: a synthetic-text regex probe; a unique-max
near-tie rejection; a widened-family rejection (both under the pin
predicate and under the float64 render); and a pin-below-radius
rejection.  Writes `results/2314_owner_support_lean_pin.json`; exit code
1 on any failure.
"""
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_SUPPORT = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerSupport.lean'
LEAN_PROBE = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerSupportProbe.lean'
LEAN_AUDIT = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean'
LEAN_ARITH = ROOT / 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean'
LEAN_GRID = ROOT / 'ConnesWeilRH/Dev/C1RouteAGridSampling.lean'
LEAN_TRANSFER = ROOT / 'ConnesWeilRH/Dev/C1RouteAStripTransfer.lean'
AUDIT_2275 = ROOT / 'results/2275_gap_owner_audit.json'
PRICE_2276 = ROOT / 'results/2276_owner_scale_price.json'
ENVELOPE_2303 = ROOT / 'results/2303_corrected_strip_envelope.json'
PIN_2312 = ROOT / 'results/2312_strip_transfer_lean_pin.json'
PIN_2313 = ROOT / 'results/2313_grid_sampling_lean_pin.json'
OUT = ROOT / 'results/2314_owner_support_lean_pin.json'

ULP_PIN = Fraction(1, 2 ** 50)            # ulp of 6.5536001 (binade [4, 8))
DECIMAL_STRICT = Fraction('6.5536')       # would-be decimal pin, checked to fail
WIDEN = Fraction(1, 10 ** 7)              # control bump above the exact slack

STORED_WIDTHS = re.compile(r'def\s+storedWidth.*?!\[(.*?)\]', re.S)
RADIUS_DEF = re.compile(r'def\s+stripRadius2303\s*:\s*Real\s*:=\s*(\S+)')

AXIOM_DECLS = [
    'widthBump_eq_zero_of_not_lt',
    'ofReal_widthBump_eq_zero_of_not_lt',
    'widthBump_support_subset',
    'familyTerm_support_subset',
    'physicalFamilySum_support_subset',
    'physicalFamilySum_tsupport_subset',
    'storedWidth_nonneg',
    'storedWidth_le_four',
    'storedWidth_sq_le_four',
    'storedWidth_four_sq_le_pin',
    'correctedPhysical_tsupport_subset_four',
    'correctedPhysical_tsupport_subset_pin',
]


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def sha256(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def parse_fraction_literal(lit):
    # same normalization as the record 2276 selftest: strip the wrapping
    # parentheses and spaces, then let Fraction read `num/den` exactly
    return Fraction(lit.strip().strip('()').replace(' ', ''))


def parse_stored_widths(text):
    m = STORED_WIDTHS.search(text)
    if not m:
        raise ValueError('storedWidth literals not found')
    return [parse_fraction_literal(p) for p in m.group(1).split(',')]


def unique_max_index(widths):
    mx = max(widths)
    idx = [i for i, w in enumerate(widths) if w == mx]
    return idx[0] if len(idx) == 1 else None


def pin_ok(widths, pin):
    idx = unique_max_index(widths)
    return idx is not None and widths[idx] ** 2 <= pin


def main():
    failures = []
    controls = {}
    for path in (AUDIT_2275, PRICE_2276, ENVELOPE_2303, PIN_2312, PIN_2313):
        if not path.exists():
            raise FileNotFoundError(f'required artifact missing: {path}')

    support_text = LEAN_SUPPORT.read_text(encoding='utf-8')
    audit_text = LEAN_AUDIT.read_text(encoding='utf-8')
    probe_text = LEAN_PROBE.read_text(encoding='utf-8')

    # 1. width literals: Lean source vs the 2275 owner capture
    widths = parse_stored_widths(audit_text)
    capture = json.loads(AUDIT_2275.read_text(encoding='utf-8'))
    fam = capture['owner_capture']['families_hex']
    cap_widths = [Fraction.from_float(float.fromhex(pair[0])) for pair in fam]
    widths_ok = len(widths) == len(cap_widths) == 30 and widths == cap_widths
    if not widths_ok:
        failures.append('Lean storedWidth literals differ from the owner '
                        'capture family widths')
    max_idx = unique_max_index(widths)
    if max_idx != 4:
        failures.append('family 4 is not the unique strictly largest width')

    # 2. exact radius vs the 2276 artifact and the 2303 render
    a4 = widths[4]
    a4sq = a4 ** 2
    price = json.loads(PRICE_2276.read_text(encoding='utf-8'))
    env = json.loads(ENVELOPE_2303.read_text(encoding='utf-8'))
    legacy_exact = Fraction(price['legacy_max_radius_exact'])
    corrected_exact = Fraction(price['corrected_max_radius_exact'])
    render = env['owner']['rmax']
    radius_ok = (legacy_exact == a4 and corrected_exact == a4sq and
                 float(a4sq) == render == 6.553600000000003 and
                 env['owner']['capture'] == '2275_gap_owner_audit.json')
    if not radius_ok:
        failures.append('exact owner radius differs from the 2276/2303 '
                        'artifacts')

    # 3. the Lean pin dominates the exact radius
    m = RADIUS_DEF.search(LEAN_ARITH.read_text(encoding='utf-8'))
    if not m:
        raise ValueError('stripRadius2303 definition not found')
    pin_literal = m.group(1)
    pin = Fraction(pin_literal)
    slack = pin - a4sq
    pin_dominates = a4sq <= pin and slack > 0
    if not pin_dominates:
        failures.append('stripRadius2303 does not dominate the exact radius')
    if pin != Fraction(65536001, 10 ** 7):
        failures.append('stripRadius2303 literal is not the design pin')

    # 4. cross-record continuity
    pin2312 = json.loads(PIN_2312.read_text(encoding='utf-8'))
    pin2313 = json.loads(PIN_2313.read_text(encoding='utf-8'))
    prov2312 = pin2312.get('provenance', {})
    prov2313 = pin2313.get('provenance', {})
    continuity = {
        'arith_recorded': prov2312.get('lean_arithmetic', {}).get('md5'),
        'arith_live': md5(LEAN_ARITH),
        'transfer_recorded': prov2312.get('lean_transfer', {}).get('md5'),
        'transfer_live': md5(LEAN_TRANSFER),
        'grid_recorded': prov2313.get('lean_grid_sampling', {}).get('md5'),
        'grid_live': md5(LEAN_GRID),
        'audit_sha256_recorded':
            price['input_sha256'].get(
                'ConnesWeilRH/Dev/C1RouteAOwnerScaleAudit.lean'),
        'audit_sha256_live': sha256(LEAN_AUDIT),
    }
    continuity_ok = (
        continuity['arith_recorded'] is not None and
        continuity['arith_recorded'] == continuity['arith_live'] and
        continuity['transfer_recorded'] is not None and
        continuity['transfer_recorded'] == continuity['transfer_live'] and
        continuity['grid_recorded'] is not None and
        continuity['grid_recorded'] == continuity['grid_live'] and
        continuity['audit_sha256_recorded'] is not None and
        continuity['audit_sha256_recorded'] == continuity['audit_sha256_live'])
    if not continuity_ok:
        failures.append('cross-record hash continuity broken')

    # 5. transcription guards on the Lean sources
    w4_num, w4_den = a4.numerator, a4.denominator
    guards = {
        'imports_audit':
            'import ConnesWeilRH.Dev.C1RouteAOwnerScaleAudit' in support_text,
        'imports_arith':
            'import ConnesWeilRH.Dev.C1RouteAItem5Arithmetic' in support_text,
        'no_sorry': 'sorry' not in support_text and
                    'admit' not in support_text,
        'bump_zero':
            'theorem widthBump_eq_zero_of_not_lt (radius position : ℝ)' in
            support_text and 'rw [widthBump, if_neg h]' in support_text,
        'bump_zero_complex':
            'theorem ofReal_widthBump_eq_zero_of_not_lt '
            '(radius position : ℝ)' in support_text and
            'Complex.ofReal_zero' in support_text,
        'bump_support':
            'theorem widthBump_support_subset (radius : ℝ) :' in
            support_text and 'abs_lt.mp hlt' in support_text,
        'term_support':
            'theorem familyTerm_support_subset '
            '(coefficient : ℂ) (modulation radius : ℝ) :' in support_text,
        'sum_support':
            'theorem physicalFamilySum_support_subset '
            '(coefficients : Fin 30 → ℂ)' in support_text and
            'Finset.sum_eq_zero' in support_text,
        'sum_tsupport':
            'theorem physicalFamilySum_tsupport_subset '
            '(coefficients : Fin 30 → ℂ)' in support_text and
            'isClosed_Icc.closure_subset_iff.mpr' in support_text,
        'width_nonneg':
            'theorem storedWidth_nonneg (index : Fin 30) : '
            '0 ≤ storedWidth index := by' in support_text,
        'width_le_four':
            'theorem storedWidth_le_four (index : Fin 30) :' in
            support_text and
            f'change storedWidth index ≤ ({w4_num} / {w4_den} : ℝ)' in
            support_text,
        'width_sq_le_four':
            'theorem storedWidth_sq_le_four (index : Fin 30) :' in
            support_text and
            'pow_le_pow_left₀ (storedWidth_nonneg index) '
            '(storedWidth_le_four index) 2' in support_text,
        'pin_theorem':
            'theorem storedWidth_four_sq_le_pin :' in support_text and
            f'storedWidth 4 ^ 2 ≤ stripRadius2303' in support_text and
            f'change ({w4_num} / {w4_den} : ℝ) ^ 2 ≤ '
            f'({pin_literal} : ℝ)' in support_text,
        'owner_four':
            'theorem correctedPhysical_tsupport_subset_four '
            '(coefficients : Fin 30 → ℂ)' in support_text and
            'change tsupport' in support_text and
            '(fun index => storedWidth index ^ 2)' in support_text,
        'owner_pin':
            'theorem correctedPhysical_tsupport_subset_pin '
            '(coefficients : Fin 30 → ℂ)' in support_text and
            'Set.Icc_subset_Icc (neg_le_neg storedWidth_four_sq_le_pin)' in
            support_text,
        'probe_axioms':
            all(f'#print axioms {name}' in probe_text
                for name in AXIOM_DECLS),
    }
    for key, ok in guards.items():
        if not ok:
            failures.append(f'Lean transcription guard failed: {key}')

    # controls
    synthetic = (r'def storedWidth : Fin 3 → ℝ := ![1 / 2, 3 / 4, 5 / 4]')
    synth_parsed = parse_stored_widths(synthetic)
    controls['synthetic_parse'] = {
        'parsed': [str(w) for w in synth_parsed],
        'ok': synth_parsed == [Fraction(1, 2), Fraction(3, 4),
                               Fraction(5, 4)]}
    if not controls['synthetic_parse']['ok']:
        failures.append('synthetic parse control failed')

    tie = list(widths)
    tie[6] = widths[4]
    widened = list(widths)
    widened[4] = widths[4] + WIDEN
    controls['predicates'] = {
        'accepts_design': pin_ok(widths, pin),
        'rejects_tie': unique_max_index(tie) != 4 and not pin_ok(tie, pin),
        'rejects_widened': not pin_ok(widened, pin),
        'rejects_low_pin': not pin_ok(widths, a4sq - Fraction(1, 10 ** 8)),
    }
    controls['predicates']['ok'] = all(
        controls['predicates'][k] for k in
        ('accepts_design', 'rejects_tie', 'rejects_widened',
         'rejects_low_pin'))
    if not controls['predicates']['ok']:
        failures.append('width/pin predicate controls failed')

    controls['render_and_decimal'] = {
        'rejects_widened_render': float(widened[4] ** 2) != render,
        'decimal_pin_6p5536_excludes': a4sq > DECIMAL_STRICT,
        'ok': float(widened[4] ** 2) != render and a4sq > DECIMAL_STRICT}
    if not controls['render_and_decimal']['ok']:
        failures.append('render/decimal controls failed')

    payload = {
        'record': 2314, 'mode': 'check',
        'verdict': ('PINNED-OWNER-SUPPORT-VERIFIED' if not failures
                    else 'FAILED'),
        'widths': {
            'lean_count': len(widths), 'capture_count': len(cap_widths),
            'lean_equals_capture': widths_ok,
            'unique_max_index': max_idx,
            'a4_exact': str(a4),
            'a4sq_exact': str(a4sq),
            'a4sq_render': float(a4sq),
        },
        'radius_vs_pin': {
            'lean_pin_literal': pin_literal,
            'pin_exact': str(pin),
            'pin_render': float(pin),
            'a4sq_le_pin': a4sq <= pin,
            'slack_exact': str(slack),
            'slack_float': float(slack),
            'slack_in_pin_ulps': float(slack / ULP_PIN),
            'design_pin_ok': pin == Fraction(65536001, 10 ** 7),
        },
        'artifact_agreement': {
            'legacy_max_radius_exact': str(legacy_exact),
            'corrected_max_radius_exact': str(corrected_exact),
            'envelope_owner_rmax': render,
            'ok': radius_ok,
        },
        'continuity': {**continuity, 'ok': continuity_ok},
        'lean_guards': guards,
        'controls': controls,
        'provenance': {
            'lean_support': {
                'path': 'ConnesWeilRH/Dev/C1RouteAOwnerSupport.lean',
                'md5': md5(LEAN_SUPPORT)},
            'lean_probe': {
                'path': 'ConnesWeilRH/Dev/C1RouteAOwnerSupportProbe.lean',
                'md5': md5(LEAN_PROBE)},
            'audit_sha256': sha256(LEAN_AUDIT),
            'inputs': ['results/2275_gap_owner_audit.json',
                       'results/2276_owner_scale_price.json',
                       'results/2303_corrected_strip_envelope.json',
                       'results/2312_strip_transfer_lean_pin.json',
                       'results/2313_grid_sampling_lean_pin.json'],
            'render_convention': 'float64 renders of exact rationals; '
                                 'capture widths via Fraction.from_float '
                                 '(float.fromhex ...) are bit-exact',
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'verdict': payload['verdict'],
                      'a4sq_exact': str(a4sq),
                      'a4sq_render': float(a4sq),
                      'pin_dominates': pin_dominates,
                      'slack_float': float(slack),
                      'slack_ulps': float(slack / ULP_PIN),
                      'continuity_ok': continuity_ok,
                      'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()