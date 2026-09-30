"""Record 2315 pin check: the packaged corrected owner as a
`CompactLogTest` against the committed owner radius and the 2314 module.

The Lean module `ConnesWeilRH/Dev/C1RouteAOwnerTest.lean` proves that the
corrected width-a^2 owner `correctedPhysical` is smooth and compactly
supported for arbitrary coefficient and modulation vectors, by the
flat-junction identity

    widthBump radius x = expNegInvGlue ((1 - (x / radius)^2) / 30)
      (0 < radius),

and packages it as a `CompactLogTest`, with the support bound in exactly
the hypothesis shape of the record 2313 node consumer.

This check machine-verifies:

  1. the record 2314 module is byte-frozen (its live md5 equals the md5
     recorded in the 2314 pin artifact provenance);
  2. the `CompactLogTest` structure still has the two fields the
     packaging must supply (`test : TestFunction`, `compactSupport :
     HasCompactSupport test`), and records a live md5 anchor for the
     definition file;
  3. the Lean text carries the expected declarations and proof steps
     (transcription guards), does NOT fall back to `Real.smoothTransition`
     (the logistic transition is a different function; the flat-junction
     base must be `expNegInvGlue`), and the packaged-definition
     parameters stay free (`coefficients`, `modulations`);
  4. the sampled identity witness at dps 70 over interior, boundary and
     exterior points of the exact owner radius a_4^2 (from the record
     2276 artifact): the two implemented branches agree to < 1e-50,
     vanish exactly at |x| >= radius, and are strictly positive inside;
  5. the witness predicates REJECT wrong pairings: an argument offset
     and a halved radius both change the sampled values measurably.

Controls run in the same pass; the identity witness is a sampled
sanity check, the Lean theorem is the proof.  Writes
`results/2315_owner_test_lean_pin.json`; exit code 1 on any failure.
"""
import hashlib
import json
import sys
from fractions import Fraction
from pathlib import Path

from mpmath import mp

ROOT = Path(__file__).resolve().parents[1]
LEAN_TEST = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerTest.lean'
LEAN_PROBE = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerTestProbe.lean'
LEAN_SUPPORT = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerSupport.lean'
LEAN_CLT = ROOT / 'ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean'
PRICE_2276 = ROOT / 'results/2276_owner_scale_price.json'
PIN_2314 = ROOT / 'results/2314_owner_support_lean_pin.json'
OUT = ROOT / 'results/2315_owner_test_lean_pin.json'

DPS = 70
TOL = mp.mpf('1e-50')                 # sampled branch-agreement tolerance
CTRL_MIN_DIFF = mp.mpf('1e-20')       # wrong pairings must exceed this

DECLS = [
    'widthBump_eq_expNegInvGlue',
    'widthBump_contDiff',
    'familyTerm_contDiff',
    'physicalFamilySum_contDiff',
    'physicalFamilySum_hasCompactSupport',
    'storedWidth_pos',
    'correctedPhysical_contDiff',
    'correctedPhysical_hasCompactSupport',
    'correctedPhysicalCompactLogTest',
    'correctedPhysicalCompactLogTest_toFun',
    'correctedPhysicalCompactLogTest_tsupport_subset',
    'correctedPhysicalCompactLogTest_compactSupport',
]


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def width_bump(r, x):
    """The audit implementation: if |x| < r then exp (-30 / (1 - (x/r)^2))
    else 0."""
    if abs(x) < r:
        return mp.exp(-30 / (1 - (x / r) ** 2))
    return mp.mpf(0)


def exp_neg_inv_glue(t):
    """Mathlib's expNegInvGlue: if t <= 0 then 0 else exp (-t^-1)."""
    if t <= 0:
        return mp.mpf(0)
    return mp.exp(-1 / t)


def main():
    failures = []
    controls = {}
    py = ROOT / 'scripts/routea_owner_test_lean_pin_2315.py'
    for path in (PRICE_2276, PIN_2314):
        if not path.exists():
            raise FileNotFoundError(f'required artifact missing: {path}')

    test_text = LEAN_TEST.read_text(encoding='utf-8')
    probe_text = LEAN_PROBE.read_text(encoding='utf-8')
    clt_text = LEAN_CLT.read_text(encoding='utf-8')

    # 1. record 2314 module byte-frozen
    pin2314 = json.loads(PIN_2314.read_text(encoding='utf-8'))
    support_recorded = pin2314.get('provenance', {}).get(
        'lean_support', {}).get('md5')
    continuity = {
        'support_recorded': support_recorded,
        'support_live': md5(LEAN_SUPPORT),
    }
    continuity_ok = (support_recorded is not None and
                     support_recorded == continuity['support_live'])
    if not continuity_ok:
        failures.append('record 2314 module changed since its pin artifact')

    # 2. CompactLogTest shape
    shape = {
        'structure': 'structure CompactLogTest where' in clt_text,
        'test_field': 'test : TestFunction' in clt_text,
        'compact_field': 'compactSupport : HasCompactSupport test' in clt_text,
    }
    shape_ok = all(shape.values())
    if not shape_ok:
        failures.append('CompactLogTest shape differs from the packaging '
                        'contract')

    # 3. transcription guards
    guards = {
        'imports_support':
            'import ConnesWeilRH.Dev.C1RouteAOwnerSupport' in test_text,
        'imports_clt':
            'import ConnesWeilRH.Source.CCM25Concrete.CompactLogConvolution'
            in test_text,
        'imports_glue':
            'import Mathlib.Analysis.SpecialFunctions.SmoothTransition'
            in test_text,
        'no_sorry': 'sorry' not in test_text and 'admit' not in test_text,
        'base_is_glue_not_transition':
            'expNegInvGlue' in test_text and
            'Real.smoothTransition' not in test_text,
        'identity_theorem':
            'theorem widthBump_eq_expNegInvGlue (radius : ℝ) '
            '(hr : 0 < radius) :' in test_text,
        'identity_argument':
            'expNegInvGlue ((1 - (x / radius) ^ 2) / 30)' in test_text,
        'identity_algebra':
            'rw [inv_div, neg_div]' in test_text and
            'expNegInvGlue.zero_of_nonpos' in test_text,
        'bump_contDiff':
            'expNegInvGlue.contDiff.comp' in test_text and
            'funext (widthBump_eq_expNegInvGlue radius hr)' in test_text,
        'term_contDiff':
            'Complex.ofRealCLM.contDiff.comp' in test_text and
            'Complex.contDiff_exp.comp' in test_text,
        'sum_contDiff':
            'ContDiff.sum (fun index _ => familyTerm_contDiff' in test_text,
        'sum_compact':
            'IsCompact.of_isClosed_subset isCompact_Icc '
            '(isClosed_tsupport _)' in test_text,
        'width_pos':
            'theorem storedWidth_pos (index : Fin 30) : '
            '0 < storedWidth index := by' in test_text and
            'fin_cases index <;> norm_num [storedWidth]' in test_text,
        'owner_contDiff_change':
            'change ContDiff ℝ ∞ (physicalFamilySum coefficients '
            'modulations' in test_text and
            'pow_pos (storedWidth_pos index) 2' in test_text,
        'packaging':
            'HasCompactSupport.toSchwartzMap' in test_text and
            'noncomputable def correctedPhysicalCompactLogTest' in test_text,
        'packaging_params':
            '(coefficients : Fin 30 → ℂ) (modulations : Fin 30 → ℝ) :'
            in test_text,
        'toFun':
            'HasCompactSupport.toSchwartzMap_toFun' in test_text and
            'funext x' in test_text,
        'tsupport_shape':
            'theorem correctedPhysicalCompactLogTest_tsupport_subset'
            in test_text and
            'rw [correctedPhysicalCompactLogTest_toFun]' in test_text and
            'Set.Icc (-stripRadius2303) stripRadius2303' in test_text,
        'probe_axioms':
            all(f'#print axioms {name}' in probe_text for name in DECLS),
    }
    for key, ok in guards.items():
        if not ok:
            failures.append(f'Lean transcription guard failed: {key}')

    # 4. sampled identity witness at the exact owner radius
    mp.dps = DPS
    price = json.loads(PRICE_2276.read_text(encoding='utf-8'))
    a4sq = Fraction(price['corrected_max_radius_exact'])
    r = mp.mpf(a4sq.numerator) / mp.mpf(a4sq.denominator)
    eps = mp.mpf('1e-9')
    off = mp.mpf('1e-6')
    xs = [mp.mpf(v) for v in
          ['-40', '-8', '-3.14159265358979', '-1', '-0.25', '0', '0.25',
           '1', '3.14159265358979', '8', '40']]
    xs.extend([-(r - eps), -r, -(r + off), r - eps, r, r + off])
    max_diff = mp.mpf(0)
    outside_zero_ok = True
    inside_pos_ok = True
    boundary_count = 0
    interior_count = 0
    for x in xs:
        lhs = width_bump(r, x)
        rhs = exp_neg_inv_glue((1 - (x / r) ** 2) / 30)
        max_diff = max(max_diff, abs(lhs - rhs))
        if abs(x) < r:
            interior_count += 1
            if not lhs > 0:
                inside_pos_ok = False
        else:
            boundary_count += 1
            if not (lhs == 0 and rhs == 0):
                outside_zero_ok = False
    # design sample split: 9 interior points, 8 boundary/outside points;
    # exact counts so a silent sample-list edit fails the check
    witness_ok = (max_diff < TOL and outside_zero_ok and inside_pos_ok and
                  interior_count == 9 and boundary_count == 8)
    if not witness_ok:
        failures.append('sampled identity witness failed')

    # 5. wrong pairings must be rejected
    off_shift = mp.mpf(1) / 50
    max_diff_offset = mp.mpf(0)
    max_diff_half_radius = mp.mpf(0)
    rhalf = r / 2
    for x in xs:
        if not abs(x) < r:
            continue
        lhs = width_bump(r, x)
        u = 1 - (x / r) ** 2
        wrong_arg = exp_neg_inv_glue(u / 30 - off_shift)
        wrong_radius = exp_neg_inv_glue((1 - (x / rhalf) ** 2) / 30)
        max_diff_offset = max(max_diff_offset, abs(lhs - wrong_arg))
        max_diff_half_radius = max(max_diff_half_radius,
                                   abs(lhs - wrong_radius))
    controls['wrong_pairings'] = {
        'rejects_argument_offset':
            max_diff_offset > CTRL_MIN_DIFF,
        'rejects_halved_radius':
            max_diff_half_radius > CTRL_MIN_DIFF,
        'max_diff_argument_offset': mp.nstr(max_diff_offset, 8),
        'max_diff_halved_radius': mp.nstr(max_diff_half_radius, 8)}
    controls['wrong_pairings']['ok'] = all(
        controls['wrong_pairings'][k] for k in
        ('rejects_argument_offset', 'rejects_halved_radius'))
    if not controls['wrong_pairings']['ok']:
        failures.append('wrong-pairing controls failed')

    dip = width_bump(r, mp.mpf(0))

    payload = {
        'record': 2315, 'mode': 'check',
        'verdict': ('PINNED-OWNER-TEST-VERIFIED' if not failures
                    else 'FAILED'),
        'continuity': {**continuity, 'ok': continuity_ok},
        'compact_log_test_shape': {**shape, 'ok': shape_ok,
                                   'md5': md5(LEAN_CLT)},
        'identity_witness': {
            'dps': DPS,
            'radius_source': str(a4sq),
            'samples': len(xs),
            'interior': interior_count,
            'boundary_or_outside': boundary_count,
            'max_branch_diff': mp.nstr(max_diff, 8),
            'tolerance': mp.nstr(TOL, 4),
            'outside_exact_zero': outside_zero_ok,
            'interior_strict_positive': inside_pos_ok,
            'dip_at_zero_e_minus_30': mp.nstr(dip, 20),
            'ok': witness_ok,
            'note': 'sampled sanity witness at the exact owner radius; '
                    'the Lean theorem is the proof',
        },
        'lean_guards': guards,
        'controls': controls,
        'provenance': {
            'lean_test': {
                'path': 'ConnesWeilRH/Dev/C1RouteAOwnerTest.lean',
                'md5': md5(LEAN_TEST)},
            'lean_probe': {
                'path': 'ConnesWeilRH/Dev/C1RouteAOwnerTestProbe.lean',
                'md5': md5(LEAN_PROBE)},
            'check_script': {
                'path': 'scripts/routea_owner_test_lean_pin_2315.py',
                'md5': md5(py)},
            'support_module_md5': continuity['support_live'],
            'compact_log_test_md5': md5(LEAN_CLT),
            'inputs': ['results/2276_owner_scale_price.json',
                       'results/2314_owner_support_lean_pin.json'],
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'verdict': payload['verdict'],
                      'max_branch_diff': mp.nstr(max_diff, 8),
                      'dip_at_zero': mp.nstr(dip, 20),
                      'dip_float': float(dip),
                      'continuity_ok': continuity_ok,
                      'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()