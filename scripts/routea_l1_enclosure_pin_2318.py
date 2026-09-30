"""Record 2318 pin check: the certified L1 enclosure (record 2249) wired
into the producer margin lane.

The Lean module `ConnesWeilRH/Dev/C1RouteAL1Enclosure.lean` introduces the
outward-rounded enclosure pair and the margin-lane interface:

    l1MarginEnclosure2249 = 1675396046388.2736   (certified |Q| lower bound)
    l1UpperEnclosure2249  = -1675396046388.2736  (signed functional upper)
    hmargin_of_certified_l1_enclosure :
        q <= l1UpperEnclosure2249 -> l1MarginEnclosure2249 <= -q
    a005_item5_producer_wired_owner_nodes_margin : the composed producer

This check machine-verifies:

  1. the record 2249 artifact is byte-frozen (first freeze: 4fb81ff7...) and
     still carries its verdict fields, and its stored relations replay in
     exact rational arithmetic:
         q + E_total == q_hi,  q - E_total == q_lo   (bitwise, float64)
         -q_hi == margin_lo,   -q_lo == margin_hi    (bitwise, negation)
     with the measured sub-ulp readings that motivate the outward rounding:
     the exact shadow upper bound q + E_total sits ABOVE the stored render
     q_hi (rounding) and above the naive shortest-decimal transcription
     `-1675396046388.2737`, so a Lean pin at that decimal would sit strictly
     inside the certified bound; the shipped constants round outward by
     1e-4 and cover the exact bound with measured slack;
  2. the owner cross-tie: the artifact's base/corr md5s equal the captured
     owner md5s recorded by the record 2316 node table (same owner on the
     strip and margin sides), and the record 2275 capture root is frozen;
  3. the new module carries the expected statement shapes (transcription
     guards: constants, both defs, the negation and order theorems, the
     ledger re-run, the terminal variant, the consumer, the composed
     producer variant; no sorry; trailing newline), and the probe prints the
     new theorems' axioms;
  4. continuity: the arithmetic pins file stays byte-frozen since record
     2312, the producer module since record 2311, the owner-nodes module and
     its pin artifact since record 2317;
  5. controls: a synthetic literal parse; the naive equal-decimal pin must
     fail the soundness direction; a shifted lower constant at the naive
     render must fail the certified-lower-bound direction; a one-ulp
     mutation of the stored q_hi must fail the bitwise relation; a
     sign-flipped upper literal must fail the negation guard.
  6. replay evidence (recorded when the pre/post-replay copies are present):
     the pre-replay backup equals the frozen bytes, and the full instrument
     re-run reproduces every CERTIFIED field of the artifact bitwise.  The
     only fields allowed to differ are the plain-float cross-check
     diagnostics routed through numpy/BLAS (`base @ vp`, `corr @ vp`,
     np.trapezoid): q_plain_2103_pipeline, rel_lb_diff_mid, rel_lc_diff_mid.
     None of the three enters any certified quantity, join, or Lean pin;
     their measured before/after deltas must stay at plain-path rounding
     scale (q_plain relative <= 1e-13; the other two absolute deltas
     <= 1e-13 / <= 1e-6, they are O(1e-15)- and O(2)-scale diagnostics).

Writes `results/2318_l1_enclosure_pin.json`; exit code 1 on any failure.
"""
import hashlib
import json
import re
import struct
import sys
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / 'results'
LEAN_L1 = ROOT / 'ConnesWeilRH/Dev/C1RouteAL1Enclosure.lean'
LEAN_PROBE = ROOT / 'ConnesWeilRH/Dev/C1RouteAL1EnclosureProbe.lean'
LEAN_ARITH = ROOT / 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean'
LEAN_PRODUCER = ROOT / 'ConnesWeilRH/Dev/C1RouteAProducerWired.lean'
LEAN_OWNER_NODES = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerNodes.lean'
L1_2249 = R / '2249_l1_enclosure.json'
NODES_2316 = R / '2316_node_values.json'
PIN_2317 = R / '2317_owner_nodes_lean_pin.json'
CAPTURE_2275 = R / '2275_gap_owner_audit.json'
OUT = R / '2318_l1_enclosure_pin.json'
# Replay copies live in the build-log directory beside the workspace
# mirror; derived relatively so no host-absolute path appears in the
# repository or the recorded artifact.
BUILDLOGS = ROOT.parent / 'buildlogs'
BACKUP = BUILDLOGS / '2249_l1_before_2318.json'
AFTER = BUILDLOGS / '2249_l1_after_2318.json'
PLAIN_VOLATILE = {('diagnostics', 'q_plain_2103_pipeline'),
                  ('diagnostics', 'rel_lb_diff_mid'),
                  ('diagnostics', 'rel_lc_diff_mid')}

L1_2249_FROZEN = '4fb81ff76dae5b012c49a29d18d82ea9'
ARITH_FROZEN = 'b3fb88c3dd1e2e289454193dfc000376'
PRODUCER_FROZEN = '3b15d733875f50ae7c23a767a1b6a14e'
OWNER_NODES_FROZEN = '68550f52601ad8b23920ec4f3813c676'
PIN_2317_FROZEN = '408bfb5a78e482f51fac6963575072b4'
CAPTURE_2275_FROZEN = 'd83ee0ffccdbf1b193cb7a9a065d5c82'

LIT_LM = '1675396046388.2736'
LIT_LU = '-1675396046388.2736'
NAIVE_D = '1675396046388.2737'

ULP = F(2) ** -12  # ulp of numbers in [2^40, 2^41)

DEF_LM = re.compile(r'def\s+l1MarginEnclosure2249\s*:\s*Real\s*:=\s*(\S+)')
DEF_LU = re.compile(r'def\s+l1UpperEnclosure2249\s*:\s*Real\s*:=\s*(\S+)')
DEF_MARGIN = re.compile(r'def\s+margin2249\s*:\s*Real\s*:=\s*(\S+)')


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def bitwise(a, b):
    return struct.pack('<d', a) == struct.pack('<d', b)


def statement_guards(text):
    return {
        'def_lower': 'def l1MarginEnclosure2249 : Real := 1675396046388.2736'
            in text,
        'def_upper': 'def l1UpperEnclosure2249 : Real := -1675396046388.2736'
            in text,
        'neg_theorem':
            'theorem l1UpperEnclosure2249_eq_neg' in text
            and 'l1UpperEnclosure2249 = -l1MarginEnclosure2249' in text,
        'order_theorem':
            'theorem l1MarginEnclosure2249_le_margin2249' in text
            and 'l1MarginEnclosure2249 ≤ margin2249' in text,
        'ledger_rerun':
            'theorem transfer_free_charge_le_l1Enclosure_sub_slack' in text
            and 'l1MarginEnclosure2249 - eps0FullTail2249' in text,
        'terminal_l1':
            'theorem a005_item5_terminal_count_free_l1' in text
            and '(hmargin : l1MarginEnclosure2249 ≤ -q)' in text,
        'consumer':
            'theorem hmargin_of_certified_l1_enclosure' in text
            and '(hq : q ≤ l1UpperEnclosure2249)' in text
            and 'l1MarginEnclosure2249 ≤ -q' in text,
        'producer_decl':
            'theorem a005_item5_producer_wired_owner_nodes_margin' in text,
        'hnode_binder':
            '(hnode : ∀ j : ℤ, -(50 : ℤ) ≤ j → j ≤ 50 →' in text,
        'hnode_bound': '≤ stripGridMax2303)' in text,
        'call_owner_nodes':
            'frozenStripHypothesis_of_owner_nodes baseCoefficients '
            'corrCoefficients' in text,
        'call_tsum': 'directProduct_highShell_tsum_bound _ _ hstrip' in text,
        'call_gap': 'hgap_of_certified_split hsplit hwindow htail' in text,
        'call_mult':
            'spectralMultiplicityConstant_le_multProxy2248' in text,
        'call_tail2248': 'four_mul_mult_mul_B_le_highShellTail hmult le_rfl'
            in text,
        'call_margin': 'hmargin_of_certified_l1_enclosure hq' in text,
        'producer_conclusion':
            'chargeRest + gap + eps0FullTail2249 < -q' in text,
        'no_sorry': 'sorry' not in text and 'admit' not in text,
        'trailing_newline': text.endswith('\n'),
    }


def main():
    failures = []
    controls = {}

    text = LEAN_L1.read_text(encoding='utf-8')
    probe = LEAN_PROBE.read_text(encoding='utf-8')
    arith_text = LEAN_ARITH.read_text(encoding='utf-8')

    m_lm = DEF_LM.search(text)
    m_lu = DEF_LU.search(text)
    m_mar = DEF_MARGIN.search(arith_text)
    if not m_lm or m_lm.group(1) != LIT_LM:
        failures.append('l1MarginEnclosure2249 literal differs from the pin')
    if not m_lu or m_lu.group(1) != LIT_LU:
        failures.append('l1UpperEnclosure2249 literal differs from the pin')
    if not m_mar or m_mar.group(1) != NAIVE_D:
        failures.append('margin2249 literal differs from the recorded render')

    # 1. the record 2249 artifact frozen and replayed
    l1 = json.loads(L1_2249.read_text(encoding='utf-8'))
    l1_live = md5(L1_2249)
    if l1_live != L1_2249_FROZEN:
        failures.append('record 2249 L1 artifact changed bytes')
    if l1.get('record') != 2249 or \
            l1.get('status') != 'L1-DISCRETE-ENCLOSURE':
        failures.append('record 2249 L1 artifact lost its verdict fields')
    diag = l1.get('diagnostics', {})
    q = diag.get('q')
    e = diag.get('E_total')
    qlo = diag.get('q_lo')
    qhi = diag.get('q_hi')
    mlo = diag.get('margin_lo_certified')
    mhi = diag.get('margin_hi_certified')
    bitwise_rel = {
        'q_plus_E_eq_q_hi': bitwise(q + e, qhi),
        'q_minus_E_eq_q_lo': bitwise(q - e, qlo),
        'neg_q_hi_eq_margin_lo': bitwise(-qhi, mlo),
        'neg_q_lo_eq_margin_hi': bitwise(-qlo, mhi),
    }
    for key, ok in bitwise_rel.items():
        if not ok:
            failures.append(f'artifact bitwise relation failed: {key}')
    Fq, Fe, Fqhi, Fqlo, Fmlo = F(q), F(e), F(qhi), F(qlo), F(mlo)
    exact_upper = Fq + Fe
    exact_lower = Fq - Fe
    naive_upper = F('-' + NAIVE_D)
    shipped_upper = F(LIT_LU)
    shipped_lower = F(LIT_LM)
    readings = {
        'exact_upper_minus_render_ulps': float((exact_upper - Fqhi) / ULP),
        'exact_lower_minus_render_ulps': float((exact_lower - Fqlo) / ULP),
        'exact_upper_minus_naive_decimal_ulps':
            float((exact_upper - naive_upper) / ULP),
        'shipped_upper_slack_ulps': float((shipped_upper - exact_upper) / ULP),
        'shipped_lower_slack_vs_stored_ulps':
            float((Fmlo - shipped_lower) / ULP),
    }
    if not (exact_lower < Fqlo < Fq < Fqhi < exact_upper):
        failures.append('stored enclosure bounds are not ordered')
    if not (exact_upper <= shipped_upper):
        failures.append('shipped upper constant does not cover the exact '
                        'shadow bound')
    if not (shipped_lower <= -exact_upper and shipped_lower <= Fmlo):
        failures.append('shipped lower constant is not a certified lower '
                        'bound')

    # 2. owner cross-tie and capture root
    nodes = json.loads(NODES_2316.read_text(encoding='utf-8'))
    cap = nodes.get('continuity', {}).get('capture', {})
    owner_tie = {
        'base_artifact': diag.get('base_md5'),
        'base_2316_claimed': cap.get('base_md5_claimed'),
        'corr_artifact': diag.get('corr_md5'),
        'corr_2316_claimed': cap.get('corr_md5_claimed'),
        'capture_2275_recorded': nodes.get('provenance', {}).get(
            'capture', {}).get('md5'),
        'capture_2275_live': md5(CAPTURE_2275),
    }
    if owner_tie['base_artifact'] != owner_tie['base_2316_claimed'] or \
            owner_tie['corr_artifact'] != owner_tie['corr_2316_claimed']:
        failures.append('owner vectors differ from the record 2316 capture')
    if owner_tie['capture_2275_recorded'] != owner_tie['capture_2275_live']:
        failures.append('record 2275 capture root changed bytes')

    # 3. statement and probe guards
    guards = statement_guards(text)
    print_marks = [
        '#print axioms ConnesWeilRH.Dev.l1UpperEnclosure2249_eq_neg',
        '#print axioms ConnesWeilRH.Dev.l1MarginEnclosure2249_le_margin2249',
        '#print axioms ConnesWeilRH.Dev.transfer_free_charge_le_l1Enclosure_sub_slack',
        '#print axioms ConnesWeilRH.Dev.a005_item5_terminal_count_free_l1',
        '#print axioms ConnesWeilRH.Dev.hmargin_of_certified_l1_enclosure',
        '#print axioms ConnesWeilRH.Dev.a005_item5_producer_wired_owner_nodes_margin',
    ]
    guards['probe_axioms'] = all(mark in probe for mark in print_marks)
    for key, ok in guards.items():
        if not ok:
            failures.append(f'Lean transcription guard failed: {key}')

    # 4. continuity
    continuity = {
        'arith_recorded_2312': ARITH_FROZEN,
        'arith_live': md5(LEAN_ARITH),
        'producer_recorded_2311': PRODUCER_FROZEN,
        'producer_live': md5(LEAN_PRODUCER),
    }
    pin2317 = json.loads(PIN_2317.read_text(encoding='utf-8'))
    continuity['owner_nodes_recorded_2317'] = pin2317.get(
        'provenance', {}).get('lean_nodes', {}).get('md5')
    continuity['owner_nodes_live'] = md5(LEAN_OWNER_NODES)
    continuity['pin_2317_live'] = md5(PIN_2317)
    if continuity['arith_recorded_2312'] != continuity['arith_live']:
        failures.append('arithmetic pins file changed since record 2312')
    if continuity['producer_recorded_2311'] != continuity['producer_live']:
        failures.append('producer module changed since record 2311')
    if continuity['owner_nodes_recorded_2317'] != continuity['owner_nodes_live']:
        failures.append('owner-nodes module changed since record 2317')
    if continuity['pin_2317_live'] != PIN_2317_FROZEN:
        failures.append('record 2317 pin artifact changed bytes')
    if pin2317.get('verdict') != 'PINNED-OWNER-NODES-VERIFIED':
        failures.append('record 2317 artifact lost its verdict')

    # 5. exact arithmetic replay of the Lean joins
    hf = F('4894093747.7643')
    ke = F('74601530.30234718')
    gc = F('10000000')
    eps = F('1670000000000')
    margin_dec = F(NAIVE_D)
    joins = {
        'negation': shipped_upper == -shipped_lower,
        'order_le_margin2249': shipped_lower <= margin_dec,
        'ledger_rerun': hf + ke + gc < shipped_lower - eps,
    }
    for key, ok in joins.items():
        if not ok:
            failures.append(f'Lean join replay failed: {key}')
    consumer_replay = {
        'at_bound': (-shipped_upper) == shipped_lower,
        'at_exact_upper': shipped_lower <= -exact_upper,
    }
    if not all(consumer_replay.values()):
        failures.append('consumer direction replay failed')

    # 6. replay evidence (optional, recorded): the full 2249 instrument re-run
    # (post-replay copy) reproduces every certified field bitwise; only the
    # plain-float cross-check diagnostics may differ.
    def diff_paths(a, b, prefix=()):
        if isinstance(a, dict):
            out = []
            if set(a) != set(b):
                out.append(prefix + ('<keys>',))
            for k in sorted(set(a) & set(b)):
                out += diff_paths(a[k], b[k], prefix + (k,))
            return out
        if isinstance(a, list):
            if len(a) != len(b):
                return [prefix + ('<len>',)]
            out = []
            for i, (u, v) in enumerate(zip(a, b)):
                out += diff_paths(u, v, prefix + (i,))
            return out
        return [] if a == b else [prefix]

    replay = {
        'backup_path': 'buildlogs/2249_l1_before_2318.json',
        'after_path': 'buildlogs/2249_l1_after_2318.json',
        'backup_exists': BACKUP.exists(), 'after_exists': AFTER.exists(),
        'plain_path_volatile': sorted('.'.join(p) for p in PLAIN_VOLATILE),
    }
    if replay['backup_exists']:
        replay['backup_equals_frozen'] = md5(BACKUP) == l1_live
        if not replay['backup_equals_frozen']:
            failures.append('pre-replay backup differs from the frozen bytes')
    if replay['after_exists']:
        after = json.loads(AFTER.read_text(encoding='utf-8'))
        fields = diff_paths(l1, after)
        replay['after_diff_fields'] = sorted('.'.join(p) for p in fields)
        replay['certified_bitwise_ok'] = set(fields) <= PLAIN_VOLATILE
        if not replay['certified_bitwise_ok']:
            failures.append('2249 replay changed a certified field: '
                            + ', '.join(replay['after_diff_fields']))
        deltas = {}
        qp_frozen = diag.get('q_plain_2103_pipeline')
        a_diag = after.get('diagnostics', {})
        a_qp = a_diag.get('q_plain_2103_pipeline')
        if qp_frozen and a_qp:
            deltas['q_plain_rel'] = abs(qp_frozen - a_qp) / abs(a_qp)
        for key in ('rel_lb_diff_mid', 'rel_lc_diff_mid'):
            av = a_diag.get(key)
            bv = diag.get(key)
            if av is not None and bv is not None:
                deltas[key + '_abs'] = abs(bv - av)
        replay['volatile_deltas'] = deltas
        if deltas.get('q_plain_rel', 0.0) > 1e-13:
            failures.append('q_plain plain-path drift exceeds the '
                            'rounding-scale bound')
        if deltas.get('rel_lb_diff_mid_abs', 0.0) > 1e-13:
            failures.append('rel_lb_diff_mid drift exceeds the bound')
        if deltas.get('rel_lc_diff_mid_abs', 0.0) > 1e-6:
            failures.append('rel_lc_diff_mid drift exceeds the bound')

    # 7. controls
    synthetic = 'def l1MarginEnclosure2249 : Real := 1\n'
    controls['synthetic_parse'] = {
        'regex_match': bool(DEF_LM.search(synthetic)),
        'ok': bool(DEF_LM.search(synthetic))}
    controls['naive_decimal_rejected'] = {
        'measured_unsound': not (exact_upper <= naive_upper),
        'ok': not (exact_upper <= naive_upper)}
    controls['naive_lower_rejected'] = {
        'measured_unsound': not (margin_dec <= -exact_upper),
        'ok': not (margin_dec <= -exact_upper)}
    qhi_mut = struct.unpack('<d', struct.pack('<Q',
        struct.unpack('<Q', struct.pack('<d', qhi))[0] + 1))[0]
    controls['one_ulp_mutation_detected'] = {
        'mutated_differs': not bitwise(qhi_mut, qhi),
        'relation_fails': not bitwise(q + e, qhi_mut),
        'ok': (not bitwise(qhi_mut, qhi)) and (not bitwise(q + e, qhi_mut))}
    sign_flip = text.replace(
        'def l1UpperEnclosure2249 : Real := -1675396046388.2736',
        'def l1UpperEnclosure2249 : Real := 1675396046388.2736')
    controls['sign_flip_rejected'] = {
        'mutated_differs': sign_flip != text,
        'guard_fails': not statement_guards(sign_flip)['def_upper'],
        'ok': (sign_flip != text)
              and (not statement_guards(sign_flip)['def_upper'])}
    for key, c in controls.items():
        if not c.get('ok'):
            failures.append(f'control failed: {key}')

    payload = {
        'record': 2318, 'mode': 'check',
        'verdict': 'PINNED-L1-ENCLOSURE-VERIFIED' if not failures
                   else 'FAILED',
        'scope': 'record 2249 L1 enclosure wired into the producer margin '
                 'lane: outward-rounded constants, enclosure consumer, and '
                 'the owner-nodes producer variant',
        'enclosure': {
            'q': q, 'E_total': e, 'q_lo': qlo, 'q_hi': qhi,
            'margin_lo_certified': mlo, 'margin_hi_certified': mhi,
            **bitwise_rel,
            **readings,
            'naive_decimal_upper': '-' + NAIVE_D,
            'shipped_upper': LIT_LU, 'shipped_lower': LIT_LM,
        },
        'owner_tie': owner_tie,
        'lean_guards': guards,
        'continuity': continuity,
        'joins': {k: bool(v) for k, v in joins.items()},
        'consumer_replay': {k: bool(v) for k, v in consumer_replay.items()},
        'replay': replay,
        'controls': controls,
        'provenance': {
            'lean_l1_enclosure': {
                'path': 'ConnesWeilRH/Dev/C1RouteAL1Enclosure.lean',
                'md5': md5(LEAN_L1)},
            'lean_probe': {
                'path': 'ConnesWeilRH/Dev/C1RouteAL1EnclosureProbe.lean',
                'md5': md5(LEAN_PROBE)},
            'check_script': {
                'path': 'scripts/routea_l1_enclosure_pin_2318.py',
                'md5': md5(Path(__file__))},
            'inputs': ['results/2249_l1_enclosure.json',
                       'results/2316_node_values.json',
                       'results/2317_owner_nodes_lean_pin.json',
                       'results/2275_gap_owner_audit.json'],
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({
        'verdict': payload['verdict'],
        'readings': readings,
        'naive_sound': bool(exact_upper <= naive_upper),
        'shipped_sound': bool(exact_upper <= shipped_upper),
        'replay': replay,
        'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()