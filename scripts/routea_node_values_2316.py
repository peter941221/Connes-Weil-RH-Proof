"""Record 2316 node-value check: the 101 certified node values of the
captured owner min-product, replayed bitwise against the 2303 artifact
and pinned below the Lean constant `stripGridMax2303`.

Record 2313's `frozenStripHypothesis_of_certified_nodes` needs, at each
of the 101 grid nodes `j/100`, `-50 <= j <= 50`,

    min (stripSecondNorm (j/100) b * stripNorm (j/100) c)
        (stripSecondNorm (j/100) c * stripNorm (j/100) b) <= stripGridMax2303

for the owner pair (b, c) whose coefficient and modulation vectors are
the record 2275 capture.  Record 2303 computed certified per-node uppers
of exactly this min-product (the `B_point` field of its 101 `grid_rows`)
and took their maximum (2644542.851480454) for the Lean pin.  This check
turns that table into a first-class, re-verifiable input:

  1. continuity: the live 2275 capture parses and is bitwise equal to
     the 2267 replay operands (families, base and corr vectors -- the
     captured coefficient and modulation vectors enter bitwise); the
     101 `results/2303_sigma_j.json` files are present, indexed, and
     bitwise equal to the corresponding `grid_rows` point values; the
     2303 envelope artifact bytes are frozen by md5 (first record to do
     so);
  2. assembly replay: for all 101 rows the check re-derives, with the
     record 2303 expressions verbatim (2238 ladder + panel law, 2234
     majorant inflation, upward rounding chains), the four panel, four
     inflation, four certified-norm, two channel-product values, the
     min, the binding channel and `B_point`, and requires bitwise
     equality with the committed fields; the transfer, continuum sup,
     covered flag, margin, raw-check ratios and the `anchor_raw`
     summary are replayed the same way;
  3. certification directions in exact rational arithmetic: each
     `B_point` is an upper of min(db*mc, dc*mb), each `B_point` is at
     most the pinned `stripGridMax2303` parsed from the Lean source,
     and each certified min-product dominates the live numpy raw
     screen (the 2277 reproduction, recomputed here from the capture);
  4. the per-node table (j, sigma, channel products, B_point, binding,
     margin to the pin in ulp) is emitted as the first-class
     `results/2316_node_values.json` node-value record.

Controls run in the same pass: a synthetic pin-parse probe, a shifted
pin rejected by the direction predicate, a one-ulp point mutation
rejected by the bitwise replay, a doubled raw screen rejected by the
dominance ratio, and a capture mutation rejected by the operand anchor.
Writes `results/2316_node_values.json`; exit code 1 on any failure.
"""
import hashlib
import importlib.util
import json
import math
import re
import struct
import sys
from fractions import Fraction
from pathlib import Path

import numpy as np

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / 'results'
LEAN_ARITH = ROOT / 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean'
ENVELOPE = R / '2303_corrected_strip_envelope.json'
RECON = R / '2303_recon.json'
OWNER_CAPTURE = R / '2275_gap_owner_audit.json'
REPLAY_OPERANDS = R / '2267_replay_operands.json'
PIN_2311 = R / '2311_strip_envelope_lean_pin.json'
PIN_2313 = R / '2313_grid_sampling_lean_pin.json'
OUT = R / '2316_node_values.json'

K = 30.0
NX = 240001
GRID_J = list(range(-50, 51))
HALF_STEP = 0.005
FROZEN_B = 9506275.102584327
R_BASE_2237 = 1005486.289224448
R_CORR_2237 = 2057069012.526474
PIN_LITERAL = '2644542.8515'
CHANNELS = ('base_M0', 'base_D2', 'corr_M0', 'corr_D2')

GM_DEF = re.compile(r'def\s+stripGridMax2303\s*:\s*Real\s*:=\s*(\S+)')
DECIMAL = re.compile(r'^\d+\.\d+$')


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / 'scripts' / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


o34 = _load('o34_2316', 'routea_weighted_zero_direct_product_outward_2234.py')
p38 = _load('p38_2316', 'routea_weighted_zero_panel_dx2_2238.py')


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def same(a, b):
    """Bitwise equality of two IEEE doubles (false on any NaN)."""
    if math.isnan(a) or math.isnan(b):
        return False
    return struct.pack('<d', a) == struct.pack('<d', b)


def up_many(v, n):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


def parse_pin(text):
    m = GM_DEF.search(text)
    if not m:
        raise ValueError('stripGridMax2303 definition not found in Lean source')
    raw = m.group(1)
    if not DECIMAL.match(raw):
        raise ValueError(f'stripGridMax2303 literal is not a plain decimal: {raw}')
    return raw


class Owner:
    """capture + operands, bitwise-anchored."""

    def __init__(self):
        cap = json.loads(OWNER_CAPTURE.read_text(encoding='utf-8'))['owner_capture']
        self.cap = cap
        self.fam = [(float.fromhex(w), float.fromhex(t))
                    for w, t in cap['families_hex']]
        self.base = [complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap['base_hex']]
        self.corr = [complex(float.fromhex(re), float.fromhex(im))
                     for re, im in cap['corr_hex']]
        op = json.loads(REPLAY_OPERANDS.read_text(encoding='utf-8'))
        fam67 = [tuple(float.fromhex(v) for v in f) for f in op['families_hex']]
        b67 = [complex(*(float.fromhex(v) for v in c)) for c in op['base_hex']]
        c67 = [complex(*(float.fromhex(v) for v in c)) for c in op['corr_hex']]
        self.anchors = {
            'families_bitwise': all(same(x[0], y[0]) and same(x[1], y[1])
                                    for x, y in zip(self.fam, fam67)),
            'base_bitwise': all(same(x.real, y.real) and same(x.imag, y.imag)
                                for x, y in zip(self.base, b67)),
            'corr_bitwise': all(same(x.real, y.real) and same(x.imag, y.imag)
                                for x, y in zip(self.corr, c67)),
            'base_md5_claimed': cap['base_md5'],
            'corr_md5_claimed': cap['corr_md5'],
        }
        self.cfam = [(a * a, th) for a, th in self.fam]
        self.rmax = max(a for a, _ in self.cfam)

    def dx(self):
        return 2.0 * self.rmax / (NX - 1)


def panel_em_sym(owner, channel, sigma, m):
    """Record 2303 panel law, verbatim operator order."""
    k = 0 if channel.endswith('M0') else 2
    s = abs(sigma)
    return (owner.dx() ** 2 / 12.0) * (2.0 * owner.rmax) * math.exp(
        s * owner.rmax) * (m[k + 2] + 2.0 * s * m[k + 1]
                           + sigma * sigma * m[k])


def coeff_infl_sym(owner, coef, sigma, radius, order):
    """Record 2303 inflation law, verbatim operator order."""
    s = abs(sigma)
    acc = 0.0
    for (a, _th), _coef in zip(owner.cfam, coef):
        acc += 2.0 * a * math.exp(s * owner.rmax) * o34.majorant_phi_le(
            order, K, a)
    return radius * acc


def raw_screen(owner):
    """Record 2303 recon screen, recomputed live (numpy float64)."""
    grid = np.linspace(-owner.rmax, owner.rmax, NX)
    h = {}
    for name, coef in (('base', owner.base), ('corr', owner.corr)):
        value = np.zeros(grid.shape, dtype=complex)
        second = np.zeros(grid.shape, dtype=complex)
        for c, (a, th) in zip(coef, owner.cfam):
            u = grid / a
            q = 1.0 - u * u
            mk = q > 0.0
            phi = np.zeros_like(grid)
            phi[mk] = np.exp(-K / q[mk])
            e1 = np.zeros_like(grid)
            e1[mk] = -2.0 * K * u[mk] / (a * q[mk] ** 2)
            e2 = np.zeros_like(grid)
            e2[mk] = (-2.0 * K / a ** 2) * (q[mk] ** -2
                                            + 4.0 * u[mk] ** 2 * q[mk] ** -3)
            term = c * phi * np.exp(1j * th * grid)
            value += term
            second += term * (e2 + e1 * e1 + 2j * th * e1 - th * th)
        h[name + '_M0'] = np.abs(value)
        h[name + '_D2'] = np.abs(second)
    rows = []
    for j in GRID_J:
        w = np.exp((j / 100.0) * grid)
        vals = {name: float(np.trapezoid(arr * w, grid))
                for name, arr in h.items()}
        rows.append({'j': j, 'sigma': j / 100.0, 'values': vals,
                     'B': min(vals['base_D2'] * vals['corr_M0'],
                              vals['corr_D2'] * vals['base_M0'])})
    return rows


def main():
    F = Fraction  # exact rational arithmetic for every direction check
    failures = []
    controls = {}
    mismatches = {name: [] for name in
                  ('j', 'sigma', 'point', 'panel', 'infl', 'norms',
                   'channel_a', 'channel_b', 'C_upper', 'binding',
                   'B_point', 'raw_check', 'raw_values', 'raw_B')}

    lean_text = LEAN_ARITH.read_text(encoding='utf-8')
    pin_raw = parse_pin(lean_text)
    if pin_raw != PIN_LITERAL:
        failures.append(f'Lean stripGridMax2303 literal is {pin_raw}, '
                        f'expected {PIN_LITERAL}')
    pin = Fraction(pin_raw)

    controls['synthetic_parse'] = {
        'parsed': parse_pin('def stripGridMax2303 : Real := 12.345\n'),
        'ok': parse_pin('def stripGridMax2303 : Real := 12.345\n') == '12.345'}
    if not controls['synthetic_parse']['ok']:
        failures.append('synthetic pin-parse control failed')

    owner = Owner()
    if len(owner.fam) != 30:
        failures.append('expected 30 captured families')
    for key in ('families_bitwise', 'base_bitwise', 'corr_bitwise'):
        if not owner.anchors[key]:
            failures.append(f'capture anchor failed: {key}')

    env = json.loads(ENVELOPE.read_text(encoding='utf-8'))
    recon = json.loads(RECON.read_text(encoding='utf-8'))
    if env.get('status') != 'CORRECTED-STRIP-COVERED':
        failures.append('envelope artifact is not CORRECTED-STRIP-COVERED')
    gate = env.get('gate', {})
    if not (gate.get('zero_free') and gate.get('edge') == 'EDGE-ZERO-FREE-CERTIFIED'
            and all(v == 'ZERO-FREE-CERTIFIED'
                    for v in gate.get('zero_count', {}).values())
            and len(gate.get('zero_count', {})) == 4):
        failures.append('zero-count gate of the envelope artifact is not certified')
    if env['grid']['x_nodes'] != NX or env['grid']['sigma_nodes'] != 101:
        failures.append('grid shape of the envelope artifact changed')
    if not same(env['owner']['rmax'], owner.rmax):
        failures.append('envelope rmax differs from the live capture')

    ladders = {'base': p38.ladder(owner.cfam, owner.base),
               'corr': p38.ladder(owner.cfam, owner.corr)}
    ladder_bitwise = {
        name: all(same(x, y) for x, y in
                  zip(ladders[name], env['panel'][f'ladder_{name}']))
        and all(same(x, y) for x, y in
                zip(ladders[name], recon['channels'][name]['ladder']))
        for name in ('base', 'corr')}
    if not all(ladder_bitwise.values()):
        failures.append('2238 ladder replay differs from the committed ladders')

    if not same(env['grid']['dx'], owner.dx()):
        failures.append('envelope dx differs from the replayed grid step')

    rows = env['grid_rows']
    if len(rows) != 101:
        failures.append('envelope does not carry 101 grid rows')

    sigma_digests = []
    for idx, j in enumerate(GRID_J):
        sig = R / f'2303_sigma_{j}.json'
        if not sig.exists():
            failures.append(f'sigma file missing for j={j}')
            continue
        sigma_digests.append(md5(sig))
        s = json.loads(sig.read_text(encoding='utf-8'))
        row = rows[idx]
        if row['j'] != j:
            mismatches['j'].append(j)
        if not same(row['sigma'], j / 100.0):
            mismatches['sigma'].append(j)
        if not (s['sigma_index'] == j and s['nodes'] == NX
                and same(s['sigma'], j / 100.0)):
            mismatches['sigma'].append(f'{j}:file')
        for ch in CHANNELS:
            if not same(s['values'][ch], row['point'][ch]):
                mismatches['point'].append(f'{j}:{ch}')

    tp2 = up_many((2.0 * math.pi) ** 2, 3)
    node_table = []
    per_row = []
    for idx, j in enumerate(GRID_J):
        row = rows[idx]
        sigma = j / 100.0
        pb = panel_em_sym(owner, 'base_M0', sigma, ladders['base'])
        pb2 = panel_em_sym(owner, 'base_D2', sigma, ladders['base'])
        pc = panel_em_sym(owner, 'corr_M0', sigma, ladders['corr'])
        pc2 = panel_em_sym(owner, 'corr_D2', sigma, ladders['corr'])
        eb = coeff_infl_sym(owner, owner.base, sigma, R_BASE_2237, 0)
        eb2 = coeff_infl_sym(owner, owner.base, sigma, R_BASE_2237, 2)
        ec = coeff_infl_sym(owner, owner.corr, sigma, R_CORR_2237, 0)
        ec2 = coeff_infl_sym(owner, owner.corr, sigma, R_CORR_2237, 2)
        v = row['point']
        mb = up_many(up_many(up_many(v['base_M0'] + pb, 2) * (1.0 + eb), 3), 3)
        db = up_many(up_many(up_many(v['base_D2'] + pb2, 2) * (1.0 + eb2), 3), 3)
        mc = up_many(up_many(up_many(v['corr_M0'] + pc, 2) * (1.0 + ec), 3), 3)
        dc = up_many(up_many(up_many(v['corr_D2'] + pc2, 2) * (1.0 + ec2), 3), 3)
        c1 = up_many(up_many(db * mc, 3) / tp2, 3)
        c2 = up_many(up_many(dc * mb, 3) / tp2, 3)
        B = up_many(up_many(tp2 * min(c1, c2), 3), 3)
        panel = {ch: val for ch, val in
                 zip(CHANNELS, (pb, pb2, pc, pc2))}
        infl = {ch: val for ch, val in
                zip(CHANNELS, (eb, eb2, ec, ec2))}
        norms = {ch: val for ch, val in
                 zip(CHANNELS, (mb, db, mc, dc))}
        if panel != row['panel']:
            mismatches['panel'].append(j)
        if infl != row['infl']:
            mismatches['infl'].append(j)
        if norms != row['norms']:
            mismatches['norms'].append(j)
        if not same(c1, row['C_channel_a']):
            mismatches['channel_a'].append(j)
        if not same(c2, row['C_channel_b']):
            mismatches['channel_b'].append(j)
        if not same(min(c1, c2), row['C_upper']):
            mismatches['C_upper'].append(j)
        if row['binding'] != ('a' if c1 <= c2 else 'b'):
            mismatches['binding'].append(j)
        if not same(B, row['B_point']):
            mismatches['B_point'].append(j)
        # exact-rational certification directions
        min_product = min(F(db) * F(mc), F(dc) * F(mb))
        if not (F(B) >= min_product):
            failures.append(f'row {j}: B_point below the certified min-product')
        if not (F(B) <= pin):
            failures.append(f'row {j}: B_point above the pinned grid maximum')
        margin_ulps = float((pin - F(B)) / F(math.ulp(B)))
        per_row.append({'j': j, 'sigma': sigma, 'B_point': B,
                        'binding': row['binding'],
                        'certified_min_product': float(min_product),
                        'margin_to_pin_ulps': margin_ulps})
        node_table.append({'j': j, 'sigma': row['sigma'], 'B_point': B,
                           'certified_min_product': float(min_product),
                           'binding': row['binding'],
                           'margin_to_pin_ulps': margin_ulps})

    for field, bad in mismatches.items():
        if bad:
            failures.append(f'bitwise replay mismatch in {field}: {bad[:6]}'
                            + ('...' if len(bad) > 6 else ''))

    # live raw screen + raw-check replay
    raw_rows = raw_screen(owner)
    for idx, j in enumerate(GRID_J):
        rr = raw_rows[idx]
        sr = recon['raw']['rows'][idx]
        if rr['j'] != j or not same(rr['sigma'], j / 100.0):
            mismatches['raw_values'].append(j)
        for ch in CHANNELS:
            if not same(rr['values'][ch], sr['values'][ch]):
                mismatches['raw_values'].append(f'{j}:{ch}')
        if not same(rr['B'], sr['B']):
            mismatches['raw_B'].append(j)
    if mismatches['raw_values'] or mismatches['raw_B']:
        failures.append('live numpy raw screen differs from the committed recon')
    if not recon['screen_2277']['match']:
        failures.append('recon artifact lost the 2277 bitwise reproduction flag')

    raw_ratios = []
    for idx, j in enumerate(GRID_J):
        row = rows[idx]
        db = F(row['norms']['base_D2'])
        mc = F(row['norms']['corr_M0'])
        dc = F(row['norms']['corr_D2'])
        mb = F(row['norms']['base_M0'])
        min_product = min(db * mc, dc * mb)
        raw_b = F(raw_rows[idx]['B'])
        if not (min_product >= raw_b):
            failures.append(f'row {j}: certified min-product below the raw screen')
        raw_ratios.append((j, min_product / raw_b))
        stored = row['raw_check']
        live_float = min(row['norms']['base_D2'] * row['norms']['corr_M0'],
                         row['norms']['corr_D2'] * row['norms']['base_M0']) \
            / raw_rows[idx]['B']
        if not same(live_float, stored['v_min_over_raw']):
            failures.append(f'row {j}: stored raw-check ratio is not the replay value')
        if not same(raw_rows[idx]['B'], stored['raw_B']):
            failures.append(f'row {j}: stored raw-check reference is not the live screen')
    worst_ratio = min(raw_ratios, key=lambda t: t[1])
    stored_ratios = [row['raw_check']['v_min_over_raw'] for row in rows]
    ratio_rel_max = max(abs(v - 1.0) for v in stored_ratios)
    if not same(ratio_rel_max, env['anchor_raw']['rel_max']):
        failures.append('anchor_raw rel_max is not the replay value')
    if env['anchor_raw']['upper_ok'] is not True:
        failures.append('anchor_raw upper flag is not set')

    # transfer / continuum sup / margin replay
    transfer = up_many(math.exp(2.0 * owner.rmax * HALF_STEP), 4)
    if not same(transfer, env['grid']['transfer']):
        failures.append('transfer replay differs from the artifact')
    if not same(env['grid']['half_step'], HALF_STEP):
        failures.append('half-step pin changed')
    max_row = max(rows, key=lambda r: r['B_point'])
    sup_cert = up_many(up_many(max_row['B_point'] * transfer, 3), 3)
    if not same(sup_cert, env['centered']['sup_certified']):
        failures.append('continuum sup replay differs from the artifact')
    if env['centered']['covered'] is not True or not (sup_cert <= FROZEN_B):
        failures.append('envelope is not covered at the frozen constant')
    margin = FROZEN_B / sup_cert
    if not same(float(margin), env['centered']['margin']):
        failures.append('artifact margin is not the replay value')
    if not (same(max_row['sigma'], env['centered']['max_point_sigma'])
            and same(max_row['B_point'], env['centered']['max_point_B'])
            and max_row['binding'] == env['centered']['max_point_binding']):
        failures.append('centered maximum row is not the replayed maximizer')

    # cross-record pin artifacts
    pin2311 = json.loads(PIN_2311.read_text(encoding='utf-8'))
    if not (pin2311['verdict'] == 'PINNED-ENVELOPE-VERIFIED'
            and same(pin2311['grid_max']['artifact_render'],
                     env['centered']['max_point_B'])
            and pin2311['grid_max']['lean_literal'] == PIN_LITERAL):
        failures.append('2311 pin artifact is not consistent with the envelope')
    pin2313 = json.loads(PIN_2313.read_text(encoding='utf-8'))
    if pin2313['verdict'] != 'PINNED-GRID-SAMPLING-VERIFIED':
        failures.append('2313 pin artifact is not verified')

    pin_margin = pin - Fraction(max_row['B_point'])

    # controls
    shifted = Fraction(max_row['B_point']) - Fraction(1, 1000)
    controls['shifted_pin_rejected'] = {
        'shifted_below_max': shifted < Fraction(max_row['B_point']),
        'predicate_fails': not (Fraction(max_row['B_point']) <= shifted)}
    bad_row = dict(rows[50])
    bad_point = dict(bad_row['point'])
    bad_point['base_M0'] = up_many(bad_point['base_M0'], 1)
    sigma0 = 0.0
    pb = panel_em_sym(owner, 'base_M0', sigma0, ladders['base'])
    eb = coeff_infl_sym(owner, owner.base, sigma0, R_BASE_2237, 0)
    mutant = up_many(up_many(up_many(bad_point['base_M0'] + pb, 2)
                             * (1.0 + eb), 3), 3)
    controls['one_ulp_point_mutation_rejected'] = {
        'mutant_differs': not same(mutant, rows[50]['norms']['base_M0']),
        'detector_has_teeth': mutant != rows[50]['norms']['base_M0']}
    inflated = Fraction(raw_rows[50]['B']) * Fraction(5, 2)
    minp0 = min(Fraction(rows[50]['norms']['base_D2'])
                * Fraction(rows[50]['norms']['corr_M0']),
                Fraction(rows[50]['norms']['corr_D2'])
                * Fraction(rows[50]['norms']['base_M0']))
    controls['inflated_raw_rejected'] = {
        'ratio_at_j0': float(minp0 / Fraction(raw_rows[50]['B'])),
        'inflated_above_certified': inflated > minp0,
        'ratio_below_one': minp0 < inflated}
    mutated_family = list(owner.fam)
    w0, t0 = mutated_family[0]
    mutated_family[0] = (up_many(w0, 1), t0)
    op = json.loads(REPLAY_OPERANDS.read_text(encoding='utf-8'))
    fam67 = [tuple(float.fromhex(v) for v in f) for f in op['families_hex']]
    controls['capture_mutation_rejected'] = {
        'anchor_fails': not all(same(x[0], y[0]) and same(x[1], y[1])
                                for x, y in zip(mutated_family, fam67))}
    for key, c in controls.items():
        if not all(v for k, v in c.items() if k != 'shifted_below_max'):
            failures.append(f'control failed: {key}')

    payload = {
        'record': 2316, 'mode': 'check',
        'verdict': 'NODE-VALUES-CERTIFIED' if not failures else 'FAILED',
        'scope': 'the 101 certified node values of '
                 'min(D2_b M_c, D2_c M_b) at the grid nodes j/100, '
                 '-50 <= j <= 50, of the record 2275 captured owner pair; '
                 'the value half of the owner bridge (artifact grade)',
        'pin': {
            'lean_literal': pin_raw,
            'parse_source': 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean',
            'max_point_B': max_row['B_point'],
            'max_point_j': max_row['j'],
            'max_point_sigma': max_row['sigma'],
            'max_point_binding': max_row['binding'],
            'pin_margin': float(pin_margin),
            'pin_margin_ulps': float(pin_margin / F(math.ulp(max_row['B_point']))),
            'all_rows_at_most_pin': not failures,
        },
        'replay': {
            'rows_replayed': len(rows),
            'ladder_bitwise': ladder_bitwise,
            'dx_bitwise': same(env['grid']['dx'], owner.dx()),
            'transfer_bitwise': same(transfer, env['grid']['transfer']),
            'sup_certified_bitwise': same(sup_cert, env['centered']['sup_certified']),
            'margin_bitwise': same(float(margin), env['centered']['margin']),
            'mismatches': {k: v for k, v in mismatches.items()},
        },
        'node_table': node_table,
        'summary': {
            'rows': len(node_table),
            'min_margin_to_pin_ulps': min(r['margin_to_pin_ulps']
                                          for r in per_row),
            'max_margin_to_pin_ulps': max(r['margin_to_pin_ulps']
                                          for r in per_row),
            'worst_raw_ratio': [worst_ratio[0], float(worst_ratio[1])],
            'raw_ratio_rel_max': ratio_rel_max,
            'covered': True,
            'frozen': FROZEN_B,
            'sup_certified': sup_cert,
            'margin_ratio': float(FROZEN_B / sup_cert),
        },
        'continuity': {
            'capture': owner.anchors,
            'sigma_files': {'count': len(sigma_digests),
                            'digest': hashlib.md5(
                                ''.join(sigma_digests).encode()).hexdigest()},
            'envelope_md5': md5(ENVELOPE),
            'recon_md5': md5(RECON),
        },
        'controls': controls,
        'provenance': {
            'check_script': {'path': 'scripts/routea_node_values_2316.py',
                             'md5': md5(Path(__file__))},
            'lean_arithmetic': {'path': 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean',
                                'md5': md5(LEAN_ARITH)},
            'capture': {'path': 'results/2275_gap_owner_audit.json',
                        'md5': md5(OWNER_CAPTURE)},
            'operands': {'path': 'results/2267_replay_operands.json',
                         'md5': md5(REPLAY_OPERANDS)},
            'machinery': [
                {'path': 'scripts/routea_weighted_zero_direct_product_outward_2234.py',
                 'md5': md5(ROOT / 'scripts'
                            / 'routea_weighted_zero_direct_product_outward_2234.py')},
                {'path': 'scripts/routea_weighted_zero_panel_dx2_2238.py',
                 'md5': md5(ROOT / 'scripts'
                            / 'routea_weighted_zero_panel_dx2_2238.py')}],
            'render_convention': 'bitwise replay of the record 2303 reduce in '
                                 'IEEE double arithmetic (numpy 2.5.3, '
                                 'glibc libm); certified point quadrature '
                                 'values are the committed 2303 directed-MPFR '
                                 'sigma files, anchored here by index, node '
                                 'count, bitwise row equality and the raw-screen '
                                 'dominance directions',
            'nonclaims': [
                'no Lean certificate of the strip integrals; the node values '
                'remain artifact-grade inputs to the Lean consumer',
                'the sigma point quadrature itself is not re-run; only its '
                'committed files are re-linked and direction-checked',
                'no producer GO, no gate sign change, no RH claim'],
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({
        'verdict': payload['verdict'],
        'rows': len(node_table),
        'max_point_B': max_row['B_point'],
        'max_point_sigma': max_row['sigma'],
        'max_point_binding': max_row['binding'],
        'pin_margin': float(pin_margin),
        'pin_margin_ulps': payload['pin']['pin_margin_ulps'],
        'min_margin_ulps': payload['summary']['min_margin_to_pin_ulps'],
        'worst_raw_ratio': [worst_ratio[0], float(worst_ratio[1])],
        'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()