"""Record 2313 pin check: the Lean grid-sampling arithmetic against the
certified 2303 grid artifact.

The Lean module `ConnesWeilRH/Dev/C1RouteAGridSampling.lean` proves that
every `sigma` in the centered window `[-1/2, 1/2]` lies within the pinned
half-step `stripHalfStep2303` of a grid node `j / 100`,
`-50 <= j <= 50` — the record 2303 sigma grid.  This check
machine-verifies, in exact rational arithmetic, that

  1. the Lean statement's node geometry (index bounds 50/50, denominator
     100, bound `stripHalfStep2303`) is parsed from the source and
     matches the committed `grid_rows` (101 rows, `j = -50..50`
     contiguous, `sigma = j/100` renders);
  2. the half-step pin equals the exact design value
     `1/(2*(101-1)) = 1/200` and equals the committed
     `grid.half_step` render;
  3. the covering-radius claim itself: with design nodes `j/100`, every
     node-to-node midpoint is at distance exactly `1/200` and every node
     at distance 0, so the sup of the distance-to-nearest-node over
     `[-1/2, 1/2]` (a piecewise-linear tent per node gap) equals the
     Lean bound target exactly;
  4. the record 2312 files are byte-frozen: their live md5 hashes equal
     the hashes recorded in the 2312 pin artifact (cross-record hash
     continuity; the 2313 record narrows the 2312 non-claim without
     touching its files);
  5. the Lean text carries the expected declarations and proof steps
     (transcription guards): the `Int.floor` round-to-nearest argument,
     the consumer `frozenStripHypothesis_of_certified_nodes` with the
     101-node hypothesis, and its call into the 2312 corner consumer.

Controls run in the same pass: a synthetic-text regex probe; a
shifted-grid rejection (nodes shifted by 6e-3, just above the covering
radius, break coverage at the window endpoint); a short-grid rejection
(100 nodes fail to cover `sigma = 1/2`); and a tight-bound rejection
(bound 1/1000 below the exact sup).  Writes
`results/2313_grid_sampling_lean_pin.json`; exit code 1 on any failure.
"""
import hashlib
import json
import re
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
LEAN_GRID = ROOT / 'ConnesWeilRH/Dev/C1RouteAGridSampling.lean'
LEAN_PROBE = ROOT / 'ConnesWeilRH/Dev/C1RouteAGridSamplingProbe.lean'
LEAN_ARITH = ROOT / 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean'
LEAN_TRANSFER = ROOT / 'ConnesWeilRH/Dev/C1RouteAStripTransfer.lean'
ENVELOPE_2303 = ROOT / 'results/2303_corrected_strip_envelope.json'
PIN_2312 = ROOT / 'results/2312_strip_transfer_lean_pin.json'
OUT = ROOT / 'results/2313_grid_sampling_lean_pin.json'

SIGMA_TOL = 1e-12                       # sigma render vs exact j/100

STMT_LO = re.compile(
    r'∃ j : ℤ, -\((\d+) : ℤ\) ≤ j ∧ j ≤ (\d+) ∧')
STMT_DEN = re.compile(
    r'\|σ - \(j : ℝ\) / (\d+)\| ≤ stripHalfStep2303')
HNODE_RANGE = re.compile(
    r'hnode : ∀ j : ℤ, -\((\d+) : ℤ\) ≤ j → j ≤ (\d+) →')
H_DEF = re.compile(r'def\s+stripHalfStep2303\s*:\s*Real\s*:=\s*(\S+)')


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def parse_statement_geometry(text):
    lo = STMT_LO.search(text)
    den = STMT_DEN.search(text)
    if not lo or not den:
        raise ValueError('grid-sampling statement geometry not found')
    return {'j_lo': int(lo.group(1)), 'j_hi': int(lo.group(2)),
            'den': int(den.group(1))}


def parse_node_range(text):
    m = HNODE_RANGE.search(text)
    if not m:
        raise ValueError('consumer node range not found')
    return {'j_lo': int(m.group(1)), 'j_hi': int(m.group(2))}


def covering_sup(j_lo, j_hi, den, shift=Fraction(0)):
    """Exact sup of distance-to-nearest-node over the window
    `[-1/2, 1/2]`, as a discrete certificate: the distance function is
    piecewise linear with breakpoints at the nodes and their midpoints,
    so its sup over the window is attained on the window endpoints, the
    node points and the midpoints inside the window."""
    nodes = [Fraction(j, den) + shift for j in range(j_lo, j_hi + 1)]
    lo, hi = Fraction(-1, 2), Fraction(1, 2)
    pts = [lo, hi]
    pts.extend(n for n in nodes if lo <= n <= hi)
    for k in range(len(nodes) - 1):
        mid = (nodes[k] + nodes[k + 1]) / 2
        if lo <= mid <= hi:
            pts.append(mid)
    return max(min(abs(p - n) for n in nodes) for p in pts)


def covering_ok(j_lo, j_hi, den, bound, shift=Fraction(0),
                drop_last=False):
    hi = j_hi - 1 if drop_last else j_hi
    return covering_sup(j_lo, hi, den, shift) <= bound


def main():
    failures = []
    controls = {}

    grid_text = LEAN_GRID.read_text(encoding='utf-8')
    geom = parse_statement_geometry(grid_text)
    hnode = parse_node_range(grid_text)

    # control 1: synthetic-text regex probe
    synthetic = (r'∃ j : ℤ, -(60 : ℤ) ≤ j ∧ j ≤ 60 ∧' '\n'
                 r'|σ - (j : ℝ) / 120| ≤ stripHalfStep2303' '\n'
                 r'hnode : ∀ j : ℤ, -(60 : ℤ) ≤ j → j ≤ 60 →')
    synth_geom = parse_statement_geometry(synthetic)
    synth_hnode = parse_node_range(synthetic)
    controls['synthetic_parse'] = {
        'stmt': synth_geom, 'hnode': synth_hnode,
        'ok': synth_geom == {'j_lo': 60, 'j_hi': 60, 'den': 120} and
              synth_hnode == {'j_lo': 60, 'j_hi': 60}}
    if not controls['synthetic_parse']['ok']:
        failures.append('synthetic parse control failed')

    # reference values from the certified artifact
    artifact = json.loads(ENVELOPE_2303.read_text(encoding='utf-8'))
    grid = artifact['grid']
    rows = artifact['grid_rows']
    nodes = grid['sigma_nodes']
    half_render = Fraction(str(grid['half_step']))
    js = [r['j'] for r in rows]
    design = Fraction(1, 2 * (nodes - 1))

    # check 1: Lean statement geometry vs the committed grid
    geom_ok = (geom['j_lo'] == 50 and geom['j_hi'] == 50 and
               geom['den'] == 100)
    if not geom_ok:
        failures.append('Lean statement geometry differs from 50/50/100')
    rows_ok = (len(rows) == nodes == 101 and
               js == list(range(-geom['j_lo'], geom['j_hi'] + 1)))
    if not rows_ok:
        failures.append('committed grid_rows do not match the Lean nodes')
    node_member_ok = (hnode['j_lo'] == geom['j_lo'] and
                      hnode['j_hi'] == geom['j_hi'])
    if not node_member_ok:
        failures.append('consumer node range differs from the statement')
    sigma_max_diff = 0.0
    for r in rows:
        diff = abs(float(r['sigma']) - float(Fraction(r['j'], geom['den'])))
        sigma_max_diff = max(sigma_max_diff, diff)
    sigma_ok = sigma_max_diff <= SIGMA_TOL
    if not sigma_ok:
        failures.append('sigma renders differ from exact j/100')

    # check 2: half-step pin equals the exact design value and render
    h_def = H_DEF.search(LEAN_ARITH.read_text(encoding='utf-8'))
    if not h_def:
        raise ValueError('stripHalfStep2303 definition not found')
    half_pin = Fraction(h_def.group(1))
    half_ok = half_pin == design == half_render == Fraction(1, 200)
    if not half_ok:
        failures.append('half-step pin differs from the design value')

    # check 3: the covering-radius claim in exact arithmetic
    sup_quarter = covering_sup(-geom['j_lo'], geom['j_hi'], geom['den'])
    cover_ok = sup_quarter == design == half_pin
    if not cover_ok:
        failures.append('covering radius differs from the design half-step')

    # controls: the covering predicate must fail on broken grids
    shifted = covering_ok(-50, 50, 100, Fraction(1, 200),
                          shift=Fraction(6, 1000))
    short = covering_ok(-50, 50, 100, Fraction(1, 200), drop_last=True)
    tight = covering_ok(-50, 50, 100, Fraction(1, 1000))
    good = covering_ok(-50, 50, 100, Fraction(1, 200))
    controls['covering_predicate'] = {
        'accepts_design': good, 'rejects_shift_6e3': not shifted,
        'rejects_short_grid': not short, 'rejects_tight_bound': not tight,
        'ok': good and not shifted and not short and not tight}
    if not controls['covering_predicate']['ok']:
        failures.append('covering predicate controls failed')

    # check 4: record 2312 files byte-frozen across records
    frozen_ok = None
    frozen = {}
    if PIN_2312.exists():
        pin2312 = json.loads(PIN_2312.read_text(encoding='utf-8'))
        prov = pin2312.get('provenance', {})
        frozen = {
            'arith_recorded': prov.get('lean_arithmetic', {}).get('md5'),
            'arith_live': md5(LEAN_ARITH),
            'transfer_recorded': prov.get('lean_transfer', {}).get('md5'),
            'transfer_live': md5(LEAN_TRANSFER)}
        frozen_ok = (frozen['arith_recorded'] == frozen['arith_live'] and
                     frozen['transfer_recorded'] == frozen['transfer_live'])
        if not frozen_ok:
            failures.append('record 2312 files changed since their pin '
                            'artifact (hash continuity broken)')

    # check 5: transcription guards on the Lean source
    guards = {
        'sampling_theorem':
            'theorem gridSample2303 (σ : ℝ) (hσ : σ ∈ Set.Icc '
            '(-(1 / 2) : ℝ) (1 / 2)) :' in grid_text,
        'statement_shape':
            '∃ j : ℤ, -(50 : ℤ) ≤ j ∧ j ≤ 50 ∧' in grid_text and
            '|σ - (j : ℝ) / 100| ≤ stripHalfStep2303 := by' in grid_text,
        'floor_round':
            '⌊σ * 100 + 1 / 2⌋' in grid_text,
        'floor_lower': 'rw [Int.le_floor]' in grid_text,
        'floor_upper': 'rw [Int.floor_le_iff]' in grid_text,
        'floor_bounds':
            'Int.floor_le _' in grid_text and
            'Int.lt_floor_add_one _' in grid_text,
        'nearest_half':
            'abs_le.mpr ⟨by linarith, by linarith⟩' in grid_text,
        'abs_rewrite':
            'rw [hrw, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 100)]'
            in grid_text,
        'pin_norm_num':
            'norm_num [stripHalfStep2303]' in grid_text,
        'consumer_theorem':
            'theorem frozenStripHypothesis_of_certified_nodes '
            '(b c : CompactLogTest)' in grid_text,
        'consumer_node_hypothesis':
            'hnode : ∀ j : ℤ, -(50 : ℤ) ≤ j → j ≤ 50 →' in grid_text and
            'min (stripSecondNorm ((j : ℝ) / 100) (b.test : ℝ → ℂ) *'
            in grid_text,
        'consumer_corner_call':
            'frozenStripHypothesis_of_certified_grid_rmax b c htsupp_b '
            'htsupp_c' in grid_text,
        'consumer_sampling_call':
            'gridSample2303 σ hσ' in grid_text and
            'hnode j hjlo hjhi' in grid_text,
        'candidate_open':
            'open ConnesWeilRH.Source.C1RouteAItem5Arithmetic' in grid_text,
        'probe_axioms':
            '#print axioms gridSample2303' in
            LEAN_PROBE.read_text(encoding='utf-8') and
            '#print axioms frozenStripHypothesis_of_certified_nodes' in
            LEAN_PROBE.read_text(encoding='utf-8'),
    }
    for key, ok in guards.items():
        if not ok:
            failures.append(f'Lean transcription guard failed: {key}')

    payload = {
        'record': 2313, 'mode': 'check',
        'verdict': ('PINNED-GRID-SAMPLING-VERIFIED' if not failures
                    else 'FAILED'),
        'geometry': {
            'lean_statement': geom, 'lean_consumer': hnode,
            'artifact_sigma_nodes': nodes,
            'artifact_j_range': [js[0], js[-1]] if js else None,
            'artifact_rows_contiguous_ok': rows_ok,
            'sigma_render_max_diff': sigma_max_diff,
            'sigma_render_ok': sigma_ok,
            'node_member_ok': node_member_ok,
        },
        'half_step': {
            'lean_literal': h_def.group(1),
            'design_value': str(design),
            'artifact_render': float(half_render),
            'ok': half_ok,
        },
        'covering_radius': {
            'sup_window_distance': str(sup_quarter),
            'design_value': str(design),
            'lean_bound_target': 'stripHalfStep2303',
            'ok': cover_ok,
        },
        'cross_record_frozen': {
            'computed': frozen, 'ok': frozen_ok,
            'note': 'record 2312 module and arithmetic module hashes '
                    'equal the record 2312 pin-artifact provenance',
        },
        'lean_guards': guards,
        'controls': controls,
        'provenance': {
            'lean_grid_sampling': {
                'path': 'ConnesWeilRH/Dev/C1RouteAGridSampling.lean',
                'md5': md5(LEAN_GRID)},
            'lean_probe': {
                'path': 'ConnesWeilRH/Dev/C1RouteAGridSamplingProbe.lean',
                'md5': md5(LEAN_PROBE)},
            'envelope_artifact': 'results/2303_corrected_strip_envelope.json',
            'pin_2312_artifact': 'results/2312_strip_transfer_lean_pin.json',
            'render_convention': 'artifact sigmas are float64 renders of '
                                 'the design nodes j/100; design values are '
                                 'compared in exact rationals',
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'verdict': payload['verdict'],
                      'geometry': geom,
                      'sup_window_distance': str(sup_quarter),
                      'half_ok': half_ok,
                      'frozen_ok': frozen_ok,
                      'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()