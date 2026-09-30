"""Record 2317 pin check: the owner-nodes instantiation against the
committed owner-test, grid-sampling and node-value records.

The Lean module `ConnesWeilRH/Dev/C1RouteAOwnerNodes.lean` instantiates
the record 2313 consumer `frozenStripHypothesis_of_certified_nodes` with
the record 2315 packaged owner pair, leaving the record 2316 node table's
101-node bound as the single strip hypothesis:

    frozenStripHypothesis_of_owner_nodes
      (baseCoefficients corrCoefficients : Fin 30 → ℂ)
      (modulations : Fin 30 → ℝ)
      (hnode : ∀ j : ℤ, -50 <= j → j <= 50 →
        min (stripSecondNorm (j/100) (correctedPhysical base mods) *
             stripNorm (j/100) (correctedPhysical corr mods))
            (mirror) <= stripGridMax2303) :
      FrozenStripHypothesis (packaged base) (packaged corr)

This check machine-verifies:

  1. the record 2315 module and the record 2313 module are byte-frozen
     (their live md5s equal the md5s recorded in their pin artifacts);
  2. the record 2316 node-values artifact is byte-frozen from here on
     (live md5 equals the value frozen in this artifact), still carries
     verdict NODE-VALUES-CERTIFIED with `all_rows_at_most_pin`, and its
     101-node table is contiguous (j = -50..50, sigma = j/100) with the
     maximum at most the pinned `stripGridMax2303` parsed from the Lean
     source;
  3. the new module carries the expected statement and proof shape
     (transcription guards: statement fragments, the two tsupport calls,
     the two `_toFun` rewrites, the `exact hnode` close; files end with a
     trailing newline), and the probe prints the theorem's axioms;
  4. controls: a synthetic statement probe, a mutated constant in the
     module text must fail the shape guard, and a missing final newline
     must fail the newline guard.

Writes `results/2317_owner_nodes_lean_pin.json`; exit code 1 on any
failure.
"""
import hashlib
import json
import re
import struct
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / 'results'
LEAN_NODES = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerNodes.lean'
LEAN_PROBE = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerNodesProbe.lean'
LEAN_OWNER_TEST = ROOT / 'ConnesWeilRH/Dev/C1RouteAOwnerTest.lean'
LEAN_GRID = ROOT / 'ConnesWeilRH/Dev/C1RouteAGridSampling.lean'
LEAN_ARITH = ROOT / 'ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean'
PIN_2315 = R / '2315_owner_test_lean_pin.json'
PIN_2313 = R / '2313_grid_sampling_lean_pin.json'
NODES_2316 = R / '2316_node_values.json'
OUT = R / '2317_owner_nodes_lean_pin.json'

PIN_LITERAL = '2644542.8515'
NODES_2316_FROZEN = '07d3f9e5f59b8daa4b398e4322694205'

GM_DEF = re.compile(r'def\s+stripGridMax2303\s*:\s*Real\s*:=\s*(\S+)')
THEOREM = re.compile(r'theorem\s+frozenStripHypothesis_of_owner_nodes')


def md5(path):
    return hashlib.md5(path.read_bytes()).hexdigest()


def same(a, b):
    if a != a or b != b:
        return False
    return struct.pack('<d', a) == struct.pack('<d', b)


def statement_guards(text):
    return {
        'theorem_decl':
            'theorem frozenStripHypothesis_of_owner_nodes' in text,
        'params': '(baseCoefficients corrCoefficients : Fin 30 → ℂ)' in text
            and '(modulations : Fin 30 → ℝ)' in text,
        'hnode_binder':
            '(hnode : ∀ j : ℤ, -(50 : ℤ) ≤ j → j ≤ 50 →' in text,
        'hnode_min': 'min (stripSecondNorm ((j : ℝ) / 100)' in text,
        'hnode_base': '(correctedPhysical baseCoefficients modulations)' in text,
        'hnode_corr': '(correctedPhysical corrCoefficients modulations)' in text,
        'hnode_bound': '≤ stripGridMax2303)' in text,
        'conclusion':
            'FrozenStripHypothesis\n      (correctedPhysicalCompactLogTest '
            'baseCoefficients modulations)' in text
            and '(correctedPhysicalCompactLogTest corrCoefficients modulations) := by'
            in text,
        'call_consumer':
            'frozenStripHypothesis_of_certified_nodes _ _ ?_ ?_ ?_' in text,
        'tsupport_calls':
            text.count('correctedPhysicalCompactLogTest_tsupport_subset') >= 2,
        'toFun_rewrites':
            'correctedPhysicalCompactLogTest_toFun baseCoefficients modulations,'
            in text and
            'correctedPhysicalCompactLogTest_toFun corrCoefficients modulations]'
            in text,
        'close': 'exact hnode j hjlo hjhi' in text,
        'no_sorry': 'sorry' not in text and 'admit' not in text,
        'trailing_newline': text.endswith('\n'),
    }


def main():
    failures = []
    controls = {}

    text = LEAN_NODES.read_text(encoding='utf-8')
    probe = LEAN_PROBE.read_text(encoding='utf-8')
    arith_text = LEAN_ARITH.read_text(encoding='utf-8')

    m = GM_DEF.search(arith_text)
    if not m or m.group(1) != PIN_LITERAL:
        failures.append('stripGridMax2303 literal differs from the pin')
    pin = Fraction(PIN_LITERAL)

    # 1. upstream Lean modules byte-frozen
    pin2315 = json.loads(PIN_2315.read_text(encoding='utf-8'))
    test_recorded = pin2315.get('provenance', {}).get('lean_test', {}).get('md5')
    pin2313 = json.loads(PIN_2313.read_text(encoding='utf-8'))
    grid_recorded = pin2313.get('provenance', {}).get(
        'lean_grid_sampling', {}).get('md5')
    continuity = {
        'owner_test_recorded': test_recorded,
        'owner_test_live': md5(LEAN_OWNER_TEST),
        'grid_recorded': grid_recorded,
        'grid_live': md5(LEAN_GRID),
        'arith_from_2316': None, 'arith_live': md5(LEAN_ARITH),
    }
    if test_recorded != continuity['owner_test_live']:
        failures.append('record 2315 module changed since its pin artifact')
    if grid_recorded != continuity['grid_live']:
        failures.append('record 2313 module changed since its pin artifact')

    # 2. record 2316 node-values artifact frozen and consistent
    nodes = json.loads(NODES_2316.read_text(encoding='utf-8'))
    nodes_live = md5(NODES_2316)
    continuity['arith_from_2316'] = nodes.get('provenance', {}).get(
        'lean_arithmetic', {}).get('md5')
    if continuity['arith_from_2316'] != continuity['arith_live']:
        failures.append('arithmetic pins file changed since the 2316 record')
    if nodes_live != NODES_2316_FROZEN:
        failures.append('record 2316 node-values artifact changed bytes')
    if (nodes.get('verdict') != 'NODE-VALUES-CERTIFIED'
            or nodes.get('pin', {}).get('all_rows_at_most_pin') is not True
            or nodes.get('pin', {}).get('lean_literal') != PIN_LITERAL):
        failures.append('record 2316 node-values artifact lost its verdict')
    table = nodes.get('node_table', [])
    table_ok = (len(table) == 101 and
                all(row['j'] == j and same(row['sigma'], j / 100.0)
                    for j, row in zip(range(-50, 51), table)))
    max_B = max((row['B_point'] for row in table), default=0.0)
    if not table_ok:
        failures.append('record 2316 node table is not the 101-node grid')
    if not (Fraction(max_B) <= pin):
        failures.append('record 2316 node maximum exceeds the pin')

    # 3. statement and proof guards
    guards = statement_guards(text)
    guards['probe_axioms'] = \
        '#print axioms frozenStripHypothesis_of_owner_nodes' in probe
    for key, ok in guards.items():
        if not ok:
            failures.append(f'Lean transcription guard failed: {key}')

    # 4. controls
    synthetic = ('theorem frozenStripHypothesis_of_owner_nodes (x : ℝ) : '
                 'True := trivial\n')
    controls['synthetic_statement'] = {
        'regex_match': bool(THEOREM.search(synthetic)),
        'ok': bool(THEOREM.search(synthetic))}
    mutated = text.replace('≤ stripGridMax2303)',
                           '≤ bUpper2243)')
    controls['mutated_constant_rejected'] = {
        'mutated_differs': mutated != text,
        'guard_fails': not statement_guards(mutated)['hnode_bound'],
        'ok': (mutated != text
               and not statement_guards(mutated)['hnode_bound'])}
    no_newline = text[:-1] if text.endswith('\n') else text
    controls['missing_newline_rejected'] = {
        'guard_fails': not statement_guards(no_newline)['trailing_newline'],
        'ok': not statement_guards(no_newline)['trailing_newline']}
    for key, c in controls.items():
        if not c.get('ok'):
            failures.append(f'control failed: {key}')

    payload = {
        'record': 2317, 'mode': 'check',
        'verdict': 'PINNED-OWNER-NODES-VERIFIED' if not failures else 'FAILED',
        'scope': 'the record 2313 consumer instantiated with the record 2315 '
                 'packaged owner pair; the residual strip hypothesis is the '
                 'record 2316 node table\'s 101-node bound',
        'pin': {
            'lean_literal': m.group(1) if m else None,
            'nodes_2316_max_B_point': max_B,
            'nodes_2316_max_at_most_pin': bool(Fraction(max_B) <= pin),
            'node_table_rows': len(table),
        },
        'continuity': {**continuity, 'nodes_2316_live': nodes_live,
                       'nodes_2316_frozen': NODES_2316_FROZEN},
        'lean_guards': guards,
        'controls': controls,
        'provenance': {
            'lean_nodes': {'path': 'ConnesWeilRH/Dev/C1RouteAOwnerNodes.lean',
                           'md5': md5(LEAN_NODES)},
            'lean_probe': {'path': 'ConnesWeilRH/Dev/C1RouteAOwnerNodesProbe.lean',
                           'md5': md5(LEAN_PROBE)},
            'check_script': {'path': 'scripts/routea_owner_nodes_lean_pin_2317.py',
                             'md5': md5(Path(__file__))},
            'inputs': ['results/2315_owner_test_lean_pin.json',
                       'results/2313_grid_sampling_lean_pin.json',
                       'results/2316_node_values.json'],
        },
        'failures': failures,
    }
    OUT.write_text(json.dumps(payload, indent=2, allow_nan=False) + '\n',
                   encoding='utf-8')
    print(json.dumps({'verdict': payload['verdict'],
                      'max_B': max_B,
                      'rows': len(table),
                      'continuity_ok': test_recorded == continuity['owner_test_live']
                      and grid_recorded == continuity['grid_live'],
                      'failures': failures}, indent=2), flush=True)
    if failures:
        sys.exit(1)


if __name__ == '__main__':
    main()