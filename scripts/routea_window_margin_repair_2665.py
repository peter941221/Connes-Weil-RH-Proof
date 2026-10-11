"""2665 M1: window-charge margin re-measurement on the repaired coefficients.

Preregistration (AGENTS section 3 discipline):
  consumer : healthy selected detector producer margin. The gap pair is
             closed in Lean (2310 hgap_of_certified_split: window 477248.99 +
             tail <= 1e7, margin 20.953x) but on the CAPTURED coefficients,
             which record 2337 excluded from the mandatory targets. The strip
             side was already re-measured on the repaired pair by record 2340
             (101/101 nodes under the pin). This probe covers the window side
             plus monotone screens for hmargin/hcharge-rest.
  owner    : the SAME 30-family corrected a^2 basis (2275 capture: nodes,
             widths, modulations) with the 2338 ideal coefficient pair
             (exact interpolation repair). Pipeline object = the float64
             realization of the repaired pair; the exact-to-float cast is
             charged by the certified homogeneity multiplier (1 + eps_cast).
  premise  : "the certified window margin survives the repair" -- currently
             unverified (measured only on captured coefficients).
  decision : treatment window charge at STEP_DENOM = 256, inflated by
             (1 + eps_cast), <= budget 1e7 with stated margin => premise
             removed at measurement grade. Otherwise => named no-go:
             WINDOW-MARGIN-REPAIR-FAIL on this owner.
  controls : C1 same-run control (captured coefficients, unpatched loader)
             must reproduce the committed 2309 denom-256 charge
             477248.9858117574 (same-run reprice law); C2 run_grid's
             inherited order-0 bitwise + sandwich controls; C3 eps_cast
             computed exactly from Fraction midpoints of the 2338 balls.
  disclosure: inputs['radii'] remain the captured-owner 2302 object radii
             (they over-cover: the coefficient-storage slot prices a stored
             float that this run does not use); no radii term is loosened.
"""
import json
import sys
import time
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / 'scripts'))

import mpmath as mp  # noqa: E402

import routea_hgap_transform_cert_2309 as rig  # noqa: E402
import routea_direct_functional_difference_screen_2295 as direct2295  # noqa: E402

BUDGET = Fraction(10) ** 7
COMMITTED_2309_DEN256 = Fraction('477248.9858117574')
DENOM = 256
REPAIR = ROOT / 'results/2338_exact_interpolation_repair.json'


def coefficient_mid_fraction(ball):
    parts = {}
    for component in ('real', 'imag'):
        slot = ball[component]
        low = Fraction(slot['lower_exact'])
        high = Fraction(slot['upper_exact'])
        if not low <= high:
            raise ValueError('invalid coefficient ball ' + component)
        parts[component] = (low + high) / 2
    return parts


def eps_cast_exact(rows):
    worst = Fraction(0)
    for row in rows:
        for channel in ('ideal_base_coefficient', 'ideal_correction_coefficient'):
            parts = coefficient_mid_fraction(row[channel])
            for component in ('real', 'imag'):
                mid = parts[component]
                if mid == 0:
                    continue
                rounding = abs(Fraction(float(mid)) - mid)
                worst = max(worst, rounding / abs(mid))
    return worst


def repaired_arrays(rows):
    base, corr = [], []
    for row in rows:
        for target, channel in ((base, 'ideal_base_coefficient'),
                                (corr, 'ideal_correction_coefficient')):
            parts = coefficient_mid_fraction(row[channel])
            target.append(complex(float(parts['real']), float(parts['imag'])))
    return base, corr


def main():
    started = time.time()
    mp.mp.dps = mp.iv.dps = 80  # the rig's own main() convention
    repair = json.loads(REPAIR.read_text())
    rows = repair['coefficient_rows']
    eps_cast = eps_cast_exact(rows)
    base_rep, corr_rep = repaired_arrays(rows)
    print('eps_cast =', float(eps_cast), flush=True)

    # C1 control: unpatched loader, same process. Captured coefficient
    # arrays for the rmax screen come straight from the original loader.
    capture, families, base_cap, corr_cap = direct2295.filon.load_owner()
    control_inputs = rig.grid_inputs()
    if control_inputs['families'] != families:
        raise SystemExit('loader value drift between calls')
    control_row = rig.run_grid(DENOM, control_inputs)
    control_charge = Fraction(str(control_row['charge_hi']))
    print('control charge_hi =', float(control_charge), flush=True)
    if control_charge < COMMITTED_2309_DEN256:
        raise SystemExit('C1 FAIL: control below the committed charge')
    control_drift = control_charge / COMMITTED_2309_DEN256 - 1
    if control_drift > Fraction(1, 10 ** 6):
        raise SystemExit('C1 FAIL: control drift ' + str(control_drift))

    # Treatment: swap in the repaired pair, keep families/capture.
    def load_owner_repaired():
        return capture, control_inputs['families'], base_rep, corr_rep

    direct2295.filon.load_owner = load_owner_repaired
    treatment_inputs = rig.grid_inputs()
    treatment_row = rig.run_grid(DENOM, treatment_inputs)
    treatment_charge = Fraction(str(treatment_row['charge_hi']))
    print('treatment charge_hi =', float(treatment_charge), flush=True)

    inflated = treatment_charge * (1 + eps_cast)
    ratio_budget = inflated / BUDGET
    margin = BUDGET - inflated
    survives = margin > 0

    # Monotone screens for hmargin (2249) and hcharge-rest (2109):
    # absolute-value majorants are multi-linear in |coefficients|, so the
    # repaired charge is bounded by (rmax)^2 x the captured charge with
    # rmax = max_i |c_rep,i| / |c_cap,i| over all 60 coefficient slots.
    def max_ratio(channel_rep, channel_cap):
        worst = Fraction(0)
        for rep, cap in zip(channel_rep, channel_cap):
            magnitude = abs(complex(cap))
            if magnitude == 0.0:
                continue
            worst = max(worst, abs(complex(rep)) / Fraction(magnitude))
        return worst

    r_base = max_ratio(base_rep, base_cap)
    r_corr = max_ratio(corr_rep, corr_cap)
    rmax = max(r_base, r_corr)

    hmargin = json.loads(
        (ROOT / 'results/2249_l1_enclosure_ledger.json').read_text()) \
        if (ROOT / 'results/2249_l1_enclosure_ledger.json').exists() else None
    screen = {'rmax_base': float(r_base), 'rmax_corr': float(r_corr),
              'rmax': float(rmax), 'rmax_squared': float(rmax * rmax),
              'hmargin_artifact_found': hmargin is not None}
    if hmargin is not None:
        for key in ('e_total', 'E_total', 'margin', 'margin_lo'):
            if key in hmargin:
                screen['hmargin_' + key] = hmargin[key]
        for key in ('e_total', 'E_total', 'margin', 'margin_lo'):
            if key in hmargin and isinstance(hmargin[key], (int, float)):
                screen.setdefault('hmargin_inflated_' + key,
                                  hmargin[key] * float(rmax * rmax))

    artifact = {
        'record': 2665,
        'status': 'WINDOW-MARGIN-SURVIVES-REPAIR' if survives
        else 'WINDOW-MARGIN-REPAIR-FAIL',
        'denom': DENOM,
        'budget': float(BUDGET),
        'committed_2309_den256': float(COMMITTED_2309_DEN256),
        'control_charge_hi': float(control_charge),
        'control_drift_vs_committed': float(control_drift),
        'eps_cast': float(eps_cast),
        'treatment_charge_hi': float(treatment_charge),
        'treatment_inflated': float(inflated),
        'treatment_vs_control': float(treatment_charge / control_charge - 1),
        'ratio_budget': float(ratio_budget),
        'margin': float(margin),
        'monotone_screens': screen,
        'timing_sec': time.time() - started,
        'producer_go': False,
        'rh_claim': False,
        'notes': [
            'radii kept at the captured-owner 2302 object radii (over-cover)',
            'verdict charge = treatment x (1 + eps_cast), certified homogeneity',
            'C1 control reproduced the committed charge in the same process',
        ],
        'provenance': {
            'repair': 'results/2338_exact_interpolation_repair.json',
            'committed': 'results/2309_hgap_transform_certified.json',
            'rig': 'scripts/routea_hgap_transform_cert_2309.py',
        },
    }
    out = ROOT / 'results/2665_window_margin_repair.json'
    out.write_text(json.dumps(artifact, indent=2) + '\n', encoding='utf-8')
    (ROOT / 'results/2665_window_repair_control_den{}.json'.format(DENOM)
     ).write_text(json.dumps(control_row, indent=2) + '\n', encoding='utf-8')
    (ROOT / 'results/2665_window_repair_treatment_den{}.json'.format(DENOM)
     ).write_text(json.dumps(treatment_row, indent=2) + '\n', encoding='utf-8')
    print(json.dumps({k: artifact[k] for k in (
        'status', 'control_charge_hi', 'treatment_charge_hi',
        'treatment_inflated', 'ratio_budget', 'margin',
        'treatment_vs_control', 'timing_sec')}, indent=2), flush=True)


if __name__ == '__main__':
    main()
