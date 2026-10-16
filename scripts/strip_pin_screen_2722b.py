"""2722B - decision screen: can the record-2722A IBP-bridge TRIANGLE pins
close the wired row-B strip envelopes at pipeline grade?

Question settled (no open-ended computation):
  for the concrete row-B cardinal owners (record-1980/2720 model), the
  bridge corollaries reduce each wired strip premise to a scalar pin

      hquartic   :  e^B * ||base^(4)||_1           <= C4  = 61000000
      hquadratic :  e^B * ||correction^(2)||_1     <= C2  = 29000000
      hcontract  :  e^B * ||base^(K)||_1           <= q * 64^K, some K

  with B the common support radius of the cardinal time function
  (seed = f_tilde^{*10}, supp f_tilde = [-1,1], so B = 10).  L1 masses
  are bounded by the MIN over derivative splits across the ten seed
  factors, using the certified seed ladder D_k (record 2720 machinery,
  re-run in this same process to a deeper order) and the node-product
  polynomial coefficients at the stored binary64 nodes.

Verdict rule (pre-registered): a pin that fails by a huge margin at
every admissible order is a scoped NO-GO for the triangle-ladder
discharge of that wired premise at pipeline grade; the strip envelope
must then travel through the cancellation-preserving 2720 envelope
(the 2722C owner-identification duty).  A pass licenses the Lean
instantiation of the bridge corollary at that pin.

Writes results/2722b_strip_pin_screen.json.  Numeric screen only: no
Lean theorem, no producer GO, no map-103 reopening, no RH claim.
"""

import hashlib
import importlib.util
import json
import math
import os
import sys
import time
from pathlib import Path

import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

SMOKE = bool(os.environ.get("STRIP_PIN_SMOKE"))

T_START = time.time()


def _load(name, rel):
    spec = importlib.util.spec_from_file_location(name, ROOT / rel)
    assert spec is not None and spec.loader is not None
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


p3 = _load("p3_2720", "scripts/p3_certified_strip_constants_2720.py")

ART = json.load(open(ROOT / "results" / "2720_p3_certified_strip_constants.json"))
ROW_B = ART["rows"][1]
CAND_B = p3.CANDIDATES[1]
assert CAND_B["gamma"] == 21.022039638771556 and CAND_B["N"] == 5

SEED0 = 3 ** 10
SUPPORT_RADIUS = mp.mpf(10)          # supp(f_tilde^{*10}) = [-10, 10]
WIRED_Q = mp.mpf(26) / 10 ** 17
WIRED_C4 = mp.mpf(61000000)
WIRED_C2 = mp.mpf(29000000)
T_CONTRACT = 64
# ladder depth: corr pin at K=2 needs derivative order K + (owner-1) = 57
D_DEEP = 12 if SMOKE else 58         # certified ladder depth for this screen
# contract ladder spans every order priceable on the certified ladder:
# base term needs q = K + (targets-1) = K + 7 <= D_DEEP
K_CONTRACT_MAX = (4 if SMOKE else D_DEEP - 7)


def log(msg):
    print("[ %6.1fs ] %s" % (time.time() - T_START, msg), flush=True)


def _num(x):
    """JSON-safe rendering of an mpf: float where representable, else the
    mpmath decimal string (never a silent inf)."""
    if x is None:
        return None
    try:
        f = float(x)
    except (OverflowError, ValueError):
        return mp.nstr(x, 20)
    if math.isinf(f) and x != mp.inf:
        return mp.nstr(x, 20)
    return f


def build_row():
    row = p3.Row_(CAND_B)
    # same-run reproduction anchors against the committed 2720 artifact
    assert len(row.owner) == ROW_B["owner_cardinality"]
    assert abs(row.H - ROW_B["H"]) < 1e-9
    active = [z for z, v in zip(row.owner, row.values) if abs(v) > 0.5]
    assert len(active) == ROW_B["corr_active"]
    assert abs(row.radius - ROW_B["radius"]) < 1e-9
    return row


def certified_ladder():
    """Re-run the 2720 interval certification to depth D_DEEP and anchor
    the first 12 entries bitwise against the committed artifact."""
    old = p3.K_MAX
    p3.K_MAX = D_DEEP
    D, ctl = p3.certified_D_table()
    p3.K_MAX = old
    assert ctl[1] and ctl[2], "2720 internal ladder checks failed"
    committed = {int(k): v for k, v in ART["D_table"].items()}
    drift = {}
    for k in sorted(committed):
        rel = abs(mp.mpf(committed[k]) - D[k]) / mp.mpf(committed[k])
        drift[k] = float(rel)
    log("ladder: D_12=%.4e D_%d=%.4e, anchor drift max=%.3e"
        % (D[12], D_DEEP, D[D_DEEP], max(drift.values())))
    return D, drift


def seed_ladder_masses(D):
    """S[q] = ||seed^(q)||_1 bound, min over derivative splits across the
    ten identical convolution factors; a[j] = ||f_tilde^(j)||_1 = 2^j D_j
    (a[0] = mass 3).  Each factor split order must stay within the
    certified ladder depth."""
    a = [mp.mpf(3)] + [mp.mpf(2) ** j * D[j] for j in range(1, D_DEEP + 1)]
    NEG = mp.mpf("1e100000")
    S = [[None] * (D_DEEP + 1) for _ in range(11)]
    for q in range(D_DEEP + 1):
        S[0][q] = mp.mpf(1) if q == 0 else NEG
    for n in range(1, 11):
        for q in range(D_DEEP + 1):
            best = NEG
            for j in range(0, min(q, D_DEEP) + 1):
                cand = a[j] * S[n - 1][q - j]
                if cand < best:
                    best = cand
            S[n][q] = best
    return [S[10][q] for q in range(D_DEEP + 1)]


def term_bound(z, c_abs, nodes, K, S):
    """|| (P_z(D)[e^{z id} seed])^(K) ||_1 bound for one cardinal term,
    with P_z(X) = prod_{w != z} (X - w).  Uses P_z(D)[e^{z x} h]
    = e^{z x} P_z(D + z)[h], the binomial split of the K derivative, and
    the support weight e^{10 |Re z|}."""
    roots = [mp.mpc(z) - mp.mpc(w) for w in nodes if w != z]
    # coefficients of prod (X + r) : alpha[p] on X^p, p = 0..m
    poly = [mp.mpc(1)]
    for r in roots:
        old = poly + [mp.mpc(0)]          # pad so the top shift is defined
        poly = [old[0] * r] + [old[i - 1] + old[i] * r
                              for i in range(1, len(old))]
    m = len(poly) - 1
    acc = mp.mpf(0)
    for j in range(0, K + 1):
        binom = math.comb(K, j)
        zpow = abs(mp.mpc(z)) ** (K - j)
        inner = mp.mpf(0)
        for p in range(0, m + 1):
            q = j + p
            if q > D_DEEP:
                return None  # ladder exhausted: pin not priceable here
            inner += abs(poly[p]) * S[q]
        acc += binom * zpow * inner
    weight = mp.exp(SUPPORT_RADIUS * abs(mp.re(mp.mpc(z))))
    return c_abs * weight * acc


def pin(K, nodes, values, consts_map):
    """e^B * ||f^(K)||_1 triangle pin for the cardinal f."""
    total = mp.mpf(0)
    for z, y in zip(nodes, values):
        if abs(y) == 0.0:
            continue
        c_abs = consts_map[z]
        t = term_bound(z, c_abs, nodes, K, SEED_MASSES)
        if t is None:
            return None
        total += t
    return mp.exp(SUPPORT_RADIUS) * total


# structural selftest: prod(X+r) expansion against (X+1)(X+2) = 2 + 3X + X^2
_t = [mp.mpc(1)]
for _r in (mp.mpc(1), mp.mpc(2)):
    _old = _t + [mp.mpc(0)]
    _t = [_old[0] * _r] + [_old[i - 1] + _old[i] * _r for i in range(1, len(_old))]
assert _t == [mp.mpc(2), mp.mpc(3), mp.mpc(1)]

row = build_row()
D, anchor_drift = certified_ladder()
SEED_MASSES = seed_ladder_masses(D)
log("seed masses: S_2=%.4e S_4=%.4e S_11=%.4e S_%d=%.4e"
    % (SEED_MASSES[2], SEED_MASSES[4], SEED_MASSES[11],
       D_DEEP, SEED_MASSES[D_DEEP]))

# c_abs exactly as record 2720 make_consts (same formula, same pads)
def c_abs_of(nodes, values):
    table = {}
    for z, y in zip(nodes, values):
        if abs(y) == 0.0:
            continue
        Q = mp.mpc(1)
        for w in nodes:
            if w != z:
                Q = Q * mp.mpc(w.real - z.real, w.imag - z.imag)
        table[z] = mp.mpf(float(abs(y) / (abs(Q) * mp.mpf(SEED0)))) \
            * (1 + mp.mpf(10) ** -12)
    return table


base_consts = c_abs_of(row.base_nodes, [1.0] * len(row.base_nodes))
corr_consts = c_abs_of(row.owner, row.values)

# ---- pins -------------------------------------------------------------
pin_base_4 = pin(4, row.base_nodes, [1.0] * len(row.base_nodes), base_consts)
pin_corr_2 = pin(2, row.owner, row.values, corr_consts)
contract_rows = []
for K in range(0, K_CONTRACT_MAX + 1):
    pv = pin(K, row.base_nodes, [1.0] * len(row.base_nodes), base_consts)
    if pv is None:
        contract_rows.append({"K": K, "status": "ladder-exhausted"})
        continue
    budget = WIRED_Q * mp.mpf(T_CONTRACT) ** K
    contract_rows.append({"K": K, "pin": _num(pv), "budget": _num(budget),
                          "ratio": _num(pv / budget)})

checks = {
    "hquartic_base_K4": {
        "pin": _num(pin_base_4),
        "wired_C4": 61000000.0,
        "certified_C4_star_2720": ROW_B["certified"]["C4_star"],
        "ratio_pin_over_wired": _num(pin_base_4 / WIRED_C4),
    },
    "hquadratic_corr_K2": {
        "pin": _num(pin_corr_2),
        "wired_C2": 29000000.0,
        "certified_C2_star_2720": ROW_B["certified"]["C2_star_corr"],
        "ratio_pin_over_wired": (None if pin_corr_2 is None
                                 else _num(pin_corr_2 / WIRED_C2)),
    },
    "hcontract_base_ladder": contract_rows,
}
_ok = [x for x in contract_rows if "ratio" in x]
_mn = min(_ok, key=lambda x: x["ratio"])
checks["hcontract_base_ladder_summary"] = {"argmin_K": _mn["K"],
                                           "min_ratio": _mn["ratio"],
                                           "K_range_measured":
                                               [_ok[0]["K"], _ok[-1]["K"]]}

def verdict_pin(c, key):
    r = c[key]["ratio_pin_over_wired"]
    return "PASS" if (r is not None and r <= 1) else "FAIL"

min_contract = min((x["ratio"] for x in contract_rows if "ratio" in x),
                   default=None)
verdicts = {
    "hquartic": verdict_pin(checks, "hquartic_base_K4"),
    "hquadratic": verdict_pin(checks, "hquadratic_corr_K2"),
    "hcontract": ("PASS" if (min_contract is not None and min_contract <= 1)
                  else "FAIL"),
}
verdicts["lane"] = ("SCREEN-NO-GO-TRIANGLE-LADDER"
                    if all(v == "FAIL" for v in
                           [verdicts["hquartic"], verdicts["hquadratic"],
                            verdicts["hcontract"]])
                    else "MIXED-OR-PASS")

script_bytes = open(Path(__file__).resolve(), "rb").read()
out = {
    "record": "2722B",
    "date": "2026-10-16",
    "question": "triangle IBP-bridge pins vs wired row-B strip constants",
    "owner_model": "record-1980 builder via record-2720 Row_, row B "
                   "(gamma_2, N=5), support radius 10 (f_tilde^{*10})",
    "reproduction_anchors": {
        "owner_cardinality": len(row.owner),
        "base_target_count": len(row.base_nodes),
        "corr_active": sum(1 for v in row.values if abs(v) > 0.5),
        "H": row.H,
        "radius": row.radius,
        "D_table_anchor_max_relative_drift_vs_2720": max(
            anchor_drift.values()),
    },
    "ladder_depth": D_DEEP,
    "D_tail": {str(k): _num(D[k]) for k in
               ((4, 8, 12) if SMOKE else (12, 20, 30, 40, 57))},
    "seed_mass_tail": {str(k): _num(SEED_MASSES[k]) for k in
                      ((2, 4, 11) if SMOKE else (4, 12, 24, 40, 57))},
    "checks": checks,
    "verdicts": verdicts,
    "nonclaims": "numeric pipeline-grade screen only; no Lean theorem, "
                 "no wired hypothesis removed, no producer GO, no RH claim",
    "provenance": {
        "script": "scripts/strip_pin_screen_2722b.py",
        "script_sha256": hashlib.sha256(script_bytes).hexdigest(),
        "depends": {
            "results/2720_p3_certified_strip_constants.json": hashlib.sha256(
                open(ROOT / "results/2720_p3_certified_strip_constants.json",
                     "rb").read()).hexdigest(),
            "scripts/p3_certified_strip_constants_2720.py": hashlib.sha256(
                open(ROOT / "scripts/p3_certified_strip_constants_2720.py",
                     "rb").read()).hexdigest(),
        },
        "mp_dps": mp.mp.dps,
        "wall_seconds": time.time() - T_START,
    },
}

dest = ROOT / "results" / "2722b_strip_pin_screen.json"
if not SMOKE:
    with open(dest, "w", newline="\n") as f:
        json.dump(out, f, indent=2)
        f.write("\n")

log("verdicts: %s" % json.dumps(verdicts))
log("ratios: hquartic %s | hquadratic %s | hcontract min %s"
    % (checks["hquartic_base_K4"]["ratio_pin_over_wired"],
       checks["hquadratic_corr_K2"]["ratio_pin_over_wired"],
       min_contract))
log("SMOKE (no artifact written)" if SMOKE else "wrote %s" % dest)
