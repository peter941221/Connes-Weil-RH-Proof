#!/usr/bin/env python3
"""Record 2724: row-B seed-object screen -- the wired seed is the WRONG object.

Binding-route contract (core-progress gate form per the project route
rules in docs/map):

  consumer  : the three cardinal-sum pins of the stored row-B
              contradiction (`fourPointContradictionRowBStored2722F`,
              `...BStored2723`), whose seed argument is
              `explicitSeed storedRadius2722F storedHRadius2722F`;
  owner     : the same stored row-B lists (record 1980 builder,
              gamma_2 = 21.022039638771556, re = 0.55, N = 5);
  question  : the record-2722E residual list names one open leg --
              "explicitSeed identification for the model seed".  The
              2720/2722C certified constants (q*, C4*, C2*) were
              computed for the MODEL seed (`L_pow(s) = L1(s/2)^10`,
              seed0 = 3^10 = 59049, support +-10).  The wired pins
              quantify over `explicitSeed r hr = rescale bumpLogTest r
              hr` with r = storedRadius2722F, whose Laplace transform
              is `S(r*v)`, `S(w) = int e^{wx} T(2-|x|) dx`,
              `S(0) = 3` -- a DIFFERENT function.  Provable, or false?
  decision  : it is FALSE, not merely open.  Both seeds share the same
              base profile (`baseBump` is the inner-product bump
              instance `smoothTransition ((R-|x|)/(R-1))`, i.e.
              `T(2-|x|)`, the record-1980 `smooth_seed_raw` -- verified
              pointwise in this run), but the explicit seed evaluates it
              at `r*v` while the model seed evaluates `S(v/2)^10`.  The
              flat-1 plateau at |x| <= 1 makes the explicit transform
              grow like e^{2|Re w|} in the left half-plane; at the named
              cells the wired objects exceed their pins by astronomical
              factors.  This screen certifies the mismatch and FALSIFIES
              the wired C4/C2 pins at named cells with rigorous
              two-sided accounting (monotone-window lower bounds for the
              transition integrals, exact plateau terms, crude/IBP
              upper bounds, exact rational prefactors; no oscillatory
              quadrature anywhere);
  completion: the certified model-side constants re-anchor bitwise in
              the same run (2720/2722C engines), the model object
              passes the same pins through the same accounting, the
              explicit object overshoots at named cells with all
              controls green, and the verdict artifact + record land;
  budget    : one script, one artifact, no Lean build, no re-seed brick
              (named as record 2725);
  stop      : at the verdict.  Repair object = `poweredSeed`
              (`C1ExplicitSmoothSeed.lean`, `poweredSeed_laplaceAt`),
              which IS the model seed in Lean; re-seeding the stored
              row-B carrier at `poweredSeed` is record 2725.  No
              producer GO, no RH claim, map-103 freeze unchanged.

Note on pin shapes (verbatim from C1RowBStoredCapture2722F.lean): the
contract pin carries `64 <= |t|`; the C4 and C2 pins carry NO |t|
threshold and are falsified at |t| < 64.  The q pin is NOT touched here
(recorded as deferred; not needed for the verdict).

Sections
  S1  parse the Lean capture (storedTargets2722F / storedNodes2722F /
      storedY2722F / storedRadius2722F) as exact rationals; tie to the
      engine's record-1980 floats elementwise; parse the wired pin
      literals; tie the base profile to `smooth_seed_raw`;
  S2  the shared bump transform S: int_0^1 T = 1/2, S(0) = 3, engine
      tie against `make_powered_seed`;
  S3  certified model-side re-anchor in the same run (2720 D-table /
      scan_channel / q_star_at bitwise, 2722C tie, tail extension);
  S4  the object mismatch at the named cells (per-node term tables);
  S5  the falsifier margins and the robustness controls;
  S6  verdict + artifact.

Writes results/2724_seed_object_screen.json.
Usage: python3 scripts/screen_seed_object_2724.py
"""

import hashlib
import importlib.util
import json
import os
import re
import sys
import time
from fractions import Fraction

import mpmath as mp

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
T_START = time.time()

P3 = os.path.join(ROOT, "scripts", "p3_certified_strip_constants_2720.py")
P81 = os.path.join(ROOT, "scripts", "fourpoint_powered_seed_1981.py")
OP = os.path.join(ROOT, "scripts", "fourpoint_actual_owner_1980.py")
ART2720 = os.path.join(ROOT, "results", "2720_p3_certified_strip_constants.json")
ART2722C = os.path.join(ROOT, "results", "2722c_strip_transport_tie.json")
CAPTURE = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                       "C1RowBStoredCapture2722F.lean")
WIRE = os.path.join(ROOT, "ConnesWeilRH", "Dev",
                    "C1FourPointRowBWired2721.lean")
OUT = os.path.join(ROOT, "results", "2724_seed_object_screen.json")

BIGNUM = 10 ** 17  # wiredQ denominator
PAD = mp.mpf(10) ** -40

mp.mp.dps = 60

failures = []
checks = {}


def sha(p):
    with open(p, "rb") as fh:
        return hashlib.sha256(fh.read()).hexdigest()


def guard(name, ok, detail=""):
    checks[name] = bool(ok)
    if not ok:
        failures.append((name, str(detail)))
    print(("PASS " if ok else "FAIL ") + name
          + (" " + str(detail) if detail else ""))


def load(name, path):
    spec = importlib.util.spec_from_file_location(name, path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


# ---------------------------------------------------------------------------
# S1: parse the Lean capture as exact rationals; tie to the engine floats
# ---------------------------------------------------------------------------
ENTRY_RE = re.compile(
    r"⟨\(\((-?\d+) : ℝ\) / (\d+)\),\s*\(\((-?\d+) : ℝ\) / (\d+)\)⟩"
    r"|\((\d+) / (\d+) : ℂ\)"
    r"|\((\d+) : ℂ\)")


STMT_RE = re.compile(
    r"^(?:def |private def |noncomputable def |theorem |lemma |end\b)", re.M)


def def_block(text, header):
    """Region from a def header to the sooner of its closing brace (Finset
    literals) or the next top-level statement (lambda-valued defs).
    A `find` miss returns -1 and must be treated as absent, not as an
    index (a missed brace otherwise swallows the rest of the module)."""
    i = text.index(header)
    jbrace = text.find("}", i)
    m = STMT_RE.search(text, i + len(header) + 1)
    cands = [x for x in (jbrace if jbrace != -1 else None,
                         m.start() if m else None) if x is not None]
    j = min(cands) if cands else i + 4000
    return text[i:j]


COMPLEX_RE = re.compile(
    r"⟨\(\((-?\d+) : ℝ\) / (\d+)\),\s*\(\((-?\d+) : ℝ\) / (\d+)\)⟩")


def parse_complex_literals(btext):
    out = []
    for m in COMPLEX_RE.finditer(btext):
        out.append((Fraction(int(m.group(1)), int(m.group(2))),
                    Fraction(int(m.group(3)), int(m.group(4)))))
    return out


def parse_entries(btext):
    out = []
    for m in ENTRY_RE.finditer(btext):
        if m.group(1) is not None:
            out.append((Fraction(int(m.group(1)), int(m.group(2))),
                        Fraction(int(m.group(3)), int(m.group(4)))))
        elif m.group(5) is not None:
            out.append((Fraction(int(m.group(5)), int(m.group(6))),
                        Fraction(0)))
        else:
            out.append((Fraction(int(m.group(7))), Fraction(0)))
    return out


def frc(c):
    """Exact (re, im) Fraction pair of a stored binary64 complex."""
    return (Fraction(c.real), Fraction(c.imag))


cap_text = open(CAPTURE, encoding="utf-8").read()
targets_f = parse_entries(def_block(cap_text, "def storedTargets2722F"))
nodes_f = parse_entries(def_block(cap_text, "def storedNodes2722F"))
y_lits = parse_complex_literals(def_block(cap_text, "def storedY2722F"))
mrad = re.search(
    r"def storedRadius2722F : ℝ :=\s*\n\s*\(\((\d+) : ℝ\) / (\d+)\)", cap_text)
assert mrad is not None, "storedRadius literal not found"
radius_f = Fraction(int(mrad.group(1)), int(mrad.group(2)))
guard("S1.hradius_def_present", "theorem storedHRadius2722F" in cap_text)

guard("S1.targets_count", len(targets_f) == 8, str(len(targets_f)))
guard("S1.nodes_count", len(nodes_f) == 56, str(len(nodes_f)))
guard("S1.y_literals_count", len(y_lits) == 3, str(len(y_lits)))
guard("S1.targets_distinct", len(set(targets_f)) == len(targets_f))
guard("S1.nodes_distinct", len(set(nodes_f)) == len(nodes_f))
guard("S1.targets_subset_nodes", all(t in set(nodes_f) for t in targets_f))

TRIPLE = [(Fraction(1, 2), Fraction(0)), (Fraction(1), Fraction(0)),
          (Fraction(3, 2), Fraction(0))]
guard("S1.triple_in_targets", all(t in set(targets_f) for t in TRIPLE))
active_f = [y_lits[0], y_lits[1], y_lits[2]]
active_vals = [Fraction(1), Fraction(-1), Fraction(-1)]
guard("S1.actives_in_nodes", all(a in set(nodes_f) for a in active_f))
guard("S1.actives_distinct", len(set(active_f)) == 3)
im0 = active_f[0][1]
guard("S1.actives_same_height", all(a[1] == im0 for a in active_f))
guard("S1.actives_radius_inside", all(abs(a[1]) < radius_f for a in active_f))

RHO_F = active_f[0]
RHO_IM_F = RHO_F[1]

p3 = load("p3_2720", P3)
p81 = load("p81_1981", P81)
op = load("op_1980", OP)
row = p3.Row_(p3.CANDIDATES[1])
art = json.load(open(ART2720, encoding="utf-8"))
artc = json.load(open(ART2722C, encoding="utf-8"))
rowB = art["rows"][1]
cert = rowB["certified"]
assert rowB["gamma"] == 21.022039638771556 and rowB["N"] == 5

guard("S1.tie_rho_re", frc(row.rho)[0] == RHO_F[0], str(frc(row.rho)[0]))
guard("S1.tie_rho_im", frc(row.rho)[1] == RHO_IM_F, str(frc(row.rho)[1]))
guard("S1.tie_targets",
      sorted(map(str, (frc(z) for z in row.targets)))
      == sorted(map(str, targets_f)))
guard("S1.tie_base_nodes_eq_targets",
      sorted(map(str, (frc(z) for z in row.base_nodes)))
      == sorted(map(str, targets_f)))
guard("S1.tie_nodes",
      sorted(map(str, (frc(z) for z in row.owner)))
      == sorted(map(str, nodes_f)))
eng_active = [(frc(z), Fraction(int(v.real)))
              for z, v in zip(row.owner, row.values) if abs(v) > 0.5]
guard("S1.tie_actives",
      sorted((str(a), str(b)) for a, b in eng_active)
      == sorted((str(active_f[i]), str(active_vals[i])) for i in range(3)))

wsrc = open(WIRE, encoding="utf-8").read()
m_q = re.search(r"def wiredQRowB2721 : Real := ([^\n]+)", wsrc)
m_c4 = re.search(r"def wiredC4RowB2721 : Real := ([^\n]+)", wsrc)
m_c2 = re.search(r"def wiredC2RowB2721 : Real := ([^\n]+)", wsrc)
assert m_q and m_c4 and m_c2, "wired pin defs not found"
assert m_q.group(1).strip() == "26 / 10 ^ 17", m_q.group(1)
assert m_c4.group(1).strip() == "61000000", m_c4.group(1)
assert m_c2.group(1).strip() == "29000000", m_c2.group(1)
WQ = Fraction(26, BIGNUM)
WC4 = Fraction(61000000)
WC2 = Fraction(29000000)
guard("S1.wired_pins_parsed", WQ == Fraction(26, 10 ** 17))

# ---------------------------------------------------------------------------
# S2: the shared bump transform S(w) = int e^{wx} T(2-|x|) dx
# ---------------------------------------------------------------------------
TWO_PI = mp.mpf(2) * mp.pi
TINY = mp.mpf(10) ** -40


def Tval(y):
    """smoothTransition: 0 for y<=0, 1 for y>=1, logistic between."""
    y = mp.mpf(y)
    if y <= TINY:
        return mp.mpf(0)
    if y >= 1 - TINY:
        return mp.mpf(1)
    return mp.e ** (-1 / y) / (mp.e ** (-1 / y) + mp.e ** (-1 / (1 - y)))


def ramp_T(eps):
    return Tval(eps)


def ramp_T2(eps):
    t = Tval(eps)
    return t * t


def prof1(x):
    """baseBump profile: T(2-|x|)."""
    return Tval(2 - abs(mp.mpf(x)))


intT = mp.quad(lambda y: Tval(y), [0, 1])
guard("S2.int_T_half", abs(intT - mp.mpf(1) / 2) <= mp.mpf(10) ** -50,
      mp.nstr(intT, 20))
S0 = mp.quad(lambda x: prof1(x), [-2, -1, 1, 2])
guard("S2.S0_eq_3", abs(S0 - 3) <= mp.mpf(10) ** -40, mp.nstr(S0, 30))

# profile identity vs the record-1980 python profile (same-run tie)
worst_prof = 0.0
for xx in (0.0, 0.3, 1.0, 1.4, 1.8, 2.5):
    a = float(prof1(mp.mpf(xx)))
    b = float(op.smooth_seed_raw(xx))
    worst_prof = max(worst_prof, abs(a - b))
guard("S2.profile_tie_smooth_seed_raw", worst_prof <= 1e-12,
      "worst |diff| = %.3e" % worst_prof)
# support/plateau interface facts (instance-independent)
guard("S2.support_ball2", float(prof1(mp.mpf("2.0001"))) == 0.0)
guard("S2.plateau_one", float(prof1(mp.mpf("0.99"))) == 1.0)

LADDER = [mp.mpf(2) ** (-j) for j in range(0, 91)]  # 1 .. 2^-90


def S_bounds(w, ramp=ramp_T):
    """Rigorous lower/upper bounds of |S(w)| for
    S = int e^{wx} rho(x) dx with rho the flat-1-on-[-1,1] bump whose
    transitions on [1,2] / [-2,-1] follow `ramp` (monotone 0->1,
    ramp(0)=0).  Exact decomposition:
      P  = (e^w - e^{-w})/w                      (plateau, exact)
      R+ = e^{2w}  ev(+w),  ev(u) = int_0^1 e^{-u e} ramp(e) de
      R- = e^{-2w} ev(-w)
    For REAL w all three pieces are positive: S_lo = sum of certified
    positive lower bounds (no cancellation).  For complex w, modulus
    bounds: |S| >= |piece|_lo - (uppers of the other pieces)."""
    w = mp.mpc(w)
    if abs(w) < TINY * TINY:
        return mp.mpf(3) * (1 - TINY), mp.mpf(3) * (1 + TINY)
    wr, wi = w.real, w.imag
    aw = abs(w)
    real_w = abs(wi) < mp.mpf(10) ** -50

    def ev_lo(u, ramp):
        """Lower bound of |ev(u)| via monotone windows: on [d1,d2],
        |int| >= cos(|Im u| d2) * ramp(d1) * int_{d1}^{d2} e^{-Re(u) e} de
        (ramp(eps) >= ramp(d1) by monotonicity; phase amplitude <= |Im u| d2)."""
        ur, ui = mp.re(u), mp.im(u)
        best = mp.mpf(0)
        for j in range(len(LADDER) - 1):
            d1, d2 = LADDER[j + 1], LADDER[j]
            c = mp.cos(abs(ui) * d2)
            if c <= 0:
                continue
            if ur == 0:
                integ = d2 - d1
            elif ur > 0:
                integ = (mp.e ** (-ur * d1) - mp.e ** (-ur * d2)) / ur
            else:
                integ = (mp.e ** (-ur * d2) - mp.e ** (-ur * d1)) / (-ur)
            val = c * ramp(d1) * integ
            if val > best:
                best = val
        return best

    def ev_up(u):
        ur = mp.re(u)
        if abs(ur) < mp.mpf(10) ** -50:
            return mp.mpf(1)
        if ur > 0:
            return (1 - mp.e ** (-ur)) / ur
        return (mp.e ** (-ur) - 1) / (-ur)

    P = (mp.e ** w - mp.e ** (-w)) / w
    crude = 3 * mp.e ** (2 * abs(wr))
    ibp1 = 2 * mp.e ** (2 * abs(wr)) / aw
    S_up = min(crude, ibp1) * (1 + TINY)
    if real_w:
        P_lo = abs(P) * (1 - TINY)
        Rp_lo = mp.e ** (2 * wr) * ev_lo(w, ramp)
        Rm_lo = mp.e ** (-2 * wr) * ev_lo(-w, ramp)
        S_lo = (P_lo + Rp_lo + Rm_lo) * (1 - TINY)
        return S_lo, S_up
    P_up = (mp.e ** wr + mp.e ** (-wr)) / aw
    Rp_up = mp.e ** (2 * wr) * ev_up(w)
    Rm_up = mp.e ** (-2 * wr) * ev_up(-w)
    P_lo = abs(P) * (1 - TINY)
    Rp_lo = mp.e ** (2 * wr) * ev_lo(w, ramp)
    Rm_lo = mp.e ** (-2 * wr) * ev_lo(-w, ramp)
    S_lo = max(P_lo - Rp_up - Rm_up,
               Rp_lo - P_up - Rm_up,
               Rm_lo - P_up - Rp_up,
               mp.mpf(0)) * (1 - TINY)
    return S_lo, S_up


# engine tie: an INDEPENDENT mp.quad truth for S, containment of the truth
# inside my rigorous S-bounds, and the committed engine at the same points
# (make_powered_seed's transform(s) = S(s/2)^10).
seed_transform = p81.make_powered_seed()


def S_true(w):
    return mp.quad(lambda x: mp.e ** (mp.mpc(w) * x) * prof1(x),
                   [-2, -1, 1, 2])


for tag, w in (("half", mp.mpf("0.5")), ("one", mp.mpf(1)),
               ("neg3.5", mp.mpf("-3.5")),
               ("complex", mp.mpc("-1.2", "0.3"))):
    st = S_true(w)
    lo_w, up_w = S_bounds(w)
    guard("S2.containment_" + tag, lo_w <= abs(st) <= up_w,
          "lo = %s |S| = %s up = %s"
          % (mp.nstr(lo_w, 6), mp.nstr(abs(st), 6), mp.nstr(up_w, 6)))

for tag, w, s in (("half", mp.mpf("0.5"), 1.0), ("one", mp.mpf(1), 2.0)):
    truth = S_true(w) ** 10
    eng = complex(seed_transform(s)).real
    relc = abs(mp.mpf(eng) - truth.real) / abs(truth.real)
    guard("S2.engine_tie_" + tag, relc <= mp.mpf("1e-9"),
          "rel = %s" % mp.nstr(relc, 6))

# ---------------------------------------------------------------------------
# mp conversion of the exact literals
# ---------------------------------------------------------------------------


def to_mpc(z):
    return mp.mpc(mp.mpf(z[0].numerator) / mp.mpf(z[0].denominator),
                  mp.mpf(z[1].numerator) / mp.mpf(z[1].denominator))


targets_m = [to_mpc(z) for z in targets_f]
nodes_m = [to_mpc(z) for z in nodes_f]
RADIUS_M = mp.mpf(radius_f.numerator) / mp.mpf(radius_f.denominator)
RHO_IM_M = mp.mpf(RHO_IM_F.numerator) / mp.mpf(RHO_IM_F.denominator)


def ycurve(z_f):
    for a, v in zip(active_f, active_vals):
        if a == z_f:
            return v
    return Fraction(0)


def nodeprod(nodes_use, z, s):
    out = mp.mpc(1)
    for t in nodes_use:
        if t == z:
            continue
        out *= (t - s)
    return out


def active_terms(nodes_use_f, values_of, s_mp, kind, ramp=ramp_T,
                 r_scale=None):
    """Per-active-node terms with rigorous |L(v)| bounds.
    kind 'explicit': L(v) = S(r*v),  L(0) = 3;
    kind 'model'   : L(v) = S(v/2)^10, L(0) = 3^10."""
    nodes_use_m = nodes_m if nodes_use_f is nodes_f else targets_m
    r_use = RADIUS_M if r_scale is None else mp.mpf(r_scale)
    L0 = mp.mpf(3) if kind == "explicit" else mp.mpf(3) ** 10
    terms = []
    for z_f in nodes_use_f:
        y_f = values_of(z_f)
        if y_f == 0:
            continue
        z = to_mpc(z_f)
        c = (mp.mpf(y_f.numerator) / mp.mpf(y_f.denominator)) * \
            nodeprod(nodes_use_m, z, s_mp) / \
            (nodeprod(nodes_use_m, z, z) * L0)
        v = s_mp - z
        if kind == "explicit":
            lo, up = S_bounds(r_use * v, ramp)
            real_s = abs(mp.im(r_use * v)) < mp.mpf(10) ** -50
        else:
            lo, up = S_bounds(v / 2, ramp)
            lo, up = lo ** 10, up ** 10
            real_s = abs(mp.im(v)) < mp.mpf(10) ** -50
        terms.append({"z": [mp.nstr(z.real, 20), mp.nstr(z.imag, 20)],
                      "c_re": mp.nstr(c.real, 12), "c_im": mp.nstr(c.imag, 12),
                      "abs_c": mp.nstr(abs(c), 12),
                      "L_lo": mp.nstr(lo, 12), "L_up": mp.nstr(up, 12),
                      "real_S": bool(real_s),
                      "_c": c, "_lo": lo, "_up": up})
    return terms


def account(terms, weight):
    """Rigorous lower/upper of weight * |sum|.  Dominance for every term;
    plus, when every term's S is real, the projection scan:
    max over unit phases phi of the interval bound of Re(e^{-i phi} sum)."""
    lower = mp.mpf(0)
    for i, t in enumerate(terms):
        others = mp.mpf(0)
        for j, u in enumerate(terms):
            if i != j:
                others += abs(u["_c"]) * u["_up"]
        cand = abs(t["_c"]) * t["_lo"] - others
        if cand > lower:
            lower = cand
    if terms and all(t["real_S"] for t in terms):
        angles = [mp.arg(t["_c"]) for t in terms]
        angles += [2 * mp.pi * k / 24 for k in range(24)]
        for phi in angles:
            A = mp.mpf(0)
            B = mp.mpf(0)
            u_ph = mp.e ** (mp.mpc(0, -phi))
            for t in terms:
                kappa = mp.re(u_ph * t["_c"])
                if kappa >= 0:
                    A += kappa * t["_lo"]
                    B += kappa * t["_up"]
                else:
                    A += kappa * t["_up"]
                    B += kappa * t["_lo"]
            cand = A if A > 0 else (-B if B < 0 else mp.mpf(0))
            if cand > lower:
                lower = cand
    upper = mp.mpf(0)
    for t in terms:
        upper += abs(t["_c"]) * t["_up"]
    w = abs(mp.mpf(weight))
    return lower * w * (1 - PAD), upper * w * (1 + PAD)


# ---------------------------------------------------------------------------
# S3: certified model-side re-anchor in the same run (2722E E3/E4 pattern)
# ---------------------------------------------------------------------------
D, ctl = p3.certified_D_table()
guard("S3.D_table_controls", ctl[1] and ctl[2])
cb = p3.make_consts(row.base_nodes, [1.0] * len(row.base_nodes))
cc = p3.make_consts(row.owner, row.values)
sup_b, C4rep = p3.scan_channel(cb, 4, D)
sup_c, C2rep = p3.scan_channel(cc, 2, D)
q64rep = p3.q_star_at(cb, 64, D)


def rel(a, b):
    return abs(a - b) / max(abs(b), 1e-300)


guard("S3.anchor_C4_bitwise", rel(C4rep, cert["C4_star"]) == 0.0)
guard("S3.anchor_C2_bitwise", rel(C2rep, cert["C2_star_corr"]) == 0.0)
guard("S3.anchor_q_bitwise", rel(q64rep, cert["q_star_T64"]) == 0.0)
tie = {"C4_star": C4rep, "C4_pin": float(WC4), "C4_margin": float(WC4) - C4rep,
       "C2_star": C2rep, "C2_pin": float(WC2), "C2_margin": float(WC2) - C2rep,
       "q_star_T64": q64rep, "q_pin": float(WQ),
       "q_margin": float(WQ - Fraction(q64rep))}
guard("S3.tie_equals_2722C",
      all(tie[k] == artc["numeric_tie"][k] for k in tie),
      "same-run tie must equal the committed 2722C renders")
guard("S3.pin_q", Fraction(q64rep) <= WQ)
guard("S3.pin_C4", Fraction(C4rep) <= WC4)
guard("S3.pin_C2", Fraction(C2rep) <= WC2)
margins = {"C4_frac_of_pin": float(WC4 - Fraction(C4rep)) / float(WC4),
           "C2_frac_of_pin": float(WC2 - Fraction(C2rep)) / float(WC2),
           "q_frac_of_pin": float(WQ - Fraction(q64rep)) / float(WQ)}
print("S3 margins:", json.dumps(margins))

T0 = float(p3.TAIL_T)
TMAX = 1.0e7


def extend(consts, weight_p):
    t = T0
    mx = mp.mpf(0)
    vals = []
    while t < TMAX:
        t2 = min(t * 1.05, TMAX)
        v = mp.mpf(0)
        for sgn in (1, -1):
            _, vw = p3.cell_val(consts, float(t), float(t2), D, weight_p, sgn)
            v = max(v, vw)
        vals.append(v)
        mx = max(mx, v)
        t = t2
    return mx, vals


ext = {}
for nm, consts, wp, pin, key in [
        ("base_quartic", cb, 4, WC4, "base_quartic"),
        ("corr_quadratic", cc, 2, WC2, "corr_quadratic"),
        ("base_contract", cb, 0, WQ, "base_contract")]:
    mx, vals = extend(consts, wp)
    committed = artc["tail_extension"][key]["max_weighted_envelope"]
    guard("S3.tail_anchor_" + nm, rel(float(mx), committed) <= 1e-12,
          "rel=%.3e" % rel(float(mx), committed))
    guard("S3.tail_below_pin_" + nm, float(mx) <= float(pin))
    tail5 = vals[-6:]
    dec = all(tail5[i + 1] < tail5[i] for i in range(len(tail5) - 1))
    ratios = [float(tail5[i + 1] / tail5[i]) for i in range(len(tail5) - 1)]
    guard("S3.tail_decreasing_" + nm, dec)
    ext[nm] = {"max_weighted_envelope": float(mx),
               "vs_pin": float(mx) / float(pin),
               "last_ratios": ratios}

# ---------------------------------------------------------------------------
# S4/S5: the object mismatch and the falsifier at the named cells
# ---------------------------------------------------------------------------
CELLS = {
    "F1_base_t0.25": ("base", mp.mpc(0, mp.mpf(1) / 4), 4, WC4),
    "F2_corr_tImrho": ("corr", mp.mpc(0, RHO_IM_M), 2, WC2),
}
mismatch = {}
rob = {}

for cname, (chan, s_mp, wp, pin) in CELLS.items():
    nodes_use = targets_f if chan == "base" else nodes_f
    values_of = (lambda zf: Fraction(1)) if chan == "base" else ycurve
    wgt = (abs(mp.im(s_mp)) / TWO_PI) ** wp
    for kind in ("model", "explicit"):
        terms = active_terms(nodes_use, values_of, s_mp, kind)
        lo, up = account(terms, wgt)
        rec = {"channel": chan, "sigma": 0,
               "t": mp.nstr(mp.im(s_mp), 25),
               "weight": mp.nstr(wgt, 12),
               "active_terms": len(terms),
               "lower": mp.nstr(lo, 15), "upper": mp.nstr(up, 15),
               "pin": str(pin),
               "lower_over_pin": mp.nstr(lo / mp.mpf(pin), 8),
               "upper_over_pin": mp.nstr(up / mp.mpf(pin), 8),
               "terms": terms}
        mismatch[cname + "_" + kind] = rec
        print("S4 %s %s: lo=%s up=%s pin=%s" %
              (cname, kind, rec["lower"], rec["upper"], rec["pin"]))

for cname in CELLS:
    le = mp.mpf(mismatch[cname + "_explicit"]["lower"])
    um = mp.mpf(mismatch[cname + "_model"]["upper"])
    mismatch[cname + "_factor_lower_expl_over_upper_model"] = \
        mp.nstr(le / um, 10) if um > 0 else "inf"
    mismatch[cname + "_explicit_lower_over_upper"] = \
        mp.nstr(le / mp.mpf(mismatch[cname + "_explicit"]["upper"]), 10)

guard("S4.F1_model_below_C4pin",
      mp.mpf(mismatch["F1_base_t0.25_model"]["upper"]) <= mp.mpf(WC4))
guard("S4.F2_model_below_C2pin",
      mp.mpf(mismatch["F2_corr_tImrho_model"]["upper"]) <= mp.mpf(WC2))
guard("S4.F1_explicit_over_C4pin",
      mp.mpf(mismatch["F1_base_t0.25_explicit"]["lower"]) > mp.mpf(WC4))
guard("S4.F2_explicit_over_C2pin",
      mp.mpf(mismatch["F2_corr_tImrho_explicit"]["lower"]) > mp.mpf(WC2))

# robustness: t-slice on the base channel
for tstr in ("0.1", "0.5"):
    s_mp = mp.mpc(0, mp.mpf(tstr))
    wgt = (abs(mp.im(s_mp)) / TWO_PI) ** 4
    terms = active_terms(targets_f, lambda zf: Fraction(1), s_mp, "explicit")
    lo, _ = account(terms, wgt)
    rob["base_t" + tstr] = {"lower_over_pin": mp.nstr(lo / mp.mpf(WC4), 8)}
    guard("S5.robust_base_t" + tstr, lo > mp.mpf(WC4))

# ramp-shape control (squared logistic ramp)
terms = active_terms(targets_f, lambda zf: Fraction(1),
                     mp.mpc(0, mp.mpf(1) / 4), "explicit", ramp=ramp_T2)
lo2, _ = account(terms, (mp.mpf(1) / 4 / TWO_PI) ** 4)
rob["base_t0.25_ramp2_over_pin"] = mp.nstr(lo2 / mp.mpf(WC4), 8)
guard("S5.ramp_shape_control", lo2 > mp.mpf(WC4))

# window-ladder refinement (verdict + order-of-magnitude stability)
_keep = list(LADDER)
LADDER[:] = [mp.mpf(2) ** (-mp.mpf(j) / 2) for j in range(0, 181)]
terms = active_terms(targets_f, lambda zf: Fraction(1),
                     mp.mpc(0, mp.mpf(1) / 4), "explicit")
lo3, _ = account(terms, (mp.mpf(1) / 4 / TWO_PI) ** 4)
LADDER[:] = _keep
lo1 = mp.mpf(mismatch["F1_base_t0.25_explicit"]["lower"])
ratio = lo3 / lo1
rob["ladder_refine_ratio"] = mp.nstr(ratio, 8)
guard("S5.ladder_refine_stable",
      lo3 > mp.mpf(WC4) and mp.mpf(1) / 100 <= ratio <= 100)

# specificity control: the unrescaled bumpLogTest object (r = 1) must NOT fire
terms = active_terms(targets_f, lambda zf: Fraction(1),
                     mp.mpc(0, mp.mpf(1) / 4), "explicit", r_scale=1)
lo4, _ = account(terms, (mp.mpf(1) / 4 / TWO_PI) ** 4)
rob["base_t0.25_r1_over_pin"] = mp.nstr(lo4 / mp.mpf(WC4), 8)
guard("S5.r1_control_does_not_fire", lo4 <= mp.mpf(WC4))

# accounting sanity: lower <= upper on every recorded lane
for k, rec in mismatch.items():
    if not isinstance(rec, dict) or "lower" not in rec:
        continue
    guard("S5.order_" + k, mp.mpf(rec["lower"]) <= mp.mpf(rec["upper"]))

# ---------------------------------------------------------------------------
# S6: verdict + artifact
# ---------------------------------------------------------------------------
verdict = "SCREEN-CONTROL-FAIL" if failures else "SEED-OBJECT-MISMATCH"

payload = {
    "record": 2724,
    "name": "2724 row-B seed-object screen",
    "verdict": verdict,
    "lane": "map-103 reopen motion; resolves the 2722E residual "
            "'explicitSeed identification for the model seed'",
    "decision": "the identification is FALSE. The wired pins quantify "
                "the cardinal sums at seed = explicitSeed storedRadius "
                "(= rescale bumpLogTest, transform S(87.0719873 * v), "
                "L(0) = S(0) = 3), while the 2720/2722C certified "
                "constants were computed for the model seed "
                "(transform S(v/2)^10, L(0) = 3^10 = 59049, support "
                "+-10; the same object as Lean poweredSeed). The two "
                "objects share the base profile but differ by enormous "
                "factors at the named cells; the wired C4 and C2 pins "
                "are FALSIFIED there with rigorous two-sided "
                "accounting. The Lean repair object already exists: "
                "poweredSeed (C1ExplicitSmoothSeed.lean, "
                "poweredSeed_laplaceAt); the re-seed brick is record "
                "2725.",
    "mismatch": mismatch,
    "robustness": rob,
    "certified_model_side": {
        "anchors_rel": {"C4": rel(C4rep, cert["C4_star"]),
                        "C2": rel(C2rep, cert["C2_star_corr"]),
                        "q": rel(q64rep, cert["q_star_T64"])},
        "margins_frac_of_pin": margins,
        "tail_extension": ext,
    },
    "wired_pins": {"wiredQ": str(WQ), "wiredC4": str(WC4),
                   "wiredC2": str(WC2), "storedRadius": str(radius_f),
                   "storedRhoIm": str(RHO_IM_F)},
    "pin_shapes": {
        "hcontractPin": "|t| >= 64 -> ||card|| <= wiredQ  (NOT touched)",
        "hquarticPin": "(t/2pi)^4 * ||card_base|| <= wiredC4  "
                       "(no |t| threshold; falsified at t = 0.25)",
        "hquadraticPin": "(t/2pi)^2 * ||card_corr|| <= wiredC2  "
                         "(no |t| threshold; falsified at t = Im rho)",
    },
    "q_pin_status": "NOT directly falsified here: hcontractPin "
                    "quantifies |t| >= 64, where the monotone-window "
                    "lower bound does not reach (oscillation regime). "
                    "The premise set is unsatisfiable already through "
                    "the C4 and C2 pins.",
    "residuals_named": [
        "re-seed the stored row-B carrier/pins at poweredSeed (record "
        "2725): support radius drops from 5*(2r+1) ~= 875.7 to ~105 and "
        "the 2720/2722C constants apply to the actual pins' object",
        "hgate24: P5 gate sign on the carrier source test (RH core, "
        "map-103 frozen premise -- untouched)",
        "Lean-grade discharge of the three cardinal pins (unchanged)",
        "q-pin falsification at |t| >= 64 deferred (not needed for the "
        "verdict)",
    ],
    "wired_hypotheses_removed": 0,
    "map103_freeze_unchanged": True,
    "producer_GO": False,
    "rh_claim": False,
    "checks": checks,
    "failures": [list(f) for f in failures],
    "elapsed_s": round(time.time() - T_START, 2),
    "provenance": {
        "scripts/p3_certified_strip_constants_2720.py": sha(P3),
        "scripts/fourpoint_powered_seed_1981.py": sha(P81),
        "scripts/fourpoint_actual_owner_1980.py": sha(OP),
        "results/2720_p3_certified_strip_constants.json": sha(ART2720),
        "results/2722c_strip_transport_tie.json": sha(ART2722C),
        "ConnesWeilRH/Dev/C1RowBStoredCapture2722F.lean": sha(CAPTURE),
        "ConnesWeilRH/Dev/C1FourPointRowBWired2721.lean": sha(WIRE),
        "checker": sha(os.path.abspath(__file__)),
    },
}
with open(OUT, "w", encoding="utf-8", newline="\n") as fh:
    json.dump(payload, fh, indent=2, default=str)
    fh.write("\n")
print("wrote", os.path.basename(OUT))
print("VERDICT:", payload["verdict"], "failures:", len(failures))
if failures:
    for f in failures:
        print("  -", f)
    sys.exit(1)