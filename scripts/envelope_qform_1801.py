#!/usr/bin/env python3
# envelope_qform_1801.py — record 1801
#
# The producer, exactly: the gate-matrix representation theorem
# (C1GateMatrixRepresentation, k=1 span) collapses the exit producer to
#
#     PRODUCER(rho)  <=>  exists g : OrbitG8Geometry rho g  AND  ICgate(g^2) <= 0.
#
# The span freedom is a re-parameterization of that single gate condition.
# The geometry is a FINITE interpolation system (targets + orbit sum -2 +
# ball zeros + minimal zeros + per-zero tail bookkeeping with free
# tailStart), so the solution space is A + (node-orthogonal perturbations W)
# through the correction slot:  W = e^{x/2}((base^{*k}) * dc),  the owner
# form is preserved for every lambda, and
#
#     q(lambda) = ICgate((A - lambda W)^2) = G_AA - 2*lambda*G_AB + lambda^2*G_BB.
#
# Measured here, per zero case:
#   - the 2x2 Gram (G_AA, G_AB, G_BB) on (pinned head A, node-orthogonal W),
#   - its definiteness (Delta = G_AB^2 - G_AA G_BB, eigenvalues),
#   - the lambda-window with q <= 0 (the producer certificate candidate),
#   - a random search over the nullspace family for min q_min,
#   - minimal node family vs strengthened family (extra off-line zeros).
#
# Instruments reused from the validated 1799 rig: +s Laplace (convolution =
# product), 1741 sigma-identity arch engine, committed prime term, E-E
# modulated basis, E-G constructed-zero base.  The gate = arch + finite
# prime faces (the 1799 readout convention).
#
# Scope / boundary (same as 1799): dyadic ball zero-control instantiated
# only on a finite strengthened list; tail conditions are per-zero
# bookkeeping (tailStart free, (3/4)^tailStart) and are NOT instantiated;
# RH not claimed either way.

import json
import math
import os
import time

import numpy as np
from scipy.interpolate import CubicSpline

LOGPI = math.log(math.pi)
LOG2 = math.log(2.0)
T0 = time.time()


def log(msg):
    print("[%7.1fs] %s" % (time.time() - T0, msg), flush=True)


LX = 8.0
DU = 5.0e-4
N = int(round(2 * LX / DU)) + 1
XG = -LX + np.arange(N) * DU
NF = 131072


def bump(c, center=0.0):
    f = np.zeros_like(XG)
    m = np.abs(XG - center) < c
    xm = (XG[m] - center) / c
    f[m] = np.exp(-1.0 / (1.0 - xm * xm))
    return f


def l2_normalize(f):
    return f / math.sqrt(DU * float(np.sum(np.abs(f) ** 2)))


def conv_off(a, b):
    ca = a if np.iscomplexobj(a) else a.astype(complex)
    cb = b if np.iscomplexobj(b) else b.astype(complex)
    full = DU * np.fft.ifft(np.fft.fft(ca, NF) * np.fft.fft(cb, NF))
    off = (N - 1) // 2
    return full[off: off + N]


# ------------------------------------------------- sigma engine (1741)

def psi_asym(z, M=7):
    w = 1.0 / (z * z)
    coeffs = [1.0 / 12.0, -1.0 / 120.0, 1.0 / 252.0, -1.0 / 240.0,
              1.0 / 132.0, -691.0 / 32760.0, 1.0 / 12.0]
    s = sum(coeffs[k] * w ** (k + 1) for k in range(M))
    return np.log(z) - 0.5 / z - s


def sigma_vec(om):
    z = 0.25 - 0.5j * np.asarray(om, dtype=complex)
    return LOGPI - psi_asym(z).real


def arch_sigma(F):
    Fp = np.zeros(NF, dtype=complex)
    Fp[:N] = F
    Fh = DU * np.fft.fft(Fp)
    xi = 2.0 * np.pi * np.fft.fftfreq(NF, d=DU)
    Fh = Fh * np.exp(2j * np.pi * xi * LX)      # grid offset phase
    dxi = 2.0 * np.pi / (NF * DU)
    om = 2.0 * np.pi * xi
    return complex(np.sum(sigma_vec(om) * Fh) * dxi).real


def profile_support_radius(F):
    m = np.max(np.abs(F))
    if m == 0.0:
        return 1.0
    idx = np.where(np.abs(F) > 1e-13 * m)[0]
    return float(min(max(abs(XG[idx[0]]), abs(XG[idx[-1]])) + 0.3, LX - 0.5))


def prime_sum(sp, S):
    n_max = int(math.floor(math.exp(S)))
    if n_max < 2:
        return 0.0, {}
    sieve = np.ones(n_max + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(n_max ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p:: p] = False
    total = 0.0
    terms = {}
    for p in range(2, n_max + 1):
        if sieve[p]:
            pk = p
            while pk <= n_max:
                v = complex(sp(math.log(pk))) + complex(sp(-math.log(pk)))
                t = math.log(p) / math.sqrt(pk) * v.real
                total += t
                terms[pk] = t
                pk *= p
    return total, terms


def gate_of(F):
    """ICgate face convention of 1799: arch sigma engine + finite primes."""
    S = profile_support_radius(F)
    arch = arch_sigma(F)
    psum, terms = prime_sum(CubicSpline(XG, F), S)
    return arch + psum, arch, psum, S, terms


# ------------------------------------------------------------ the owner

def build_owner(beta, gamma, cb, k):
    """1799 pinned owner (E-G constructed-zero base + E-E modulated basis)."""
    wb = cb / gamma
    mu = np.array([-0.45, -0.15, 0.15, 0.45])
    Amat = np.array([[math.exp(m * s) for m in mu] for s in (0.5, 1.0, 1.5)])
    cvec = np.linalg.svd(Amat)[2][-1]
    base = sum(cvec[j] * bump(wb, mu[j]) for j in range(4))
    base = base / math.sqrt(DU * float(np.sum(base ** 2)))

    def lap(f, s):
        return DU * complex(np.sum(f * np.exp(s * XG)))

    nodes = [complex(beta, gamma), complex(1.0 - beta, gamma),
             complex(beta, -gamma), complex(1.0 - beta, -gamma),
             complex(beta + 0.5, gamma)]
    targets = [1.0, -1.0, 0.0, 0.0, -1.0]
    bhk = [lap(base, s) ** k for s in nodes]

    mod = np.exp(-1j * gamma * XG)
    basis = [l2_normalize(bump(w, c)) * mod
             for (w, c) in [(0.35, -0.2), (0.35, 0.2), (0.5, 0.0)]] \
          + [l2_normalize(bump(w, c)) / mod
             for (w, c) in [(0.3, -0.15), (0.3, 0.15)]]
    M = np.array([[lap(ph, s) for ph in basis] for s in nodes])
    rhs = np.array([t / b for t, b in zip(targets, bhk)])
    al = np.linalg.solve(M, rhs)
    corr = sum(al[j] * basis[j] for j in range(5))

    T = corr
    for _ in range(k):
        T = conv_off(base, T)
    A = np.exp(XG / 2.0) * T          # the pinned head, g-level
    resid = max(abs(lap(T, s) - t) for t, s in zip(targets, nodes))

    u = complex(beta - 0.5, gamma)
    vs = [u, -np.conj(u), np.conj(u), -u]
    gh = {v: lap(A, v) for v in set(vs)}
    orbit_sum = complex(sum(np.conj(gh[-np.conj(v)]) * gh[v] for v in vs))

    G_AA, arch_AA, pr_AA, supp_AA, terms_AA = gate_of(
        conv_off(np.conj(A[::-1]), A))
    return {
        "wb": wb, "base": base, "T": T, "A": A, "nodes": nodes,
        "targets": targets, "vs": vs, "resid": float(resid),
        "orbit_sum": orbit_sum,
        "G_AA": G_AA, "arch_AA": arch_AA, "pr_AA": pr_AA,
        "supp_AA": supp_AA, "terms_AA": terms_AA,
    }


# ------------------------------------------- node-orthogonal perturbation

def dc_basis(gamma):
    """18 modulated correction-slot bumps (E-E law: modulation mandatory)."""
    out = []
    for sgn in (1, -1, 0):
        for w in (0.3, 0.5):
            for c in (-0.35, 0.0, 0.35):
                b = l2_normalize(bump(w, c))
                if sgn == 1:
                    b = b * np.exp(-1j * gamma * XG)
                elif sgn == -1:
                    b = b / np.exp(-1j * gamma * XG)
                out.append(b)
    return out


def condition_nodes(beta, gamma, extra_zeros):
    """Node conditions on dc, all at the T level.

    +s convention: L[base * dc](s) = L[base](s) L[dc](s)  (plain product),
    so preservation of the T-level targets L[T](s) = target pulls back to
    L[dc](s) = 0 at the SAME nodes s.  The orbit-vs conditions coincide
    with the targets (centered identity: v + 1/2 in vs for g = e^{x/2} T
    lands exactly on the target nodes).  The minimal/healthy nodes
    {0, 1/2, 1} (g level) hit the base zeros {1/2, 1, 3/2} where
    L[base^k] vanishes: structurally preserved, vacuous for dc.
    Strengthened family adds off-line zeros z: T-level nodes z + 1/2 and
    -conj(z) + 1/2 (the two square factors of L[g^2](z)).
    """
    ws = [complex(beta, gamma), complex(1.0 - beta, gamma),
          complex(beta, -gamma), complex(1.0 - beta, -gamma),
          complex(beta + 0.5, gamma)]
    for z in extra_zeros:
        ws.append(z + 0.5)
        ws.append(-np.conj(z) + 0.5)
    uniq = []
    for w in ws:
        if all(abs(w - v) > 1e-9 for v in uniq):
            uniq.append(w)
    return uniq


def build_W(own, dcvec):
    """W = e^{x/2} ((base^{*k}) * dc) — owner-form perturbation."""
    T = dcvec
    for _ in range(own["k"]):
        T = conv_off(own["base"], T)
    return T, np.exp(XG / 2.0) * T


def gram_probe(own, basis, dcnull, coeffs, ws_extra):
    """Build W from nullspace coefficients, verify preservation, return
    Gram cells + lambda feasibility.  dcnull lives in COEFFICIENT space
    (rows of V^t): the candidate coefficient vector is the nullspace
    combination, then the grid profile is assembled from the basis.
    Verification is at the T level: L[T_W](s) = 0 at the target nodes
    (exact algebra up to SVD noise), plus L[dc](w) = 0 at the extra
    strengthened nodes."""
    cv = np.zeros(len(basis), dtype=complex)
    for a, b in zip(coeffs, dcnull):
        cv = cv + a * np.asarray(b, dtype=complex)
    dc = np.zeros_like(XG, dtype=complex)
    for a, ph in zip(cv, basis):
        dc = dc + a * ph
    T_W, W = build_W(own, dc)

    def lap(f, s):
        return DU * complex(np.sum(f * np.exp(s * XG)))

    worst = 0.0
    for s in own["nodes"]:
        worst = max(worst, abs(lap(T_W, s)))
    for w in ws_extra:
        worst = max(worst, abs(lap(dc, w)))
    # orbit-sum preservation at a general lambda factors through the SAME
    # node values (orbit nodes v satisfy v + 1/2 = target node), so the
    # target-node check above is the preservation certificate; we still
    # spot-check the mixed orbit sum at lambda = 1 directly on T:
    T_mix = own["T"] - T_W
    orbit_sum_mix = complex(sum(
        np.conj(lap(T_mix, -np.conj(v) + 0.5)) * lap(T_mix, v + 0.5)
        for v in own["vs"]))
    F_BB = conv_off(np.conj(W[::-1]), W)
    F_AB = conv_off(np.conj(own["A"][::-1]), W)
    G_BB, arch_BB, pr_BB, supp_BB, _ = gate_of(F_BB)
    G_AB, _, _, supp_AB, _ = gate_of(F_AB)
    G_AA = own["G_AA"]
    disc = G_AB * G_AB - G_AA * G_BB
    if abs(G_BB) < 1e-14:
        lam_star, q_min = float("nan"), G_AA
    elif G_BB < 0:
        lam_star = math.sqrt(max(G_AA, 0.0) / (-G_BB))
        q_min = G_AA - 2 * lam_star * G_AB + lam_star * lam_star * G_BB
    else:
        lam_star = G_AB / G_BB
        q_min = G_AA - G_AB * G_AB / G_BB
    normW2 = DU * float(np.sum(np.abs(W) ** 2))
    return {
        "coeffs": [complex(a) for a in coeffs],
        "preserv_worst": float(worst),
        "orbit_sum_mix": orbit_sum_mix,
        "G_BB": G_BB, "G_AB": G_AB, "disc": disc,
        "arch_BB": arch_BB, "pr_BB": pr_BB,
        "supp_BB": supp_BB, "supp_AB": supp_AB,
        "normW2": normW2,
        "lam_star": lam_star, "q_min": q_min,
        "feasible": (worst < 1e-6) and (q_min <= 0.0),
    }


def main():
    log("record 1801 — envelope q-form feasibility (producer anatomy)")
    log("grid N=%d du=%.0e LX=%.1f NF=%d" % (N, DU, LX, NF))

    extra = [complex(0.5, g) for g in (21.022039638871587,
                                       25.010857580145689,
                                       30.424876125859513)]
    results = []
    for beta in (0.55, 0.6):
        for gamma in (14.13472514173497, 40.0):
            for (cb, k) in ((0.6, 1), (1.2, 2)):
                tag = "beta=%.4f gamma=%5.2f cb=%.1f k=%d" % (beta, gamma, cb, k)
                own = build_owner(beta, gamma, cb, k)
                own["beta"], own["gamma"], own["cb"], own["k"] = beta, gamma, cb, k
                if own["resid"] > 1e-6 or abs(own["orbit_sum"] + 2) > 1e-4:
                    log("%s | owner NOT admissible (resid=%.1e orb=%+.4f) — skip"
                        % (tag, own["resid"], own["orbit_sum"].real))
                    continue
                log("%s | owner OK resid=%.1e orbSum=%+.6f G_AA=%+.5f "
                    "(arch %+.5f + primes %+.5f)"
                    % (tag, own["resid"], own["orbit_sum"].real,
                       own["G_AA"], own["arch_AA"], own["pr_AA"]))

                fams = {}
                for famname, ez in (("minimal", []), ("strengthened", extra)):
                    ws = condition_nodes(beta, gamma, ez)
                    basis = dc_basis(gamma)
                    Mc = np.array([[DU * complex(np.sum(ph * np.exp(w * XG)))
                                    for ph in basis] for w in ws])
                    svals = np.linalg.svd(Mc, compute_uv=False)
                    _, _, Vt = np.linalg.svd(Mc)
                    tol = max(Mc.shape) * (svals[0] if len(svals) else 0) * 1e-9
                    rank = int(np.sum(svals > tol))
                    # numpy: M = U S Vh, so the right nullspace vectors are
                    # the CONJUGATES of the trailing Vh rows (M v = 0 with
                    # v = conj(Vh[i]) for i >= rank).
                    dcnull = [Vt[-(j + 1)].conj()
                              for j in range(len(basis) - rank)]
                    fams[famname] = {"ws": ws, "rank": rank,
                                     "dcnull": dcnull,
                                     "smin": float(svals[-1])}

                for famname, fam in fams.items():
                    dcnull = fam["dcnull"]
                    probes = []
                    rng = np.random.default_rng(1799)
                    cands = []
                    d = len(dcnull)
                    for j in range(min(d, 3)):
                        c = [0.0] * d
                        c[j] = 1.0
                        cands.append(c)
                    for _ in range(16):
                        z = rng.standard_normal(d) + 1j * rng.standard_normal(d)
                        z = z / np.linalg.norm(z)
                        cands.append(list(z))
                    for c in cands:
                        p = gram_probe(own, basis, dcnull, c, fam["ws"])
                        if p["preserv_worst"] < 1e-6:
                            probes.append(p)
                    if not probes:
                        log("%s %s | NO preservation-passing probe" % (tag, famname))
                        continue
                    gbb = [p["G_BB"] for p in probes]
                    best = min(probes, key=lambda p: p["q_min"])
                    feas = [p for p in probes if p["q_min"] <= 0.0]
                    log("%s %s | null dim=%d probes=%d "
                        "G_BB[min..max]=[%+.4e, %+.4e] "
                        "q_min best=%+.5e (lam*=%s) feasible=%d/%d"
                        % (tag, famname, len(dcnull), len(probes),
                           min(gbb), max(gbb), best["q_min"],
                           ("%.3f" % best["lam_star"])
                           if best["lam_star"] == best["lam_star"] else "nan",
                           len(feas), len(probes)))
                    results.append({
                        "beta": beta, "gamma": gamma, "cb": cb, "k": k,
                        "family": famname, "null_dim": len(dcnull),
                        "cond_rank": fam["rank"],
                        "G_AA": own["G_AA"], "arch_AA": own["arch_AA"],
                        "pr_AA": own["pr_AA"],
                        "orbit_sum": own["orbit_sum"].real,
                        "G_BB_min": min(gbb), "G_BB_max": max(gbb),
                        "G_BB_neg_count": int(sum(1 for x in gbb if x < 0)),
                        "q_min_best": best["q_min"],
                        "lam_star_best": best["lam_star"],
                        "feasible_count": len(feas),
                        "probes": [{
                            "G_BB": p["G_BB"], "G_AB": p["G_AB"],
                            "disc": p["disc"], "q_min": p["q_min"],
                            "lam_star": p["lam_star"],
                            "arch_BB": p["arch_BB"], "pr_BB": p["pr_BB"],
                            "normW2": p["normW2"],
                            "preserv": p["preserv_worst"],
                        } for p in probes],
                    })

    log("=" * 100)
    tot = sum(1 for r in results)
    feas = sum(r["feasible_count"] for r in results)
    neg = sum(r["G_BB_neg_count"] for r in results)
    nprobe = sum(len(r["probes"]) for r in results)
    log("SUMMARY: %d family-cases, %d probes, feasible(q_min<=0)=%d, "
        "G_BB<0 count=%d" % (tot, nprobe, feas, neg))
    if feas:
        best = min(results, key=lambda r: r["q_min_best"])
        log("BEST: beta=%.4f gamma=%.2f %s q_min=%+.6e lam*=%.4f"
            % (best["beta"], best["gamma"], best["family"],
               best["q_min_best"], best["lam_star_best"]))
    else:
        pd = all(r["q_min_best"] > 0 for r in results)
        log("VERDICT: no feasible direction in the measured family — "
            "positive-gate picture %s"
            % ("CONSISTENT (all q_min > 0)" if pd else "(some near-zero)"))

    os.makedirs("results", exist_ok=True)

    def flat(o):
        if isinstance(o, complex):
            return [o.real, o.imag]
        if isinstance(o, dict):
            return {kk: flat(vv) for kk, vv in o.items()}
        if isinstance(o, (list, tuple)):
            return [flat(vv) for vv in o]
        return o

    with open("results/1801_envelope_qform.json", "w") as fh:
        json.dump({"record": 1801, "cases": flat(results)}, fh,
                  indent=1, default=float)
    log("results → results/1801_envelope_qform.json")


if __name__ == "__main__":
    main()
