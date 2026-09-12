#!/usr/bin/env python3
"""CB-PD1 phase calculator (record 1373 prereg, MODEL evidence).

Implements EXACTLY the locked formulas of 1373 section 1. Mapping
instrument only: outputs are scoreboard entries over placeholder
constants, not candidate verdicts. Acceptance is the final DONE line.
"""
import json
import math
import sys

DS = [0.005, 0.01, 0.02, 0.05, 0.1, 0.2, 0.3, 0.45]
LGTS = [12, 20, 30, 40, 60, 100, 200, 1000]
NS = list(range(1, 9))
RHOS = [0.0, 0.5, 1.0]
BANDS = [(1, 3, 1), (3, 10, 10), (10, 30, 100)]
MS = [1, 3]
KLOC = 1.5 * 2.13
LN10 = math.log(10)
REF = dict(d=0.05, lgT=13, rho=0.0, band=(1, 3, 1), m=1)


def _exp_safe(x):
    return math.exp(x) if x > -700 else 0.0


def gain(d, lgT, n, rho, kloc=None):
    R = n + 2
    if kloc is None:
        kloc = KLOC
    # log(t0/(2*pi)) evaluated as lgT*ln(10) - ln(2*pi): identical formula,
    # log-domain so 10^1000 never materializes as a float.
    return math.exp(-2 * d * (1 + rho * (n + 1) * R)) * (lgT * LN10 - math.log(2 * math.pi)) / (2 * kloc * R)


def absorb(d, lgT, n, band):
    Cb, Cc, C8 = band
    log_a = (2 * math.log(Cc) + (2 * n + 2) * math.log(Cb)
             - (4 * n + 2) * lgT * LN10 - math.log(0.05 * (4 * n + 2)))
    return _exp_safe(log_a)


def r8err(d, lgT, n, band):
    Cb, Cc, C8 = band
    log_e = (math.log(C8) + math.log(1 + lgT * LN10) + 2 * math.log(Cc)
             + (2 * n + 2) * math.log(Cb) - (4 * n + 2) * lgT * LN10)
    return _exp_safe(log_e)


def ratio(d, lgT, n, rho, band, m, kloc=None):
    return (gain(d, lgT, n, rho, kloc) - absorb(d, lgT, n, band)
            - r8err(d, lgT, n, band)) / (2 * m)


def band_of(r):
    if r >= 1.0:
        return "PASS"
    if r >= 0.8:
        return "MARGINAL"
    return "OPEN"


def best_n(d, lgT, rho, band, m):
    vals = [(ratio(d, lgT, n, rho, band, m), n) for n in NS]
    r, n = max(vals)
    return n, r


def main():
    results = {"prereg": "1373", "model": "CB-PD1 phase calculator", "evidence": "MODEL",
               "combos": [], "gates": {}}
    lines = []

    def say(s):
        lines.append(s)
        print(s, flush=True)

    say("CB-PD1 PHASE CALCULATOR - prereg 1373 - MODEL digits (law 65)")
    say("KLOC=%.6f  grids: d=%d lgT=%d n=%d rho=%d bands=%d m=%d"
        % (KLOC, len(DS), len(LGTS), len(NS), len(RHOS), len(BANDS), len(MS)))

    # ---- G2: gain monotonicity in lgT at reference cell ----
    g_vals = [gain(REF["d"], L, 1, REF["rho"]) for L in (12, 20, 30)]
    g2 = all(a < b for a, b in zip(g_vals, g_vals[1:]))
    say("G2 gain monotonicity ref cell: %s (%s)" % ("PASS" if g2 else "FAIL",
        ", ".join("%.6g" % g for g in g_vals)))
    results["gates"]["G2"] = "PASS" if g2 else "FAIL"

    # ---- G1: negative control (KLOC x10 must drop the band) ----
    # Reference cell re-locked by amendment 1374 s2: lgT=20 (run-1 used
    # lgT=13, whose baseline band was already OPEN; control cannot drop).
    d0, L0, m0, band0 = REF["d"], 20, REF["m"], REF["band"]
    n0, r0 = best_n(d0, L0, REF["rho"], band0, m0)
    vals_scaled = [(ratio(d0, L0, n, REF["rho"], band0, m0, kloc=10 * KLOC), n)
                   for n in NS]
    r0s, _ = max(vals_scaled)
    b0, b0s = band_of(r0), band_of(r0s)
    order = {"OPEN": 0, "MARGINAL": 1, "PASS": 2}
    g1 = order[b0] >= 1 and order[b0s] < order[b0]
    say("G1 negative control ref cell (lgT=20): base n=%d ratio=%.4f band=%s ; KLOCx10 ratio=%.4f band=%s -> %s"
        % (n0, r0, b0, r0s, b0s, "PASS" if g1 else "FAIL"))
    results["gates"]["G1"] = "PASS" if g1 else "FAIL"
    results["ref_cell"] = {"n": n0, "ratio": r0, "band": b0, "ratio_kloc10": r0s,
                           "band_kloc10": b0s}

    # ---- G3: bridge ordering over every cell ----
    g3 = True
    for d in DS:
        for L in LGTS:
            for band in BANDS:
                for m in MS:
                    seq = [best_n(d, L, rho, band, m)[1] for rho in RHOS]
                    if not (seq[0] >= seq[1] - 1e-12 and seq[1] >= seq[2] - 1e-12):
                        g3 = False
    say("G3 bridge ordering over all cells: %s" % ("PASS" if g3 else "FAIL"))
    results["gates"]["G3"] = "PASS" if g3 else "FAIL"

    # ---- G4 (informational) ----
    frac = {}
    for rho in RHOS:
        small = sum(1 for d in DS for L in LGTS for band in BANDS for m in MS
                    if best_n(d, L, rho, band, m)[0] <= 3)
        frac[rho] = small / (len(DS) * len(LGTS) * len(BANDS) * len(MS))
    say("G4 informational: argmax n<=3 fraction rho=0: %.3f rho=0.5: %.3f rho=1: %.3f"
        % (frac[0.0], frac[0.5], frac[1.0]))
    results["g4_fractions"] = {str(k): v for k, v in frac.items()}

    # ---- phase maps per combo ----
    for m in MS:
        for band in BANDS:
            for rho in RHOS:
                combo = "m=%d band=%s rho=%.1f" % (m, band, rho)
                say("COMBO %s" % combo)
                grid = {}
                for L in LGTS:
                    row = []
                    for d in DS:
                        n, r = best_n(d, L, rho, band, m)
                        row.append("%s(n=%d,%.2f)" % (band_of(r), n, r))
                        grid["%g|%d" % (d, L)] = {"band": band_of(r), "n": n, "ratio": round(r, 4)}
                    say("  lgT=%4d %s" % (L, " ".join("%16s" % x for x in row)))
                results["combos"].append({"combo": combo, "grid": grid})

    # ---- frontier + seam (headline combo: m=1, band=(1,3,1)) ----
    frontier = {}
    seam = {}
    for rho in RHOS:
        fr = {}
        for d in DS:
            hit = next((L for L in LGTS
                        if best_n(d, L, rho, (1, 3, 1), 1)[1] >= 1.0), None)
            fr["%g" % d] = hit
        sm = {}
        for L in LGTS:
            worst = next((d for d in reversed(DS[:3])
                          if best_n(d, L, rho, (1, 3, 1), 1)[1] < 0.8), None)
            sm[str(L)] = worst
        frontier["rho=%.1f" % rho] = fr
        seam["rho=%.1f" % rho] = sm
        say("FRONTIER rho=%.1f (smallest lgT with PASS, band=(1,3,1), m=1): %s"
            % (rho, fr))
        say("SEAM rho=%.1f (largest OPEN d among 0.005..0.02): %s" % (rho, sm))
    results["frontier"] = frontier
    results["seam"] = seam

    g_all = all(results["gates"][g] == "PASS" for g in ("G1", "G2", "G3"))
    say("FINAL gates=%s" % ",".join("G%d:%s" % (i, results["gates"]["G%d" % i])
                                    for i in (1, 2, 3)))
    say("DONE gates=G1:%s,G2:%s,G3:%s" % (results["gates"]["G1"],
                                          results["gates"]["G2"],
                                          results["gates"]["G3"]))
    if not g_all:
        say("WARNING: instrument gate failure - run VOID per prereg 1373 s3", )
    results["done"] = "DONE gates=G1:%s,G2:%s,G3:%s" % (results["gates"]["G1"],
                                                        results["gates"]["G2"],
                                                        results["gates"]["G3"])
    with open("docs/proofs/1373_phase_rig_results.json", "w", encoding="utf-8") as fh:
        json.dump(results, fh, indent=1)
    return 0


if __name__ == "__main__":
    sys.exit(main())
