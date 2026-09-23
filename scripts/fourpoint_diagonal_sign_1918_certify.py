#!/usr/bin/env python3
# fourpoint_diagonal_sign_1918_certify.py — record 1918 post-analysis
#
# Reads results/1918_fourpoint_diagonal_sign.json (produced by
# scripts/fourpoint_diagonal_sign_1918.py) and re-classifies every case with
# the certified engine reading:
#
#   D_cert          = the analytic-Fhat engine E4 when present (agrees with
#                     the sigma-FFT engine E3 to <= 6e-7 on all u*u entries),
#                     else E3;
#   disc            = Bs^2 - 4 C D_cert with C, B01, B10 from E3;
#   ddisc_cert      = certified-pair propagation: 2|Bs| (dB01 + dB10)
#                     + 4 C |E4 - E3| + 4 D dC;
#   ddisc_cons      = ddisc_cert plus a deliberately pessimistic 1e-5
#                     relative envelope on the shared inputs;
#   margin_rel      = disc / (4 C D) = B01^2/(D C) - 1 under the cross-term
#                     symmetry (the relative indefiniteness margin of the
#                     gate form on span{u, g});
#   Q_vertex        = -disc / (4 C) = det / C with det = D C - (Bs / 2)^2
#                     (the strict vertex value).
#
# Prints an aligned table and writes results/1918_fourpoint_diagonal_sign_certified.json.
# Pure stdlib post-analysis; all numerics come from the probe JSON.

import json
import sys


def main():
    with open("results/1918_fourpoint_diagonal_sign.json") as fh:
        d = json.load(fh)
    cs = d["cases"]
    rows = []
    robust_cert_all = True
    robust_cons_all = True
    disc_pos_all = True
    for c in cs:
        Ds = c["D_engines"]
        D = Ds.get("E4", Ds["E3"])
        C, B01, B10 = c["C"]["IC"], c["B01"]["IC"], c["B10"]["IC"]
        Bs = B01 + B10
        disc = Bs * Bs - 4.0 * C * D
        dD_cert = abs(Ds.get("E4", Ds["E3"]) - Ds["E3"])

        def eng(e):
            return [e["IC"], e["IC_direct"], e["IC_split"]]

        dC = max(eng(c["C"])) - min(eng(c["C"]))
        dB = (max(eng(c["B01"])) - min(eng(c["B01"]))
              + max(eng(c["B10"])) - min(eng(c["B10"])))
        ddisc_cert = 2.0 * abs(Bs) * dB + 4.0 * abs(C) * dD_cert + 4.0 * abs(D) * dC
        ddisc_cons = (ddisc_cert + 4.0 * abs(C) * 1e-5 * abs(D)
                      + 2.0 * abs(Bs) * 1e-5 * (abs(B01) + abs(B10)))
        margin = disc / (4.0 * C * D)
        qv = -disc / (4.0 * C)
        rc = abs(disc) > 10.0 * ddisc_cert
        rcons = abs(disc) > 10.0 * ddisc_cons
        robust_cert_all &= rc
        robust_cons_all &= rcons
        disc_pos_all &= disc > 0
        c["cert"] = {"D_cert": D, "ddisc_cert": ddisc_cert,
                     "ddisc_cons": ddisc_cons, "robust_cert": rc,
                     "robust_cons": rcons, "margin_rel": margin,
                     "Q_vertex": qv}
        rows.append((c["tag"], D, disc, margin, qv, c["lam_vertex"], rc, rcons))

    print("%-22s %12s %12s %10s %12s %11s %6s %6s" % (
        "case", "D_cert", "disc", "margin_rel", "Q_vertex", "lam_vertex",
        "rcert", "rcons"))
    for tag, D, disc, margin, qv, lv, rc, rcons in rows:
        print("%-22s %12.4e %12.4e %10.3e %12.4e %11.4e %6s %6s" % (
            tag, D, disc, margin, qv, lv, rc, rcons))
    print("disc>0 all: %s; robust_cert all: %s; robust_cons all: %s"
          % (disc_pos_all, robust_cert_all, robust_cons_all))
    m = sorted((r[3], r[0]) for r in rows)
    print("min margin_rel: %s (%.3e); max: %s (%.3e)"
          % (m[0][1], m[0][0], m[-1][1], m[-1][0]))
    devs = [c["dev_D_engines"] for c in cs]
    print("engine deviations vs certified E4: |E3-E4|/E4 max %.2e, "
          "E1 dev max %.2e, E5 dev max %.2e"
          % (max(abs(x.get("E3", 0.0)) for x in devs),
             max(abs(x.get("E1", 0.0)) for x in devs),
             max(abs(x.get("E5", 0.0)) for x in devs)))
    worst = min((abs(c["disc"]) / c["cert"]["ddisc_cert"], c["tag"]) for c in cs)
    print("min |disc|/ddisc_cert over cases: %.1f (%s)" % worst)
    worst_cons = min((abs(c["disc"]) / c["cert"]["ddisc_cons"], c["tag"])
                     for c in cs)
    print("min |disc|/ddisc_cons over cases: %.1f (%s)" % worst_cons)
    # normalize the shipped summary: drop the vacuous self-comparison key and
    # record the certified statistics alongside the probe's own summary.
    if isinstance(d.get("summary"), dict):
        d["summary"].pop("max_dev_E4", None)
        d["summary"]["max_dev_E3_pair"] = max(abs(x.get("E3", 0.0))
                                              for x in devs)
        d["summary"]["min_disc_over_ddisc_cert"] = worst[0]
        d["summary"]["min_disc_over_ddisc_cons"] = worst_cons[0]
    with open("results/1918_fourpoint_diagonal_sign_certified.json", "w") as fh:
        json.dump(d, fh, indent=1, default=float)
    print("wrote results/1918_fourpoint_diagonal_sign_certified.json")


if __name__ == "__main__":
    sys.exit(main())