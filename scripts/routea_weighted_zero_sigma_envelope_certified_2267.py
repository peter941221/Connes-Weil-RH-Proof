"""Record 2267: certified centered-strip envelope of the direct-product screen.

Record 2264 audited the raw binary64 min-product of the two product channels
over sigma in [-0.6, 1.1] and found the centered-strip maximum
2874525.124523096 at sigma = -1/2 (channel b), 0.302382 of the frozen screen
constant, but only at screen grade: the raw scan re-integrates the same node
values without panels, coefficient inflation, or a sigma-transfer.  Record
2265 pinned the producer side of the weighted-zero C3' candidate to the Lean
lemma `laplaceAt_convolution_spectral_bound_of_strip`, whose hypothesis is
exactly a certified bound on

    N(sigma) = min (D2_b(sigma) * M_c(sigma), D2_c(sigma) * M_b(sigma))

over the CENTERED strip sigma in [-1/2, 1/2].  This script delivers that
certified envelope with the 2234/2243 machinery:

1. point values: `results/2234_sigma_{j}.json` for j = -50..50 (sigma =
   j/100); the negative-sigma rows are fresh 256-bit MPFR sigma-worker runs
   over the committed per-node upper chunks, same machinery as the frozen
   positive rows;
2. panels: the 2238 composite-EM identity with the 2242 certified zero count
   (N_risk = 0), in the sigma-symmetric form

       panel_cem_sym(sigma) = (dx^2/12) (2 a_max)
           e^{|sigma| a_max} (m_{k+2} + 2|sigma| m_{k+1} + sigma^2 m_k),

   which reduces to the 2243 `panel_cem` at sigma >= 0 (the weight supremum
   on the support [-a_max, a_max] is e^{sigma a_max} for sigma >= 0 and
   e^{-sigma a_max} for sigma < 0);
3. coefficient inflation on the 2237 certified radii, likewise with the
   support-supremum weight e^{|sigma| a_max};
4. the sigma-transfer: |d/dsigma log N| <= 2 a_max (each strip norm is an
   e^{sigma x}-weighted L1 integral with support |x| <= a_max, so its
   log-derivative lies in [-a_max, a_max]; the min of the two products
   inherits the factor 2), giving the continuum sup bound

       sup_{[-1/2,1/2]} N <= max_j B_point(j) * e^{2 a_max * 0.005}

   for the 0.01 grid (half-step 0.005).

Verdict line: CERTIFIED-STRIP-COVERED iff the certified sup is at most the
frozen constant bUpper2243 = 9506275.102584327 of record 2243.

Anchors: (a) the sigma = 1.0 row recomputed with the 2243-identical
construction (plain panel/inflation plus the embedded exp(a_max * 0.01)
cover) must reproduce the 2243 binding row C_upper and B_upper; (b) the raw
per-norm cross-check against all 101 overlapping 2264 grid rows: the
certified point sums are uppers of the raw binary64 sums.

No producer GO, no gate sign change, no RH claim.
"""
import importlib.util
import json
import math
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
FROZEN_B = 9506275.102584327
FROZEN_C = 240796.76135588222
GRID_J = list(range(-50, 51))
HALF_STEP = 0.005
OUT = R / "2267_sigma_envelope_certified.json"


def up_many(v, n):
    for _ in range(n):
        v = math.nextafter(v, math.inf)
    return v


def _load(name, filename):
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


def panel_cem_sym(name, sigma, table):
    m, k, nrisk, a_max, dx = table[name]
    s = abs(sigma)
    g = math.exp(s * a_max)
    Mk = g * (m[k + 2] + 2.0 * s * m[k + 1] + sigma * sigma * m[k])
    return up_many((dx * dx / 12.0) * ((2.0 * a_max) * Mk), 4)


def coeff_inflation_sym(coef, fam, K, a_max, sigma, radius, order, majorant):
    s = abs(sigma)
    acc = 0.0
    for (a, _), _c in zip(fam, coef):
        acc += 2.0 * a * math.exp(s * a_max) * majorant(order, K, a)
    return radius * acc


def main():
    cert = json.loads((R / "2242_zero_count_certificate.json")
                      .read_text(encoding="utf-8"))
    assert cert["status"] == "ZERO-COUNT-CERTIFIED", cert["status"]
    o34 = _load("o34f", "routea_weighted_zero_direct_product_outward_2234.py")
    s97 = _load("s97h", "routea_weighted_zero_direct_product_mass_screen_2197.py")
    o38 = _load("o38e", "routea_weighted_zero_panel_dx2_2238.py")
    table = o38.panel_table()
    fam, base, corr, a_max = o34.build_construction()
    majorant = o34.majorant_phi_le
    cert37 = json.loads((R / "2237_generation_certificate.json")
                        .read_text(encoding="utf-8"))
    radii = {"r_base": cert37["radius"]["r_base"],
             "r_corr": cert37["radius"]["r_corr"]}
    rec43 = json.loads((R / "2243_panel_cem_reprice.json")
                       .read_text(encoding="utf-8"))
    rec64 = json.loads((R / "2264_sigma_range_audit.json")
                       .read_text(encoding="utf-8"))
    raw_by_sigma = {round(r["sigma"], 6): r for r in rec64["grid"]}
    tp2 = up_many((2.0 * math.pi) ** 2, 3)

    rows = []
    for j in GRID_J:
        sigma = j / 100.0
        p = R / f"2234_sigma_{j}.json"
        assert p.exists(), p
        v = json.loads(p.read_text(encoding="utf-8"))["values"]
        pb = panel_cem_sym("base_M0", sigma, table)
        pb2 = panel_cem_sym("base_D2", sigma, table)
        pc = panel_cem_sym("corr_M0", sigma, table)
        pc2 = panel_cem_sym("corr_D2", sigma, table)
        eb = coeff_inflation_sym(base, fam, s97.K, a_max, sigma,
                                 radii["r_base"], 0, majorant)
        eb2 = coeff_inflation_sym(base, fam, s97.K, a_max, sigma,
                                  radii["r_base"], 2, majorant)
        ec = coeff_inflation_sym(corr, fam, s97.K, a_max, sigma,
                                 radii["r_corr"], 0, majorant)
        ec2 = coeff_inflation_sym(corr, fam, s97.K, a_max, sigma,
                                  radii["r_corr"], 2, majorant)
        mb = up_many(up_many((v["base_M0"] + pb) * (1.0 + eb), 3), 3)
        db = up_many(up_many((v["base_D2"] + pb2) * (1.0 + eb2), 3), 3)
        mc = up_many(up_many((v["corr_M0"] + pc) * (1.0 + ec), 3), 3)
        dc = up_many(up_many((v["corr_D2"] + pc2) * (1.0 + ec2), 3), 3)
        c1 = up_many(up_many(db * mc, 3) / tp2, 3)
        c2 = up_many(up_many(dc * mb, 3) / tp2, 3)
        c_up = min(c1, c2)
        b_point = up_many(up_many(tp2 * c_up, 3), 3)
        v_min = min(v["base_D2"] * v["corr_M0"], v["corr_D2"] * v["base_M0"])
        raw = raw_by_sigma.get(round(sigma, 6))
        raw_check = None
        if raw is not None:
            raw_check = {"raw_B": float(raw["B"]),
                         "v_min_over_raw": v_min / float(raw["B"]),
                         "v_min_minus_raw": v_min - float(raw["B"])}
        rows.append({"j": j, "sigma": sigma,
                     "panel_base_M0": pb, "panel_base_D2": pb2,
                     "panel_corr_M0": pc, "panel_corr_D2": pc2,
                     "coeff_infl_base_M0": eb, "coeff_infl_base_D2": eb2,
                     "coeff_infl_corr_M0": ec, "coeff_infl_corr_D2": ec2,
                     "C_channel_a": c1, "C_channel_b": c2,
                     "C_upper": c_up,
                     "binding": "a" if c1 <= c2 else "b",
                     "B_point": b_point,
                     "v_min_product": v_min,
                     "raw_check": raw_check})

    assert all(r["raw_check"] is not None for r in rows)
    raw_rel_max = max(abs(r["raw_check"]["v_min_over_raw"] - 1.0)
                      for r in rows)
    raw_upper_ok = all(r["raw_check"]["v_min_minus_raw"] >= 0.0 for r in rows)

    # anchor: the 2243-identical sigma = 1.0 row (cover embedded)
    sigma1 = 1.0
    v1 = json.loads((R / "2234_sigma_100.json").read_text(encoding="utf-8"))["values"]
    cover1 = math.exp(a_max * 0.01)
    pbA = panel_cem_sym("base_M0", sigma1, table)
    pb2A = panel_cem_sym("base_D2", sigma1, table)
    pcA = panel_cem_sym("corr_M0", sigma1, table)
    pc2A = panel_cem_sym("corr_D2", sigma1, table)
    ebA = coeff_inflation_sym(base, fam, s97.K, a_max, sigma1,
                              radii["r_base"], 0, majorant)
    eb2A = coeff_inflation_sym(base, fam, s97.K, a_max, sigma1,
                               radii["r_base"], 2, majorant)
    ecA = coeff_inflation_sym(corr, fam, s97.K, a_max, sigma1,
                              radii["r_corr"], 0, majorant)
    ec2A = coeff_inflation_sym(corr, fam, s97.K, a_max, sigma1,
                               radii["r_corr"], 2, majorant)
    mbA = up_many(up_many((v1["base_M0"] + pbA) * (1.0 + ebA), 3) * cover1, 3)
    dbA = up_many(up_many((v1["base_D2"] + pb2A) * (1.0 + eb2A), 3) * cover1, 3)
    mcA = up_many(up_many((v1["corr_M0"] + pcA) * (1.0 + ecA), 3) * cover1, 3)
    dcA = up_many(up_many((v1["corr_D2"] + pc2A) * (1.0 + ec2A), 3) * cover1, 3)
    c1A = up_many(up_many(dbA * mcA, 3) / tp2, 3)
    c2A = up_many(up_many(dcA * mbA, 3) / tp2, 3)
    cA = min(c1A, c2A)
    bA = up_many(up_many(tp2 * cA, 3), 3)
    anchor_2243 = {
        "C_upper_computed": cA, "C_upper_2243": FROZEN_C,
        "C_rel": abs(cA - FROZEN_C) / FROZEN_C,
        "B_computed": bA, "B_2243": FROZEN_B,
        "B_rel": abs(bA - FROZEN_B) / FROZEN_B,
        "panel_match_2243": {
            "base_M0": [pbA, rec43["binding_row"]["panel_base"]],
            "base_D2": [pb2A, rec43["binding_row"]["panel_base_D2"]],
            "corr_M0": [pcA, rec43["binding_row"]["panel_corr"]],
            "corr_D2": [pc2A, rec43["binding_row"]["panel_corr_D2"]]},
    }

    transfer = math.exp(2.0 * a_max * HALF_STEP)
    max_row = max(rows, key=lambda r: r["B_point"])
    sup_cert = up_many(max_row["B_point"] * transfer, 4)
    neg_max = max((r for r in rows if r["sigma"] <= 0), key=lambda r: r["B_point"])
    pos_max = max((r for r in rows if r["sigma"] >= 0), key=lambda r: r["B_point"])
    covered = sup_cert <= FROZEN_B
    margin = FROZEN_B / sup_cert
    result = {
        "record": 2267,
        "status": ("CERTIFIED-STRIP-COVERED" if covered
                   else "STRIP-REPRICE-NEEDED"),
        "lever": "2234/2243 certified reduction on the centered strip with "
                 "sigma-symmetric panel/inflation and the log-derivative "
                 "transfer e^{2 a_max h}, h = 0.005",
        "gate": {"zero_count_certificate": cert["status"]},
        "radius": radii,
        "a_max": a_max,
        "transfer": {"half_step": HALF_STEP, "factor": transfer},
        "grid_rows": rows,
        "centered": {
            "max_point_sigma": max_row["sigma"],
            "max_point_B": max_row["B_point"],
            "max_point_binding": max_row["binding"],
            "neg_half_max_sigma": neg_max["sigma"],
            "neg_half_max_B": neg_max["B_point"],
            "pos_half_max_sigma": pos_max["sigma"],
            "pos_half_max_B": pos_max["B_point"],
            "sup_certified": sup_cert,
            "frozen_bUpper2243": FROZEN_B,
            "covered": covered,
            "margin": margin,
        },
        "anchor_raw_2264": {
            "points": len(rows),
            "v_min_over_raw_rel_max": raw_rel_max,
            "upper_ok": raw_upper_ok,
        },
        "anchor_2243": anchor_2243,
        "anchors_ok": bool(raw_upper_ok and raw_rel_max <= 1e-8
                           and anchor_2243["C_rel"] <= 1e-12
                           and anchor_2243["B_rel"] <= 1e-12),
        "nonclaims": [
            "the numeric core (per-node upper chunks with the committed "
            "2^-200 slack, 256-bit RNDN sigma sums with the 4-ulp guards, "
            "2237 certified radii) is exactly the 2243 machinery; no new "
            "certification standard is introduced",
            "for sigma < 0 the panel and inflation use the support-supremum "
            "weight e^{a|sigma|} and the cross term 2|sigma| m_{k+1}; this "
            "is conservative, not tight",
            "the sigma-transfer is the log-derivative law |d/dsigma log N| "
            "<= 2 a_max at half-step 0.005; the certified sup is a grid "
            "maximum times e^{2 a_max 0.005}, valid on the continuum "
            "[-1/2, 1/2] but not tight",
            "the envelope covers the centered strip only; the sigma = 1.0 "
            "row is reported as a reproducibility anchor of the frozen 2243 "
            "constant and lies outside the producer's hB range",
            "no producer GO, no gate sign change, no RH claim",
        ],
        "provenance": {
            "script": "scripts/routea_weighted_zero_sigma_envelope_certified_2267.py",
            "sigma_sums": "results/2234_sigma_*.json (j = -50..50)",
            "gate": "results/2242_zero_count_certificate.json",
            "radius": "results/2237_generation_certificate.json",
            "prior": ["results/2243_panel_cem_reprice.json",
                      "results/2264_sigma_range_audit.json"],
        },
    }
    OUT.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8",
                   newline="\n")
    print(json.dumps({
        "status": result["status"],
        "max_point_sigma": max_row["sigma"],
        "max_point_B": max_row["B_point"],
        "transfer": transfer,
        "sup_certified": sup_cert,
        "frozen": FROZEN_B,
        "covered": covered,
        "margin": margin,
        "raw_rel_max": raw_rel_max,
        "raw_upper_ok": raw_upper_ok,
        "anchor_C_rel": anchor_2243["C_rel"],
        "anchor_B_rel": anchor_2243["B_rel"],
        "anchors_ok": result["anchors_ok"],
    }, indent=2), flush=True)


if __name__ == "__main__":
    main()