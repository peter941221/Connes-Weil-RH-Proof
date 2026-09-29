"""Record 2236: solve-floor coefficient radius; the direct-product outward
envelope repriced to viability.

Record 2235 attributed the 2234 envelope blow-up to the coefficient channel
and measured the system scales of the committed 2197 construction:
A_inf = 7.942e-13, Ainv_inf = 6.770e17, c_inf = 5.688e17 (correction
solve), residuals 6.5e-15 / 1.1e-11.  The record-2201 radius
(3.536e11) mixes two channels that separate under the discrete-defined
operand convention (2230):

  generation  stored matrix entries vs their embedded-float ideal; priced
              by a screen eta (2233 w-channel 9.16e-14), currently only
              provisional - the registered open lever of this record;
  solve       the binary64 LU chain's own forward error, bounded by the
              standard backward-error charge
                  r_c = Ainv_inf * (||resid||_inf + gamma_30 * A_inf * c_inf)

This record charges the solve channel at its computed floor and reports the
envelope under both readings of the coefficient channel:

  solve-floor   r_base = Ainv (resid + gamma_30 A c), the computed floor;
  stored-exact  r = 0 (the convention-A reading: the stored solve is exact
                and the generation channel lives in the ledger).

The verdict is read from the binding row, where both readings agree.

Reads results/2235_direct_product_reprice.json (system scales),
results/2234_sigma_*.json (sigma sums),
writes results/2236_direct_product_solve_floor.json.
"""
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
R = ROOT / "results"
UP = lambda v: __import__("math").nextafter(v, __import__("math").inf)


def up_many(v, n):
    for _ in range(n):
        v = UP(v)
    return v


def _load(name, filename):
    import importlib.util
    sp = importlib.util.spec_from_file_location(name, ROOT / "scripts" / filename)
    assert sp is not None and sp.loader is not None
    mod = importlib.util.module_from_spec(sp)
    sp.loader.exec_module(mod)
    return mod


def floor_radii():
    """Solve-floor radii from the committed 2235 system scales."""
    d = json.loads((R / "2235_direct_product_reprice.json")
                   .read_text(encoding="utf-8"))
    sc = d["radius"]
    gamma30 = up_many(30.0 * 2.0 ** -52 / (1.0 - 30.0 * 2.0 ** -52), 2)
    r_base = up_many(sc["ainv_inf"] * (sc["resid_base"]
                                       + gamma30 * sc["a_inf"]
                                       * sc["base_c_inf"]), 3)
    r_corr = up_many(sc["ainv_inf"] * (sc["resid_corr"]
                                       + gamma30 * sc["a_inf"]
                                       * sc["corr_c_inf"]), 3)
    return {"a_inf": sc["a_inf"], "ainv_inf": sc["ainv_inf"],
            "cond_inf": sc["cond_inf"], "base_c_inf": sc["base_c_inf"],
            "corr_c_inf": sc["corr_c_inf"], "resid_base": sc["resid_base"],
            "resid_corr": sc["resid_corr"], "gamma30": gamma30,
            "r_base": r_base, "r_corr": r_corr,
            "r_base_2201": 1.725905221940381e8,
            "r_corr_2201": 3.536472115641207e11,
            "charge_2201_over_floor_base": 1.725905221940381e8 / r_base,
            "charge_2201_over_floor_corr": 3.536472115641207e11 / r_corr}


def main():
    rp = _load("rp2235", "routea_weighted_zero_direct_product_reprice_2235.py")
    rad = floor_radii()
    eth = 1e-12
    gen = {"r_base": eth * rad["a_inf"] * rad["base_c_inf"],
           "r_corr": eth * rad["a_inf"] * rad["corr_c_inf"]}
    solve_radii = {"r_base": rad["r_base"], "r_corr": rad["r_corr"]}
    zero_radii = {"r_base": 0.0, "r_corr": 0.0}
    result = rp.run_reduce(
        solve_radii, 2236,
        "solve-floor coefficient radius: r_c = Ainv (resid + gamma_30 A c); "
        "generation channel left to the ledger",
        "2236_direct_product_solve_floor.json",
        "DIRECT-PRODUCT-OUTWARD-STILL-LOOSE",
        extra={"floor_radius": rad,
               "generation_channel_registered": {
                   "screen": eth,
                   "epsilon_charge_base": gen["r_base"],
                   "epsilon_charge_corr": gen["r_corr"],
                   "note": "the 2201-style charged version of this channel "
                           "is the registered lever; it is not absorbed "
                           "into this envelope"}})
    robust = rp.run_reduce(
        zero_radii, 2236,
        "robustness reading: stored solve exact (convention A), coefficient "
        "channel zero",
        "2236_robustness_zero_coeff.json",
        "DIRECT-PRODUCT-OUTWARD-STILL-LOOSE")
    result["robustness"] = {
        "stored_exact_C_upper": robust["screen"]["C_upper"],
        "stored_exact_tail_over_margin":
            robust["screen"]["tail_upper_over_margin"],
        "solve_floor_C_upper": result["screen"]["C_upper"],
        "binding_row_invariant": (robust["binding_row"]["sigma"]
                                  == result["binding_row"]["sigma"]),
        "note": "the binding row is channel a (db*mc); both coefficient "
                "channels enter it only through the small base/corr_M0 "
                "inflatons, so the verdict is read identically under both "
                "readings",
    }
    (R / "2236_direct_product_solve_floor.json").write_text(
        json.dumps(result, indent=2) + "\n", encoding="utf-8")
    print(json.dumps({"status": result["status"],
                      "binding_sigma": result["binding_row"]["sigma"],
                      "C_upper": result["screen"]["C_upper"],
                      "tail_upper_over_margin":
                      result["screen"]["tail_upper_over_margin"],
                      "repricing_factor_vs_2234":
                      result["comparison_2234"]["C_repricing_factor"],
                      "r_base_floor": rad["r_base"],
                      "r_corr_floor": rad["r_corr"],
                      "charge_2201_over_floor_corr":
                      rad["charge_2201_over_floor_corr"],
                      "robustness_stored_exact_C_upper":
                      robust["screen"]["C_upper"]}, indent=2), flush=True)


if __name__ == "__main__":
    main()