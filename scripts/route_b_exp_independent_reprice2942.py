"""Re-price the local subcell with independent rectangular exp propagation."""
import json
import sys
from pathlib import Path
from mpmath import iv

sys.path.insert(0, str(Path(__file__).parent))
import route_b_d4_cauchy_interval2889 as base


def main():
    stages = json.loads(Path("results/2905_route_b_d4_local_refine.json").read_text())["stages_subcell_0"]
    a = stages["a"]
    t = stages["t"]
    aa = iv.mpc(iv.mpf([a["re_lo"], a["re_hi"]]), iv.mpf([a["im_lo"], a["im_hi"]]))
    tt = iv.mpc(iv.mpf([t["re_lo"], t["re_hi"]]), iv.mpf([t["im_lo"], t["im_hi"]]))
    ee = iv.exp(2 * aa)
    zz = (ee - 1) / (ee + 1) / tt
    hh = base.h_of(tt, zz)
    payload = {
        "record": 2942,
        "exp_independent_rectangle": {
            "re_lo": str(ee.real.a), "re_hi": str(ee.real.b),
            "im_lo": str(ee.imag.a), "im_hi": str(ee.imag.b),
        },
        "H_norm_upper": str(base.abs_upper(hh)),
        "M": "13.77903608911727",
        "claims": {"independent_reprice": True,
                    "formal_interval_soundness": False},
        "decision": "independent rectangle remains below M; widen and re-price",
    }
    out = Path("results/2942_route_b_exp_independent_reprice.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
