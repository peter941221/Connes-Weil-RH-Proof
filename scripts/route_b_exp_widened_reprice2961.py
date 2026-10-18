"""Reprice the deliberately widened formal exp rectangle used by stage 2907."""
import json
from pathlib import Path
from mpmath import iv

import route_b_d4_cauchy_interval2889 as base


def main() -> None:
    stages = json.loads(
        Path("results/2905_route_b_d4_local_refine.json").read_text()
    )["stages_subcell_0"]
    t = stages["t"]
    tt = iv.mpc(
        iv.mpf([t["re_lo"], t["re_hi"]]),
        iv.mpf([t["im_lo"], t["im_hi"]]),
    )
    ee = iv.mpc(iv.mpf(["1.0914", "1.0922"]), iv.mpf(["-0.1893", "-0.1887"]))
    zz = (ee - 1) / (ee + 1) / tt
    hh = base.h_of(tt, zz)
    payload = {
        "record": 2961,
        "formal_exp_rectangle": {
            "re_lo": "1.0914",
            "re_hi": "1.0922",
            "im_lo": "-0.1893",
            "im_hi": "-0.1887",
        },
        "H_norm_upper": str(base.abs_upper(hh)),
        "M": "13.77903608911727",
        "margin": str(iv.mpf("13.77903608911727") - base.abs_upper(hh)),
        "claims": {"independent_reprice": True, "formal_membership": False},
    }
    out = Path("results/2961_route_b_exp_widened_reprice.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
