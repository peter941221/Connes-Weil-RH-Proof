"""Independent interval reprice of the real/imaginary argument coordinates.

This is a planning artifact for the Lean rectangle proof.  It uses the
stored subcell t rectangle and mpmath interval arithmetic; it is not a Lean
certificate and deliberately carries that nonclaim in the output.
"""
import json
from pathlib import Path
from mpmath import iv


def main() -> None:
    stages = json.loads(
        Path("results/2905_route_b_d4_local_refine.json").read_text()
    )["stages_subcell_0"]
    t = stages["t"]
    tt = iv.mpc(
        iv.mpf([t["re_lo"], t["re_hi"]]),
        iv.mpf([t["im_lo"], t["im_hi"]]),
    )
    argument = 2 * tt / (1 - tt**2)
    payload = {
        "record": 2946,
        "source": "results/2905_route_b_d4_local_refine.json",
        "t_rectangle": {
            "re_lo": t["re_lo"],
            "re_hi": t["re_hi"],
            "im_lo": t["im_lo"],
            "im_hi": t["im_hi"],
        },
        "argument_interval": {
            "re_lo": str(argument.real.a),
            "re_hi": str(argument.real.b),
            "im_lo": str(argument.imag.a),
            "im_hi": str(argument.imag.b),
        },
        "claims": {
            "independent_interval_replay": True,
            "formal_lean_membership": False,
        },
    }
    out = Path("results/2946_route_b_argument_interval.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
