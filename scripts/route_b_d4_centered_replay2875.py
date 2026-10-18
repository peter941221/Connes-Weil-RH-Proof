"""Replay the centred D4 factorisation against the original derivative."""
import json
from pathlib import Path
import mpmath as mp

mp.mp.dps = 60


def transition(u):
    return 1 / (1 + mp.exp(1 / u - 1 / (1 - u)))


def z_of(t):
    return mp.tanh(2 * t / (1 - t * t)) / t if t else mp.mpf(2)


def h_of(t, z):
    x = t * t
    return (24*x**5*z**3 + 36*x**5*z**2 + 18*x**5*z + 3*x**5
            + 96*x**4*z**3 + 144*x**4*z**2 + 68*x**4*z + 9*x**4
            + 144*x**3*z**3 + 72*x**3*z**2 - 148*x**3*z - 114*x**3
            + 96*x**2*z**3 - 144*x**2*z**2 - 240*x**2*z + 18*x**2
            + 24*x*z**3 - 108*x*z**2 + 50*x*z + 63*x - 4*z + 21)


def reconstructed_d4(u):
    t = 2 * u - 1
    z = z_of(t)
    return (t * (t*z - 1) * (t*z + 1) * h_of(t, z) / 512
            / (u**8 * (u - 1)**8))


def main():
    points = [mp.mpf(x) for x in ("0.01", "0.1", "0.2", "0.4", "0.49")]
    rows = []
    for u in points:
        original = mp.diff(transition, u, 4)
        replay = reconstructed_d4(u)
        rows.append({
            "u": str(u),
            "original": mp.nstr(original, 40),
            "reconstructed": mp.nstr(replay, 40),
            "absolute_residual": mp.nstr(abs(original - replay), 20),
        })
    payload = {
        "record": 2875,
        "rows": rows,
        "claims": {
            "pointwise_replay_check": True,
            "sign_certificate": False,
            "integral_bound_certificate": False,
        },
    }
    out = Path("results/2875_route_b_d4_centered_replay.json")
    out.write_text(json.dumps(payload, indent=2) + "\n", encoding="utf-8")
    print(json.dumps(payload, indent=2))


if __name__ == "__main__":
    main()
