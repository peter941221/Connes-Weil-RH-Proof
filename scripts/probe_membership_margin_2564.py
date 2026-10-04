"""Membership margin probe: rational representatives against the 2338 boxes.

External pre-check for the coefficient-membership brick; no theorem changes.
Per channel (base, correction), for all 30 families this measures
- the per-component half widths and the L1 half-diagonal against the channel
  error constant (base: the committed 2540 uniform 1/10^30; correction: the
  recommended 1/10^28 ceiling over the raw 2338 widths);
- the 2^-200 truncation of each box midpoint as a candidate Lean-import
  representative: its exact squared complex offset from the midpoint against
  the channel L2 ball, and the smallest truncation exponent k that keeps the
  offset under half the channel error ball;
- whether the representatives stay inside their boxes (informational; the
  membership premise only needs the distance to the center).
"""
from fractions import Fraction as Q
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
K = 200
ERRORS = {"base": Q(1, 10**30), "correction": Q(1, 10**28)}


def trunc(v, k):
    scaled = v * 2**k
    return Q(scaled.numerator // scaled.denominator, 2**k)


def main():
    source = ROOT / "results/2338_exact_interpolation_repair.json"
    data = json.loads(source.read_text())
    rows = data["coefficient_rows"]
    report = {}
    for channel in ("base", "correction"):
        kind = f"ideal_{channel}_coefficient"
        error = ERRORS[channel]
        error_sq = error * error
        slots = []
        smallest_k = 0
        for row in rows:
            box = row[kind]
            lo_re, hi_re = Q(box["real"]["lower_exact"]), Q(box["real"]["upper_exact"])
            lo_im, hi_im = Q(box["imag"]["lower_exact"]), Q(box["imag"]["upper_exact"])
            mid_re, mid_im = (lo_re + hi_re) / 2, (lo_im + hi_im) / 2
            half_l1 = (hi_re - lo_re) / 2 + (hi_im - lo_im) / 2
            rep = (trunc(mid_re, K), trunc(mid_im, K))
            off_sq = (rep[0] - mid_re) ** 2 + (rep[1] - mid_im) ** 2
            assert off_sq <= error_sq, (row["index"], channel, "offset leaves error ball")
            k_here = None
            for k in range(64, 257):
                d = trunc(mid_re, k) - mid_re, trunc(mid_im, k) - mid_im
                if d[0] * d[0] + d[1] * d[1] <= error_sq / 4:
                    k_here = k
                    break
            assert k_here is not None, (row["index"], channel)
            smallest_k = max(smallest_k, k_here)
            slots.append(dict(
                index=row["index"],
                half_width_re=str((hi_re - lo_re) / 2),
                half_width_im=str((hi_im - lo_im) / 2),
                half_l1=str(half_l1),
                rep_inside_box=bool(lo_re <= rep[0] <= hi_re and lo_im <= rep[1] <= hi_im),
                rep_offset_sq=str(off_sq)))
        max_half_l1 = max(Q(s["half_l1"]) for s in slots)
        max_off_sq = max(Q(s["rep_offset_sq"]) for s in slots)
        inside = sum(1 for s in slots if s["rep_inside_box"])
        report[channel] = dict(
            error_constant=str(error),
            slots_checked=len(slots),
            max_half_l1=str(max_half_l1), max_half_l1_display=float(max_half_l1),
            box_slack_ratio=float(error / max_half_l1),
            representative_offset_sq_max=str(max_off_sq),
            representative_offset_slack_ratio=float((error_sq - max_off_sq) / error_sq),
            representatives_inside_boxes=inside,
            smallest_k_within_half_error=smallest_k)
    result = dict(
        record=2564, scope="membership margin probe; external only, no Lean claim",
        note="base error matches the committed baseBox_widths2540 constant; "
             "correction error is this probe's recommended ceiling 1/10^28 over "
             "the raw 2338 widths (the committed 2540 constant does not cover "
             "the correction boxes)",
        **report,
        truncation_exponent=K,
        source_sha256=hashlib.sha256(source.read_bytes()).hexdigest(),
        lean_import_module=False, membership_proof=False,
        producer_go=False, rh_claim=False)
    (ROOT / "results/2564_membership_margin_probe.json").write_text(
        json.dumps(result, indent=2) + "\n")
    for channel in ("base", "correction"):
        r = result[channel]
        print(f"MEMBERSHIP_MARGIN_PROBE {channel}: slack {r['box_slack_ratio']:.3e} "
              f"max_half_l1 {r['max_half_l1_display']:.3e} "
              f"offset_slack {r['representative_offset_slack_ratio']:.3e} "
              f"smallest_k {r['smallest_k_within_half_error']} "
              f"inside_box {r['representatives_inside_boxes']}/30", flush=True)


if __name__ == "__main__":
    main()
