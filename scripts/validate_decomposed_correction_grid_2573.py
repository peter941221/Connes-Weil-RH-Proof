"""Independent controls and exact artifact validation for record 2573."""
import argparse
import copy
from fractions import Fraction
import hashlib
import json
from pathlib import Path

from flint import acb, ctx
import mpmath as mp
import price_decomposed_correction_grid_2573 as pricing

ROOT = Path(__file__).resolve().parents[1]


def mp_exact(value):
    value = Fraction(value)
    return mp.mpf(value.numerator) / value.denominator


def midpoint(value):
    return mp_exact(str(value.mid().fmpq()))


def independent_controls():
    ctx.prec = 192
    mp.mp.dps = 90
    families = pricing.load_families()
    derivative_checks = 0
    identity_checks = 0
    envelope_checks = 0
    worst = mp.mpf(0)
    for index in (0, 15, 29):
        family = families[index]
        radius = mp_exact(family["r"])
        modulation = mp_exact(family["theta_exact"])
        for sigma in (Fraction(-1, 2), Fraction(1, 2)):
            weight = pricing.base.lift(sigma)
            def weighted_atom(position):
                return mp.exp(-30 / (1 - (position / radius) ** 2) +
                              (mp_exact(sigma) + 1j * modulation) * position)
            for fraction in (Fraction(-3, 5), Fraction(0), Fraction(2, 5)):
                position = family["r"] * fraction
                observed = pricing.base.atom_jets(family, position, weight, 4)
                for order in range(5):
                    expected = mp.diff(weighted_atom, mp_exact(position), order)
                    center = mp.mpc(midpoint(observed[order].real),
                                    midpoint(observed[order].imag))
                    scaled = abs(center - expected) / (abs(expected) + mp.mpf("1e-70"))
                    assert scaled < mp.mpf("1e-45"), (index, sigma, order, str(scaled))
                    worst = max(worst, scaled)
                    derivative_checks += 1
                direct = pricing.direct.jets(family, position, sigma, 0)[0]
                reconstructed = observed[2] - 2 * weight * observed[1] + weight ** 2 * observed[0]
                assert (reconstructed - direct).contains(0)
                identity_checks += 1
            for left, right in ((-family["r"], -family["r"] * Fraction(99, 100)),
                                (-family["r"] / 100, family["r"] / 100),
                                (family["r"] * Fraction(99, 100),
                                 family["r"] * Fraction(101, 100))):
                bound = pricing.base.fourth_envelope(family, left, right, weight)
                for fraction in (Fraction(0), Fraction(1, 4), Fraction(1, 2),
                                 Fraction(3, 4), Fraction(1)):
                    jets = pricing.base.atom_jets(family, left + (right - left) * fraction,
                                                 weight, 4)
                    assert abs(jets[4]) <= bound
                    envelope_checks += 1
    return dict(derivative_checks=derivative_checks, reconstruction_checks=identity_checks,
                fourth_sample_checks=envelope_checks, max_scaled_error=str(worst),
                samples_are_not_integral_certificates=True)


def validate_payload(payload):
    assert payload["record"] == 2573
    assert payload["coefficient_row"] == "ideal_correction_coefficient"
    assert Fraction(payload["error"]) == pricing.ERROR
    assert payload["curvature_weight"] == "abs(real(center))+abs(imag(center))+error"
    assert Fraction(payload["pin"]) == pricing.PIN
    for key in ("lean_certificate", "table_rounding_priced", "exact_coefficient_membership",
                "producer_go", "rh_claim"):
        assert payload[key] is False, key
    for relative, expected in payload["source_sha256"].items():
        path = ROOT / relative
        assert path.resolve().is_relative_to(ROOT.resolve())
        assert hashlib.sha256(path.read_bytes()).hexdigest() == expected, relative
    rows = payload["rows"]
    assert [row["sign"] for row in rows] == [-1, 1]
    assert len({row["cells"] for row in rows}) == 1
    cells = rows[0]["cells"]
    assert cells > 0 and payload["production_grid"] == (cells == pricing.PRODUCTION_CELLS)
    step = 2 * pricing.base.RADIUS / cells
    for row in rows:
        sigma = Fraction(row["sign"], 2)
        exact = {key: Fraction(value) for key, value in row["exact"].items()}
        assert all(value >= 0 for value in exact.values())
        assert exact["curvature"] == exact["second"] + step / 2 * exact["third"]
        assert exact["curvature_piece"] == step * exact["curvature"]
        assert exact["first_piece"] == 2 * abs(sigma) * step * (
            exact["first"] + exact["curvature"] * step / 2)
        assert exact["value_piece"] == sigma ** 2 * (
            step / 2 * exact["endpoints"] + exact["curvature"] * step ** 3 / 12)
        assert exact["total"] == sum(exact[key] for key in
                                     ("curvature_piece", "first_piece", "value_piece"))
        assert sum(Fraction(value) for value in row["profile"]) == exact["total"]
        assert Fraction(row["margin"]) == pricing.PIN - exact["total"]
        assert row["fits_pin"] == (exact["total"] <= pricing.PIN)
        for key, value in exact.items():
            assert row["display"][key] == float(value)
    assert payload["analytic_grid_fits"] == all(row["fits_pin"] for row in rows)
    for reading in payload["anchor_controls"]:
        reference = json.loads((ROOT / f"results/{reading['record']}_generation_readback.json").read_text())
        assert Fraction(reading["committed_bound"]) == Fraction(reference["cell_bound"])
        assert Fraction(reading["total"]) <= Fraction(reference["cell_bound"])
    assert {(row["record"], row["index"], row["sign"]) for row in payload["anchor_controls"]} == {
        (2570, 2700, -1), (2571, 2700, 1), (2572, 2701, -1)}
    assert payload["direct_control"]["status"] == "SAME_RUN_DIRECT_2561_EXACT_REPRODUCTION"
    reference = json.loads((ROOT / f"results/2561_correction_second_{cells}.json").read_text())
    for observed, committed in zip(payload["direct_control"]["rows"], reference["rows"]):
        for key in ("sign", "node", "remainder", "total", "margin", "fits_pin"):
            assert observed[key] == committed[key]
    assert len(payload["direct_control"]["rows"]) == 2


def mutation_controls(payload):
    mutations = []
    changed = copy.deepcopy(payload)
    changed["rows"][0]["exact"]["total"] = "0"
    mutations.append(("zero_total", changed))
    changed = copy.deepcopy(payload)
    changed["rows"] = changed["rows"][:1]
    mutations.append(("missing_sign", changed))
    changed = copy.deepcopy(payload)
    changed["coefficient_row"] = "ideal_base_coefficient"
    mutations.append(("wrong_coefficient_owner", changed))
    changed = copy.deepcopy(payload)
    changed["exact_coefficient_membership"] = True
    mutations.append(("unproved_membership", changed))
    rejected = []
    for name, changed in mutations:
        try:
            validate_payload(changed)
        except AssertionError:
            rejected.append(name)
        else:
            raise AssertionError(f"mutation accepted: {name}")
    return rejected


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--cells", type=int, default=pricing.PRODUCTION_CELLS)
    args = parser.parse_args()
    source = ROOT / f"results/2573_decomposed_grid_{args.cells}.json"
    payload = json.loads(source.read_text())
    controls = independent_controls()
    validate_payload(payload)
    rejected = mutation_controls(payload)
    result = dict(record=2573, cells=args.cells, status="DECOMPOSED_GRID_PRICE_VALIDATED",
                  analytic_grid_fits=payload["analytic_grid_fits"], controls=controls,
                  mutation_rejections=rejected, source_artifact_sha256=hashlib.sha256(
                      source.read_bytes()).hexdigest(), validator_sha256=hashlib.sha256(
                          Path(__file__).read_bytes()).hexdigest(),
                  lean_certificate=False, table_rounding_priced=False,
                  exact_coefficient_membership=False, producer_go=False, rh_claim=False)
    out = ROOT / f"results/2573_decomposed_controls_{args.cells}.json"
    out.write_text(json.dumps(result, indent=2) + "\n", encoding="utf-8", newline="\n")
    print(json.dumps(result), flush=True)


if __name__ == "__main__":
    main()
