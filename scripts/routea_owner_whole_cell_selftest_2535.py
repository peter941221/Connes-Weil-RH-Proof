"""Independent derivative and support-edge controls for record 2535."""
from fractions import Fraction
import json

import mpmath as mp
from flint import acb, arb, ctx

import routea_owner_whole_cell_2535 as target


def main():
    ctx.prec = 192
    mp.mp.dps = 100
    assert target.POLYS == [
        {0: 1}, {1: -60}, {0: -60, 2: 3480, 4: 180},
        {1: 10080, 3: -193680, 5: -31680, 7: -720},
        {0: 10080, 2: -1085040, 4: 10189440, 6: 3575520, 8: 266400, 10: 3600}]
    # Explicit positive floor, not underflow-to-zero, at a flat support edge.
    assert target.exact_upper(arb(-100000).exp()) == Fraction(1, 2**128)
    assert target.exact_upper(arb(0)) == 0
    families = target.load_families()
    checks = 0
    worst_relative = mp.mpf(0)
    # Independent differentiation of the original exponential, not the recurrence.
    for f in (families[0], families[14], families[-1]):
        r = mp.mpf(f["r"].numerator)/f["r"].denominator
        theta = mp.mpf(f["theta_exact"].numerator)/f["theta_exact"].denominator
        for sign in (Fraction(-1, 2), Fraction(1, 2)):
            for ratio in (Fraction(-9, 10), Fraction(-1, 3), Fraction(0), Fraction(2, 5), Fraction(9, 10)):
                x = ratio*f["r"]
                xm = mp.mpf(x.numerator)/x.denominator
                fn = lambda y: mp.exp(-30/(1-(y/r)**2)+(mp.mpf(sign.numerator)/sign.denominator+1j*theta)*y)
                jets = target.atom_jets(f, x, target.lift(sign), 4)
                for order, got in enumerate(jets):
                    expected = mp.diff(fn, xm, order)
                    real_mid = Fraction(str(got.real.mid().fmpq()))
                    imag_mid = Fraction(str(got.imag.mid().fmpq()))
                    measured = (mp.mpf(real_mid.numerator)/real_mid.denominator
                                + 1j*mp.mpf(imag_mid.numerator)/imag_mid.denominator)
                    rel = abs(measured-expected)/max(abs(expected), mp.mpf("1e-200"))
                    worst_relative = max(worst_relative, rel)
                    assert rel < mp.mpf("1e-45"), (order, ratio, sign, rel)
                    checks += 1
    # Whole-cell envelope must include interior, crossing, exterior and zero-crossing cells.
    envelope_checks = 0
    for f in (families[0], families[-1]):
        for lo, hi in ((-11, -9), (-10, -8), (-1, 1), (2, 3), (9, 11), (11, 12)):
            a, b = f["r"]*Fraction(lo, 10), f["r"]*Fraction(hi, 10)
            for sign in (Fraction(-1, 2), Fraction(1, 2)):
                bound = target.fourth_envelope(f, a, b, target.lift(sign))
                for j in range(33):
                    x = a+(b-a)*Fraction(j, 32)
                    value = abs(target.atom_jets(f, x, target.lift(sign), 4)[4])
                    assert value.upper() <= bound, (lo, hi, j)
                    envelope_checks += 1
        assert all(z == 0 for z in target.atom_jets(f, f["r"], arb(0), 4))
        assert all(z == 0 for z in target.atom_jets(f, -f["r"], arb(0), 4))
    # Inject coefficient uncertainty: error must survive exact cancellation of centers.
    f = dict(families[0])
    f["center"], f["error"] = acb(0), arb(7)
    value, _ = target.point_data([f], Fraction(0), arb(0))
    assert value >= (7*arb(-30).exp()).lower() and value > 0
    print(json.dumps(dict(status="PASS", derivative_checks=checks,
                          worst_relative=str(worst_relative),
                          whole_cell_sample_controls=envelope_checks,
                          injected_error_survives=True)), flush=True)


if __name__ == "__main__":
    main()
