"""Probe 988: one smooth finite-vanishing compact-log test."""

import numpy as np

from canonical_weil_numeric import (
    assert_canonical_invariants,
    canonical_weil_value,
    smooth_finite_vanishing_test,
)


def run(sample_count=40001, domain_radius=4.0, lo=0.4, hi=2.2):
    grid = np.linspace(-domain_radius, domain_radius, sample_count)
    owner = smooth_finite_vanishing_test(grid, lo, hi)
    result = canonical_weil_value(owner["test"], grid, support_radius=hi - lo)
    moments = owner["moments"]
    audit = assert_canonical_invariants(result, moments)

    print("# smooth finite-vanishing test on [%+.2f,%+.2f]" % (lo, hi))
    print(
        "M0=%+.3e Mhalf=%+.3e M1=%+.3e L2=%.8f"
        % (moments[0.0], moments[0.5], moments[1.0], owner["l2"])
    )
    print(
        "A=%+.8f arch=%+.8f pole=%+.8f primes=%+.8f psi=%+.8f"
        % (
            result["A"],
            result["arch"],
            result["pole"],
            result["prime_sum"],
            result["psi"],
        )
    )
    print("prime_terms=" + repr(result["prime_terms"]))
    print("pole_identity_error=%+.3e" % result["pole_identity_error"])
    print(
        "invariants: abs(A-L2)=%.3e abs(pole-product)=%.3e max|M|=%.3e"
        % (audit["leading_error"], audit["pole_error"], audit["moment_error"])
    )
    print("# RH NOT claimed; floating-point evidence is not a sign theorem.")


if __name__ == "__main__":
    run()
