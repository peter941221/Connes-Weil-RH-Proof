"""Probe 987: canonical Weil value on the raw centered bump."""

import numpy as np

from canonical_weil_numeric import (
    CRITICAL_POINTS,
    assert_canonical_invariants,
    canonical_weil_value,
    centered_bump,
    mellin_moment,
)


def run(sample_count=40001, domain_radius=4.0):
    grid = np.linspace(-domain_radius, domain_radius, sample_count)
    test = centered_bump(grid)
    result = canonical_weil_value(test, grid, support_radius=2.0)
    moments = {point: mellin_moment(test, grid, point) for point in CRITICAL_POINTS}
    audit = assert_canonical_invariants(result)

    print("# raw centered bump under the canonical complete functional")
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
    print(
        "M0=%+.8e Mhalf=%+.8e M1=%+.8e pole_identity_error=%+.3e"
        % (moments[0.0], moments[0.5], moments[1.0], result["pole_identity_error"])
    )
    print("prime_terms=" + repr(result["prime_terms"]))
    print(
        "invariants: abs(A-L2)=%.3e abs(pole-product)=%.3e"
        % (audit["leading_error"], audit["pole_error"])
    )
    print("# RH NOT claimed; this bump does not satisfy the three vanishings.")


if __name__ == "__main__":
    run()
