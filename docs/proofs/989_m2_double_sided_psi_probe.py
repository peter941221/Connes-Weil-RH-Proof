"""Probe 989: smooth finite-vanishing tests under the complete functional."""

import numpy as np

from canonical_weil_numeric import (
    assert_canonical_invariants,
    canonical_weil_value,
    smooth_finite_vanishing_test,
)


def one_case(sample_count, domain_radius, lo, hi, verbose=True):
    grid = np.linspace(-domain_radius, domain_radius, sample_count)
    owner = smooth_finite_vanishing_test(grid, lo, hi)
    result = canonical_weil_value(owner["test"], grid, support_radius=hi - lo)
    moments = owner["moments"]
    audit = assert_canonical_invariants(result, moments)
    output = {
        "M0": moments[0.0],
        "Mh": moments[0.5],
        "M1": moments[1.0],
        "L2": owner["l2"],
        "A": result["A"],
        "arch": result["arch"],
        "pole": result["pole"],
        "prime_sum": result["prime_sum"],
        "prime_terms": result["prime_terms"],
        "psi": result["psi"],
        "pole_identity_error": result["pole_identity_error"],
        "leading_error": audit["leading_error"],
        "moment_error": audit["moment_error"],
    }
    if verbose:
        print("# window=[%+.2f,%+.2f] width=%.2f" % (lo, hi, hi - lo))
        print(
            "M0=%+.3e Mhalf=%+.3e M1=%+.3e L2=%.8f A=%.8f"
            % (output["M0"], output["Mh"], output["M1"], output["L2"], output["A"])
        )
        print(
            "arch=%+.8f pole=%+.8f primes=%+.8f psi=%+.8f"
            % (output["arch"], output["pole"], output["prime_sum"], output["psi"])
        )
        print("prime_terms=" + repr(output["prime_terms"]))
        print("pole_identity_error=%+.3e" % output["pole_identity_error"])
    return output


def convergence_table():
    print("# convergence: complete functional, invariant assertions enabled")
    print("# window              N         psi          arch        primes      max|M|")
    for lo, hi in [(-0.5, 1.5), (-1.5, 1.5), (-2.0, 2.5)]:
        for sample_count in (10001, 20001, 40001):
            result = one_case(sample_count, 5.0, lo, hi, verbose=False)
            print(
                "[%+.1f,%+.1f] %7d  %+.9f  %+.9f  %+.9f  %.2e"
                % (
                    lo,
                    hi,
                    sample_count,
                    result["psi"],
                    result["arch"],
                    result["prime_sum"],
                    result["moment_error"],
                )
            )


def main():
    for lo, hi in [
        (-0.5, 1.5),
        (-1.0, 1.0),
        (-1.5, 1.5),
        (-2.0, 2.0),
        (-1.5, 2.0),
        (-2.0, 2.5),
    ]:
        one_case(40001, 5.0, lo, hi)
        print()
    convergence_table()
    print("# RH NOT claimed; values are floating-point diagnostics.")


if __name__ == "__main__":
    main()
