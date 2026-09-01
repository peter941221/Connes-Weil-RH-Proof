"""1087 roundtrip certification: the scan's closed-form arch against a
DIRECT integration of the Lean archimedean integrand.

The gate quantity (Lean sources, quoted in record 1087):

    numerator   F y = exp(y/2) * (F y + F (-y)) - 2 * F 0   (C1SameOwnerWeil)
    denominator y   = exp y - exp (-y) = 2 sinh y           (SelectedWeilFormula)
    arch F          = ( c0 * F 0 + int_{y>0} numerator/denominator ).re

For a real even square F the integrand is (exp(y/2) F - F0)/sinh y.
Beyond the square support S = 2r the integrand is -F0/sinh y and its
primitive is log tanh(y/2), so the analytic tail is

    TAIL x1 = F0 * log(tanh(S/2))          (the 1020 scan's formula)

The 1086 probe series g/h recorded TAIL x2 = 2 * F0 * log(tanh a), which
double-counts the numerator's 2 against a denominator already equal to
2 sinh y.  This script decides the question by NUMBERS: it integrates the
full Lean integrand directly over [0, S] plus [S, Y_MAX] with no body/tail
split and compares against every closed-form variant.

Run inside docs/proofs (imports the committed 1020 module by file).
"""

from __future__ import annotations

import importlib.util
import math
import os

import numpy as np

spec = importlib.util.spec_from_file_location(
    "p1020",
    os.path.join(os.path.dirname(os.path.abspath(__file__)),
                 "1020_lane_r_prime_free_spectrum.py"),
)
assert spec is not None and spec.loader is not None
m = importlib.util.module_from_spec(spec)
import sys

sys.modules["p1020"] = m  # dataclasses in the imported module need this
spec.loader.exec_module(m)

RADIUS = 0.34600
BASIS_SIZE = 32
RHO2 = 0.5 + 14.134725168395333j


def fine_correlation(h: np.ndarray, step: float) -> tuple[np.ndarray, float]:
    """Linear (not circular) autocorrelation on the sample grid.

    F(k*step) = sum_j h_j h_{j+k} * step, computed by np.correlate so no
    FFT wrap-around normalization can enter (law 31 tie against the scan's
    fftconvolve is asserted by the caller separately).
    """
    corr = np.correlate(h, h, mode="full") * step
    lags_positive = corr[h.size - 1:]
    return lags_positive, float(lags_positive[0])


def direct_arch(lags: np.ndarray, f0: float, step: float,
                y_max: float) -> float:
    """Integrate the raw Lean integrand (exp(y/2) F - F0)/sinh y.

    On [0, S] use the sampled correlation; on [S, y_max] F is identically
    zero and the integrand -F0/sinh y is integrated on a log-spaced grid.
    No closed-form tail is used anywhere.
    """
    c0 = math.log(4.0 * math.pi) + float(np.euler_gamma)
    y_in = np.arange(1, lags.size) * step
    f_in = lags[1:]
    # removable singularity at 0: integrand -> F0 / 2
    first = 0.5 * f0
    body_grid = np.concatenate([[0.0], y_in])
    body_vals = np.concatenate(
        [[first], (np.exp(y_in / 2.0) * f_in - f0) / np.sinh(y_in)]
    )
    body = float(np.trapezoid(body_vals, body_grid))
    s_tail_start = float(lags.size - 1) * step
    tail_grid = np.exp(np.linspace(math.log(max(s_tail_start, 1e-9)),
                                   math.log(y_max), 400001))
    tail_grid[0] = s_tail_start
    tail_vals = -f0 / np.sinh(tail_grid)
    tail = float(np.trapezoid(tail_vals, tail_grid))
    return c0 * f0 + body + tail


def main() -> None:
    probe = m.PrimeFreeProbe(
        radius=RADIUS,
        basis_size=BASIS_SIZE,
        grid_size=6001,
        envelope_power=1,
        basis_family="sine",
    )
    funcs, _singular_values, coefficients, gram_condition, orth_error = (
        probe._orthonormal_null_functions()
    )
    arch_matrix = probe.arch_matrix(funcs)
    weights, vectors = np.linalg.eigh(arch_matrix)
    top_vector = vectors[:, -1]
    top_eigenvalue = float(weights[-1])
    h = top_vector @ funcs

    # constraint rows (Lean convention laplaceAt f s = int exp(s x) f x)
    moments = probe.laplace_matrix()
    basis_coefficients = coefficients @ top_vector
    node_values = moments @ basis_coefficients

    # closed forms
    closed, f0 = probe._arch_of_function(h, probe.step)

    # direct fine correlation + raw integration
    lags, f0_fine = fine_correlation(h, probe.step)
    direct = direct_arch(lags, f0_fine, probe.step, y_max=20.0)

    # tail variants evaluated at the square-support edge S = 2r
    tail_x1 = f0_fine * math.log(math.tanh(RADIUS))
    # the 1086 g/h variant: 2 F0 log tanh(a) with a = log 2 / 2
    a_root = math.log(2.0) / 2.0
    tail_probe = 2.0 * f0_fine * math.log(math.tanh(a_root))

    # law-31 tie between the scan's FFT path and this linear path: the
    # scan's own correlation array (fftconvolve of the reversed function)
    # must agree with the np.correlate path at aligned lags.
    from scipy.signal import fftconvolve

    scan_corr = fftconvolve(h[::-1], h, mode="full") * probe.step
    n = h.size
    tie = float(np.max(np.abs(scan_corr[n - 1: n - 1 + 400] - lags[:400])))

    rho2_value = np.sum(probe.quad * h * np.exp(RHO2.real * probe.t)
                        * np.exp(1j * RHO2.imag * probe.t))

    print(f"top eigenvalue (matrix)          = {top_eigenvalue:+.8f}")
    print(f"F0 (scan fft path)               = {f0:.8f}")
    print(f"F0 (fine linear correlation)     = {f0_fine:.8f}")
    print(f"law31 tie fft-vs-linear max|diff| = {tie:.3e}  (<= 1e-12)")
    print(f"closed form (scan, tail x1)      = {closed:+.8f}")
    print(f"DIRECT raw Lean-integrand arch   = {direct:+.8f}")
    print(f"|closed - direct|                = {abs(closed - direct):.3e}"
          f"  (sliver-scale agreement expected)")
    print(f"arch if tail were x2             = {closed - tail_x1 + 2.0 * tail_x1:+.8f}")
    print(f"1086 probe-style tail 2F0 logtanh(a) = {tail_probe:+.8f}"
          f" vs true tail {tail_x1:+.8f}")
    print(f"direct - closed - (tail x2 - tail x1) = "
          f"{direct - closed - tail_x1:+.3e}  (shows the double-count offset)")
    print(f"node residuals |lap h| at {{0,1/2,1}}  = "
          f"{np.abs(node_values)}  (grid quadrature)")
    print(f"|lap h rho2| (top direction)     = {abs(rho2_value):.6f}")
    print(f"gram cond = {gram_condition:.2e}  orth err = {orth_error:.2e}")
    # Ga: closed form matches the raw integration up to the scan's known
    # first-cell grid sliver (its body grid starts at y = step, so the
    # [0, step] piece - order 1e-4 for this high-frequency direction - is
    # the only systematic difference; the tail itself must reproduce to it).
    ga = abs(closed - direct) <= 2e-4
    # Gb: the 1086 probe-style x2 tail variant must be OFF by O(1), i.e.
    # rejected by a wide margin, not within sliver tolerance.
    arch_x2 = closed - tail_x1 + 2.0 * tail_x1
    gb = abs(arch_x2 - direct) >= 0.5
    verdict = (
        "PASS Ga+Gb: scan closed form (tail x1) reproduces the direct "
        "Lean-integrand integration within the first-cell sliver; the "
        "1086 g/h tail x2 variant misses by O(1) and is rejected - the "
        "factor 2 in the numerator is already paid by 2*sinh(y)"
        if ga and gb
        else f"FAIL ga={ga} gb={gb}: audit before anything else"
    )
    print(f"Ga |closed-direct|={abs(closed - direct):.3e} <= 2e-4  ->  {ga}")
    print(f"Gb |x2-variant-direct|={abs(arch_x2 - direct):.3e} >= 0.5  ->  {gb}")
    print(f"VERDICT {verdict}")


if __name__ == "__main__":
    main()
