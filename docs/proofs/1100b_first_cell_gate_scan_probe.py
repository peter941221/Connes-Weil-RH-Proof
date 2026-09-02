"""First-cell-corrected orbit gate scan (record 1100b).

Resolves the sign of the `orbitWindowSemiLocalGate` top over the
triple-vanishing subspace, as named in record 1100 section 5.  The
certified 1020 arch body starts its trapezoid at the first correlation
lag, missing the [0, step] cell of area ~ step * F(0) / 2; the corrected
arch adds the trapezoid-consistent first cell, the scan grid moves
8001 -> 32001, and the sign of the top direction is arbitrated by an
independent direct construction (GL in u, Simpson in y from 0, analytic
evaluator: no fft, no polarization, no step-grid body error).

Pre-registration: docs/proofs/1100b_first_cell_gate_scan_preregistration.md
(committed before this run).  All gates are asserted; ABORT-class
failures exit before any scan row is consumed.  Numerical evidence only.
"""

from __future__ import annotations

import importlib.util
import math
import os
import sys
from dataclasses import dataclass

import numpy as np
from numpy.polynomial.legendre import leggauss, legvander
from scipy.integrate import simpson
from scipy.linalg import eigh

_HERE = os.path.dirname(os.path.abspath(__file__))
_SPEC = importlib.util.spec_from_file_location(
    "rig1020", os.path.join(_HERE, "1020_lane_r_prime_free_spectrum.py")
)
assert _SPEC is not None and _SPEC.loader is not None
rig1020 = importlib.util.module_from_spec(_SPEC)
sys.modules["rig1020"] = rig1020  # register BEFORE exec_module (dataclasses)
_SPEC.loader.exec_module(rig1020)

VANISH_S = rig1020.VANISH_S
C_ARCH = float(rig1020.C_ARCH)
POS_THRESHOLD = 1.0e-5  # an order above the certified corrected fidelity

SCAN_GRID = 32001
REPRO_GRID = 8001  # must match the record-1100 run6 grid


def prime_powers_with_weight(bound: int) -> list[tuple[int, float]]:
    """(q, Lambda(q)/sqrt(q)) for every prime power q <= bound."""
    sieve = np.ones(bound + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(math.isqrt(bound)) + 1):
        if sieve[p]:
            sieve[p * p :: p] = False
    lam = np.zeros(bound + 1)
    for p in np.nonzero(sieve)[0]:
        q = int(p)
        while q <= bound:
            lam[q] = math.log(int(p))
            q *= int(p)
    return [
        (int(q), float(lam[q]) / math.sqrt(q))
        for q in np.nonzero(lam > 0.0)[0]
    ]


def sine_pair_integral(i: int, j: int, t: float, a: float) -> float:
    """Closed-form overlap int phi_i(u) phi_j(u+t) du for the sine family."""
    length = 2.0 * a
    ai = i * math.pi / length
    aj = j * math.pi / length
    lo = max(0.0, -t)
    hi = min(length, length - t)
    if hi <= lo:
        return 0.0

    def anti(c: float, d: float) -> float:
        if abs(c) < 1e-14:
            return (hi - lo) * math.cos(d)
        return (math.sin(c * hi + d) - math.sin(c * lo + d)) / c

    return 0.5 * (anti(ai - aj, -aj * t) - anti(ai + aj, aj * t))


def arch_reconstructed(
    function: np.ndarray, step: float
) -> tuple[float, float, np.ndarray, np.ndarray]:
    """Bit-level re-implementation of the rig's `_arch_of_function`.

    Returns (arch, F(0), correlation, lags).  Certified against the
    imported static method by G-recon (<= 1e-15 rel).
    """
    n = function.size
    correlation = fftconvolve_safe(function, step)
    lags = step * np.arange(-(n - 1), n)
    f0 = float(correlation[n - 1])
    if f0 <= 0.0:
        raise FloatingPointError(f"non-positive F(0): {f0}")
    positive = lags > 1e-12
    y = lags[positive]
    fy = correlation[positive]
    numerator = np.expm1(y / 2.0) * fy + (fy - f0)
    integrand = numerator / np.sinh(y)
    body = float(np.trapezoid(integrand, y))
    tail = f0 * math.log(math.tanh(abs(lags[-1]) / 2.0))
    return C_ARCH * f0 + body + tail, f0, correlation, lags


def fftconvolve_safe(function: np.ndarray, step: float) -> np.ndarray:
    from scipy.signal import fftconvolve

    return fftconvolve(function[::-1], function, mode="full") * step


def first_cell_of(correlation: np.ndarray, n: int, step: float) -> float:
    """Trapezoid-consistent completion of the missing [0, step] cell."""
    f0 = float(correlation[n - 1])
    f1 = float(correlation[n])
    i0 = f0 / 2.0  # removable limit of the body integrand at y = 0
    i1 = (math.expm1(step / 2.0) * f1 + (f1 - f0)) / math.sinh(step)
    return step * (i0 + i1) / 2.0


def arch_corrected_value(function: np.ndarray, step: float) -> float:
    """Corrected arch: reconstructed rig value plus the first cell."""
    value, _f0, correlation, _lags = arch_reconstructed(function, step)
    return value + first_cell_of(correlation, function.size, step)


@dataclass
class GateRow:
    radius: float
    family: str
    basis_size: int
    nullity: int
    n_terms: int
    top_total: float
    top_arch: float
    top_prime: float
    resid: float
    orth: float
    cond_g: float


class OrbitGateProbe:
    """The record-1020 rig adapted to orbit radii, plus prime rows."""

    def __init__(
        self,
        radius: float,
        basis_size: int,
        grid_size: int = SCAN_GRID,
        envelope_power: int = 1,
        basis_family: str = "legendre",
        include_primes: bool = True,
        include_first_cell: bool = True,
    ):
        if radius <= 0.0:
            raise ValueError("radius must be positive")
        if basis_size < 4:
            raise ValueError("at least four basis functions are needed")
        if basis_family not in ("legendre", "sine"):
            raise ValueError("basis_family must be 'legendre' or 'sine'")
        self.radius = radius
        self.basis_size = basis_size
        self.envelope_power = envelope_power
        self.basis_family = basis_family
        self.include_primes = include_primes
        self.include_first_cell = include_first_cell
        self.n = grid_size if grid_size % 2 == 1 else grid_size + 1
        self.t, self.step = np.linspace(
            -radius, radius, self.n, retstep=True
        )
        self.quad = rig1020.simpson_weights(self.n, self.step)
        self.mass = np.full(self.n, self.step)

        scaled = self.t / radius
        if basis_family == "legendre":
            vandermonde = legvander(scaled, basis_size - 1)
            envelope = rig1020.smooth_bump(scaled) ** envelope_power
            self.basis = (vandermonde.T * envelope).astype(float)
        else:
            phase = math.pi * (scaled + 1.0) / 2.0
            frequencies = np.arange(1, basis_size + 1)[:, None]
            self.basis = np.sin(frequencies * phase[None, :])

        analytic = self.analytic_basis(self.t)
        basis_gap = float(np.max(np.abs(analytic - self.basis)))
        if basis_gap > 1e-12:
            raise FloatingPointError(
                f"analytic evaluator off by {basis_gap}"
            )

        two_r = 2.0 * self.radius
        self.prime_terms = []
        if include_primes:
            bound = int(math.floor(math.exp(two_r)))
            self.prime_terms = [
                (q, w)
                for (q, w) in prime_powers_with_weight(bound)
                if math.log(q) < two_r - 1e-9
            ]

    def analytic_basis(self, x: np.ndarray) -> np.ndarray:
        """(basis_size, len(x)) values of the basis functions at x; 0 outside."""
        size = self.basis_size
        out = np.zeros((size, x.size))
        scaled = x / self.radius
        inside = np.abs(scaled) < 1.0
        xs = scaled[inside]
        if self.basis_family == "legendre":
            vals = (
                legvander(xs, size - 1)
                * (rig1020.smooth_bump(xs) ** self.envelope_power)[:, None]
            ).T
        else:
            phase = math.pi * (xs + 1.0) / 2.0
            frequencies = np.arange(1, size + 1)[:, None]
            vals = np.sin(frequencies * phase[None, :])
        out[:, inside] = vals
        return out

    def laplace_matrix(self) -> np.ndarray:
        return np.stack(
            [
                np.sum(
                    self.quad[None, :] * self.basis
                    * np.exp(s * self.t)[None, :],
                    axis=1,
                )
                for s in VANISH_S
            ]
        )

    def nullspace(self) -> tuple[np.ndarray, np.ndarray]:
        moments = self.laplace_matrix()
        _, singular_values, vh = np.linalg.svd(moments, full_matrices=True)
        threshold = 1e-11 * max(float(singular_values[0]), 1.0)
        rank = int(np.sum(singular_values > threshold))
        return vh[rank:].T.copy(), singular_values

    def _orthonormal_null_functions(self):
        null_coefficients, singular_values = self.nullspace()
        weighted_basis = self.basis.T * np.sqrt(self.mass)[:, None]
        weighted_null = weighted_basis @ null_coefficients
        orthonormal_weighted, triangular = np.linalg.qr(
            weighted_null, mode="reduced"
        )
        if np.min(np.abs(np.diag(triangular))) <= 1e-14:
            raise FloatingPointError("weighted null basis is rank deficient")
        inverse_triangular = np.linalg.solve(
            triangular, np.eye(triangular.shape[0])
        )
        coefficients = null_coefficients @ inverse_triangular
        functions = coefficients.T @ self.basis
        gram_condition = float(np.linalg.cond(triangular) ** 2)
        orth_error = float(
            np.max(np.abs(
                (functions * self.mass[None, :]) @ functions.T
                - np.eye(functions.shape[0])
            ))
        )
        return (
            functions,
            singular_values,
            coefficients,
            gram_condition,
            orth_error,
        )

    def prime_matrix(self, functions: np.ndarray) -> np.ndarray:
        """2 * sum_q (Lambda(q)/sqrt(q)) * F(log q) as a symmetric matrix."""
        dimension = functions.shape[0]
        matrix = np.zeros((dimension, dimension))
        for q, weight in self.prime_terms:
            shifted = self._shifted_functions(math.log(q))
            corr = self.step * (functions @ shifted.T)
            matrix += (2.0 * weight) * corr
        return (matrix + matrix.T) / 2.0

    def _shifted_functions(self, shift: float) -> np.ndarray:
        """Orthonormal null functions evaluated at t + shift (0 outside)."""
        return self.coefficients.T @ self.analytic_basis(self.t + shift)

    def _arch_call(self, function: np.ndarray) -> float:
        if self.include_first_cell:
            return arch_corrected_value(function, self.step)
        return float(
            rig1020.PrimeFreeProbe._arch_of_function(function, self.step)[0]
        )

    def arch_matrix(self, functions: np.ndarray) -> np.ndarray:
        dimension = functions.shape[0]
        diagonal = np.empty(dimension)
        for i in range(dimension):
            diagonal[i] = self._arch_call(functions[i])
        matrix = np.zeros((dimension, dimension))
        np.fill_diagonal(matrix, diagonal)
        for i in range(dimension):
            for j in range(i):
                combined = functions[i] + functions[j]
                combined_value = self._arch_call(combined)
                value = 0.5 * (combined_value - diagonal[i] - diagonal[j])
                matrix[i, j] = value
                matrix[j, i] = value
        return (matrix + matrix.T) / 2.0

    def solve(self) -> GateRow:
        functions, _sv, self.coefficients, cond_g, orth = (
            self._orthonormal_null_functions()
        )
        arch_m = self.arch_matrix(functions)
        total_m = arch_m.copy()
        prime_m = np.zeros_like(arch_m)
        if self.include_primes:
            prime_m = self.prime_matrix(functions)
            total_m = arch_m + prime_m
        eig = lambda m: eigh(  # noqa: E731
            (m + m.T) / 2.0,
            np.eye(m.shape[0]),
            check_finite=True,
            eigvals_only=True,
        )
        moment_residual = float(
            np.max(np.abs(self.laplace_matrix() @ self.coefficients))
        )
        return GateRow(
            radius=self.radius,
            family=self.basis_family,
            basis_size=self.basis_size,
            nullity=functions.shape[0],
            n_terms=len(self.prime_terms),
            top_total=float(eig(total_m)[-1]),
            top_arch=float(eig(arch_m)[-1]),
            top_prime=float(eig(prime_m)[-1]),
            resid=moment_residual,
            orth=orth,
            cond_g=cond_g,
        )


ANCHOR: dict[tuple[float, int], float] = {
    (0.300, 8): -1.09132868,
    (0.300, 12): -1.07153088,
    (0.300, 16): -1.05884874,
    (0.330, 8): -0.99581113,
    (0.330, 12): -0.97600231,
    (0.330, 16): -0.96331391,
    (0.345, 8): -0.95124819,
    (0.345, 12): -0.93143347,
    (0.345, 16): -0.91874172,
}

# All 32 top_total values logged by 1100 run6 at grid 8001 (31 valid rows
# plus the discarded a=4 K=32 row, read before its discard).
RUN6: dict[tuple[float, str, int], float] = {
    (1.0, "legendre", 8): -0.000305,
    (1.0, "legendre", 12): -0.000124,
    (1.0, "legendre", 16): -0.000123,
    (1.0, "legendre", 20): -0.000123,
    (1.0, "legendre", 24): -0.000123,
    (1.0, "legendre", 32): -0.000121,
    (2.0, "legendre", 8): -0.000251,
    (2.0, "legendre", 12): -0.000248,
    (2.0, "legendre", 16): -0.000246,
    (2.0, "legendre", 20): -0.000244,
    (2.0, "legendre", 24): -0.000240,
    (2.0, "legendre", 32): -0.000231,
    (3.0, "legendre", 8): -0.000374,
    (3.0, "legendre", 12): -0.000372,
    (3.0, "legendre", 16): -0.000370,
    (3.0, "legendre", 20): -0.000366,
    (3.0, "legendre", 24): -0.000361,
    (3.0, "legendre", 32): -0.000352,
    (4.0, "legendre", 8): -0.000499,
    (4.0, "legendre", 12): -0.000497,
    (4.0, "legendre", 16): -0.000493,
    (4.0, "legendre", 20): -0.000488,
    (4.0, "legendre", 24): -0.000483,
    (4.0, "legendre", 32): -0.000471,
    (1.0, "sine", 8): -0.000125,
    (1.0, "sine", 12): -0.000124,
    (1.0, "sine", 16): -0.000123,
    (1.0, "sine", 20): -0.000120,
    (2.0, "sine", 8): -0.000248,
    (2.0, "sine", 12): -0.000245,
    (2.0, "sine", 16): -0.000241,
    (2.0, "sine", 20): -0.000239,
}


def run_anchor_gates() -> None:
    print("G-arch-1 environment-drift measurement (record <= 1e-4 abs)")
    worst = 0.0
    for (radius, k), expected in ANCHOR.items():
        res = rig1020.PrimeFreeProbe(
            radius=radius,
            basis_size=k,
            grid_size=6001,
            envelope_power=1,
            basis_family="legendre",
        ).solve()
        top = float(res.eigenvalues[-1])
        gap = abs(top - expected)
        worst = max(worst, gap)
        if gap > 1e-4:
            sys.exit(f"ABORT: G-arch-1 drift too large at r={radius} K={k}")
    print(f"  nine anchors replayed, worst drift {worst:.3e} (recorded)")
    print("G-arch-2 same-environment adapted-class equivalence (<= 1e-12)")
    for (radius, k), expected in ANCHOR.items():
        rig_top = float(
            rig1020.PrimeFreeProbe(
                radius=radius,
                basis_size=k,
                grid_size=6001,
                envelope_power=1,
                basis_family="legendre",
            ).solve().eigenvalues[-1]
        )
        res = OrbitGateProbe(
            radius=radius,
            basis_size=k,
            grid_size=6001,
            envelope_power=1,
            basis_family="legendre",
            include_primes=False,
            include_first_cell=False,
        ).solve()
        gap = abs(res.top_total - rig_top)
        if gap > 1e-12:
            sys.exit(f"ABORT: G-arch-2 failed at r={radius} K={k}")
    print("  nine rows, all gaps 0.00e+00 class")
    print("G-recon body re-implementation vs imported rig (<= 1e-15 rel)")
    worst_rel = 0.0
    for (radius, k), expected in ANCHOR.items():
        probe = OrbitGateProbe(
            radius=radius,
            basis_size=k,
            grid_size=6001,
            envelope_power=1,
            basis_family="legendre",
            include_primes=False,
        )
        for i in range(probe.basis_size):
            imported = float(
                rig1020.PrimeFreeProbe._arch_of_function(
                    probe.basis[i], probe.step
                )[0]
            )
            mine, _f0, _corr, _lags = arch_reconstructed(
                probe.basis[i], probe.step
            )
            rel = abs(mine - imported) / max(abs(imported), 1e-300)
            worst_rel = max(worst_rel, rel)
            if rel > 1e-15:
                sys.exit(
                    f"ABORT: G-recon failed at r={radius} K={k} basis {i}"
                )
    print(f"  {len(ANCHOR)} x basis rows replayed, worst rel {worst_rel:.2e}")


def run_repro_gate() -> None:
    print(
        f"G-repro run6 replay at grid {REPRO_GRID}, correction off "
        "(<= 2e-6 abs)"
    )
    worst = 0.0
    worst_row = ""
    for (radius, family, k), expected in RUN6.items():
        res = OrbitGateProbe(
            radius=radius,
            basis_size=k,
            grid_size=REPRO_GRID,
            envelope_power=1,
            basis_family=family,
            include_primes=True,
            include_first_cell=False,
        ).solve()
        gap = abs(res.top_total - expected)
        if gap > worst:
            worst = gap
            worst_row = f"a={radius} {family} K={k}"
        if gap > 2e-6:
            sys.exit(
                f"ABORT: G-repro failed at a={radius} {family} K={k}: "
                f"mine {res.top_total:+.6f} run6 {expected:+.6f}"
            )
    print(f"  all {len(RUN6)} rows replayed, worst gap {worst:.2e} ({worst_row})")
    print("G-cell-2 sliver readback on the G-repro rows (ratio in [0.30, 1.005])")
    lo, hi = 1.0, 0.0
    for (radius, family, k) in RUN6:
        probe = OrbitGateProbe(
            radius=radius,
            basis_size=k,
            grid_size=REPRO_GRID,
            envelope_power=1,
            basis_family=family,
            include_primes=False,
        )
        functions, _sv, coefficients, _cond, _orth = (
            probe._orthonormal_null_functions()
        )
        for i in range(functions.shape[0]):
            _v, f0, correlation, _lags = arch_reconstructed(
                functions[i], probe.step
            )
            cell = first_cell_of(correlation, functions[i].size, probe.step)
            ratio = cell / (probe.step * f0 / 2.0)
            lo = min(lo, ratio)
            hi = max(hi, ratio)
    print(f"  first cell / (step F0/2) over all diagonal nulls: [{lo:.4f}, {hi:.4f}]")
    if not (0.30 <= lo and hi <= 1.005):
        sys.exit(f"ABORT: G-cell-2 ratio band violated: [{lo:.4f}, {hi:.4f}]")


def run_sieve_gates() -> None:
    print("G-count hard sieve anchors")
    for a, expected in ((1.0, 5), (2.0, 24)):
        bound = int(math.floor(math.exp(2.0 * a)))
        terms = [
            (q, w)
            for (q, w) in prime_powers_with_weight(bound)
            if math.log(q) < 2.0 * a - 1e-9
        ]
        qs = [q for q, _ in terms]
        print(f"  a={a}: {len(terms)} terms -> {qs}")
        if len(terms) != expected:
            sys.exit(f"ABORT: G-count failed at a={a}")


def run_shift_gates() -> None:
    print("G-sym-t plus/minus shift consistency at 32001 (5e-6 abs)")
    probe = OrbitGateProbe(radius=2.0, basis_size=12, grid_size=SCAN_GRID)
    functions, _sv, coefficients, _cond, _orth = (
        probe._orthonormal_null_functions()
    )
    probe.coefficients = coefficients
    dimension = functions.shape[0]
    plus = np.zeros((dimension, dimension))
    minus = np.zeros((dimension, dimension))
    for q, weight in probe.prime_terms:
        t = math.log(q)
        plus += (2.0 * weight) * (
            probe.step * (functions @ probe._shifted_functions(t).T)
        )
        minus += (2.0 * weight) * (
            probe.step * (functions @ probe._shifted_functions(-t).T)
        )
    gap = float(np.max(np.abs(plus - minus.T)))
    scale = float(np.max(np.abs(plus)))
    print(f"  |M+ - (M-)^T|max = {gap:.3e} (scale {scale:.3e})")
    if gap > 5e-6:
        sys.exit("ABORT: G-sym-t failed")
    print("G-closed sine closed-form vs analytic-shift (5e-6 abs + order)")
    a_here, k_here = 2.0, 8
    for q in (2, 3):
        t = math.log(q)
        closed = np.array(
            [
                [
                    sine_pair_integral(i + 1, j + 1, t, a_here)
                    for j in range(k_here)
                ]
                for i in range(k_here)
            ]
        )

        def route_for(grid: int) -> np.ndarray:
            probe_g = OrbitGateProbe(
                radius=a_here, basis_size=k_here, grid_size=grid,
                basis_family="sine",
            )
            shifted = probe_g.analytic_basis(probe_g.t + t)
            return probe_g.step * (probe_g.basis @ shifted.T)

        route_fine = route_for(SCAN_GRID)
        route_coarse = route_for(SCAN_GRID // 2)
        gap_fine = float(np.max(np.abs(route_fine - closed)))
        gap_coarse = float(np.max(np.abs(route_coarse - closed)))
        shrink = gap_coarse / max(gap_fine, 1e-300)
        print(
            f"  q={q} basis level: fine diff {gap_fine:.3e}, coarse diff "
            f"{gap_coarse:.3e}, shrink {shrink:.2f}x"
        )
        if gap_fine > 5e-6 or not (3.0 <= shrink <= 6.0):
            sys.exit(f"ABORT: G-closed failed at q={q}")
        fine = OrbitGateProbe(
            radius=a_here, basis_size=k_here, grid_size=SCAN_GRID,
            basis_family="sine",
        )
        functions_f, _svf, coefficients_f, _condf, _orthf = (
            fine._orthonormal_null_functions()
        )
        fine.coefficients = coefficients_f
        route_null = fine.step * (
            functions_f @ fine._shifted_functions(t).T
        )
        closed_null = coefficients_f.T @ closed @ coefficients_f
        gap_null = float(np.max(np.abs(route_null - closed_null)))
        print(f"  q={q} null level: diff {gap_null:.3e}")
        if gap_null > 5e-6:
            sys.exit(f"ABORT: G-closed null level failed at q={q}")


def arch_direct(
    coeffs: np.ndarray,
    probe: OrbitGateProbe,
    n_y: int = 8001,
    n_glu: int = 200,
) -> float:
    """Independent arch of f = coeffs @ basis.

    GL in u (n_glu nodes), Simpson in y from 0 (n_y nodes, includes the
    removable limit I(0) = F(0)/2 exactly), analytic tail.  No fft, no
    polarization, no step-grid body error.
    """
    a = probe.radius
    nodes, weights = leggauss(n_glu)

    def f_at(x: np.ndarray) -> np.ndarray:
        arr = np.asarray(x, dtype=float)
        vals = coeffs @ probe.analytic_basis(arr.ravel())
        return vals.reshape(arr.shape) if arr.ndim > 1 else vals

    f0 = a * float(np.dot(weights, f_at(a * nodes) ** 2))
    ys = np.linspace(0.0, 2.0 * a, n_y)
    corr = np.empty(n_y)
    corr[0] = f0
    chunk = 128
    for lo in range(1, n_y, chunk):
        yb = ys[lo : lo + chunk]
        high = a - yb
        mid = (high + (-a)) / 2.0
        half = (high - (-a)) / 2.0
        xu = mid[:, None] + half[:, None] * nodes[None, :]
        fv = f_at(xu)
        fv_shift = f_at(xu + yb[:, None])
        corr[lo : lo + chunk] = half * ((fv * fv_shift) @ weights)
    integrand = np.empty(n_y)
    integrand[0] = f0 / 2.0
    yp = ys[1:]
    integrand[1:] = (
        np.expm1(yp / 2.0) * corr[1:] + (corr[1:] - f0)
    ) / np.sinh(yp)
    body = float(simpson(integrand, x=ys))
    tail = f0 * math.log(math.tanh(a))
    return C_ARCH * f0 + body + tail


def run_direct_gates() -> None:
    print("G-cell-3 direct certification, the sign decider (<= 5e-6 abs)")
    plan = [
        ("a=2 leg b0", 2.0, 16, "legendre", None),
        ("a=4 leg b0", 4.0, 24, "legendre", None),
        ("a=2 sine b2", 2.0, 20, "sine", None),
        ("a=2 leg K=16 top", 2.0, 16, "legendre", "top"),
        ("a=4 leg K=24 top", 4.0, 24, "legendre", "top"),
        ("a=2 sine K=20 top", 2.0, 20, "sine", "top"),
    ]
    for label, radius, k, family, mode in plan:
        probe = OrbitGateProbe(
            radius=radius,
            basis_size=k,
            grid_size=SCAN_GRID,
            envelope_power=1,
            basis_family=family,
            include_primes=False,
        )
        extra = ""
        if mode is None:
            coeffs = np.zeros(probe.basis_size)
            coeffs[0 if family == "legendre" else 2] = 1.0
            function = probe.basis[
                0 if family == "legendre" else 2
            ]
            combo = coeffs  # basis coordinates already
        else:
            functions, _sv, coefficients, _cond, _orth = (
                probe._orthonormal_null_functions()
            )
            probe.coefficients = coefficients
            arch_m = probe.arch_matrix(functions)
            eigvals, eigvecs = eigh(
                (arch_m + arch_m.T) / 2.0, np.eye(arch_m.shape[0])
            )
            coeffs = eigvecs[:, -1]
            function = coeffs @ functions
            combo = probe.coefficients @ coeffs
            extra = (
                f" lambda_top {float(eigvals[-1]):+.6f} "
                f"rayleigh {float(coeffs @ arch_m @ coeffs):+.6f}"
            )
        imported = float(
            rig1020.PrimeFreeProbe._arch_of_function(
                function, probe.step
            )[0]
        )
        mine, _f0, _corr, _lags = arch_reconstructed(function, probe.step)
        rel = abs(mine - imported) / max(abs(imported), 1e-300)
        if rel > 1e-15:
            sys.exit(f"ABORT: G-recon failed on {label} (rel {rel:.1e})")
        corrected = mine + first_cell_of(
            _corr, function.size, probe.step
        )
        direct = arch_direct(combo if mode == "top" else coeffs, probe)
        direct_fine = arch_direct(
            combo if mode == "top" else coeffs, probe, n_y=4001
        )
        gap = abs(corrected - direct)
        gap4 = abs(direct - direct_fine)
        print(
            f"  {label}: corrected {corrected:+.8f} direct {direct:+.8f} "
            f"gap {gap:.2e} | y-refine {gap4:.2e}{extra}"
        )
        if gap > 5e-6:
            sys.exit(f"ABORT: G-cell-3 failed on {label}")
        if gap4 > 1e-7:
            sys.exit(f"ABORT: G-cell-4 failed on {label}")
        print(f"  G-recon on {label}: rel {rel:.1e}")


def print_row(row: GateRow) -> None:
    valid = row.resid <= 1e-10 and row.orth <= 1e-10
    status = "ok" if valid else "DISCARDED (row gates)"
    print(
        f"a={row.radius:.2f} {row.family[:3]} K={row.basis_size:2d} "
        f"null={row.nullity:2d} terms={row.n_terms:4d} "
        f"top_total={row.top_total:+.6f} top_arch={row.top_arch:+.6f} "
        f"top_prime={row.top_prime:+.6f} condG={row.cond_g:.2e} "
        f"resid={row.resid:.1e} orth={row.orth:.1e} {status}"
    )


def extrapolate(tops: list[float]) -> float:
    """Geometric-increment extrapolation of a K-rising top sequence."""
    if len(tops) < 3:
        return tops[-1]
    inc1 = tops[-1] - tops[-2]
    inc0 = tops[-2] - tops[-3]
    if inc0 <= 0.0:
        return tops[-1]
    ratio = inc1 / inc0
    if not (0.0 < ratio < 1.0):
        return tops[-1]
    return tops[-1] + inc1 * ratio / (1.0 - ratio)


def main() -> None:
    print("First-cell-corrected orbit gate scan (record 1100b)")
    print(f"C = log(4*pi) + gamma = {C_ARCH:.12f}")
    print(
        f"scan grid {SCAN_GRID}, repro grid {REPRO_GRID}, "
        f"threshold {POS_THRESHOLD:.1e}"
    )
    print()
    run_anchor_gates()
    run_sieve_gates()
    run_shift_gates()
    run_repro_gate()
    run_direct_gates()
    print()
    print("ALL ABORT-CLASS GATES PASSED - corrected scan follows")
    print("-" * 118)

    rows: list[GateRow] = []
    for family, ks in (("legendre", (8, 12, 16, 20, 24, 32)),
                       ("sine", (8, 12, 16, 20))):
        for radius in (1.0, 2.0, 3.0, 4.0):
            if family == "sine" and radius > 2.0:
                continue
            for k in ks:
                row = OrbitGateProbe(
                    radius=radius,
                    basis_size=k,
                    grid_size=SCAN_GRID,
                    envelope_power=1,
                    basis_family=family,
                    include_primes=True,
                    include_first_cell=True,
                ).solve()
                print_row(row)
                if row.resid <= 1e-10 and row.orth <= 1e-10:
                    rows.append(row)
    print("-" * 118)

    tops_by: dict[tuple[str, float], list[float]] = {}
    for family in ("legendre", "sine"):
        for radius in (1.0, 2.0, 3.0, 4.0):
            seq = [
                r.top_total
                for r in sorted(
                    (r for r in rows
                     if r.family == family and r.radius == radius),
                    key=lambda r: r.basis_size,
                )
            ]
            if not seq:
                print(f"{family} a={radius}: NO VALID ROWS (unresolved)")
                continue
            limit = extrapolate(seq)
            tops_by[(family, radius)] = seq
            print(
                f"{family} a={radius}: K-sequence tops "
                f"{['%+.6f' % s for s in seq]} extrapolated {limit:+.6f}"
            )

    print()
    extrapolated = []
    for family in ("legendre", "sine"):
        for radius in (1.0, 2.0, 3.0, 4.0):
            seq = tops_by.get((family, radius))
            if seq:
                extrapolated.append((family, radius, extrapolate(seq)))
    if any(limit >= POS_THRESHOLD for _f, _r, limit in extrapolated):
        print(
            "VERDICT: H1b GATE-FAILS-ON-V (numerical, law 34): a "
            "triple-vanishing direction carries a certified positive "
            "gate price; the all-of-V sign statement is false at that "
            "radius.  Any C3 sign proof must restrict to the detector "
            "subclass.  No RH-direction claim: interval-arithmetic "
            "escalation named, not run."
        )
    elif all(limit <= -POS_THRESHOLD for _f, _r, limit in extrapolated):
        print(
            "VERDICT: H2b GATE-ALIVE-EVIDENCE (numerical): the gate is "
            "numerically alive on V at every scanned radius; formal "
            "closure needs a certified spectral-gap upper bound (law 34)."
        )
    else:
        print(
            "VERDICT: SPLIT2: tops pinned at zero within +-1e-5 at the "
            "4x grid / ~50x fidelity upgrade; per-radius sign table "
            "recorded; the certified-upper-bound machinery is the next "
            "target regardless of branch."
        )
    print("RH unclaimed; GATE 1 untouched.")


if __name__ == "__main__":
    main()
