"""Lane R arch-sign probe (2026-08-18).

Question
--------
Lane R (the sole RH-level gap of the C1 route) says, on triple-vanishing
prime-free squares (support of g^2 inside (-log 2, log 2), pole killed by
laplaceAt g (1/2) = 0):

    qw g = - archimedeanTerm (g.convolutionSquare)  >= 0
    i.e. archimedeanTerm (g^2) <= 0.

This probe samples the space of triple-vanishing prime-free compact-log
tests g and reports the sign landscape of arch(g^2), together with the
detector-oriented root (extra laplaceAt g rho = -1 at an off-line point),
which the Lean theory predicts has arch(g^2) > 0.

Exact Lean definitions mirrored here (Dev/C1SameOwnerWeil.lean,
Source/CCM25Concrete/*.lean):

    laplaceAt g s          = INT g(t) e^{s t} dt
    convolutionSquare      = g* * g   (Hermitian; F(0) = ||g||_L2^2)
    archimedeanDenominator = 2 sinh y
    archimedeanTerm F      = (log(4 pi) + gamma) * F(0)
                             + Re INT_{y>0}
                               (e^{y/2} (F(y)+F(-y)) - 2 F(0)) / (2 sinh y) dy

Output verdict lines start with SIGN/OK/FAIL.
"""

import numpy as np

C_ARCH = np.log(4.0 * np.pi) + np.euler_gamma
VANISH_S = [0.0, 0.5, 1.0]


def bump(x, a, b):
    """Smooth bump supported exactly on the open interval (a, b)."""
    z = (2.0 * x - (a + b)) / (b - a)
    out = np.zeros_like(x)
    m = np.abs(z) < 1.0
    zm = z[m]
    out[m] = np.exp(-1.0 / (1.0 - zm * zm))
    return out


def simpson_weights(n):
    """Composite Simpson weights for n odd points (n-1 even intervals)."""
    if n % 2 == 0:
        raise ValueError("need odd number of points")
    w = np.ones(n)
    w[1:-1:2] = 4.0
    w[2:-1:2] = 2.0
    return w


class Probe:
    def __init__(self, w_half, n_grid=4001, k_max=6):
        self.a = np.log(1.0 - w_half)
        self.b = np.log(1.0 + w_half)
        self.n = n_grid if n_grid % 2 == 1 else n_grid + 1
        self.k_max = k_max
        # grid slightly wider so the bump is exactly zero at the ends
        self.t, self.h = np.linspace(
            self.a - 1e-9, self.b + 1e-9, self.n, retstep=True
        )
        self.phi = bump(self.t, self.a, self.b)
        self.sw = simpson_weights(self.n) * self.h
        # basis psi_k = phi * e^{k t}
        self.basis = np.stack(
            [self.phi * np.exp(k * self.t) for k in range(k_max + 1)]
        )

    def laplace_of(self, coeff, s):
        """laplaceAt (sum coeff_k psi_k) s = INT g e^{s t} dt (complex s ok)."""
        g = np.tensordot(coeff, self.basis, axes=(0, 0))
        return np.sum(self.sw * g * np.exp(s * self.t))

    def vanish_matrix(self):
        """Rows: Re/Im moments at s in VANISH_S (3 real rows)."""
        rows = []
        for s in VANISH_S:
            rows.append(
                np.array(
                    [
                        np.sum(self.sw * psi * np.exp(s * self.t))
                        for psi in self.basis
                    ]
                )
            )
        return np.stack(rows)

    def nullspace(self):
        """Orthonormal basis (columns) of the triple-vanishing null space."""
        M = self.vanish_matrix()
        sv, vt = np.linalg.svd(M)[1:]
        rank = int(np.sum(sv > 1e-10 * max(sv[0], 1.0)))
        return vt[rank:].T.copy()

    def square(self, g):
        """F = g* * g on a symmetric grid; g real => autocorrelation of g
        with reflection about 0 (grid starts at a - b, lag 0 at index n-1)."""
        m = (self.n - 1) * 2 + 1
        full = np.convolve(g[::-1], g, mode="full") * self.h
        grid = (self.a - self.b) + self.h * np.arange(m)
        return grid, full

    def arch_of_g(self, g):
        """archimedeanTerm of the Hermitian square of g (real g)."""
        y, F = self.square(g)
        F0 = F[self.n - 1]  # exact lag-0 index of mode="full"
        assert F0 >= -1e-12, f"autocorrelation at 0 negative: {F0}"
        # integrand on (0, sup]; F even
        num = np.exp(y / 2.0) * 2.0 * F - 2.0 * F0
        den = np.exp(y) - np.exp(-y)
        m_pos = y > 1e-12
        y_p = y[m_pos]
        f_p = (num / den)[m_pos]
        y0 = y_p[-1]
        # exact geometric tail beyond the square support: numerator = -2 F0
        tail = 2.0 * F0 * np.log(np.tanh(y0 / 2.0))
        arch = C_ARCH * F0 + np.trapezoid(f_p, y_p) + tail
        return arch, F0

    def qw_residuals(self, coeff):
        """Numeric check: pole term of the square must vanish."""
        zero = 0.0 + 0.0j
        for s in (0.5, -0.5):
            # laplaceAt (g^2) s = conj (laplaceAt g (-conj s)) * laplaceAt g s
            l = np.conj(self.laplace_of(coeff, -np.conj(s))) * self.laplace_of(
                coeff, s
            )
            zero += l
        return zero


def sample_laner(probe, n_samples=12, seed=20260818):
    rng = np.random.default_rng(seed)
    N = probe.nullspace()
    out = []
    for _ in range(n_samples):
        v = rng.standard_normal(N.shape[1])
        coeff = N @ v
        g = np.tensordot(coeff, probe.basis, axes=(0, 0))
        nrm = np.sqrt(np.sum(probe.sw * np.abs(g) ** 2))
        coeff = coeff / nrm
        arch, F0 = probe.arch_of_g(
            np.tensordot(coeff, probe.basis, axes=(0, 0))
        )
        resid = abs(probe.qw_residuals(coeff))
        out.append((arch, F0, resid))
    return out


def detector_root(probe, rho):
    """Solve vanishings + Re laplaceAt g rho = -1, Im laplaceAt g rho = 0."""
    rows = list(probe.vanish_matrix())
    rows.append(
        np.array(
            [
                np.sum(probe.sw * psi * np.exp(rho * probe.t)).real
                for psi in probe.basis
            ]
        )
    )
    rows.append(
        np.array(
            [
                np.sum(probe.sw * psi * np.exp(rho * probe.t)).imag
                for psi in probe.basis
            ]
        )
    )
    M = np.stack(rows)
    rhs = np.zeros(M.shape[0])
    rhs[-2] = -1.0
    coeff, *_ = np.linalg.lstsq(M, rhs, rcond=None)
    return coeff


def main():
    print("Lane R arch-sign probe (2026-08-18)")
    print(f"C = log(4 pi) + gamma = {C_ARCH:.6f}")
    print()
    hdr = (
        f"{'window':>14} {'K':>2} {'arch min':>12} {'arch max':>12}"
        f" {'|pole| max':>12}  verdict"
    )
    print(hdr)
    print("-" * len(hdr))
    for w_half in (0.15, 0.20, 0.25, 0.30):
        probe = Probe(w_half, k_max=6)
        res = sample_laner(probe)
        archs = np.array([r[0] for r in res])
        resids = np.array([r[2] for r in res])
        verdict = (
            "OK arch<=0"
            if archs.max() <= 0.0
            else "FAIL arch>0 somewhere"
        )
        print(
            f"({probe.a:+.4f},{probe.b:+.4f}) {probe.k_max:>2}"
            f" {archs.min():>+12.6f} {archs.max():>+12.6f}"
            f" {resids.max():>12.2e}  {verdict}"
        )
    print()
    print("Detector-oriented root (off-line detection at rho):")
    for rho_label, rho in (
        ("0.75+14.1347i", 0.75 + 14.1347j),
        ("0.75+21.0225i", 0.75 + 21.0225j),
        ("0.90+14.1347i", 0.90 + 14.1347j),
    ):
        probe = Probe(0.25, k_max=8)
        coeff = detector_root(probe, rho)
        g = np.tensordot(coeff, probe.basis, axes=(0, 0))
        arch, F0 = probe.arch_of_g(g)
        van = max(
            abs(probe.laplace_of(coeff, s)) for s in VANISH_S
        )
        det = probe.laplace_of(coeff, rho)
        print(
            f"  rho={rho_label}: arch(g^2)={arch:+.6f}  F0={F0:.6f}"
            f"  |laplace vanish|max={van:.2e}"
            f"  laplace(rho)={det.real:+.6f}{det.imag:+.6f}i"
        )
    print()
    print("Reading: generic triple-vanishing roots should show arch <= 0")
    print("(Lane R prime-free subfamily); detector roots should show")
    print("arch > 0 (the off-line contradiction mechanism).")


if __name__ == "__main__":
    main()
