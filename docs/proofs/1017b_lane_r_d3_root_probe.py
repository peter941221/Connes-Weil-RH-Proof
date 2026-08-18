"""Lane R D3-root arch-sign probe v2 (2026-08-18).

Construction
------------
g = D3 h with D3 = (d/dt)(d/dt + 1/2)(d/dt + 1).  Since the bilateral
Laplace transform satisfies L(f', s) = -s L(f, s) for compactly supported
smooth f, we get for ANY such h:

    laplaceAt g s = -s (s - 1/2) (s - 1) laplaceAt h s

so the triple vanishing at s in {0, 1/2, 1} is EXACT and constructive - no
null-space solving.  With supp h inside [-w, w], w < log(2)/2, the square is
prime-free and the pole term of the square dies; Lane R's prime-free
instance for this root is arch(g^2) <= 0.

This probe computes arch((D3 h)^2) for pure-bell and flat-top h at several
widths and reports the sign/margin.
"""

import numpy as np

C_ARCH = np.log(4.0 * np.pi) + np.euler_gamma


def bell(t, c):
    out = np.zeros_like(t)
    m = np.abs(t) < c
    out[m] = np.exp(-(c * c) / (c * c - t[m] ** 2))
    return out


def smooth_transition(x):
    out = np.zeros_like(x)
    m = (x > 0) & (x < 1)
    a = np.exp(-1.0 / x[m])
    b = np.exp(-1.0 / (1.0 - x[m]))
    out[m] = a / (a + b)
    out[x >= 1] = 1.0
    return out


def flat_top(t, w, b=0.9):
    """bumpEx-style flat-top bump on [-w, w], plateau |t| <= b*w."""
    z2 = (t * t / (w * w) - b * b) / (1.0 - b * b)
    return 1.0 - smooth_transition(z2)


def d3_fft(t, h_t):
    """Spectral derivative of the zero-padded compact function on grid t.

    Operator D = (d/dt)(d/dt + 1/2)(d/dt + 1) = d^3 + (3/2) d^2 + (1/2) d.
    Sign check: L((d/dt + a) f, s) = -(s - a) L(f, s), so D multiplies the
    Laplace transform by -s (s - 1/2) (s - 1)  -> kills s in {0, 1/2, 1}.
    """
    n = len(t)
    dt = t[1] - t[0]
    m = 1 << (int(np.ceil(np.log2(2 * n))) + 3)
    pad = np.zeros(m)
    pad[:n] = h_t
    k = np.fft.fftfreq(m, d=dt) * 2.0 * np.pi
    dk = 1.0j * k
    op = dk**3 + 1.5 * dk**2 + 0.5 * dk
    full = np.real(np.fft.ifft(op * np.fft.fft(pad)))
    return full[:n], dt


def simpson_w(n, dt):
    w = np.ones(n)
    w[1:-1:2] = 4.0
    w[2:-1:2] = 2.0
    return w * dt / 3.0


def arch_sign(t, g, dt):
    n = len(t)
    F = np.convolve(g[::-1], g, mode="full") * dt
    y = (t[0] - t[-1]) + dt * np.arange(2 * n - 1)
    F0 = F[n - 1]
    assert F0 > 0
    num = np.exp(y / 2.0) * 2.0 * F - 2.0 * F0
    den = np.exp(y) - np.exp(-y)
    m = y > 1e-12
    f = (num / den)[m]
    yp = y[m]
    tail = 2.0 * F0 * np.log(np.tanh(yp[-1] / 2.0))
    lead = C_ARCH * F0
    body = np.trapezoid(f, yp)
    return lead, body, tail, lead + body + tail, F0


def laplace(t, g, s, w):
    return np.sum(w * g * np.exp(s * t))


def run_case(label, t, h_t):
    dt = t[1] - t[0]
    g, _ = d3_fft(t, h_t)
    sw = simpson_w(len(t), dt)
    vanish = max(abs(laplace(t, g, s, sw)) for s in (0.0, 0.5, 1.0))
    gscale = np.max(np.abs(g))
    lead, body, tail, arch, F0 = arch_sign(t, g, dt)
    print(
        f"{label:>22}: arch={arch:+12.4f}  F0={F0:12.4f}"
        f"  arch/F0={arch / F0:+8.4f}  C*F0={lead:+12.4f}"
        f"  I={body + tail:+13.4f}"
        f"  vanish/scale={vanish / gscale:.2e}"
    )
    return arch, F0


def main():
    print("Lane R D3-root probe v2 (g = (d/dt)(d/dt+1/2)(d/dt+1) h)")
    print(f"C = log(4 pi) + gamma = {C_ARCH:.6f}")
    print()
    for c in (1.0 / 3.0, 0.30, 0.25, 0.20):
        t = np.linspace(-0.42, 0.42, 8401)
        run_case(f"bell c={c:.3f}", t, bell(t, c))
    for w in (1.0 / 3.0, 0.30, 0.25):
        t = np.linspace(-0.42, 0.42, 8401)
        run_case(f"flat-top w={w:.3f}", t, flat_top(t, w))
    print()
    print("Reading: arch < 0 with margin (arch/F0 well below 0) means the")
    print("D3 root is a viable Lean witness for the Lane R prime-free leaf.")


if __name__ == "__main__":
    main()
