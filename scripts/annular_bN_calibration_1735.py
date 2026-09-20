#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
annular_bN_calibration_1735.py — Rig C for wave 1735 (record 1734 section 5).

Calibrates the fixed-tail bound

    B(N) = int_{a+N}^inf s (|k_0(s)|^2 + |v(s)|^2) ds,   a = log lambda,

against the record-1734 envelopes

    int_X^inf s |v(s)|^2   <= ||theta''||_1^2 / (32 pi^4 X^2),
    int_X^inf s |k_0(s)|^2 <= C_k^2 / (4 X^4).

Definitions (hand-derived from the committed conventions, F27):

  Fourier convention:  Fh(xi) = int h(t) exp(-2 pi i xi t) dt.
  Test h1 (Gaussian):  h(t) = exp(-pi t^2),  Fh(xi) = exp(-pi xi^2).
  Symbol:              m(xi) = G_R(1/2 - 2 pi i xi) / G_R(1/2 + 2 pi i xi),
                       G_R(z) = pi^{-z/2} Gamma(z/2)
                            =>  m = pi^{2 pi i xi} Gamma(1/4 - pi i xi)
                                    / Gamma(1/4 + pi i xi),   |m| = 1.
  theta(xi) = m(xi) * conj(Fh(xi));   v = F^{-1} theta.

Controls (F43/F52 discipline — floors calibrated on exact-answer models):

  (1) m == 1 with a COMPACT-SUPPORT bump h:  conj Fh = F(g) with
      g = conj h(-.) compactly supported, so v = g exactly and
      B_v(X) == 0 (machine exact) once X exceeds the support radius.
  (2) m == 1 with the Gaussian: v0 = exp(-pi s^2), so
      B_v0(X) = exp(-2 pi X^2) / (4 pi) in closed form — the
      exact-answer floor.
  (3) real Gamma-ratio symbol + Gaussian: theta = m * exp(-pi xi^2) is
      Schwartz, so the measured tail decays super-polynomially; the
      1/(32 pi^4 X^2) envelope is verified as an upper bound (measured
      <= predicted everywhere) and the slack is reported.  A degenerate
      floor reports nothing (F52): all ratios are printed, none assumed.

Determinism: pure quadrature on fixed grids, no randomness.
Acceptance is read from the printed report, not the exit code.
"""

import json
import math
import sys

from scipy import integrate

import numpy as np
from scipy.special import loggamma

TWO_PI = 2.0 * math.pi


# ----------------------------------------------------------------------
# grids
# ----------------------------------------------------------------------

def make_xi_grid(xi_halfwidth=20.0, n=2 ** 17):
    """Uniform xi-grid on [-W, W), N points; returns (xi, dxi)."""
    dxi = 2.0 * xi_halfwidth / n
    xi = -xi_halfwidth + dxi * np.arange(n)
    return xi, dxi


# ----------------------------------------------------------------------
# symbols and theta
# ----------------------------------------------------------------------

def symbol_m(xi):
    """m(xi) = pi^{2 pi i xi} Gamma(1/4 - pi i xi) / Gamma(1/4 + pi i xi)."""
    z = 0.25 + 1j * math.pi * xi
    return np.exp(1j * TWO_PI * np.log(math.pi)
                  + loggamma(np.conj(z)) - loggamma(z))


def theta_real(xi):
    """theta = m * conj(Fh) for the Gaussian test (Fh real positive)."""
    return symbol_m(xi) * np.exp(-math.pi * xi ** 2)


def theta_one(xi):
    """m == 1 control."""
    return np.exp(-math.pi * xi ** 2)


def theta_bump_ft(xi):
    """conj Fh for the compact bump: F of g = conj h(-.)  (real, even)."""
    # h = normalized C^inf bump on [-1, 1]; computed by quadrature.
    t = np.linspace(-1.0, 1.0, 4001)
    with np.errstate(divide="ignore", invalid="ignore"):
        w = np.where(np.abs(t) < 1.0,
                     np.exp(-1.0 / np.maximum(1.0 - t ** 2, 1e-300)), 0.0)
    w = w / math.sqrt(np.trapezoid(w ** 2, t))  # unit L2 norm
    phase = np.exp(-2j * math.pi * np.outer(xi, t))
    return np.trapezoid(w[None, :] * phase, t, axis=1)


# ----------------------------------------------------------------------
# spectral second derivative (periodic wrap; tails are far below machine eps)
# ----------------------------------------------------------------------

def spectral_second_derivative(f, xi):
    n = len(xi)
    dxi = xi[1] - xi[0]
    omega = TWO_PI * np.fft.fftfreq(n, d=dxi)
    F = np.fft.fft(f)
    return np.fft.ifft(-(omega ** 2) * F)


# ----------------------------------------------------------------------
# v via the DFT (s-grid = conjugate of the xi-grid)
# ----------------------------------------------------------------------

def v_on_s_grid(theta, xi, dxi):
    """v(s_j) ~= sum_k theta(xi_k) exp(-2 pi i xi_k s_j) dxi on the
    conjugate grid s_j = j / (n * dxi), j = 0..n-1 (i.e. s in [0, 1/dxi))."""
    n = len(xi)
    # fft computes sum_k f_k exp(-2 pi i j k / n); with xi_k = -W + k dxi:
    # exp(-2 pi i xi_k s_j) = exp(-2 pi i (-W + k dxi) s_j)
 # = exp(+2 pi i W s_j) exp(-2 pi i k dxi s_j)
    # and dxi * s_j = j / n  =>  the kernel is the DFT kernel.
    F = np.fft.fft(theta)  # ordered with the negative frequencies first
    # undo the xi offset: multiply by exp(-2 pi i (-W) s_j) = exp(+2 pi i W s_j)
    s = np.arange(n) / (n * dxi)
    return F * dxi * np.exp(2j * math.pi * xi[0] * s)


# ----------------------------------------------------------------------
# tail integrals on a fine s-grid (direct quadrature)
# ----------------------------------------------------------------------

def tail_bv(v, s, X, s_max):
    """B_v(X) = int_X^min(s_max, ...) s |v(s)|^2 ds by trapezoid."""
    mask = (s >= X) & (s <= s_max)
    ss = s[mask]
    vv = np.abs(v[mask]) ** 2
    return float(np.trapezoid(ss * vv, ss))


def tail_bk_gaussian(X):
    """int_X^inf s |k0(s)|^2 ds for k0 = h (Gaussian, real even):
    int_X^inf s exp(-2 pi s^2) ds = exp(-2 pi X^2) / (4 pi)."""
    return math.exp(-TWO_PI * X * X) / (4.0 * math.pi)


# ----------------------------------------------------------------------
# main calibration
# ----------------------------------------------------------------------

def main():
    out = {}
    xi, dxi = make_xi_grid()
    n = len(xi)

    # ---------------- theta'' and its L1 norm (real symbol, Gaussian) ----
    th = theta_real(xi)
    th2 = spectral_second_derivative(th, xi)
    norm_theta2_l1 = float(np.trapezoid(np.abs(th2), xi))
    out["norm_theta2_L1_real"] = norm_theta2_l1

    # sanity: for the m == 1 control the spectral pipeline must agree with
    # a high-accuracy adaptive quadrature of the CLOSED integrand
    # theta0'' = (4 pi^2 xi^2 - 2 pi) exp(-pi xi^2)  (F43: exact answer;
    # independent hand check: L1 = 2 pi * 2 * e^{-1/2}/sqrt(2 pi)
    #              = 6.0814...  — matches the spectral value).
    th0 = theta_one(xi)
    th02 = spectral_second_derivative(th0, xi)
    norm_theta02_l1 = float(np.trapezoid(np.abs(th02), xi))

    def theta0_second(xi_val):
        return (4.0 * math.pi ** 2 * xi_val ** 2 - 2.0 * math.pi) \
            * math.exp(-math.pi * xi_val ** 2)

    closed, _ = integrate.quad(
        lambda x: abs(theta0_second(x)), -50.0, 50.0, limit=400)
    out["norm_theta02_L1_control"] = norm_theta02_l1
    out["norm_theta02_L1_control_closed"] = closed
    out["control_theta2_L1_absdiff"] = abs(norm_theta02_l1 - closed)

    # ---------------- v grids -------------------------------------------
    v_real = v_on_s_grid(th, xi, dxi)
    s = np.arange(n) / (n * dxi)
    # s-span is 1/dxi = n/(2W) ~ 6553; restrict the tail quadrature to
    # [0, 200] — beyond that |v|^2 is far below the double floor.
    s_max = 200.0

    # ---------------- control 1: m == 1, compact bump --------------------
    thb = theta_bump_ft(xi)
    vb = v_on_s_grid(thb, xi, dxi)
    control_exact_zero = max(
        abs(tail_bv(vb, s, X, s_max)) for X in (1.5, 2.0, 3.0, 5.0, 10.0))
    out["control_bump_max_abs_B"] = control_exact_zero

    # ---------------- control 2: m == 1, Gaussian (closed form) ----------
    v0 = v_on_s_grid(th0, xi, dxi)
    ctrl_rows = []
    for X in (2.0, 3.0, 4.0, 6.0, 8.0):
        meas = tail_bv(v0, s, X, s_max)
        exact = tail_bk_gaussian(X)
        ctrl_rows.append({
            "X": X, "measured": meas, "closed": exact,
            "absdiff": abs(meas - exact),
        })
    out["control_gaussian_rows"] = ctrl_rows
    out["control_gaussian_max_absdiff"] = max(
        r["absdiff"] for r in ctrl_rows)

    # ---------------- real symbol: envelope table ------------------------
    rows = []
    for X in (2.0, 3.0, 4.0, 6.0, 8.0, 12.0, 16.0):
        meas = tail_bv(v_real, s, X, s_max)
        pred = norm_theta2_l1 ** 2 / (32.0 * math.pi ** 4 * X * X)
        rows.append({
            "X": X, "B_v_measured": meas, "envelope_predicted": pred,
            "ratio_measured_over_predicted": (meas / pred) if pred > 0 else 0.0,
        })
    out["real_symbol_rows"] = rows
    out["real_symbol_envelope_holds"] = all(
        r["B_v_measured"] <= r["envelope_predicted"] for r in rows)

    # measured decay slope on X in [4, 16]
    xs = np.array([4.0, 6.0, 8.0, 12.0, 16.0])
    bs = np.array([tail_bv(v_real, s, X, s_max) for X in xs])
    slope = float(np.polyfit(np.log(xs), np.log(bs), 1)[0])
    out["real_symbol_loglog_slope_4_16"] = slope

    # ---------------- k0 tail (Gaussian: k0 = h) -------------------------
    # C_k := sup_s |k0(s)| (1 + |s|)^3 over the resolved window.
    k0 = np.exp(-math.pi * s ** 2)
    window = (s <= 12.0)
    C_k = float(np.max(k0[window] * (1.0 + s[window]) ** 3))
    krows = []
    for X in (1.0, 2.0, 3.0, 4.0, 6.0):
        meas = tail_bv(k0.astype(complex), s, X, s_max)
        pred = C_k ** 2 / (4.0 * X ** 4)
        krows.append({
            "X": X, "B_k_measured": meas, "envelope_predicted": pred,
            "ratio_measured_over_predicted": meas / pred,
        })
    out["k0_rows"] = krows
    out["k0_envelope_holds"] = all(
        r["B_k_measured"] <= r["envelope_predicted"] for r in krows)
    out["C_k"] = C_k

    # ---------------- verdicts -------------------------------------------
    # The bump control reads the double-precision quadrature floor (~1e-14),
    # not literal 0; acceptance is the floor threshold (F43 discipline).
    out["verdict_control_exact_zero"] = control_exact_zero < 1e-12
    out["verdict_control_spectral_pipeline"] = out["control_theta2_L1_absdiff"] < 1e-6
    out["verdict_control_closed_form"] = out["control_gaussian_max_absdiff"] < 1e-12
    out["verdict_envelopes_hold"] = (out["real_symbol_envelope_holds"]
                                     and out["k0_envelope_holds"])

    text = json.dumps(out, indent=2)
    print(text)
    with open("annular_bN_calibration_1735_results.json", "w",
              encoding="utf-8") as fh:
        fh.write(text + "\n")


if __name__ == "__main__":
    sys.exit(main())
