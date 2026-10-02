"""2451: corner-structure probe of the actual-owner omitted prime book.

Structural background.  For the captured owner (2275) the channel Laplace
sums on the critical line are

    H_ch(x) = sum_k c_ch,k * integral bump_k(y) e^{(1/2 + i m_k) y} e^{-2 pi i x y} dy,

so H_ch = Fourier[g_ch] with g_ch supported in [-rmax, rmax] and
rmax = max_k width_k^2.  The n=0 selected-square critical-line weight proxy
is W(x) = |H_base(x)|^2 |H_corr(x)|^2, hence

    What(nu) = integral W(x) e^{-2 pi i nu x} dx = (R_b * R_c)(nu),

where R_ch(t) = integral g_ch(y) conj(g_ch(y - t)) dy is the autocorrelation,
supported in [-2 rmax, 2 rmax].  Therefore supp(What) = [-4 rmax, 4 rmax]
and the support-derived visible book cutoff exp(4 rmax) = e^{26.2144...} is
exactly the transform support edge (2336 support cover).  The omitted band
(2 rmax, 4 rmax] in log-frequency, i.e. prime powers in
(492475, e^{26.2144}], is a corner region of the two autocorrelations.

This probe measures, on the stored captured coefficients,

    S_band = 2 * integral_{2 rmax}^{4 rmax} e^{-u/2} |What(u)| du

(PNT main-term density proxy for the absolute omitted-book charge of the
whole-line functional), the signed variant, an exactly enumerated
calibration stretch (492475, e^16], and the corner-decay law of R_c near
its support edge.  It is a diagnostic: no annihilator/window structure,
PNT main term only, no certificate, no producer GO.
"""
import hashlib
import json
import math
from pathlib import Path

import numpy as np
import mpmath as mp

ROOT = Path(__file__).resolve().parents[1]
CAPTURE = ROOT / "results/2275_gap_owner_audit.json"

H_Y = 0.0005          # physical y-grid step (midpoint rule)
H_R = 0.002           # R / What nu-grid step (subsample of H_Y)
DPS = 60              # mpmath precision for the coefficient sums
SIEVE_LIMIT = 8886111  # ceil(e^16); exact enumeration calibration stretch
MARGIN_2249 = 1675396046388.2736   # certified |Q| lower bound (2318 pin)
KNOWN_ERROR_2109 = 74601530.30234718
GAP_BUDGET = 1.0e7


def load_owner():
    capture = json.loads(CAPTURE.read_text())["owner_capture"]
    families = [(float.fromhex(width), float.fromhex(modulation))
                for width, modulation in capture["families_hex"]]
    base = [complex(float.fromhex(re_), float.fromhex(im_))
            for re_, im_ in capture["base_hex"]]
    corr = [complex(float.fromhex(re_), float.fromhex(im_))
            for re_, im_ in capture["corr_hex"]]
    for name, coefficients in (("base", base), ("corr", corr)):
        digest = hashlib.md5(
            np.asarray(coefficients, dtype=np.complex128).tobytes()).hexdigest()
        if digest != capture[name + "_md5"]:
            raise ValueError("stored coefficient hash mismatch: " + name)
    return families, base, corr, capture


def build_phis(families, h):
    radii = [width * width for width, _ in families]
    rmax = max(radii)
    count = int(math.ceil(2.0 * rmax / h))
    y = -rmax + (np.arange(count, dtype=np.float64) + 0.5) * h
    phis = np.empty((len(families), count), dtype=np.complex128)
    for index, (radius, (_, modulation)) in enumerate(zip(radii, families)):
        quotient = 1.0 - (y / radius) ** 2
        profile = np.zeros_like(y)
        inside = quotient > 0.0
        profile[inside] = np.exp(-30.0 / quotient[inside])
        phis[index] = profile * np.exp((0.5 + 1j * modulation) * y)
    return y, phis, rmax


def correlation_tables(phis, m_max, fft_size):
    """C[k][l][m] = h * sum_j phi_k[j+m] conj(phi_l[j]) for m = 0..m_max."""
    spectra = [np.fft.fft(phis[k], fft_size) for k in range(phis.shape[0])]
    tables = np.empty((phis.shape[0], phis.shape[0], m_max + 1),
                      dtype=np.complex128)
    for k in range(phis.shape[0]):
        spec_k = spectra[k]
        for l in range(phis.shape[0]):
            full = np.fft.ifft(spec_k * np.conj(spectra[l]))
            tables[k, l] = full[:m_max + 1] * H_Y
    return tables


def channel_r_table(tables, coefficients, subsample, terms_scale):
    """R(nu_m) = sum_{k,l} c_k conj(c_l) C[k][l][m], mpmath coefficient sums.

    Returns a list of complex Python floats at nu_m = m * H_R and the
    resolved-depth floor of the mpmath sums.
    """
    mp.mp.dps = DPS
    n_family = len(coefficients)
    depth = terms_scale * mp.mpf(10) ** (-DPS + 10)
    out = []
    coef = [mp.mpc(c.real, c.imag) for c in coefficients]
    terms = [[coef[k] * coef[l].conjugate() for l in range(n_family)]
             for k in range(n_family)]
    for m in range(subsample):
        j = m * 4
        if j > tables.shape[2] - 1:
            break
        acc = mp.mpc(0, 0)
        for k in range(n_family):
            row_k = tables[k]
            terms_k = terms[k]
            for l in range(n_family):
                term = terms_k[l]
                if term == 0:
                    continue
                row = row_k[l][j]
                acc += term * mp.mpc(row.real, row.imag)
        out.append(complex(float(acc.real), float(acc.imag)))
    return out, depth


def direct_r_spot(families, coefficients, nu, dps, panels=300, nodes=16):
    """Direct mpmath evaluation of R(nu) = int g(y) conj(g(y-nu)) dy."""
    mp.mp.dps = dps
    radii = [mp.mpf(width * width) for width, _ in families]
    rmax = max(radii)
    modulations = [mp.mpf(mod) for _, mod in families]
    coefs = [mp.mpc(c.real, c.imag) for c in coefficients]
    from scipy.special import roots_legendre
    absc, weights = roots_legendre(nodes)
    lower, upper = nu - rmax, rmax
    width = upper - lower
    total = mp.mpc(0, 0)
    edges = [lower + width * i / panels for i in range(panels + 1)]
    for p in range(panels):
        a, b = edges[p], edges[p + 1]
        mid, half = (a + b) / 2, (b - a) / 2
        for xi, w in zip(absc, weights):
            y = mid + half * mp.mpf(float(xi))
            weight = mp.mpf(float(w)) * half
            g_here = mp.mpc(0, 0)
            g_shift = mp.mpc(0, 0)
            for radius, modulation, c in zip(radii, modulations, coefs):
                q1 = 1 - (y / radius) ** 2
                if q1 > 0:
                    g_here += c * mp.exp(-30 / q1) * mp.exp((mp.mpf(0.5) + 1j * modulation) * y)
                q2 = 1 - ((y - nu) / radius) ** 2
                if q2 > 0:
                    g_shift += c * mp.exp(-30 / q2) * mp.exp((mp.mpf(0.5) + 1j * modulation) * (y - nu))
            total += weight * g_here * mp.conj(g_shift)
    return complex(float(total.real), float(total.imag))


def sieve_lambda(limit):
    """Lambda(n) for n <= limit as a dict-free array (0 where absent)."""
    sieve = np.ones(limit + 1, dtype=bool)
    sieve[:2] = False
    for p in range(2, int(limit ** 0.5) + 1):
        if sieve[p]:
            sieve[p * p::p] = False
    primes = np.nonzero(sieve)[0]
    lam = np.zeros(limit + 1, dtype=np.float64)
    for p in primes:
        power = p
        logp = math.log(p)
        while power <= limit:
            lam[power] = logp
            power *= p
    return lam, primes


def book_sums(lam, what_interp, nu_lo, nu_hi):
    """Exact enumeration of 2 Lambda(n)/sqrt(n) What(log n) over the sieve
    range, restricted to nu_lo < log n <= nu_hi (interp: linear in nu)."""
    lo_n = max(2, int(math.floor(math.exp(nu_lo))) + 1)
    hi_n = min(len(lam) - 1, int(math.ceil(math.exp(nu_hi))))
    ns = np.arange(lo_n, hi_n + 1)
    weights = lam[ns]
    mask = weights > 0
    ns = ns[mask]
    weights = weights[mask]
    if ns.size == 0:
        return {"count": 0, "abs_sum": 0.0, "signed_sum": 0.0,
                "nu_range": None}
    nus = np.log(ns)
    values = np.interp(nus, what_interp[0], what_interp[1])
    terms = 2.0 * weights / np.sqrt(ns) * values
    return {
        "count": int(ns.size),
        "abs_sum": float(np.sum(np.abs(terms))),
        "signed_sum": float(np.sum(terms)),
        "nu_range": [float(nus.min()), float(nus.max())],
    }


def corner_fit(r_pos, rmax, floor):
    """Fit log|R(2 rmax - delta)| against 1/delta over the deepest reliable
    decades; the Laplace prediction for the dominant largest-radius family
    is slope -60 * rmax."""
    deltas = []
    logs = []
    for m in range(len(r_pos)):
        nu = m * H_R
        delta = 2.0 * rmax - nu
        if delta <= 0.05:
            continue
        value = abs(r_pos[m])
        if value < floor:
            continue
        deltas.append(1.0 / delta)
        logs.append(math.log(value))
    if len(deltas) < 10:
        return {"fit_points": len(deltas)}
    order = np.argsort(deltas)
    deltas = np.asarray(deltas)[order]
    logs = np.asarray(logs)[order]
    deep = deltas >= deltas[-1] - (deltas[-1] - deltas[0]) * 0.25
    slope, _ = np.polyfit(deltas[deep], logs[deep], 1)
    return {
        "fit_points": int(deep.sum()),
        "slope_measured": float(slope),
        "slope_predicted_-60rmax": float(-60.0 * rmax),
        "delta_window": [float(1.0 / deltas[deep].max()), float(1.0 / deltas[deep].min())],
    }


def main():
    families, base, corr, capture = load_owner()
    y, phis, rmax = build_phis(families, H_Y)
    n_y = y.size
    m_max = int(math.ceil(2.0 * rmax / H_Y))
    fft_size = 1
    while fft_size < n_y + m_max + 1:
        fft_size *= 2
    m_sub = m_max // 4

    tables = correlation_tables(phis, m_max, fft_size)

    scale = float(np.abs(tables).max()) * max(
        abs(c) for c in base + corr) ** 2
    r_base, floor_b = channel_r_table(tables, base, m_sub, scale)
    r_corr, floor_c = channel_r_table(tables, corr, m_sub, scale)

    # Signed mirror: R(-nu) = conj(R(nu)).  What(nu) = int R_b(t) R_c(-t-nu) dt
    # equals conj of the plain convolution int R_b(t) R_c(nu-t) dt, so the
    # real part below is exactly Re What = the cos-transform of W(x) — the
    # quantity the book functional reads.  The imaginary part is the Hilbert
    # partner of the (not x-even, modulated) weight; it is recorded as a
    # fact, not treated as an error indicator.
    def signed(r_pos):
        arr = np.zeros(2 * m_sub - 1, dtype=np.complex128)
        arr[m_sub - 1 + np.arange(m_sub)] = r_pos
        arr[m_sub - 1 - np.arange(1, m_sub)] = np.conj(r_pos[1:])
        return arr
    r_base_sig = signed(r_base)
    r_corr_sig = signed(r_corr)
    what_full = np.convolve(r_base_sig, r_corr_sig) * H_R
    herm_dev = float(np.max(np.abs(
        what_full.imag + what_full.imag[::-1]))) if m_sub > 1 else 0.0
    what_pos = what_full[len(what_full) // 2:]
    what_imag_ratio = float(np.max(np.abs(what_pos.imag)) /
                            max(float(np.max(np.abs(what_pos.real))), 1e-300))
    what_real = what_pos.real

    nu_edge = 4.0 * rmax
    n_band_lo = int(math.ceil(2.0 * rmax / H_R))
    n_band_hi = min(len(what_real) - 1, int(math.floor(nu_edge / H_R)))
    nus = np.arange(len(what_real)) * H_R
    band = slice(n_band_lo, n_band_hi + 1)
    # PNT density: sum 2 Lambda(n)/sqrt(n) |What(log n)| ~ int 2 e^{u/2} |What(u)| du
    # (Lambda-measure contributes e^u, the kernel weight e^{-u/2}).
    e_half = np.exp(0.5 * nus[band])
    band_abs = 2.0 * float(np.trapezoid(e_half * np.abs(what_real[band]), nus[band]))
    band_signed = 2.0 * float(np.trapezoid(e_half * what_real[band], nus[band]))
    band_peak = float(np.max(np.abs(what_real[band])))

    # Beyond-support control: pad and evaluate past 4 rmax.
    pad = 256
    r_base_pad = np.zeros(len(r_base_sig) + 2 * pad, dtype=np.complex128)
    r_corr_pad = np.zeros(len(r_corr_sig) + 2 * pad, dtype=np.complex128)
    r_base_pad[pad:pad + len(r_base_sig)] = r_base_sig
    r_corr_pad[pad:pad + len(r_corr_sig)] = r_corr_sig
    what_pad = np.convolve(r_base_pad, r_corr_pad) * H_R
    half = len(what_pad) // 2
    beyond = what_pad[half + n_band_hi + 2: half + n_band_hi + 2 + pad].real
    beyond_max = float(np.max(np.abs(beyond)))

    # Included-book context and exact calibration stretch.
    lam, _ = sieve_lambda(SIEVE_LIMIT)
    included = book_sums(lam, (nus[:n_band_hi + 1], what_real[:n_band_hi + 1]),
                         0.0, 2.0 * rmax)
    calib_exact = book_sums(lam, (nus[:n_band_hi + 1], what_real[:n_band_hi + 1]),
                            2.0 * rmax, 16.0)
    calib_nus = nus[band]
    calib_mask = (calib_nus > 2.0 * rmax) & (calib_nus <= 16.0)
    calib_density = 2.0 * float(np.trapezoid(
        np.exp(0.5 * calib_nus[calib_mask]) * np.abs(what_real[band][calib_mask]),
        calib_nus[calib_mask]))

    # Spot controls.  Deep spots need high dps: at nu = 12 the Laplace depth
    # is e^{-393/1.1} ~ 1e-154 against table terms of size ~1e35.
    spots_c = {}
    for nu, dps in ((3.0, 60), (6.5, 60), (10.0, 60), (11.0, 60), (12.0, 220)):
        direct = direct_r_spot(families, corr, mp.mpf(nu), dps)
        fast = r_corr[int(round(nu / H_R))]
        spots_c[str(nu)] = {
            "dps": dps,
            "direct": direct,
            "table": fast,
            "abs_diff": abs(direct - fast),
            "rel_diff": abs(direct - fast) / max(abs(direct), 1e-300),
        }
    spots_b = {}
    for nu, dps in ((3.0, 60), (8.0, 60)):
        direct = direct_r_spot(families, base, mp.mpf(nu), dps)
        fast = r_base[int(round(nu / H_R))]
        spots_b[str(nu)] = {
            "dps": dps,
            "direct": direct,
            "table": fast,
            "abs_diff": abs(direct - fast),
            "rel_diff": abs(direct - fast) / max(abs(direct), 1e-300),
        }

    # C_{kk}(0) direct check for two families.  |phi_k|^2 carries the
    # modulation factor |e^{(0.5+i theta) y}|^2 = e^y.
    mp.mp.dps = 40
    c00_checks = []
    for k in (0, 4):
        radius = families[k][0] ** 2
        node_count = 4000
        yy = -radius + (np.arange(node_count) + 0.5) * (2 * radius / node_count)
        q = 1.0 - (yy / radius) ** 2
        prof = np.exp(-30.0 / q)
        integrand = np.abs(prof) ** 2 * np.exp(yy)
        direct_c00 = float(np.trapezoid(
            np.concatenate([[0.0], integrand, [0.0]]),
            np.concatenate([[-radius], yy, [radius]])))
        fast_c00 = float(abs(tables[k, k, 0]))
        c00_checks.append({"family": k, "direct": direct_c00,
                           "table": fast_c00,
                           "rel_diff": abs(direct_c00 - fast_c00) / direct_c00})

    corner = corner_fit(r_corr, rmax, scale * 1e-12)

    # FFT-noise propagation.  The deep-corner spot abs-diffs measure the
    # table noise floors; convolving R_b with R_c amplifies them by the
    # discrete L1 norms of the opposite channel.  The band profile values
    # are expected to sit at or below this floor, so the noise-inflated
    # band bounds are the honest budget inputs.
    l1_base = float(H_R * np.sum(np.abs(r_base_sig)))
    l1_corr = float(H_R * np.sum(np.abs(r_corr_sig)))
    eps_b = max(float(spots_b["8.0"]["abs_diff"]), 0.0)
    eps_c = max(float(spots_c["6.5"]["abs_diff"]),
                float(spots_c["10.0"]["abs_diff"]),
                float(spots_c["11.0"]["abs_diff"]))
    eps_what = H_R * (eps_c * l1_base + eps_b * l1_corr)
    kernel_mass_band = 4.0 * (math.exp(2.0 * rmax) - math.exp(rmax))
    kernel_mass_beyond_16 = 4.0 * (math.exp(2.0 * rmax) - math.exp(8.0))
    noisy_band_bound = band_abs + kernel_mass_band * eps_what
    noisy_whole_bound = (calib_exact["abs_sum"]
                         + kernel_mass_beyond_16 * eps_what)

    # Density-model Lambda mass of the band kernel: int 2 e^{u/2} du.
    interior_peak = float(np.max(np.abs(
        what_real[:int(math.ceil(2.0 * rmax / H_R)) + 1])))
    naive_strawman = interior_peak * kernel_mass_band

    # Density estimate beyond the exact-enumeration cut at nu = 16 up to the
    # support edge 4 rmax; the whole-band proxy is exact enum + this tail.
    tail_mask = nus[band] > 16.0
    tail_density = 2.0 * float(np.trapezoid(
        np.exp(0.5 * nus[band][tail_mask]) * np.abs(what_real[band][tail_mask]),
        nus[band][tail_mask]))
    whole_band_abs = calib_exact["abs_sum"] + tail_density

    band_profile = {
        "nu": [round(float(u), 4) for u in nus[band][::4]],
        "reWhat": [float(f"{v:.9e}") for v in what_real[band][::4]],
        "imWhat": [float(f"{v:.9e}") for v in what_pos.imag[band][::4]],
    }

    result = {
        "record": 2451,
        "verdict": "BOOK-CORNER-PROBE-COMPLETE",
        "scope": ("diagnostic probe of the omitted prime book on the "
                  "captured owner weight proxy |H_base|^2 |H_corr|^2; "
                  "whole line, no annihilator/window, PNT main-term "
                  "density; not a certificate"),
        "capture_sha256": hashlib.sha256(CAPTURE.read_bytes()).hexdigest(),
        "probe_source_sha256": hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
        "base_md5": capture["base_md5"],
        "corr_md5": capture["corr_md5"],
        "rmax": rmax,
        "source_radius_2rmax": 2.0 * rmax,
        "square_radius_4rmax": 4.0 * rmax,
        "book_cutoff_exp_4rmax": math.exp(4.0 * rmax),
        "legacy_book_cutoff_exp_2rmax": math.exp(2.0 * rmax),
        "grid": {"h_y": H_Y, "h_r": H_R, "n_y": n_y, "m_max": m_max,
                 "m_sub": m_sub, "dps": DPS},
        "band_charge_abs_density_proxy": band_abs,
        "band_charge_signed_density_proxy": band_signed,
        "whole_band_abs_exact_enum_16_plus_density": whole_band_abs,
        "tail_density_16_to_4rmax": tail_density,
        "fft_noise_floor": {
            "eps_base_r_table": eps_b,
            "eps_corr_r_table": eps_c,
            "l1_base": l1_base,
            "l1_corr": l1_corr,
            "eps_what": eps_what,
            "note": ("eps_what bounds the convolution noise |dWhat| per "
                     "band point; band profile values at or below it are "
                     "floor, not signal"),
        },
        "noisy_band_bound": noisy_band_bound,
        "noisy_whole_band_bound": noisy_whole_bound,
        "band_peak_abs_What": band_peak,
        "beyond_support_max_abs": beyond_max,
        "beyond_support_ratio_to_band_peak": beyond_max / max(band_peak, 1e-300),
        "what_imag_over_real": what_imag_ratio,
        "what_hermitian_max_dev": herm_dev,
        "what_semantics": ("what_real = Re What = cos-transform of W (what the "
                           "book functional reads); imaginary part is the "
                           "Hilbert partner of the modulated (non-even) "
                           "weight, recorded not error-checked"),
        "included_book_abs_exact_enum": included,
        "calibration_exact_16": calib_exact,
        "calibration_density_16": calib_density,
        "calibration_ratio_exact_over_density": (
            calib_exact["abs_sum"] / calib_density if calib_density > 0 else None),
        "kernel_mass_band_density_model": kernel_mass_band,
        "interior_peak_abs_What": interior_peak,
        "naive_strawman_interiorpeak": naive_strawman,
        "suppression_measured_over_strawman": (
            band_abs / naive_strawman if naive_strawman > 0 else None),
        "corner_fit": corner,
        "band_profile_every_4th_node": band_profile,
        "spot_checks_corr": {k: {kk: (vv if not isinstance(vv, complex) else [vv.real, vv.imag])
                                 for kk, vv in v.items()}
                             for k, v in spots_c.items()},
        "spot_checks_base": {k: {kk: (vv if not isinstance(vv, complex) else [vv.real, vv.imag])
                                 for kk, vv in v.items()}
                             for k, v in spots_b.items()},
        "c00_checks": c00_checks,
        "mpmath_floors": {"base": float(floor_b), "corr": float(floor_c)},
        "budget_comparisons": {
            "band_abs_over_gap_1e7": band_abs / GAP_BUDGET,
            "whole_band_over_gap_1e7": whole_band_abs / GAP_BUDGET,
            "noisy_band_over_gap_1e7": noisy_band_bound / GAP_BUDGET,
            "noisy_whole_over_gap_1e7": noisy_whole_bound / GAP_BUDGET,
            "band_abs_over_known_error_2109": band_abs / KNOWN_ERROR_2109,
            "band_abs_over_margin_2249": band_abs / MARGIN_2249,
        },
        "probe_tolerance": None,
        "producer_go": False,
        "rh_claim": False,
    }
    out = ROOT / "results/2451_book_corner_probe.json"
    out.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({k: result[k] for k in (
        "record", "verdict", "band_charge_abs_density_proxy",
        "whole_band_abs_exact_enum_16_plus_density",
        "fft_noise_floor", "noisy_band_bound", "noisy_whole_band_bound",
        "band_peak_abs_What", "beyond_support_ratio_to_band_peak",
        "corner_fit", "suppression_measured_over_strawman",
        "calibration_ratio_exact_over_density",
        "budget_comparisons")}, indent=2))


if __name__ == "__main__":
    main()
