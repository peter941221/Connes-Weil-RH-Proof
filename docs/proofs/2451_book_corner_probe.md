# 2451 - Omitted prime-book corner probe on the composed 4R support

Date: 2026-10-02.

The object-scope correction moved the book cutoff from `e^(2 rmax)` to
`e^(4 rmax)` (record 2336), which makes the omitted prime-power band
`(e^(2 rmax), e^(4 rmax)]` about 2.4e11 prime powers — too large to
enumerate. This probe prices that band instead of enumerating it.

## Corner structure

For the owner weight proxy `W(x) = |H_base(x)|^2 |H_corr(x)|^2` with
`H_ch = F[g_ch]` and `g_ch` supported in `[-rmax, rmax]`, the identity
`F[|H_ch|^2] = R_ch` (autocorrelation of `g_ch`, supported in
`[-2 rmax, 2 rmax]`) gives, by the product-to-convolution rule, that the
cos-transform weight of `W` is the convolution of the two autocorrelations,
supported in `[-4 rmax, 4 rmax]`. The book cutoff `e^(4 rmax)` is exactly
the support edge, so the omitted band is a corner region: the transformed
weight decays essentially exponentially into it (Laplace depth from the
flat-bump edge singularity). Because the modulations shift `|H|^2` away
from evenness, the transform weight is Hermitian-complex rather than real;
the cos-kernel functional reads its real part.

## Instrument

FFT cross-correlation tables `C_kl(m) = h sum_j phi_k[j+m] conj(phi_l[j])`
on the midpoint grid, `h = 0.0005`, zero-padded; per-channel autocorrelations
as dps-60 mpmath sums over the 900-term tables, subsampled to 0.002; signed
mirror `R(-nu) = conj(R(nu))`; convolution for the band profile; PNT
main-term density `int 2 e^(u/2) |Re What(u)| du` (Lambda-measure `e^u`
times the kernel weight `e^(-u/2)`); exact sieve enumeration up to `e^16`
as a same-window calibration of the density model. Spot controls compare
the tables against direct mpmath Gauss-Legendre evaluation of `R`.

## Results

    band charge (2rmax, 4rmax], density proxy     9.277e-07
    whole band (exact enum to e^16 + density)     9.338e-07
    noise-inflated whole-band bound               9.215e-04
    band edge peak |Re What|                      3.807e-09
    convolution noise floor eps_What              4.701e-10
    calibration exact/density (13.1, 16]          1.0067
    beyond-support residue / band peak            0.0
    corner slope measured vs predicted            -322 vs -393

The band-edge peak sits eight times above the propagated FFT noise floor,
so the dominant contribution is signal; deeper band values sink below the
floor and the profile decays smoothly across roughly thirteen orders of
magnitude. The noise-inflated bound propagates the measured table floors
(`eps_base = 2.4e-14`, `eps_corr = 8.3e-08`) through the opposite channel
L1 norms and adds the density-model kernel mass as a worst case.

Against the budget frame:

    noisy whole-band bound / gap budget 1e7     9.2e-11
    noisy whole-band bound / known error 2109   1.2e-14
    band proxy / certified margin 2249          5.5e-19

The 4R book cliff dissolves numerically: even the worst-case noise-inflated
whole-band bound is about ten orders below the 1e7 gap budget. The budget
frame opened by the object-scope correction does not move.

## Incidents found and fixed during the probe

- The correlation tables initially omitted the `h` factor; the spot
  relative differences of `1999 = 1/h` exposed it, and the fix restored
  agreement to 9.4e-12 at the shallow spot.
- The density weight initially used `e^(-u/2)`; the calibration control
  measured a ratio of 746125 against exact enumeration. With the correct
  `e^(+u/2)` (Lambda-measure `e^u` times kernel `e^(-u/2)`) the same
  control reads 1.0067. The calibration control did its job.
- A reality control expecting a real transform weight was mis-designed:
  the modulated weight is genuinely Hermitian-complex, and the imaginary
  part (max ratio 0.94 to the real part) is the Hilbert partner, not an
  error. Replaced by a Hermitian-symmetry check (max deviation 4.4e-11)
  plus the Re-based band charge.
- Deep-corner spots need scaled precision: at `nu = 12` the Laplace depth
  is about `e^(-357)`, beyond dps-60; the spot ladder uses dps 60 up to
  `nu = 11` and dps 220 at `nu = 12`.
- The `C_kk(0)` direct check initially omitted the modulation factor
  `e^y` in `|phi|^2`; corrected, both families agree.
- The first noise-inflated whole-band bound went negative through a
  kernel-mass limit error (`e^16` for `e^8`); fixed and regenerated.

## Scope

Diagnostic only, on the captured owner weight proxy, whole line, PNT
main-term density, no annihilator, no window, no archimedean structure.
Not a certificate: the corner support statement is used numerically, the
exact-economy claims are unexported, and the density model is not a
prime-power theorem at the edge. No signed selected-detector budget,
producer GO or RH claim follows.

Evidence:

- `scripts/routea_book_corner_probe_2451.py`
- `results/2451_book_corner_probe.json`
- `scripts/routea_actual_owner_marked_support_probe_2336.py` (4R geometry)
- `results/2275_gap_owner_audit.json` (owner capture)
