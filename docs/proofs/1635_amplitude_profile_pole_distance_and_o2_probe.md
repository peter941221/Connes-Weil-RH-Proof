# 1635 — amplitude profile, pole-distance dependence, and the O2 probe

Date: 2026-09-18

Status: numerical research record only. No Lean theorem, no RH claim, and no
route-map status change. The experiment serves the healthy-CompactLog B5
carrier-base investigation recorded in map 043.

## 1. Rig repair

The first draft mixed two different quantities. It computed a model defect for
a separately shifted array and then compared it with the real defect of the
requested shift. It also applied a second shift in the exact-check block. The
repaired rig evaluates both quantities on the same translated vector `h_s`
and at the same boundary `c = 2 log lambda`. The exact model check then agrees
with the incomplete-gamma formula to the grid error:

```text
D_model^2 = Gamma(2 k - 1, 2 a |c|) / Gamma(2 k - 1).
```

Rows whose model defect is near the FFT floor are not interpreted as evidence.

## 2. Profile and resolved O2-family readback

For `k = 3`, `a = 1`, the pointwise ratio
`|F^-1(m(-.) Hhat)(y)| / |h(y)|` is approximately `0.0805--0.0806`
on the resolved middle range `y = -6,...,-12`. The comparison with shifted
profiles is not flat at the tested alternative shifts, so the observed leading
term is consistent with a local constant-amplitude, zero-additional-shift
action on this family.

For the same family, the single-vector ratio `D_real / D_model` is:

```text
lambda       0.0200   0.0100   0.0050   0.0020   0.0010   0.0005
ratio        0.0795   0.0800   0.0803   0.0805   0.0806   0.0806
```

This is evidence against a visible non-uniformity explosion on this fixed
rational family. It is not uniformity on the unit sphere of `H^2`, and it does
not prove attainment of the carrier kernel.

The mixed family `h_3 + b h_2`, with `a = 1` and `lambda = 0.002`, gives

```text
b            0       0.1      1        10
ratio        0.0805  0.0805   0.0805   0.0891
```

The first three rows support persistence under moderate mixing; the last row
shows that strong mixing changes the leading profile and must not be folded
into a universal constant without normalization.

## 3. Pole-distance test and correction to F56

Changing the pole parameter shows that the coefficient is not universal in
`a`. For example, at `k = 3` and resolved scales, `a = 0.5` gives ratios
roughly `0.14` down to `0.07`, while `a = 1` stays near `0.0806`. For `a = 2`
the model defect becomes so small that the real readback reaches the FFT
floor; those rows are discarded rather than extrapolated.

Therefore the numerical conjecture that the coefficient is the universal
number `1/(4 pi)` is withdrawn. The surviving candidate is a normalized
symbol-dependent amplitude `c_0(a,k,shape)`, with the `a = 1` rational family
giving a stable value near `0.0806`. This is a numerical observation, not a
formula for the leading Fourier-integral-operator symbol.

## 4. Consequence for the analytic hand-off

The next analytic target remains the position/shear estimate, not the former
frequency-tail estimate:

```text
D_real(lambda,h) <= (c_0 + o(1)) * sqrt(mass of h on (-inf, 2 log lambda))
                         + E(h,lambda).
```

The numerical O2 probe gives no evidence that `E` blows up for the tested
fixed families. It also gives no information about the required uniform bound
over the full unit sphere. The carrier base remains open; B1 is only a
numerical direction, not a proved nonempty carrier.

## 5. Reproducibility

The repaired script is `scripts/carrier_amplitude_1635.py`. It uses the same
FFT convention and symbol evaluator as the 1630--1634 probes. The exact model
checks at `lambda = 0.002` have relative grid errors between about `1.2e-3`
and `6.6e-3` for the displayed `k` and `a` values; near-floor rows are
explicitly excluded from interpretation.
