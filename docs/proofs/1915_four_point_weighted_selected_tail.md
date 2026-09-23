# 1915 — Weighted high-shell bound for the selected four-point span

Date: 2026-09-23.

Status: FORMAL quantitative reduction; the joint spectral margin and gate
sign are open. This is a project derivation from the existing compact-test
decay and Yoshida construction, not an originality or RH claim.

## Owner and derivation

Assume a hypothetical right off-line zero `rho`. The raw selected orbit is
`raw_n = (convolutionIterate base n).convolution correction`; its centered
test is `g_n = (selectedOwner base correction n).sourceTest`. The four-point
span is `h_n(lambda) = fullFunctionalEquationOrbitAnnihilator g_n rho -
lambda*g_n`, represented by `annihilatorDetectorSpanVector`.

The correction is fixed before `n`. On the high source strip, one base
factor contributes the existing quartic vertical decay `C4`, the correction
contributes its quadratic decay `C2`, and the other `n` base factors each
contribute at most `1/2`. Therefore:

```text
r^6 * |Laplace(raw_n,z)| <= M_n,
r = |Im(z)|/(2*pi),
M_n = (1/2)^n * C4 * C2.
```

The actual selected convolution square is a reflected product of two raw
transforms at the same imaginary height. Hence its twelfth-order bound is
`r^12 * |Laplace(g_n.square,z-1/2)| <= M_n^2`.

For `z` in the critical strip with `|Im(z)| >= 1`, set
`K = 3 + norm(rho)` and `L = K^4 + abs(lambda)`. Every source orbit factor
is at most `K*|Im(z)|`; the four-point span multiplier is at most
`L*|Im(z)|^4`. The spectral distance from `z` and from `1-conj(z)` to `rho`
is also at most `K*|Im(z)|`. Multiplying the two distance weights, the two
span multipliers, and the selected square gives the explicit formal bound:

```text
|z-rho|^2 * |(1-conj(z))-rho|^2 *
  |Laplace(h_n(lambda).square,z-1/2)|
    <= K^4 * L^2 * (2*pi)^12 * M_n^2.
```

The proof uses no condition on the height of `rho` beyond what the downstream
`FourthOrderSpectralTail` interface itself asks for. It keeps the actual
selected `CompactLog` test throughout; no additive-convolution or changed
prime owner occurs.

## Lean results

The new leaf `ConnesWeilRH/Dev/C1FourPointHighShellTail.lean` and its paired
Audit prove:

- `convolutionIterate_convolution_vertical_sextic_bound`;
- `selectedOwner_convolutionSquare_vertical_twelfth_bound`;
- `fullOrbit_span_multiplier_norm_le_height_pow_four`;
- `selectedOwner_fullOrbit_span_doubleDistance_bound`;
- `selectedOwner_fullOrbit_span_fourthOrderSpectralTail`, conditional only on
  the displayed explicit upper bound being below `epsilon^2`.

The base quartic bound is already formal in `C1SpectralWeil`; the correction
quadratic decay comes from the correction construction in
`CC20YoshidaConvolution`. The leaf accepts both as explicit hypotheses for
the same base and correction. The selected all-index existential API must
preserve that quadratic witness when the final owner is chosen.

## Exact remaining margin

The four-point prefix theorem in record 1914 gives
`Re(prefix) <= -xiMultiplicity(rho)*lambda^2`. The existing shell-tail
consumer bounds the remaining norm sum by
`4*epsilon^2*spectralMultiplicityConstant*(3/4)^shellStart`.
Consequently the necessary joint budget for this route is

```text
4 * spectralMultiplicityConstant * (3/4)^shellStart *
  K^4 * (K^4 + abs(lambda_n))^2 * (2*pi)^12 *
  ((1/2)^n * C4 * C2)^2
    < xiMultiplicity(rho) * lambda_n^2.
```

Here `lambda_n` may be chosen by the same-span gate and can depend on `n`.
Taking `n` large does not alone prove this inequality; `lambda_n` could
decay at least as fast as the tail. One must prove a joint bound on one
selected index, or a uniform nonzero coefficient. The gate sign itself is
still open for `h_n(lambda_n)`: the formal narrow-root gate theorem concerns
a different test. The shell-prefix conversion for the scaled `lambda^2`
margin also remains to be assembled; existing full-sum consumers are stated
with unit prefix margin.

## Verification

Focused log: `build-logs/20260923_fourpoint_tail_interface_try10.log`
on the ext4 build mirror.
It reports `Build completed successfully (3809 jobs)`, zero `error:` lines,
zero `sorryAx`, and all five audited declarations depend only on
`[propext, Classical.choice, Quot.sound]`. Windows source and ext4 build
mirror had matching MD5 hashes before the accepted build.
