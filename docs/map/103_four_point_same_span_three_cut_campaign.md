# 103 — Three cuts for the four-point same-span contradiction

Date: 2026-09-23.

Status: Cut 1's raw sixth-order, selected-square twelfth-order, four-point
multiplier, weighted-distance bounds, and fixed-owner decay-constant
quantifiers are FORMAL. Its joint strict margin is OPEN. Cut 2 is reduced to
the scored cross-determinant inequality on the annihilator-detector pair: the
exact span parabola, its complete trichotomy, the diagonal and vertex
witnesses, and the same-owner wires are FORMAL in records 1917/1918; the sign
probe of record 1918 selects the vertex branch on a committed-class family
(`D > 0`, discriminant strictly positive in the certified engine pair, strict
vertex witness at `lambda = B'/(2*C)` near `0.5 * K^4`). The determinant
inequality on the selected owner is OPEN. Cut 3 remains a PROJECT CANDIDATE.
No RH theorem and no gate sign on the selected owner is claimed. Subordinate
to [003](003_b1_b5_minimal_exit_route_selection.md),
[091](091_two_span_sign_balancing_closed.md), and
[094](094_two_point_differential_annihilation_and_spectral_decomposition.md).

## Owner and consumer

Assume a right off-line zero `rho`. Fix one selected healthy `CompactLog`
detector `g = selectedOwner base correction n` after the correction and finite
zero prefix have been chosen. Let `u = fullFunctionalEquationOrbitAnnihilator
g rho`, and let `h(lambda) = annihilatorDetectorSpanVector u g lambda`.

The consumer is the formal finite-prefix theorem in
`C1FourPointSpectralPrefixTransport.lean`, followed by the spectral-tail
consumer in `C1HealthyYoshidaSpectralNegativity.lean` and the generic
same-test gate-to-`qw` bridge in `C1OrbitWindowSemiLocalGate.lean`. Both signs
must be proved for this exact
`h(lambda)`, with its own support-derived visible-prime set. The gate theorem
in [091] currently applies to `spanObj ![narrowArchRoot, g]`, which is a
different test. It supplies no gate sign for `h(lambda)`.

This route would prove RH by a contradiction for `h(lambda)` if completed.
It does not, by itself, prove `qw(g) >= 0` for the original selected `g`.
That distinction is part of the owner ledger, not a change to the binding
healthy-owner objective.

## Same-owner assumption ledger

```text
target:      ICgate(h(lambda).square) <= 0 and qw(h(lambda)) < 0
known:       g has triple vanishing, selected orbit values, finite-prefix
             square zeros, compact support, and a fourth-order square tail;
             fixed base/correction owners admit decay constants chosen before
             n and lambda; g's own gate is strictly positive
remove:      first the joint high-shell margin for h(lambda_n)
then remove: the gate sign premise for the same h(lambda)
failure:     an exact obstruction to the proposed tail budget or to the
             same-span gate inequality on the selected construction
```

No `HealthyYoshidaDetectorData` field for `h(lambda)` may be inferred from
the corresponding field for `g`; spectral negativity must be proved directly
for `h(lambda)`.

## Cut 1: pay for the four-point multiplier

The exact Laplace identity in [094] multiplies `laplaceAt g` by a degree-four
polynomial `P_rho(s) - lambda`. Its convolution square acquires the product of
that factor at `s` and `-star s`, with degree eight growth on high vertical
lines. The existing fourth-order square tail of `g` cannot be substituted.

Candidate producer: use the **all-index** unscaled Yoshida theorem, choosing
the correction and finite interpolation radius before the convolution count.
One base factor has an available uniform quartic strip bound
(`exists_uniform_compactLog_laplaceAt_vertical_quartic_decay`); the correction
has a quadratic bound; the remaining base factors contract by `1/2` above
the fixed threshold. For any `n`, this gives a raw sixth-order estimate of
the schematic form

```text
|t/(2*pi)|^6 * |Laplace(raw_n, sigma+it)|
    <= C_base4 * C_correction2 * (1/2)^n.
```

The reflected product yields a twelfth-order selected-square bound. This
part is FORMAL in
`C1FourPointHighShellTail.selectedOwner_convolutionSquare_vertical_twelfth_bound`:
the right side is `((1/2)^n * C_base4 * C_correction2)^2`. Its raw sixth-order
predecessor is formal in the same leaf. The leaf now also proves the exact
weighted-distance estimate for the selected four-point span. Set
`K = 3 + norm(rho)`, `L = K^4 + abs(lambda)`, and
`M_n = (1/2)^n * C_base4 * C_correction2`. On the high strip, the product of
the two spectral distance weights and the transformed square is at most
`K^4 * L^2 * (2*pi)^12 * M_n^2`. Its theorem
`selectedOwner_fullOrbit_span_fourthOrderSpectralTail` feeds the existing
tail interface whenever that explicit bound is below `epsilon^2`. These
statements are FORMAL; proof record 1915 names the focused build and audit.
Choose the finite zero prefix and high-shell start before the correction.
Increasing the shell start after interpolation would lose finite-prefix
control. Record 1916 formally completes the decay-constant quantifier
handoff: for each fixed `base, correction`, one tuple `C4, C2, T` is chosen
before `n` and `lambda`; the quartic base bound, quadratic correction bound,
and base contraction then hold uniformly for every later `n, lambda`. This
removes those analytic decay fields as independent assumptions from Cut 1.
It does not prove the joint strict margin below or provide a lower bound on
the gate-selected `lambda_n`.

The remaining acceptance for this cut is a checked joint inequality on one
selected `n, lambda_n`, including the existing shell multiplicity factor:

```text
4 * spectralMultiplicityConstant * (3/4)^shellStart *
  K^4 * (K^4 + abs(lambda_n))^2 * (2*pi)^12 *
  ((1/2)^n * C_base4 * C_correction2)^2
    < xiMultiplicity(rho) * lambda_n^2.
```

This permits an `epsilon^2` strictly between the explicit weighted bound
and the spectral-prefix margin. The strict inequality is PROJECT CANDIDATE;
the weighted bound itself is FORMAL. The shell-start and multiplicity
parameters follow `C1SpectralTailBound`. The existing full-sum consumer is
normalized to the prefix margin `-xiMultiplicity(rho)`; Cut 3 must instantiate
its shell-prefix conversion and use the proved `-xiMultiplicity(rho)*lambda^2`
margin without silently setting `lambda^2 = 1`.

**Quantifier coupling:** the gate coefficient may be `lambda_n`, depending on
the convolution count. Geometric decay of the tail alone does not show it is
smaller than `xiMultiplicity(rho) * lambda_n^2`; `lambda_n` might approach
zero equally fast or faster. The eventual certificate must prove the joint
ratio on one chosen `n` (or supply a nonzero coefficient uniformly controlled
in `n`). Selecting `n` after treating `lambda` as fixed is invalid unless
that independence has first been proved. This corrects the provisional
three-cut strategy without changing the route ruling. The record-1918 probe
pins this coupling numerically on its tested family: the vertex coefficient
`lambda = B'/(2*C)` is positive, width- and abscissa-stable, and tracks
`~0.5 * K^4` with `K = 3 + norm(rho)`, so `(K^4 + abs(lambda))^2 / lambda^2`
is an explicit O(1) factor (`~7-10`) there rather than a growing one; the
acceptance reduces to an `n`-selection with every factor explicit on that
family. This is probe evidence on a committed-class family, not a statement
about the selected owner.

## Cut 2: prove the gate on the same span

For real `lambda`, write the actual gate entries on `u` and `g` as

```text
D  = ICgate(u.square)
B' = ICgate(u.involution.convolution g) + ICgate(g.involution.convolution u)
C  = ICgate(g.square) > 0
ICgate(h(lambda).square) = D - lambda*B' + lambda^2*C.
```

Record 1917 proves this identity on the committed owners in
`C1FourPointSpanGateCertificate.annihilator_span_gate_eq_parabola` with no
cross-term symmetry assumed; the previous one-`B`, factor-`2` normalization is
exactly the symmetry `ICgate(g.involution.convolution u) = ICgate
(u.involution.convolution g)`, which is not needed. The strict positive pivot
`C` is formal for the selected detector. The complete trichotomy
`exists_nonzero_lambda_quadratic_nonpos_iff` replaces the sufficient
certificate: a nonzero coefficient with nonpositive gate exists exactly when
`D < 0`, or `D = 0` with nonvanishing cross sum, or `D > 0` with discriminant
`B'^2 - 4*C*D >= 0`. The previous `B != 0` and `D*C - B^2 <= 0` certificate
with `lambda = B/C` is the `D > 0` vertex case; its side condition is
automatic there and genuinely needed only at `D = 0`. A strictly negative
diagonal alone yields a strictly positive closed-form coefficient with no
cross-term condition (`exists_pos_lambda_quadratic_nonpos`, witness
`gatePlusRoot`), so the coefficient coupling with Cut 1 is pinned rather than
free: `lambda = gatePlusRoot D B' C` is determined by the three gate values,
and it is bounded below by `2*abs D / (sqrt (B'^2 - 4*C*D) + abs B')`
(derived on paper, rig-verified in record 1917, not formalized). The sign
probe of record 1918 finds the measured family in the third branch instead
(`D > 0`, discriminant positive), where the operative pin is the vertex
`lambda = B' / (2*C)`; both pins are explicit functions of the three gate
values. On a healthy detector the wire
`exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_gate_neg` turns
`D < 0` into `orbitWindowSemiLocalGate (h(lambda))` at that positive
`lambda`, and `exists_pos_lambda_gate_and_prefix_of_annihilator_gate_neg`
carries the committed finite-prefix bound on the same owner and coefficient.

**Probe (record 1918).** A sign probe on a committed-class family (smooth
bumps, widths `c = 0.8, 1.0, 1.3`, three off-line abscissas `delta = 0.05,
0.10, 0.30`, heights `gamma = 14.1347, 21.0220`, 18 cases) measures `D, C,
B'` with four archimedean engines plus a per-shape arbiter. Result: `D > 0`
in every engine on all 18 cases, and the discriminant `B'^2 - 4*C*D` is
strictly positive on all 18 cases under the certified engine pair `{E3, E4}`
(agreement `<= 6e-7` relative; the all-engine envelope is poisoned by an E1
shape failure up to 5.3% and an E5 failure up to ~24% on the `u *⋆ u` entry,
law F79). So the live branch of the trichotomy is the third one, `D > 0` with
discriminant positive, and the witness is the **vertex** `lambda = B' / (2*C)`
with the exact value

```text
ICgate(h(lambda).square) at lambda = B'/(2*C)
    = (4*C*D - B'^2) / (4*C) = det / C,   det = D*C - (B'/2)^2 < 0,
```

strictly negative. On the probed family `lambda = B'/(2*C)` is pinned close to
`0.5 * K^4` with `K = 3 + norm(rho)` (`4.00e4` at `gamma = 14.13`, `1.96e5` at
`gamma = 21.02`, width- and abscissa-stable), and the relative indefiniteness
margin `B01^2/(D*C) - 1` ranges over `[5.0e-5, 0.116]`, shrinking with width
and height. The certified-pair sensitivity leaves all 18 discriminant verdicts
robust; a deliberately pessimistic `1e-5` relative envelope on the shared
inputs would not clear the 10x bar at the thinnest cases, so the margins are
thin by construction and any analytic route to this determinant must be sharp.

Two further probe readings sharpen the obligation. (i) The determinant splits
into archimedean, finite-prime, and cross blocks (the polarization of the
determinant form), and each of the three is separately strictly negative on
all 18 cases (arch share `0.237 .. 0.809`; prime share `0.7% .. 51%` growing
with width): the arch block lives on the committed `sigma` symbol with its
theorem-grade sign flip at `u* = 6.289836`, the prime block is a finite
explicit sum over the visible prime powers, so the analytic route can target
one channel at a time instead of the full gate. (ii) A width/height boundary
scan (widths `1.3 .. 3.0`, heights `21.02, 30.42`, abscissa `0.05`, 10 cases)
keeps `det < 0` throughout — the sign is structurally robust on the scanned
window — but the relative margin decays to `~1e-7` (roughly quartic or
steeper in width, `~gamma^-8` in height) and the certified-pair sensitivity
overtakes `|disc|` beyond width `~2.0` (instrument limit, F77 family). The
determinant obligation is therefore robust in sign but numerically thin: any
estimate route must be exact-ish or channel-structural.

Formal wiring of this branch landed with the probe in the same module:
`gate_quadratic_at_vertex` (the exact value above),
`exists_pos_lambda_quadratic_neg_of_det_neg` (positive cross sum, positive
pivot, negative determinant give a strictly positive `lambda` with strictly
negative gate), and the two same-owner wires
`exists_pos_lambda_orbitWindowSemiLocalGate_of_annihilator_det_neg`,
`exists_pos_lambda_gate_and_prefix_of_annihilator_det_neg`, which now carry
the strict gate and the committed prefix bound at one coefficient.

Remaining acceptance for this cut, in the measured branch, is the scored
cross-determinant inequality

```text
ICgate(u.square) * ICgate(g.square) - ((ICgate(u.involution.convolution g)
  + ICgate(g.involution.convolution u)) / 2)^2 < 0
```

together with the positive cross sum, on the selected healthy detector (under
the cross-term symmetry this is exactly the probe's
`D*C - B01^2 < 0`), and the Cut 1 joint margin at the pinned coefficient. The
`D < 0` diagonal signature and its wires remain formal as the fallback branch.
The full gate of the annihilator must be estimated, including the exact finite
visible-prime set of `h(lambda)`; the narrow-root negative diagonal in [091]
does not transfer to `u` merely because both are auxiliary tests.

## Cut 3: assemble one contradiction

Use [094] to bound the same `h(lambda)` finite prefix by
`-xiMultiplicity(rho)*lambda^2`. Use Cut 1 to make its high-shell norm
strictly smaller than that amount; this proves `qw(h(lambda)) < 0`. Use Cut 2
and triple vanishing to prove `0 <= qw(h(lambda))`. Only then invoke the
existing `SourceRH` and Mathlib RH bridge. The
`C1PinnedOrbitExit.false_of_healthyDetectorData_and_orbitWindowSemiLocalGate`
consumer cannot be applied directly to `h(lambda)`, because healthy detector
data has only been proved for `g`. The direct two-sign contradiction for `h`
must be placed inside the hypothetical off-line-zero proof. No new
conditional exit theorem is needed.

The cuts are dependent: Cut 1 reduces the weighted-tail premise to the joint
scalar margin but does not close RH; Cut 2 is the decisive sign problem. The construction
quantifiers and `lambda` must be coordinated, since the strict tail margin
is proportional to `lambda^2`.

## Provenance and route ruling

The four-point multiplier and prefix bound are FORMAL in [094]. The uniform
quartic base decay and all-index contraction are FORMAL in
`C1SpectralWeil.lean`, `CC20YoshidaConvolution.lean`, and
`C1HealthyYoshidaUnscaledOrbit.lean`. The raw sixth-order, selected-square
twelfth-order, polynomial-multiplier, and weighted transfer estimates are
FORMAL in `C1FourPointHighShellTail.lean`. The span parabola, the trichotomy,
the diagonal and vertex witnesses, and all four same-owner wires are FORMAL in
`C1FourPointSpanGateCertificate.lean`; the branch selection on a
committed-class family is NUMERIC in record 1918 (probe plus certified
post-analysis, law F79); the joint margin and the cross-determinant inequality
on the selected owner are PROJECT CANDIDATES until proved. This record changes
no binding route ruling and makes no RH claim. Preserve dated proof details and
Lean/build/axiom evidence in `docs/proofs/` and `MEMORY.md` when a cut lands.
