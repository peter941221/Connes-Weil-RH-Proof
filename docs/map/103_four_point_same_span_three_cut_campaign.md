# 103 — Three cuts for the four-point same-span contradiction

Date: 2026-09-23.

Status: Cut 1's raw sixth-order, selected-square twelfth-order, four-point
multiplier, weighted-distance bounds, and fixed-owner decay-constant
quantifiers are FORMAL. Its joint strict margin is OPEN. Cuts 2 and 3 remain
PROJECT CANDIDATES. No RH theorem or gate sign is claimed. Subordinate to
[003](003_b1_b5_minimal_exit_route_selection.md),
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
three-cut strategy without changing the route ruling.

## Cut 2: prove the gate on the same span

For real `lambda`, write the actual gate entries on `u` and `g` as

```text
D = ICgate(u.square)
B = ICgate(u.involution.convolution g)
C = ICgate(g.square) > 0
ICgate(h(lambda).square) = D - 2*lambda*B + lambda^2*C.
```

The strict positive pivot `C` is formal for the selected detector. Neither
the sign of `D` nor the needed relation between `D`, `B`, and `C` is known.
One sufficient certificate is `B != 0` and `D*C - B^2 <= 0`, with
`lambda = B/C`; another may use a different nonzero coefficient. A proof
must estimate the full gate on `u`, including the exact finite visible-prime
set of `h(lambda)`. The narrow-root negative diagonal in [091] does not
transfer to `u` merely because both are auxiliary tests.

Acceptance for this cut: a nonzero real `lambda` and a proved nonpositive
gate for this exact `h(lambda)`, with no hypothesis equivalent to that sign.
An exact counterexample to the proposed determinant certificate on the
selected family would end this candidate and require a different span.

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
FORMAL in `C1FourPointHighShellTail.lean`; the joint margin and same-span
gate are PROJECT CANDIDATES until proved. This record changes no
binding route ruling and makes no RH claim. Preserve dated proof details and
Lean/build/axiom evidence in `docs/proofs/` and `MEMORY.md` when a cut lands.
