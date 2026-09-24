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
vertex witness at `lambda = B'/(2*C)` near `0.5 * K^4`), and record 1919
reduces it to an exact signed-variance identity
`det = A^2 * Var_nu(P)` on the explicit kernel measure `mu = K*W*dxi`
(verified to floating-point precision; see the Cut 2 section), and record
1920 locates the negativity in the visible prime sum (share `>= 99.7%` of the
negative mass at `c >= 1.0`; prime-only block strictly negative on 10/10
scanned widths) with the arch/cross domination delicate for wide owners. The
determinant
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

The high-shell index dependency is now existentially closed for fixed `rho`
and fixed span coefficient: record [1933](../proofs/1933_four_point_tail_index_existence.md)
proves that every positive tail budget can be met by a later convolution index
`n`, using the existing geometric factor `(1/2)^n`. This removes the former
conditional scalar `hsmall` premise from the tail interface. Uniformity in
`rho` and the gate-selected coefficient remains open.

The result is now uniform over bounded span coefficients: for fixed `rho`,
`L >= 0`, and positive `epsilon`, one threshold `N` works for every `n >= N`
and every `|lambda| <= L`. A future determinant proof therefore only needs to
provide a coefficient bound; it no longer needs to coordinate an individual
`lambda` with the convolution index at the tail stage.
See proof record [1934](../proofs/1934_four_point_uniform_tail_coefficient_bound.md).
The stronger bounded-region form is now formal as well: for `||rho|| <= R`,
`|lambda| <= L`, and fixed positive `epsilon`, one threshold `N` works
uniformly. See [1935](../proofs/1935_four_point_tail_uniform_on_bounded_rho_region.md).

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

## Current priority

Record [1932](../proofs/1932_four_point_span_route_priority_and_first_attack.md)
selects this same-span campaign as the primary attack. Route A remains a
valid direct RH producer, but its negative gate on the actual healthy owner is
already the contradiction theorem itself, not an independent preparatory
witness step.

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

**Kernel form and the variance identity (record 1919).** The whole gate
functional on the span is a single spectral pairing `ICgate(F) = integral
K(xi)*Fhat(xi) dxi` with the explicit kernel `K(xi) = sigma(2*pi*xi) +
2*sum_{visible n}(Lambda(n)/sqrt(n))*cos(2*pi*xi*log n)`, because both the
committed archimedean sigma identity and the finite-prime sum are linear in
`Fhat`; on the owner pair `uhat = P*ghat` with the real even quartic
`P(omega) = (delta^2 + gamma^2 - omega^2)^2 + 4*delta^2*omega^2` (the orbit
nodes `{+-delta +- i*gamma}`), so `D, B01, C` are the moments
`integral K*P^2*W`, `integral K*P*W`, `integral K*W` of the single signed
measure `mu = K*W*dxi`, `W = |ghat|^2 >= 0`. The determinant then has the
exact signed-variance form `det = A^2 * Var_nu(P)`, `nu = mu/A`,
`Var_nu(P) = (1+f)*Var_+ - f*Var_- - f*(1+f)*Delta^2` for the sign split of
`mu` (`f` the negative mass ratio, `Delta` the mean gap), i.e.
`det < 0 <=> f*Var_- + f*(1+f)*Delta^2 > (1+f)*Var_+` (sufficient:
`f*Delta^2 > Var_+`), and in the moment form `det = A^2*[(m4 - m2^2) +
2a*(m3 - m1*m2) + a^2*(m2 - m1^2)]` with `u = (2*pi*xi)^2`, `a =
-2*(gamma^2 - delta^2)`. Probe: four certified cases x two channels, all
identities verified to floating-point precision (P-form and moment-form
residuals `<= 1.6e-11`; arch k-form vs the E3 engine `1.7e-10 .. 2.6e-8`),
criterion holds 8/8 with `f*Delta^2/Var_+` in `0.19 .. 0.94` — the
negative-spread term is essential; the arch channel alone holds via thin mass
(`f ~ 2e-4 .. 1.8e-3`) with far-spread negative tail (`Var_- ~ 1e10`), the
primes thicken the negative mass. The channel split of this record is linearity
of the kernel map in `K`; the obligation is now a variance gap / five-moment
bracket inequality on an explicit measure whose only owner-dependent input is
the nonnegative density `W` (record 1919, artifact
`results/1919_gate_kernel_form.json`).

**Negativity origin (record 1920, scouting).** Three probes fix where the
determinant's negative mass lives and how the margin scales with the owner
width. (i) The arch-channel criterion is a SPREAD criterion for `W`: it holds
for bump widths `c <= 1.3` with `R` up to `5.0e3`, and fails for concentrated
densities (narrow gauss, wide bump) where `f -> 0`. (ii) The full kernel's
negative mass is created by the visible prime sum inside the `sigma`-positive
central zone `|xi| < xi* = 1.0011` — share `>= 99.7%` at `c >= 1.0`, `100%` at
`c >= 2.0` — and the prime-kernel amplitude `K_prime(0) = 2*sum
Lambda(n)/sqrt n` crosses the sigma scale at `c ~ 1.0` and reaches `75.2` at
`c = 3.0`. (iii) Block scan `c = 1.3 .. 3.0` x `gamma in {14.13, 21.02}`:
`det_prime < 0` on 10/10 rows with criterion ratio `R_prime` in `1.38 ..
2.06` at EVERY width, while `det_arch` flips positive between `c = 1.3` and
`1.6` (`gamma = 21.02`) and `det_cross` follows the arch sign; the full
determinant stays negative on 10/10 as a residual of large cancelling blocks
(4% of the block scale at `c = 3.0, gamma = 21.02`), which is the mechanism
behind the record-1918 boundary thinness. Route reading: the obligation
splits into the robust prime-only sign `Q(K_prime) < 0` (an
oscillation-versus-smooth-density statement for the explicit trig polynomial
`K_prime` against `W`) plus the delicate cross-domination inequality
`-Q(K_prime) > Q(sigma) + 2*B(sigma, K_prime)`; the arch-first plan is valid
only for `c <= 1.3`, exactly the instrument-certified window of record 1918
(min `|disc|/ddisc_cert = 30.4`). Artifacts
`results/1920_gate_kernel_{stress,wide,origin}.json` (record 1920).

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

The first-prefix proposal has an owner-specific guard. The formal cutoff for
`OrbitG8Geometry` gives only a finite range containing the actual visible
prime-power set; it does not imply that `n = 2` is visible. Record 1936's
ambient visibility probe therefore cannot supply this premise. Record 1937
formalizes the exact alternative: if `2` is visible, the finite prime sum is
the `n = 2` term plus the erased actual-owner remainder; if not, that term is
zero. The remaining sign proof must consequently either prove visibility of
`2` for the selected owner or select a different owner-specific nonzero term.
This is a strict refinement of the finite certificate obligation, not a gate
sign result. The stronger range-level split in record 1937 removes even the
visibility premise from the algebraic decomposition: `n = 2` is a fixed term,
and non-visibility makes it zero automatically. Visibility is still needed
only if a strict lower bound for that particular term is claimed.

The exact coefficient reduction is now formal in record 1937:
the n=2 contribution is `log(2)/sqrt(2)` times the real bilateral profile
at `log(2)`, and is negative exactly when that owner-specific profile is
negative. The next non-interface obligation is therefore a strict bound for
this physical sample together with the erased owner-specific remainder.
The physical readback is formal as well: the sample is exactly the real part
of the selected owner's `orbitPhysicalKernel` at `log 2`, with a positive
factor. The live analytic target is now an explicit physical-kernel sample
plus its finite actual-owner remainder.

Record 1938 removes the need to sign the remainder term-by-term: the actual
finite prime sum is bounded above by the exact n=2 term plus the explicit
support-overlap harmonic majorant on the erased owner range. Thus the next
strict obligation is the scalar budget
`archimedeanTerm + n2PhysicalTerm + overlapRemainder <= 0`. This is a genuine
quantitative reduction; the majorant may still be too loose and no gate sign
is claimed. The final 1938 theorem sharpens it by subtracting the overlap
majorant's own n=2 contribution, since that node is already retained exactly.

Record 1939 now removes the absolute-value loss from the live formulation:
the same actual-owner range is exactly n=2 plus an erased sum of positive
physical integrals minus negative physical integrals. This is FORMAL and is
the next producer-facing target. The overlap majorant remains only a guard;
the strict proof must exploit the signed erased remainder, consistently with
the scoped scalar-majorant no-go in map 093.

Owner guard (record 1940): this 1939 decomposition is for the original
`OrbitG8Geometry rho g` owner. It is not yet a certificate for the span owner
`h(lambda) = u - lambda * g`; passing it across would be an owner substitution.
The next core brick is therefore the exact signed physical-kernel expansion
for that same span owner.

Record 1941 closes that algebraic owner gap: the signed profile of any finite
span, hence of `h(lambda)`, is formally expanded into the four pairwise
physical integrals. This is FORMAL; the remaining producer obligation is now
only the strict signed inequality for those four channels at the
gate-selected coefficient.

Record 1942 specializes that expansion to the two-span four-channel lambda
quadratic, including the n=2 sample. The remaining strict obligation is now
the signed inequality for this quadratic at the already formal vertex
coefficient; no owner substitution remains.

Record 1945 tested the proposed shortcut of replacing the owner-specific
vertex coefficient by `0.5 * (3 + ||rho||)^4` and nearby fixed multiples. On
the 18 committed-class cases, the fixed coefficient was negative in only 6/18
cases (0.9 and 1.1 multiples: 9/18 and 3/18); the vertex was negative in all
18. This is a scoped numeric no-go for the simple fixed-coefficient shortcut,
not an analytic counterexample. The coefficient therefore remains
owner-specific, and the next quantitative target is the vertex determinant
with the actual four-channel physical readback.

Record 1946 evaluates the vertex gate after splitting the linear gate value
into its Archimedean and finite-prime contributions. Both contributions are
strictly negative on all 18 committed-class cases; the smallest full relative
margin is about `4.96e-5`. This suggests the next proof target should be two
owner-preserving signed channel estimates at the vertex, rather than a
determinant-block estimate. It remains a numerical target: no channel sign is
proved for the selected owner.

Record 1947 audits the formal boundary. The current healthy-detector data
provide support, vanishing, detection, and square positivity, but no
owner-specific gate-entry bounds or Archimedean/finite-prime signed profile
estimates. Support only gives a finite visible-prime range. Consequently the
selected-owner channel signs cannot yet be proved from the existing premises;
the next analytic brick must supply an actual-owner `L, eta` contract for the
vertex gate, or a reproducible counterexample in that owner class.

Record 1948 stress-tested the proposed separate channel signs on wider owners:
the full vertex gate and prime channel stayed negative on 10/10 cases, but the
Archimedean channel was negative only on 3/10 and became positive at wider
support. Thus the separate `Q_arch < 0`, `Q_prime < 0` target is frozen as a
scoped no-go unless a selected-owner width restriction is first proved. The
live target is the summed signed inequality with exact prime/Archimedean
cancellation retained.

together with the positive cross sum, on the selected healthy detector (under
the cross-term symmetry this is exactly the probe's
`D*C - B01^2 < 0`, and by record 1919 equivalently the variance-gap /
moment-bracket inequality on `mu = K*W*dxi`), and the Cut 1 joint margin at
the pinned coefficient. The
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
post-analysis, law F79); the kernel form, the signed-variance identity, the
variance-gap criterion, and the moment bracket are EXACT ALGEBRA plus NUMERIC
verification in record 1919; record 1943 now formally proves the finite
signed-variance identity, but signed weights still give no automatic sign.
Record 1943 also proves the strict two-atom certificate: positive mass,
negative mass, and unequal profile values imply a negative determinant.
Record 1949 formally proves the general bipartite variance-gap decomposition
and negativity criterion, wiring cross-gap domination directly to the
strictly negative vertex span gate quadratic.
Record 1950 establishes the macro-atom variance bound (`finite_signed_variance_bipartite_bound_neg`,
`exists_pos_lambda_quadratic_neg_of_macro_atom_bounds`), reducing the gate determinant
negativity to coarse-grained oscillation bounds and cross separation.
Record 1944 formally aggregates the actual span owner's finite visible
prime sum into the four same-owner physical channels, in both bilateral and
direct-integral form. This removes the opaque finite-prime aggregate but does
not prove its signed margin. The actual-owner pairwise physical-kernel budget,
joint margin, and cross-determinant inequality on the selected owner remain
PROJECT CANDIDATES until proved. This record changes
no binding route ruling and makes no RH claim. Preserve dated proof details and
Lean/build/axiom evidence in `docs/proofs/` and `MEMORY.md` when a cut lands.
