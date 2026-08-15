# AGENTS.md

Working rules for the Connes-Weil RH formalization. This file holds stable,
reusable rules only. Proof-by-proof guards, rejected routes, and chronology
live in `MEMORY.md` and `docs/proofs/`; git history owns superseded detail.
When a new theorem changes the active root, update the relevant section here
instead of appending another "current root" paragraph.

## 1. Project Target

Aimed at a formal Connes--Weil route to RH in Lean 4 / mathlib `v4.30.0`.
The repository does **not** yet prove RH unconditionally. The active theorem
root is the RH-level detector criterion coverage axiom
`normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`; Physical Gate 3U
is a separate diagnostic branch, not the current RH root.

## 2. Current RH Root And Route Split

The shortest live consumer chain is:

```text
normalizedSelectedFinalRouteDetectorCriterionCoverageRoot
  -> normalizedSelectedFinalRouteSourceRHFrom08AFromTheorems
  -> cc20FiniteVanishingExitFromTheorems
  -> rhDefinitionBridgeToMathlibFromTheorems
  -> unconditional_rh_skeleton
```

`CC20RouteRealization.normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_standardSourceRH`
proves that this coverage proposition is equivalent to `SourceRH` once the
already-proved Yoshida detector existence theorem is supplied. It is therefore
an RH-level statement, not a lower assembly socket.

The constructive route toward that root must keep one mathematically correct
test-space owner through the log/positive coordinate change, true Mellin
convolution, the pole and archimedean terms, all prime-power terms, the explicit
formula, finite-vanishing criterion, and Yoshida detectors. The repaired C1
modules now close the object and readback layer, but not the load-bearing
analytic theorem:

```text
CompactLog -> positive-variable coordinate bridge CLOSED
healthy Mellin convolution                         CLOSED
complete same-owner pole/arch/all-prime functional CLOSED as definition/readback
zero-spectral absolute summability on every test   CLOSED
xi zero-index completeness (= exact xi zero set)   CLOSED
same-owner arithmetic = zero-spectral formula      OPEN
positive-trace bridge                              OPEN
finite-vanishing Weil criterion on the same owner  OPEN (RH-level)
Yoshida detectors on that same owner               OPEN rebuild/transport
```

The spectral convergence half is unconditional and axiom-clean in
`C1SpectralSummability`: the completed-xi kernel moment gives dyadic xi growth,
Jensen bounds analytic zero multiplicity by `K * 3^n`, and compact-log Laplace
decay contributes `4^(-n)`. Since `3 < 4`, `spectralSummableProp F` holds for
every `CompactLogTest F`. Consequently `gate2ExplicitFormula_iff` reduces Gate
2 exactly to `C1SameOwnerWeil.psi F = C1SpectralWeil.spectralWeilValue F`; that
equality and the positive-trace bridge remain open.

The completed-xi zero set is exactly the source spectral index:
`completedRiemannXi_eq_zero_iff_sourceNontrivialZero` (in `CC20ZetaCounting`)
is axiom-clean; the functional equation reflects negative-even zeta zeros into
the zero-free closed right half-plane. The spectral sum indexes the exact xi
zeros, not a subset.

### C1 Coordinate, Owner, And Sign Guards

`CompactLogTest.test` and route `TestFunction` have the same Lean function type
but different mathematical coordinates. The former reads `u = log x`; the
latter reads the positive variable `x`. The canonical bridge is
`C1LogPositiveBridge.toPositiveRouteTest`, with
`mellin_toPositiveRouteTest_eq_laplaceAt` as its coordinate contract. Never
replace this map by the identity merely because the types unify.

The complete compact-log arithmetic functional is owned by
`C1SameOwnerWeil`: `psi F` is pole minus archimedean minus every nonzero visible
prime-power term, and `qw g = psi g.convolutionSquare`. The sign convention is

```text
source QW(g) = psi(g^* * g)
CC20 local sum on starConvolution(g) = -source QW(g)
```

Faithful numerical probes must use the real Laplace points `+1/2` and `-1/2`,
sample prime-power terms at `+/-log(n)`, include all visible prime powers, and
assert `F(0) = ||g||^2` plus the pole-product identity. The historical use of
`i/2`, raw coordinates such as `F(2)`, or a singleton `{2}` sum does not
evaluate this functional.

Support width is metadata, not object identity. A numerical residual and a
Lean plateau with the same support interval are different owners unless a
theorem identifies their functions and all attached data. Never transfer a
numeric sign across that gap.

### C1 Arithmetic Right-Line Guard

`C1XiArithmeticIntervalReadback` expands the von Mangoldt L-series only at
`1 < Re(s)`, where Mathlib supplies absolute summability. Its interval theorem
is a genuine `HasSum` exchange with an explicit majorant; it is not an
integrability theorem disguised as a dominated-convergence call.

Finite prime-power truncations may be continued to `c -> 1+` by ordinary
continuity after composing the two-parameter function with `c |-> (c,t)`. The
elementary pole factor `1 / (verticalPoint c t - 1)` is singular at `t = 0`:
an unrestricted pointwise boundary theorem is false because it contains
`1 / (c - 1)`. Any boundary proof must state `t != 0` or use an a.e./integral
argument that explicitly handles this null point.

The full von Mangoldt boundary at `Re(s) = 1` remains a separate
`FullPrimeBoundaryContract`; never infer it from absolute convergence on the
right half-plane.

The Gamma_R contribution is regular on `Re(s) > 0`.  The public
`continuous_gammaRIntegrand_intervalIntegral` theorem therefore works on the
positive-real subtype, and
`tendsto_gammaRIntegrand_intervalIntegral_c_to_one` gives its finite-height
right-hand `c -> 1+` limit.  This closes only the Gamma_R factor.  It does
not regularize `1 / (c - 1 + t*I)` at `t = 0`, nor does it supply the full
von Mangoldt boundary or the arithmetic/spectral equality.

The Fourier readback brick uses Mathlib's `Measure.integral_comp_mul_left`
with only `(g) (a)` explicit arguments; `volume` is implicit.  Its right-hand
side is a real scalar action on a complex integral, so normalize it with
`Complex.real_smul` before comparing it with complex multiplication.  For
`Real.fourierInv_eq'`, coerce a Schwartz Fourier transform explicitly to
`Real -> Complex` and use `SchwartzMap.fourierInv_coe` when moving between the
Schwartz and function-level inverse transforms.

`C1XiArithmeticPrimePowerReadback` now exposes the full-line Fourier inversion
API and the reflected-character consumer.  The direct profile reads
`F(log n)` and the reflected profile reads `F(-log n)` after the explicit
change of variables `t -> -t`; do not replace that step by an evenness claim
about the test.  The completed single-index readback is only at `c = 1`, and
it is a theorem for one von Mangoldt term, not a boundary convergence theorem
for the full prime-power series.  Keep the `n = 0` zero branch separate before
using `log n` or `1 / sqrt n`.

`C1XiArithmeticPrimePowerAssembly` assembles those terms over the exact finite
`C1SameOwnerWeil.globalPrimeIndexSet F`.  It proves integrability of every
single term at `c = 1`, exchanges the finite sum with the full-line integral,
and reindexes the range truncation at `globalIndexBound F` to that same owner.
The endpoint
`integral_finiteArithmeticPrimePowerIntegrand_one_at_globalIndexBound_eq`
is therefore a finite `c = 1` readback to `finitePrimeSum` (after taking real
parts), not a proof of `FullPrimeBoundaryContract`, the infinite von Mangoldt
boundary, or the arithmetic/spectral equality.

For `T >= 0`, the same module proves continuity and a right-hand `c -> 1+`
limit for the finite truncation interval integral.  This is a legitimate
finite-height parameter bridge because the finite prime-power owner is
continuous on a compact interval.  Do not transfer it to the elementary pole
term: `1 / (c - 1 + t*I)` is singular at `t = 0`, so the pole boundary still
requires an a.e. or distributional argument.

`C1XiArithmeticPoleBoundary` now isolates the elementary pole into a regular
factor and a singular Cauchy kernel.  For `c > 1`, the unweighted singular
kernel has the exact finite-height integral
`-2 * arctan(T / (c - 1)) * I`, and for `T > 0` its right-hand limit is
`-pi * I`.  The regular factor has a genuine interval-integral continuity
theorem on the positive-real subtype and a right-hand `c -> 1+` limit.
The weighted singular term must be split with its actual value
`symmetrizedLaplaceWeight F (verticalPoint c 0)`; it cannot be frozen at
`c = 1` before taking the limit.  The remainder boundary is therefore carried
by the data-bearing `ElementaryPoleSingularRemainderBoundaryContract` field
`remainderBoundaryValue`, not defined as zero.  Its assembly theorem consumes
that contract and proves only the finite-height elementary-pole limit; it does
not prove the full von Mangoldt boundary or the arithmetic/spectral equality.

### C1 Xi-Contour Guard

`logDeriv completedRiemannXi` is total at a zero, whereas a residue argument
needs its punctured meromorphic meaning. At a xi zero `rho`, obtain one local
cofactor `h` with `xi(s) = (s-rho)^m h(s)` and `h(rho) != 0`; derive the
analytic disc, zero-free disc, and principal-part identity from that same
`h`, then choose the contour radius below all three. Never read the total
value `logDeriv completedRiemannXi rho` as a residue.

The finite closed-ball xi factorization supplied by Mathlib is initially only
`codiscreteWithin`. At an interior point, first use the meromorphic identity
principle to obtain equality on `𝓝[≠] z`, then continuity to obtain equality
on `𝓝 z`; only this neighborhood equality may transport `deriv` or `logDeriv`.
The resulting finite pole sum is valid only away from the local divisor
support. Do not claim it on the closed-ball boundary or at a divisor point.
Inside the open ball, use `xiClosedBallDivisor_mem_support_iff` to translate
that owner-local exclusion exactly into `completedRiemannXi z != 0`, then use
`logDeriv_completedRiemannXi_eq_sum_add_cofactor_of_ne_zero`; this is the
public punctured-contour API and does not license evaluation at a zero.

The finite principal part and the regularized kernel are separate contour
owners. Apply rectangle Cauchy only to `xiClosedBallRegularizedKernel`, which
is differentiable on the whole open factorization ball. For a circle around
one selected zero, first prove that its closed disc contains exactly that
support point; integrate that principal term with
`circleIntegral.integral_sub_inv_of_mem_ball`, and prove every other finite
pole term has zero circle integral from
`Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable` on the
closed disc. Do not infer the latter from a support-point slogan: the
closed-ball exclusion is an explicit hypothesis of the principal-part API.

The finite-factor local-residue interface is now closed:
`circleIntegral_xiClosedBallRegularizedKernel_eq_zero_of_closedBall_subset`
uses Cauchy only for the regularized kernel on a closed disc contained in the
open factorization ball, while
`circleIntegral_xiContourKernel_eq_neg_spectralTerm_of_factorization_unique_support`
recombines it with the principal part only after the circle is xi-nonzero and
its closed disc excludes every other finite divisor support point. Callers
must preserve both `closedBall subset factorizationBall` and the explicit
unique-support premise; pairwise separation of a selected source family alone
does not exclude ambient xi zeros not selected by that family.

For a rectangle, use the named `xiRectangleBoundaryIntegral` and require both
the entire closed rectangle to lie in the same open factorization ball and all
four edges to satisfy `xiRectangleBoundaryAvoidsZeros`. The closed result
`xiRectangleBoundaryIntegral_xiContourKernel_eq_principal` removes only the
regularized remainder by Cauchy. The finite-pole rectangle readout is now
closed in `C1XiFiniteRectanglePrincipalPart`: a support-avoiding standard
rectangle reads exactly the factor-owned divisor points strictly inside it,
with the exterior contributions killed through four zero-free strips. The
result is reindexed in `C1XiFiniteRectangleSupportReindex` to the filtered
finite family `xiClosedBallSourceZerosInsideRectangle` and its one-weight
`spectralTerm` sum. Keep that filtered family tied to the same finite factor
owner; do not replace it by an arbitrary selected zero family, a circle, or a
height cutoff without a proved equivalence.

The symmetric critical-strip specialization is closed in
`C1XiFiniteHeightRectangle`: with `T > 0`, factor-ball containment, and
`xiHeightBoundaryAvoidsZeros T`, the filtered same-owner family is exactly
`finiteHeightZeros T`.  The horizontal zero-free condition is essential: it
turns the closed height condition `|Im rho| <= T` into strict rectangle
interiority. `exists_xiHeightBoundaryAvoidsZeros_gt` obtains such a height
above every lower bound by excluding the finite image `rho |-> |Im rho|`, and
`xiZeroFreeHeights` packages choices with unit gaps and `n < T_n`. Do not infer
the condition merely from finite height or from the zero-free vertical sides.
`C1XiQuantitativeHeight` strengthens this selection: for every `B >= 0`,
`exists_quantitative_xiHeightBoundaryAvoidsZeros` chooses `T` in `(B, B + 1)`
with a positive explicit separation from each ordinate in
`finiteHeightZeros (B + 2)`. Its gap is the finite-grid radius
`1 / (4 * (card + 2))`, where `card` counts the visible absolute ordinates.
The closed Jensen bridge
`xiHeightForbiddenOrdinates_dyadic_card_le` bounds that cardinality at
`B = 2^(n + 2)` by `spectralMultiplicityConstant * 3^(n + 1)`: it forgets
repeated ordinates, charges every remaining zero at least one analytic
multiplicity, enlarges the height window monotonically, then applies the
existing dyadic multiplicity estimate. This quantifies the finite grid on
dyadic base heights; its direct consumer
`xiHeightSeparation_dyadic_lower_bound` gives the corresponding reciprocal
lower bound for `xiHeightSeparation`. It supplies no `xi'/xi`, cofactor, or
contour-limit estimate.
The same selected height has an upper horizontal zero-free complex tube:
`xiHeightTubeRadius B = min (xiHeightSeparation B) (1 / 2)` and
`exists_quantitative_xiHeightBoundaryAvoidsZeros_tube` exclude xi zeros from
every ball of that radius centered at `x + T*I`. The half-unit cap keeps a
hypothetical zero in the finite `B + 2` window, while the grid gap excludes
it. This is zero-free geometry only, not a minimum-modulus, cofactor, or
`xi'/xi` bound. Its two-sided consumer
`exists_quantitative_xiHeightBoundaryAvoidsZeros_tubes` transports the same
radius and the same selected `T` to `x - T*I` through `z |-> 1 - z` and
`completedRiemannXi_one_sub`; do not select unrelated upper and lower heights.
`exists_dyadic_quantitative_xiHeightBoundaryAvoidsZeros_tubes` packages the
whole producer at each `n`: it selects `T` in
`(2^(n + 2), 2^(n + 2) + 1)` and supplies both tubes at the explicit radius
`min (1 / (4 * (spectralMultiplicityConstant * 3^(n + 1) + 2))) (1 / 2)`.
This is the correct geometric input for a quantitative analytic estimate, not
that estimate itself. `C1XiQuantitativePrincipalBound` now consumes this
input for the finite pole part only. Its
`exists_dyadic_quantitative_xiHeight_tubes_principal_bound` selects the same
height and bounds the exact origin-centered factor principal sum on both
horizontal lines by
`4 * N_n * (N_n + 2)`, where
`N_n = spectralMultiplicityConstant * 3^(n + 1)`. The proof reindexes the
same factor divisor mass to source multiplicities, bounds it by
`finiteHeightMultiplicity (T + 2) <= N_n`, and uses the zero-free tube to put
every factor pole at distance at least `1 / (4 * (N_n + 2))`. This is an
axiom-clean `O(9^n)` estimate for the finite principal part, not a bound for
`logDeriv` of the zero-free cofactor, the full `xi'/xi`, a horizontal contour
limit, Gate 2 equality, or RH. Keep the principal sum and cofactor as
separate terms of the same factorization owner.
`XiHeightRectangleFactorData` now packages each height with its own cofactor,
the containing ball centered at zero with radius `T + 2`, the zero-free
boundary, and the direct finite spectral readout; its producer is unbounded.
Do not reuse a factor owner across heights or infer any uniform cofactor bound,
horizontal-edge decay, or contour limit from this local data.

The finite-height vertical fold is closed in `C1XiFiniteHeightVerticalFold`:
`criticalStripVerticalBoundaryIntegral_eq_rightLineIntegral` converts the two
oriented zero-free vertical `xiContourKernel` integrals to the one
`verticalIntegrand` integral on `Re(s) = 1`. It uses the functional equation,
the parameter reflection `t |-> -t`, and interval integrability on the compact
height segment. It does not control either horizontal edge, any `xi'/xi`
growth, a common factor owner, or a limit as `T -> infinity`; never promote it
to a rectangle contour limit or fold the reflected weight into a local residue.

`C1XiFiniteHeightRectangleAssembly` combines that fold with the same-owner
finite rectangle readout. Its
`horizontal_add_foldedRightLine_eq_neg_finiteSpectralSum` endpoint states that
the two explicit horizontal edges plus the folded right-line integral equal
the finite spectral sum. This does not compare different height owners: any
limit argument must separately control the horizontal term and the right-line
integral along the selected zero-free sequence.

The compact-log test weight now has axiom-clean uniform fourth-order decay on
the closed critical strip:
`exists_uniform_centeredLaplaceWeight_vertical_quartic_decay_on_criticalStrip`.
`C1XiHorizontalDecay` first proves that each selected zero-free height `T`
has a finite envelope `M`: `xiHeightBoundaryAvoidsZeros T` makes
`negativeXiLogDeriv` continuous on each compact horizontal segment, and
`exists_xiHorizontalLogDerivEnvelope` applies compactness. It then bounds the
horizontal boundary by `2 * M * C / |T / (2*pi)|^4` through
`exists_quartic_horizontalBoundary_bound_of_xiHeightBoundaryAvoidsZeros`;
`XiHeightRectangleFactorData` supplies those height-local hypotheses. This
gives no rate comparing `M` at different heights, no uniform cofactor bound,
and no contour limit. Do not promote the pointwise product estimate to a
uniform `xi'/xi` growth theorem, horizontal-edge decay sequence, Gate 2
equality, or RH claim.

The next conditional layer is separated into three owners. `C1XiHABridge`
defines `GlobalWeightedLogDerivComparison` as an explicit contract and proves
that, when supplied, it reads the H-A1 zero sum back through the same finite
factor owner to `logDeriv g`; it is not a Hadamard/comparison producer.
`C1XiHorizontalLimit` combines the finite pole bound and this cofactor bound,
then proves the horizontal boundary tends to zero under the explicit
`M_n / |T_n/(2*pi)|^4 -> 0` contract. `C1XiFiniteHeightLimit` keeps a separate
`XiHeightRectangleFactorData` owner at every selected height and proves that
the folded right-line limit is `-(2*pi*i) * spectralWeilValue F` once the
horizontal, right-line, and finite-spectral limits are supplied. These are
conditional contour-spine theorems, not the arithmetic explicit formula.

Data-bearing contracts must be ordinary structures, not `structure ... : Prop`:
Lean permits only proof fields in a Prop-valued structure, so a real/complex
constant field would erase the intended projections. Each height-specific
factor owner must remain explicit; never reuse one cofactor across heights.

`xiContourKernel` carries exactly one centered Laplace weight, hence one
spectral term per xi zero. The reflected weight belongs only to
`xiRightLineKernel` after the two vertical sides are folded; adding it to the
local residue double-counts the zero spectrum.

For a finite source-indexed zero family, choose circles only after mapping its
members to their complex coordinates and applying finite `T2` separation.
Each closed-ball radius must be strictly below both its separated-neighborhood
radius and its same-cofactor safe residue radius. Distinct source subtypes do
not by themselves justify geometric disjointness.

For a common contour, choose one finite-factor owner on an outer closed ball,
then require its whole divisor support to avoid the contour boundary. The
principal-part circle integral is the finite sum over every support point in
the enclosed open disc; it is not justified by summing only a preselected
source-zero family unless a separate support-index equivalence has been
proved. A factor-owned finite-family certificate may shrink its inner discs
for `T2` separation, but must retain its own outer cofactor and ambient
support-exclusion fields.

### Diagnostic Gate-3U Branch

The canonical real Gate 3U reduces exactly to a bound on the ordinary trace of
the already-declared `sourceGramResponse` owner (Proof 264 `(AA.1)`/`(AA.32)`,
Lean `CCM24FiniteSGramResponse.lean:563`). Readout chain:

```text
canonicalRealGate3UAt(...)                                    = CC canonicalRealGate3UAt
  <=>  |rawCompletePhysicalHermitianTrace(canonicalFamily)| <= bound       (Proof 798 readout)
  <=>  |Re Tr(sourceGramResponse owner lambda (canonicalFamily))| <= bound (free contract,
       CCM24FiniteSCausalMarkovRawSourceOwnerTrace.lean)
```

**Route-root decision (2026-08-10, docs/proofs/928): canonical deliverable = finite/
decaying-band route-A Gate; infinite-carrier Gate = open analytic bottom.** The
constructible and axiom-clean deliverable is the finite-band Gate `bandTerminalGate`
(`Dev/RouteATailBandBound.lean`): along ANY finite Hilbert band `rho` of the source
carrier, `|Re Tr_b (Tail)| <= card*C0*exp(-B/4)*prod` and the split identity closes
`canonicalRealGate3UAt` on that band (axioms `[propext, Classical.choice, Quot.sound]`,
0 sorry). The ORIGINAL infinite-carrier Gate reduces to ONE load-bearing analytic identity
`(I-P)F = -(I-P)D`, equivalently `sourceActualBandCombinedCoframeLeakage =
sourceActualBandForwardCoframe + sourceSoninCoframeLeakage = 0` on non-empty prime
families; no theorem forces it, numerics (probe 884) oppose it, and the deciding F-term
(exact Sonin intersection R0) is not numerically reachable (AGENT 818/819).
Carrier re-point (Piece 2) is necessary-but-not-sufficient on the infinite carrier
the bound `card * |Support|` diverges because `|Support|` does not decay in `B` (docs/927).
Route work continues on the finite/decaying-band Gate; the infinite identity stays OPEN
and is genuinely new math, not a Lean-assembly leaf.

The missing piece is a compact-root support bound for
`abs (ordinaryTraceAlong sourceBasis (sourceGramResponse ...)).re`, uniform in
the finite family, computed before any absolute value. The statement-planting
contract `CCM24FiniteSCausalMarkovRawRenewalTailBound.lean` now fixes the exact
split/assembly structure: the real trace of the complete physical owner splits
into support + tail (`inverseLowerFactorPhysicalRenewalTrace_eq_support_add_tail`),
the abs gate is bounded by the sum of the two piece bounds
(`inverseLowerFactorPhysicalRenewalTrace_split_bound`), and a uniform tail
trace-decay producer closes the canonical real Gate
(`canonicalRealGate3UAt_of_tailNormBound`, consumed through
`canonicalRealGate3UAt_iff_abs_inverseLowerFactorPhysicalRenewalTrace_le`).
The **whole-tail operator-norm bound** is now closed
(`CCM24FiniteSCausalMarkovRawRenewalTailBound.lean`): assembly through
`tsum_fintype` + `Summable.tsum_prod` + `forwardRenewalIndexEquiv` gives
`‖R^(>B)‖ ≤ C0 · ∑'_{disp>B} twoSidedRawWeight`
(`norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const`), and chaining
the exponential tail decay from `CCM24FiniteSTwoSidedRenewal.lean`
(`finiteEulerTwoSidedRawWeight_tail_decay`; `a_p = e^{-(log p)/2}` makes `w =
exp(-D/2)` universal, on `{D>B}` pointwise `≤ exp(-B/4)·exp(-D/4)`, half-power
sum `∏_p (1+ρ_p)/(1-ρ_p)`, `ρ_p = e^{-(log p)/4} < 1`) gives
`‖R^(>B)‖ ≤ C0 · exp(-B/4) · ∏_p primeTwoSidedQuarterMass`
(`norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const_exp`).

**Apex (2026-08-06, 815):** the whole Proof-717 / Gate-3U front reduces to ONE
open operator identity in TWO orthogonal channels
`OuterCh=(I−R)∘D` + `BandCh=forward+(R−R₀)∘D = 0` on the metric coframe
`D=finiteEulerMetricCoframe=H·J·G⁻¹` (channel split already in-library at
`CCM24FiniteSPhysicalCancellationChannelSplit.lean:84-101`; the `R₀+(R−R₀)`
orthogonal split at `JetOrientation.lean:312`). The `=0` holds only for
`visiblePrimes=[]` (`MarkovRawBase.lean:92`). No non-empty finite prime set is
closed. Numeric outer probe (814) shows `(I−R)∘T†` is a non-decay (0.70/1.30/1.99);
second channel numerically unreachable without the exact `R₀`. Either channel
`=0` (or both) is the entire remaining gate. See `docs/proofs/815`.
Do not split the physical branches before compact support acts; that was a
rejected condition-number argument (785/786/776/777/778/796).

The still-open analytic bottom is the **trace assembly**: feed this tail
operator-norm+decay through an `abs (Re Tr(R^(>B)))` bound via the
trace-class/operator-norm estimate, then add it to the compact support-trace
bound. Across the transported Sonin projection, trace support is not implied by
coefficient support (Proof 807 boundary), so no trace is interchanged anywhere
in the new module. Do not bound the inverse `(K_S* K_S)⁻¹` separately, cycle to
the polar isometry, or split the physical branches before compact support acts;
each is a rejected condition-number argument (see Proofs
785/786/776/777/778/796). `sourceBandGramResponse` is a def equal to
`-sourceGramResponse`; unwinding both negs makes `raw = +Re Tr(sourceGramResponse)
**Route-A finite-band Gate assembly CLOSED (2026-08-07, axiom-clean).** On ANY
finite Hilbert band [rho] of the real route carrier, `bandTerminalGate`
(`Dev/RouteATailBandBound.lean`) bounds the diagonal real trace by band
cardinality times the closed operator-norm bounds (support piece + tail
`rawRenewalTailNormConstant * exp(-B/4) * prod`), assembles the two via
`inverseLowerFactorPhysicalRenewalTrace_split_bound`, and consumes through
`canonicalRealGate3UAt_of_tailNormBound`. Axiom audit = `[propext,
Classical.choice, Quot.sound]` (zero sorry). This is the finite-band (route-A)
form of the Gate; the original infinite-carrier Gate (docs/860 seam) and a
full RH claim stay open.
**Gate-3U 外通道尺度鲁棒（2026-08-08，probe 884）.** 物理 Sonin 尺度 lambda 扫描
（`||(I-R) o D||`，transported-Slepian frame）在 logla ∈ [-2,2] 上稳定 ~0.61-0.62
（回归锚点复现 824 的 0.6242），从不衰减到 0。故无任何物理 lambda 能通过外通道满足
`|leakage|<=1`；外通道负面是尺度鲁棒的（case-bound，非证明非 RH 反论）。仅剩的开放
解析希望是精确相消 `F == -D + J`（docs/872）。直接目标恒等式定位於 docs/872，外通道
扫描证据於 docs/proofs/884_outer_sonin_scale_sweep_*.py / .md。
`.

**Gate-3U 正向上残量已精确定位 = Proof 717 等价（2026-08-04）.** 直接 adjoint
completed-kernel 闭合 (`canonicalRealGate3UAt_of_completedKernelRightEnergy`,
`CCM24FiniteSCanonicalAdjointEnergyGate.lean:375`) 把 Gate 归约到单一 premise
`hright`，其右能量 (`sourcePhysicalCoframeCompletedKernelRightEnergy`, :183) 经
`tsum_normSq_precomp_le` 收紧为 `‖sourcePhysicalCoframeLeakage‖²·(fixed-right-majorant)`。
唯一新量是 `‖physical leakage‖`；`norm_schurMarkovMixedMetricCoframe_le_one` 只封
*mixed* (`suffix·coframe`) 不封 raw（模块自注 SchurMarkovUniformBound.lean:18-20），
biorthogonality `J†∘D=id` 强制 `‖D‖≥1`，而
`norm_sourceActualBandForwardEndpointCoframe_le_one_iff_forward_add_physicalLeakage_eq_zero`
(EndpointContractionGuard.lean:245-252) 把 `‖physical leakage‖≤1` 与 **Proof 717 的
forward+physical cancellation** 等价起来。故此右腿底是 Proof 717，不是 HS 机器可独立封的
新量。See `docs/proofs/gate3u-right-energy-leakage-norm-bottom.md`.

**【2026-08-10，corrected verdict：local CompactLog/A3 positivity CLOSED】**
下列局部正性在 **CompactLog/A3** 载体上已 axiom-clean 闭合
（docs/942，`[propext, Classical.choice, Quot.sound]`, 0 sorry）：
`detector_diagonal_re_nonneg` / `detector_isPositive` / `detector_re_inner_nonneg`
（`A3NonzeroCompactLogGateProbe`），`healthy_strict_positive_diagonal`
（`Wall1HealthyPositive`），以及 `weilStateNonempty` / `concrete_c1_input_nonempty_exists`
（`WeilC1NonEmptyProducer`）给出非空局部 producer。它们证明 `F^dagger F` 的二次型
非负，不证明“对所有 admissible tests 的完整 Weil 显式公式符号”，因此不能标记为
finite-S sign 或 C1 criterion 闭合。Gamma-arg 支路
（`Dev/GammaArg*`，docs/940/941/942）是 **redundant sibling**，只给出
`Re[Gamma(1+i/2)^4]>=0`，非 canonical gate 所需。真正剩余（非 Lean-assembly leaf）：
RH 等价 Source-criterion；Gate-3U infinite carrier 与 Burnol 属于独立支线。

`finite-S` sign, Burnol's identity, and RH stay open.

**【Source model status corrected (2026-08-12)】** The former theorem saying
`SourceWeilFormData concreteTestAlgebra` was empty described the old global
reverse-exact-support model. The S2 per-common refactor replaced that model;
`ConcreteP1SupportProbe.concreteWeilForm` now constructs the exact type
axiom-clean, and `CCM25SourceDataGuards` archives the old negation. Historical
docs 812/813/830/831 and the closure audit are superseded by docs/proofs/835 for
this point.

The remaining source-data root is different:
`normalizedCoreCCM25FinitePrimeArithmeticSourceDataRoot` requires all-pairs
finite-prime certificates plus `scopedArchimedeanContributionBalance`. The
healthy source algebra fixes the former additive-convolution defect, while
`WellFormHealthyRepoint.healthyWeilForm` supplies only per-common `{2}` support.
Neither is an all-pairs/all-prime producer, and neither closes the RH criterion.

`finite-S` sign, Burnol's identity, and RH stay open.

**【850，sign 判定（2026-08-07）】** “847/848 的 canonical Weil≤0 在 concrete 被反证”只在
additive `convolutionSquare` 模型（`weilLocalSum = -polePairing`，`M(conv²g)=2·M g` 线性，
`{0,1/2,1}` 不约束 `±i/2` 处 Mellin，可自由设 -1）下成立，是模型伪问题——该模型连
`NormalizedCC20MellinConvolutionLaw` 都违背（2=1，`CC20YoshidaConstruction:2727`）。真正载体
`CompactLogTest` 已把正半定做成定理：`convolutionSquare(0)=∫‖g‖²≥0`，HS detector `F†F` 二次型
`⟨u,F†Fu⟩=‖Fu‖²≥0`（A3 `detector_diagonal_re_nonneg`）（2026-08-07 已编译通过、axiom-clean：quadratic form 用 mathlib `apply_norm_sq_eq_inner_adjoint_right` 的 .symm 得 re⟨u,detector u⟩=‖Fu‖^2 再 sq_nonneg；同文件 hsGate_selfAdjoint / hsGate_traceClass / nonzero_hsGate_witness 均无 sorry、无项目 axiom，WSL 绿并同步回 Windows）。正确的 sign 重建 = re-type endpoint/
Weil 判定到 CompactLog 载体，不重选 sign。RH 不声明，非 milestone。见 `docs/proofs/850`。

**【859，sign slot 模型墙（2026-08-07，numeric verdict）】** 一号高斯线路的诚实结论：对自然光滑实值测试（Gaussian `e^-t^2`、`e^-t`、sech），临界点 Mellin `∫ t^(i/2-1)f` 在 `t=0` 处 `~t^-1` 发散，`(M g i/2)` 不定义（即 858c 的可积前提 `Integrable (logWeight (i/2) g)` 不成立），故 `Re[(M g i/2)⁴]≥0` 语焉不祥。而在 t=0 消光的测试上 sign **不一致**（`t^a e^-t`：a=.4 → −1.99，.55 → −1.21，.9 → +0.16，1.0 → +0.26）——通用 sign 为假，具体 sign 需选消光 band 测试并做重积分下界（A0/零算子类）。`MellinSignAssembly` 本身带可导前提，无 bug；待办 = 把 `Integrable(logWeight(i/2) g)` 编为定义域谓词。见 `docs/proofs/859`。
   剩余 open：Re[Gamma(a+i/2)^4] >= 0 之相位上界（需具体化 Stirling/积分余项证明），未证。 【888（2026-08-08）：】`|arg Gamma(1+i/2)| <= pi/8` 已在 analytic 层用元素级级数夹逼闭合：arg = -gamma/2 - arctan(1/2) + S，S = Sum_n>=1 [1/(2n) - arctan(1/(2(n+1)))] 落在 `[3.8218e-1, 5.0842e-1]`（80 位 mpmath 已验），故 `Re[Gamma(1+i/2)^4] >= 0`。Lean 内闭合需在本仓库实现 real-analysis Stirling/积分余项 bound（axiom-clean、不依赖外部），除了需构造的真实解析证明（docs/888, 886 rev2）；勿在缺该证明时伪证此 leaf（A0）。 【888-wiring（2026-08-08，WSL-verified）】arch 槽已接 data-bearing `Nonempty HilbertSignArchCorrected.HilbertArchSignDatum` 并整链绿（3193 jobs，#print axioms 全 [propext, Classical.choice, Quot.sound]，无 sorryAx）。 [ArctanCert M1 done(2026-08-08,WSL-verified)] ConnesWeilRH/Dev/ArctanCert.lean gives x/(1+x*x)<=atan x<=x, 2/5<=atan(1/2)<=1/2, 4/17<=atan(1/4)<=1/4, 6/37<=atan(1/6)<=1/6, 8/65<=atan(1/8)<=1/8; 2636 jobs green, axioms [propext Classical.choice Quot.sound], 0 sorry. [SSandwich brick2 (2026-08-08,WSL-green)] ConnesWeilRH/Dev/SSeriesSandwich.lean proves axiom-clean the elementary S-series content: a=p+u split, x-x^3 <= x/(1+x^2) <= atan x, u>=0 p>=0, u<=1/(8(n+2)^3), and the telescope sum_range_p=1/2-1/(2(N+1)).  The cleaner sandwich S=1/2+U gives 1/2 <= S <= 1/2+1/32 (supersedes docs/888 tighter-but-unneeded 0.382..0.509), inside the gate [0.3596,1.14].  brick 2+2b CLOSED (2026-08-08, WSL green, axiom-clean): lift to tsum done, hasSum_p, tsum_u_le_32 (1/32 via c-telescope), S_eq S=1/2+tsum u, S_ge_half 1/2<=S, S_le_half_plus S<=1/2+1/32; axioms [propext, Classical.choice, Quot.sound], 0 sorry. OPEN next: wire gamma/atan(1/2)/pi decimals into |arg Gamma(1+i/2)|<=pi/8 (859/Mellin-cell Stirling residue). RH not claimed.

** PhaseGateSandwich (2026-08-08, WSL green, axiom-clean) **: `ConnesWeilRH/Dev/PhaseGateSandwich.lean` closes the analytic phase shift D = S - gamma/2 - atan(1/2) with -pi/8 < D < pi/8 (D_lower / D_upper / D_abs_lt_pi_eighth), built on SSeriesSandwich.S (1/2 <= S <= 1/2+1/32), mathlib gamma bounds (0.5<gamma<2/3) and pi>3, and ArctanCert.arctan_half. Axioms = [propext, Classical.choice, Quot.sound], 0 sorry. This is the tail of the real-phase gate |arg Gamma(1+I/2)|<=pi/8; the Gamma magnitude identity arg=-gamma/2-atan+S remains an open analytic step. RH not claimed. +937-route-ruling (2026-08-10, docs/937): the naive large-band sign Re[Gamma(a+i/2)^4]>=0 extracted at a=3,5,10 equals -3.7/-2.9e5/-3.4e21. Stirling gives arg Gamma(a+i/2) ~ (1/2) ln a rather than a limit of zero, so Re = |w|^4 cos(4 arg) changes sign infinitely often. The 859 section 6 eventual-positivity conjecture is refuted. The band test t^a e^{-t} cannot be the finite-S sign producer; Step-3 sign stays on CompactLog HS/A3 positivity (`healthy_strict_positive_diagonal`). Only the isolated a=1 leaf has positive sampled value (+0.26).


**Wall-A 1.4 hI leaf — PROVABLE closure via large-plateau bump (2026-08-10, docs/970).** The sole surviving
scalar `arch(witness^2)!=0` (healthy-carrier Wall-A refutation, docs/965/969) now has a Lean-realizable
analytic route that needs NO opaque mathlib-bump analysis: choose a test with a plateau `f=1` on `[-b,b]`
(`ContDiffBump rIn=9/10 rOut=1`), rely on `F(y)>=max(0,2b-y)`, `0<=F<=A`, exact tail `2A ln tanh(R/2)`, and
the near-removable limit `tendsto_archimedeanIntegrand_nhdsGT`; conservative `arch >= +3.34` for `b=0.9`.
Re-point `witnessTest` to that bump, prove the 6 block pieces, assemble into the unchanged
`archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound` sufficiency (docs/965 layers). Lean build remains.
RH NOT claimed.
**`|F'|<=1` near-band structural reduction CLOSED (2026-08-11, Dev/Wall14PlateauFDeriv.lean, axiom-clean).**
The derivative of the explicit bump conv-square now reduces to the folded band: `bumpFderiv x` -> (support) ->
`int_{u in -2..2} bb x` -> `bb_two_band` splits to the two survivors
`int_{u in -1..-9/10} + int_{u in 9/10..1}` of `bb x u := bumpReal(x-u)*bd u`, with `bd := deriv bumpReal`
(pointwise zero on |u|<9/10 and |u|>1, odd `bd_neg`, continuous `bd_continuous`). New Leans: `bd_plateau_zero`,
`bd_outer_zero`, `bumpFderiv_eq_integral`, `bumpFderiv_custom_sub`, `interval_integral_eq_zero_of_Ioo` (integral
0 when zero on the open interval, via NoAtoms `Ioo_ae_eq_Ioc`), `bb_support_subset`, `bb_outer_left_interval` /
**`|F'|<=1` now CLOSED axiom-clean (2026-08-11).** Folded survivor via `u ↦ -u` (`pair_cvt` = `integral_comp_neg`.symm + `bb_neg_piece` + `integral_add`)
**`|bumpA - bumpF y| <= y` CLOSED axiom-clean (2026-08-11).** (two-sided MVT on `[0,y]` from `|bumpF'|<=1`, premise `bumpF 0 = bumpA`).
**hI closure at `bumpPlateauOwner` CLOSED axiom-clean (2026-08-11, Dev/Wall14PlateauBumpHI.lean).** Near <=11/4 (`bump_near_integral_le`), tail <=(4/3)A (`bump_tail_feas`/`bump_tail_integral_le` via exp decay), split, all <=11/4+(4/3)A, `bump_hi` (|Re int_(0,inf) archimedeanIntegrand| < (log(4pi)+gamma)*A), then `bumpArchimedeanTerm_ne_zero` (owner.archimedeanTerm != 0) via `archimedeanTerm_ne_zero_of_lead_pos_and_integral_bound`; C-gate`archCoeff_gt` (29/10<log(4pi)+gamma) intact; audits `[propext, Classical.choice, Quot.sound]`, 0 sorry. RH NOT claimed.
  Also `bumpArchimedeanTerm_re_pos : 0 < Re(bumpPlateauOwner.archimedeanTerm)` and its compact-log lift are axiom-clean. The former C1 four-fold wiring defect is fixed in `Dev/C1HealthyTestSpace.lean`: `weilLocalSum` reads its argument and the generic criterion applies `starConvolution` exactly once. The separate four-fold Wall14 estimates in docs/972/973 remain historical optional analysis, not a C1 requirement. RH NOT claimed.
**Gate-3U 外通道 {2}-族条件性推导（2026-08-11，docs/998）：** 纸面坐标计算提出：
metric coframe `D=(T†T)∘J∘G⁻¹` 在带状 `(logλ−log p, logλ)` 上精确等于 `−p^{−1/2}·x(t+log p)`，故
窗口非零质量应推出 `‖(I−R)∘D‖>0`。但该 strip identity 和 implication 尚无 Lean theorem；
`OuterTwoNonzeroObligation.lean` 只定义 `twoFamily` 与开放 `Prop`
`twoOuterNonzeroObligation`。下一步必须先形式化坐标桥，再构造 Sonin 窗口 witness。
关闭该支线只会否定当前 infinite-carrier Gate-3U cancellation route，不会推出 RH。

**Diagnostic PSP branch (2026-08-12, branch `feat/paley-wiener-psp`, docs/paley_wiener/).** The finite-prime `{2}` diagnostic gate asks for a Sonin-carrier element with nonzero `L2` restriction to the log-2 window. The quotient-invariant contract is `archimedeanSonin_window_mass`, implemented through `soninWindowRestriction`; it replaces the invalid test of a representative function at one point. `Dev/PaleyWindowProbe.lean` closes the ambient radial indicator and its nonzero restricted norm, while `Dev/PaleyHTAssembly.lean` and `Dev/PaleyWindowAnalysis.lean` close the HT and support reductions. These are axiom-clean assembly results, not a carrier witness.

The live analytic statement is the nontriviality of the scattering Toeplitz kernel `archimedeanScatteringToeplitzKernel_nontrivial`: find nonzero `psi : H+` with `P+(m * psi) = 0`, where `m(xi) = Gamma_R(1/2 - i*2*pi*xi) / Gamma_R(1/2 + i*2*pi*xi)`. The prior factorization route `m = Q/P`, `psi = P` is retracted: an a.e.-unimodular `P` is not in `L2(R)`, and a Wiener--Hopf factorization alone does not establish a nonzero Toeplitz kernel. The remaining viable candidate is a genuine prolate/Sonin `L2` eigenfunction, followed by transport to `sourceSoninCarrier` and a proof of nonzero window restriction. Closing this branch would prove nonzero outer leakage for `{2}` and reject the current infinite-carrier Gate-3U cancellation route; it would not prove RH.

## 3. Execution Cadence

Work top-down from the active route consumer. A substantial milestone must
change the route judgment (producer rejected by named guards, consumer switches
to a stronger data-bearing API, old weak path inactive, dependency reaches a
bottom, target proved RH-equivalent or false by counterexample).

Normal rounds attack 10–20 black boxes/branches/dependency layers. Default
build cadence: do **not** `lake build` or audit after each helper; continue to a
substantial milestone, then build/audit when Peter asks or the milestone needs
formal evidence.

Per-change memory record: every non-trivial file change logs one brief line in
`MEMORY.md` under a dated heading, format
`<date> <file> : <what + why, 1-2 lines>`. Keep it to a single line per change,
imperative-free prose, and collapse several related edits into one entry. These
lines live atop `MEMORY.md` and rot out on the next route-milestone merit scan.
Full narrative goes in `docs/proofs/` only when a proof judgment changes. Do not
re-narrate helper-by-helper chronology; log the change, not the journey.

## 3b. Standing Authorization (procedures run without asking)

Unless Peter says otherwise, the agent executes the normal engineering
procedures below **directly, without pausing to ask for permission**. Asking is
reserved for genuine ambiguities with real consequences, not for routine steps.

Granted (no confirmation needed):
- Running WSL-side builds and axiom audits (the established cadence in §3/§8),
  including `flock`-guarded `lake build`, focused `#print axioms`, and the
  numbered verification ladder.
- Editing existing Lean/`.md` files in this repo to advance the active route.
- Adding new `.lean` source modules under `ConnesWeilRH/`.
- Deleting **only** broken/stale artifacts the agent itself just wrote (never
  user or committed work without a separate check).
- Extending or reaping the route's Lean and docs (e.g. a new probe, a new
  seam, a route judgment that updates `MEMORY.md`/`docs/proofs/`).
- Recording the per-change memory line in `MEMORY.md` and updating `AGENTS.MD`
  per the stub rules.
- Treat **new mathematics / new analysis / self-created theory** (anything that
  would otherwise be labeled "open analytic bottom", "needs genuinely new
  analysis", or "not a Lean-assembly leaf") as a **standard attackable target**,
  attack it **directly**, and do **not** stop, ask permission, or wait for
  consent to work on it. Absence of a known theorem is a license to construct
  one, not a blocker to escalate to Peter.

**Broad change authorization (2026-08-09):** the agent may execute **any**
substantial or architecture-level change — new modules, module/package
boundary changes, new claims pushed into the route, new seams, dependency or
carrier changes — **directly, without asking Peter for consent**. Peter will
not be consulted for every large change. "Ask before every architecture or big
change" (project-local instruction overrides the global AGENTS default). Do
not stop to request a green light.

**New mathematics is not a blocker (2026-08-10):** whenever a step requires new
mathematics, new analysis, or a self-created theory rather than assembling
existing theorems, treat it as a standing attackable target and attack it
directly — no reporting to Peter, no asking for consent. Only the hard guards
below (sorry/axiom, RH-only claims, destructive/git/share-infra actions) still
stop the agent. "open analytic bottom" is work to be done in place, not news
that needs to be surfaced first.

**No-stop rule (2026-08-10, Peter):** unless a path has been **conclusively
judged dead** — meaning named guards/definitions actively forbid or contradict
it, a verified counterexample or model-artifact negation exists, or a route
decision (docs/proofs) already rules it unviable — do **not** stop, defer,
gold-plate, or decline it for any reason (missing theorem, "needs new math",
effort, uncertainty, desire to avoid a build, or current-route estimates).
Treat every such path as live work: advance it with the strongest available
reasoning/analysis, and either (a) push it to a closable result, or (b) produce
a precise **conclusive-dead verdict** (named guard / counterexample / docs
ruling) — the only thing that ends work on that path. Waiting-for-consent or
"let me surface this first" is a stop pattern to avoid. The never-granted hard
guards below (sorry/axiom, RH-only claims, destructive/git/share infra) still
override this rule and always require Peter.

Still requires Peter (decision with consequence / irreversibility):
- Any `git commit` / `push` / remote operation (authorized per execution, §14).
- Letting unwanted shared infra, damaging shared files, dropping/adding
  dependencies at the `lean-toolchain`/CI level, or making any public GitHub
  payload (PR/issue/comment).
- ANY step that would non-consensually violate the integrity/RH guards below
  (§6 `sorry`/`axiom`, §11 RH-only claims) — those are never granted.

Rule: when a step is on the "run directly" or broad-authorization list, do it;
do not ask "shall I proceed". If a step falls to the "requires Peter" or the
never-granted list, stop and surface it.

## 4. Single-Agent Rule

Automatic subagents and worker fan-out are paused; use one coordinating agent
unless Peter restores them. Peter may run several independent AI sessions
manually; those sessions own disjoint semantic lanes and must not edit the same
declaration, route consumer, old weak path, or plan document. On session start
and handoff, record owner/cwd/lane/files/build/audit/expected output (handoff
also records status, files, declarations, blockers, next safe action). A later
session that discovers overlap must stop editing and go read-only. Another
session's dirty diff is evidence, not accepted progress — the main worktree plus
an import-facing WSL build and axiom audit decides acceptance.

## 5. File Ownership And Safety

The Windows repository is the only source of truth. Edit, stage, commit, fetch,
merge, and push only from the Windows repository. Sync source **one way**
Windows → WSL ext4 mirror. Never treat a WSL branch/commit/dirty diff/artifact
as authoritative. If WSL experimentation changes source, reproduce the exact
semantic edit on Windows and re-verify the Windows snapshot. Do not copy a whole
WSL worktree back over Windows; port reviewed file-level edits.

## 6. Lean Integrity Standard

Do not introduce or hide gaps through `sorry`, `admit`, `axiom`, opaque
placeholders, unsafe shortcuts, `True`/`Set.univ` producer fields, or stored
conclusions disguised as source data. An axiom-free proof of a weak statement
does not count — the theorem must remove a real active dependency.

Prefer data-bearing owners when several facts must refer to the same object.
Separate propositions can silently mix different witnesses. Required-same-object
pairs include: route test and convolution square; operator and Schwartz kernel;
kernel and Hilbert-Schmidt norm; positive trace and support-square trace; source
Weil-form and evaluation data; canonical atoms and package certificate data;
restricted/global masses with one evaluation object.

## 7. Lean Failure Modes (known hazards, abbreviated)

- **Row-record destructuring**: don't flatten an existential/conjunction whose
  final item is a structure; keep `⟨r, hmatch⟩` structured.
- **Type/Prop universes**: respect the target universe when doing this.
- **Import artifact freshness**: a single-module build can pass while a clean
  dependency build fails; rebuild the owning module's artifacts, don't widen to
  full build unless narrow repair fails.
- **Axiom audits do not detect theorem premises**: `#print axioms` only shows
  what a declaration depends on; it cannot catch a wrong-stated premise.
- Keep guards naming files as rejected-route record for future reference.
- **`R` vs `R0` vs `S` naming landmine (Gate-3U outer/band channels)**: the CONPUTABLE  band projection is `radialSupportProjection` = `R` in docs/815/884/997 but `R0` in docs/995's private naming; the UNREACHABLE archimedean `sourceSoninProjection` is `R0` in docs/815 but `S`/`P` in docs/872/995. `OuterChannel = (I-R_radial).o.D` (docs/815) is the computable one and is what 824/884 measure (~0.62); `(I-Sonin)D=J-D` is a DIFFERENT operator that requires the exact Sonin intersection. Never equate the probe's `(I-R)D` with `(I-Sonin)D`, and always pin which projection a doc's `R`/`S` means.

## 8. WSL Verification

WSL2 is a **verification environment, not a source workspace**. Author/manage
git only in Windows, then copy the Windows snapshot into an ext4 mirror. Never
run Lake through Windows Lean or from `/mnt/c`.

Preferred persistent mirror: `/home/peter/verify/Connes-Weil-RH-Proof`.

Rules:
- Before syncing, run `git rev-parse --show-toplevel`; it must return the mirror
  itself. If it returns `/home/peter` or any other path, **do not sync over the
  directory**; create a fresh ext4 verification directory, seed `.lake` from the
  compatible persistent cache, and copy current sources excluding `.git`/`.lake`.
- **Do not overwrite a dirty mirror.** Record divergence and use an isolated
  ext4 verification directory.
- **Never commit or push from either mirror.** A successful WSL build accepts the
  tested Windows snapshot only; it does not transfer source ownership to WSL.
- All Lake commands take the lock:
  `flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build <target>`,
  **and must run with the mirror as cwd** (`cd /tmp/<mirror> && flock ...`).
  Without the `cd`, lake resolves the Windows project root from the caller's
  cwd and writes olean into the Windows `.lake/build` (observed 2026-08-15:
  a `flock ... lake build` without `cd` compiled Source files from
  a Windows-mounted source path and polluted the Windows build tree; kill, delete the
  same-day `*.olean/*.ilean/*.c/*.hash/*.json` under the Windows
  `.lake/build`, and rerun inside the mirror).
- `.lake/build` metadata is path-sensitive: seed package caches only, then
  recreate the project build directory; verify Lean input/output stay under the
  ext4 mirror. If a dirty mirror makes `git diff HEAD --exit-code` block on
  captured stdout, use `GIT_EXTERNAL_DIFF=true` for that one command only (suppress
  the payload, not the check).
- Verification order: (1) direct Lean check during implementation, (2) smallest
  owning module build, (3) import-facing `#check`/`#print`, (4) focused
  `#print axioms`, (5) route/Dev build after local target passes, (6) full build
  only for a final milestone/explicit request, (7) shortcut scan and
  `git diff --check`.
- Accepted focused axiom output may contain Mathlib foundations
  `[propext, Classical.choice, Quot.sound]`; it must not contain `sorryAx` or new
  project axioms outside explicitly audited roots.
- **Whitespace-linter tail trap**: mathlib's `style.whitespace` linter reports
  `'' starts on column N` on the LAST line of a file that lacks a trailing
  blank line after `end ConnesWeilRH` (the EOF implicit command lands
  off-column). End every `.lean` file with `end ConnesWeilRH` + one blank line.
- **Incrementality lies**: `lake build` re-runs nothing on unchanged files —
  a "no errors/warnings" pass can mean "not rebuilt". Force acceptance
  verification by re-copying (or `touch`) the file on the mirror first.
- **Root-cause discipline**: capture lake output WITHOUT head/tail line caps —
  the FIRST `error:` is the root cause; later `Unknown identifier` cascades
  are noise. Use `grep -B3 -A10 error:` or `grep -E "^error:"`.
- **WSL variable assignment is unreliable** in `wsl.exe -- bash -lc 'X=...; ...'`
  (observed empty expansions); write full paths inline instead of `$VAR`.

## 8b. Cold-VS-Warm Lake Rebuilds (CacheReuse diagnostics)

2026-08-06 lesson: a leaf edit (Probe + Audit `Dev` files) triggered a ~7 hour,
~130-module cold tail that looked like the cache had been thrown away. It had
**not** been. `lake` reuses a hot cache; what it recompiled were modules whose
transitive deps changed since their last `.olean`.

How to tell reuse-vs-rebuild (Windows path `/c/Projects/Connes-Weil-RH-Proof`):
- `find .lake/build/lib/lean/ConnesWeilRH -name "*.olean"` and inspect mtimes.
  Old-but-present files (`2026-06-30`, `2026-07-07`) prove the cache is shared.
  A total discard would remove those too.
- Grep the build log for `^✔ \[n/N\]` progress lines and the `n/N` total; the
  per-module `(NNNs)` is seconds, not a healthy/normal indicator.
- When the build hitches (no new `✔` / `.trace` for 10+ min but `ps` shows lake
  alive), the module is just huge (440s+ is normal here), not stalled.

**Root cause of a wide legal rebuild**: module-mtime deps changed since the last
build. In this repo the usual trigger is `proof717`-series commits touching
`CCM24FiniteSCombinedCoframeGuard` / `CCM24FiniteSEndpointContractionGuard`, which
dirty the downstream chain below them even though the probe files themselves are
late leaves.

**Do NOT** conclude cache-dropped and kill the build. A kill mid-tail burns the
hours already spent and gets no verification. Let a warm, error-free build run to
completion; only abort on a real error or an explicit Peter request.

**Dirty vendored package warning** (`mathlib/plausible/LeanSearchClient has local
changes`) is a red herring for import invalidation: all 40 modified mathlib files
are under `scripts/` (bench/dev tooling), not `.lean` mathlib sources — it does
not dirty the module graph. `plausible`/`LeanSearchClient` were clean. Check the
`git -C .lake/packages/<p> status --porcelain` path before assuming vendor dirt
is the cause.

**Foreground `sleep` SIGTERM trap**: a foreground Bash command that is mostly
`sleep 180`+check can be killed when the tool call exceeds its default 2-min
timeout (exit 143, no log output persists). Prefer: run the build itself as a
blocking command with an explicit long `timeout` (e.g. 400000ms) and `| tail`,
OR run the `wsl.exe -e` build with a high `timeout:` param and wait on the task.
Standalone `sleep N; ...` in the foreground is fragile; a killed parent also
kills a `nohup` child whose log was in the same killed tree.
Use the full path `/c/Windows/System32/wsl.exe` — bare `wsl` may not be on
PATH in this bash.

**Namespace-close pitfall**: adding a new theorem in leaf `Dev` files can leave
an outer `namespace` unclosed at EOF; the error only surfaces on the final build
(`Invalid name after end: Expected <leafnamespace>, but found ...`). Always
confirm each `namespace` opened at the top of a file has a matching `end` after
the last declaration, before launching a long build.

## 8c. Numeric probe hygiene on the metric wall (`docs/proofs/*probe.py`)

2026-08-06 lesson (Gate-3U / Proof-717): probing `(I−R)∘T†∘R` in numpy, and then
the full-metric endpoint, hit two artifacts that must be guarded:

- **Naive `G⁻¹` blows up.** The metric coframe `D = finiteEulerMetricCoframe =
  `H·J·G⁻¹` with `G=H` restricted Gram; pinv of the full-grid `G` yields
  `~3×10¹⁴` because off-carrier columns make it near-singular. `G` must be
  restricted to the carrier rank *before* inversion, else the probe reports
  "unbounded" where the analytic operator restricts to an isometry.
- **The uniform-grid proxy `I−R` annihilates `D` by construction.** The real
  `sourceBandProjection = E − R₀` (E − source Sonin projection) does NOT vanish
  on the metric coframe; the grid's `I−R` does, so `‖(I−R)∘D‖=0` is a proxy bug,
  not a fact. Faithful numeric cancellation tests need the actual R₀ band, which
  a uniform log-t grid does not realize. Off-piste numeric verdicts on this wall
  are therefore only decisive for the outer branch in isolation (`‖(I−R)∘T†∘R‖`),
  not for the three-branch cancellation.

**Lesson**: a numeric probe that "decides" Gate-3U must build the exact operator
products and inverse Gram with the same metric restriction the proof uses; grid
proxies of projections are a trap. Scope any probe result accordingly (branch
in isolation vs full cancellation) in the docstring and in any commit.

**Fidelity guard (proven-identity first)**: before trusting any norm/leak number
on the metric wall, the probe MUST first reproduce a Lean-proven identity. For
the metric coframe that identity is `J†∘D = id` (CoframeResponse:52). In 816 the
small well-conditioned grid reproduces it to `1.0000` exactly; only then are the
`(I−R)∘D` numbers trusted. Doing this separates a real fact (outer channel stays
>1 on 2+ primes) from the two 814 traps (naive `G⁻¹`→3e14, grid `I−R`→0). The
correct ambient Gram is `T†T`, not `T·T†` (T non-normal), and `G`/`G⁻¹` must be
restricted to the carrier span before inverting.

**Probe universality / carrier realism (817)**: a numeric verdict on the metric
wall is only as honest as its carrier. If the escape hypothesis names a
"prolate / exact-Sonin carrier", that must be approximated by the *exact*
band-limited family (Slepian sequences via `scipy.signal.windows.dpss`), not by
smooth bumps (816's Gaussian-sinc). Slepian dpss columns cut to radial support
do **not** make the outer leak `(I−R)∘D` decay: it stays 0.28–0.46 as the band
narrows. Lean grounding: the repo defines the Sonin space only by abstract
star-projections over the spatial half-line (`GlobalLogSoninProjection.lean:153-
163`, `cc20PositiveHalfLine = Set.Ici 0`); there are **no explicit PSWF**
objects. So an "exact prolate" carrier is not a reachable Lean object today —
state that the Slepian probe uses the mathematically-correct object the escape
names, not a repo-owned basis.

**Do not discretize the Sonin projection (818)**: the exact `R0` (Sonin =
`range(radial) ∩ range(HT†·R·HT)`, a *continuous* infinite-dim intersection,
`CCM24HardyTitchmarsh.lean:376-380`) CANNOT be "reached" numerically by von
Neumann alternating projection on a finite grid: `span(R)` and `span(HT†RHT)`
are near-transversal there, so the numerical intersection is rank 0 (or fails
idempotence).  Any second/band-channel number built on that degenerate R0 is a
proxy artifact and must be explicitly discounted (818).  The only channels a
grid probe can trust are ones free of R0/Q0 — i.e. the OUTER channel
`(I−R)∘D`.  To measure the inner (second/band) gate channel you need the actual
archimedean scattering phase `archFactor/conj(archFactor)` and its transported
Sonin/prolate frame — an analytic object, not a grid intersection.

**(819): even the TRUE archimedean phase does not converge.** The real
`m = archFactor/archFactor(−xi)` (Gamma-ratio, `CCM24HardyTitchmarsh:43-45,
74,104-106`) rescues the *dimension* (rank 0→8 at λ=0) but NOT the
*projection*: idempotence never →0 under iteration (profile 3.04e-1…2.55e-1).
Root cause: `range(R)` and `range(HT†R·HT)` are almost-parallel (thin Sonin
band), so alternating projection has no angle lower bound ⇒ no finite-grid
convergence. Do NOT spend time re-cutting R0 by iteration.

**(820): no Sobolev/decay mechanism for the outer channel (route-1 ruling).**
The outer leak of D on a radial probe is FLAT in both metric resolution (x1..x8:
0.278→0.279 / 0.374→0.375 / 0.344→0.396) and radial-cutoff depth (0..-1.5).
No threshold/mollifier scale makes `(I−R)∘D` vanish. A Lean route-1 "Sobolev/
decay" lemma has no numerical basis. Probes on this wall: keep them R0/Q0-free
(outer channel) else they inherit the 818/819 degeneracy; the outer channel is
non-zero at every analytic scale tested (815 simple, 816 band, 817 exact-Slepian,
819 real-phase dim, 820 Sobolev-scale).

**(821) verify a "0" against box growth**: a leak that prints `0.000` for a large
prime (e.g. `{101}`) is usually a box-truncation artifact — `log(101)=4.61` > box
`Lt=4`, the transport shift leaves the grid, `D` acts trivially. Always
re-check by growing `Lt` (small primes are box-stable, so the contrast is real);
the honest `{101}` leak is 0.098, not 0. Route "real primes escape to 0" is a
box trap.

**(822) build the transported-Sonin frame, don't intersect subspaces**: use the
proven `maps_sonin_intersection` (`CCM24FiniteEulerSoninTransport:69-77`): the
correct gate frame is `T·(exact Slepian radial)`. Measuring `(I−R)∘D` on it gave
the LARGEST leak of the whole family (0.38–0.56, log-stable), so the transported
frame is where the outer leaks most, not where it vanishes. Neither 821 (real
arithmetic) nor 822 (transported-Sonin) rescues the outer channel; the live
routes are RH-scale analytic, beyond a finite grid.

**(824) a non-zero leak must be checked for plateau vs decay**: a single-grid
non-zero (like 822's 0.38–0.56 at n=600) only proves "non-zero at one
resolution". To promote it to a real lower bound (or dismiss it as an artifact),
sweep resolution AND interval. On the transported-Sonin frame the outer leak is
resolution-robust: n:200→6000 and L:4→32 keep it pinned at ≈0.62 (single-family
floor ≥0.369), so it PLATEAUS to a positive constant — the 822 leak is real, the
transported-Sonin outer channel cannot vanish. A leak that decays to 0 as
`n,L→∞` would instead be a grid artifact and should be discarded. (See 824.)

## 9. CC20 Operator/Trace Rule

The current normalized core does not implement operator theory
(`positiveTrace`, `traceClass`, `cyclicLegal`, `hilbertSchmidtGate` are not
analytic closure). A valid CC20 trace producer must tie one route test to:
half-density convolution square, theta-smoothed compressed operator, measurable
Schwartz kernel, square-integrability, Hilbert-Schmidt norm, adjoint/composition
kernel, ordinary positive trace, per-move cyclicity witnesses, source-normalized
trace identity with explicit remainder, and the rank/pole corrections that
identity requires.

Keep the regularized Connes trace separate from the ordinary positive trace of
`A*A`; do not write `Tr(A*A)=QW_lambda`. Contract M3 must prove or reject control
of the nonzero remainder `D_S`. Keep the CCM25 support parameter (`lambda_qw`)
and operator cutoff (`Lambda_op`) separate.

`ordinaryTraceAlong` (CC20Concrete/PositiveTrace.lean) is the diagonal-series
trace in a named Hilbert basis; `ordinaryTraceAlong_neg` needs no trace witness.
A legal cyclic trace move requires two Hilbert-Schmidt factors or one
trace-class times one bounded factor; bounded-times-HS alone is not trace-class.

## 10. CCM25 Canonical Owner Rule

Preserve one source owner through source Weil-form, evaluation data, visible
arithmetic, canonical atom normalization, package certificate data, and
restricted/global masses. Do not lower the route by moving among equivalent
wrapper spellings unless a named theorem proves otherwise. Support data plus
visible arithmetic is insufficient when atoms can come from another source;
  package-atom alignment and same-owner transport are mandatory. The old
  globally quantified support model was uninhabited, but S2 replaced it with
  `PerCommonSourceFinitePrimeSupport`; the current concrete
  `SourceWeilFormData` is constructible (`ConcreteP1SupportProbe.concreteWeilForm`).
  Do not reuse the archived pre-S2 emptiness guard against the current type.

## 11. RH-Level Guards

Detector-only coverage is not a lower producer after detector existence is
available. Do not use `SourceRH` or no-off-line source-zero as closure for the
route.

`hilbertSchmidtGate` in the concrete CC20 model (`Test=SchwartzMap`,
`Window=(0,0)` single-point, `window-gated supportValue`) needs BOTH
`suppCarrier f` and `suppCarrier (𝓕 f)` inside the same single-point window;
only the zero test satisfies both, and a `{0}`-only trace model is an empty
producer (AGENTS §6). Do not obtain HS-gate by λ-scaling — `windowCarrier ⊆
lambdaCarrier` is passive containment that does not enlarge the window. A
  non-single-point window architecture with nonzero tests (or a new band-limited
  HS model) is required to resolve that archived A0 lane. It is not the current
  RH theorem root.

**A0 实证收窄 (2026-08-04, Dev/A0WindowGateGuard.lean**): build-reduced the
RUNNING skeleton (`#reduce normalizedCoreSourcePkg.cc20Trace...hilbertSchmidtGate`):
`traceClass g = SupportWindowData.supportInWindow g I`, `cyclicLegal g =
fourierSupportInWindow g I` over `defaultWindow=(0,0)`,
`hilbertSchmidtGate g = traceClass g ∧ cyclicLegal g` (rfl).  The concrete
single-point carrier is now PROVEN (axiom-clean, `Dev/A0WindowGateGuard.lean`):
`pointInConcreteWindow (0,0) x ↔ x.1=0 ∧ x.2=0`.  So the windowed Fourier side
(`cyclicLegal`) forces `(𝓕 g)` to be supported only at coordinate `{0}` — a
Schwartz function with Fourier support ⊆ a point is a (zero) polynomial, so
only the zero test can satisfy the gate over this window: **empty producer,
AGENTS §6**.  Statements were provable all along; the obstruction is the
carrier's zero-only satisfiability.  The skeleton statements
(`trace_class_template_statement`:462, `trace_square_statement`:481,
`ordinary_trace_support_square_statement`:487) are provable for this seed
without any window.  To clear A0 requires a genuinely non-single-point window
with a nonzero test carrying an HS trace-class witness (windowed machine
`windowedBoundaryDetector = A†A`, `CompactLogTest`), i.e. a change of the
carrier/`traceClass`/`cyclicLegal` concrete interpretation — NOT a change of the
`hilbertSchmidtGate` signature.
Both probes (supplier + statement) are axiom-clean.  A1 (Seam B) bridge
(`Dev/A1SeamBOperatorCarrierProbe.lean`) is closed axiom-clean: `0 ≤ Tr(A†A)`
via `ordinaryTrace_positiveComposition_re_nonnegative` and concrete
`HilbertBasis` of `cc20GlobalLogCrossingL2` exist.  The sign chain bottoms out
at `cc20Trace.sourceHilbertSchmidtGate sourceTraceTest`
(UnconditionalSkeleton.lean:5205), a structural gate on one test — so A0's
remaining open item is the existence of a **nonzero** `CompactLogTest` test
satisfying the HS gate, not the downstream positive-trace machinery (that
segment is now fully proved).  A2 (`Dev/A2CompactLogCarrierProbe.lean`) shows
this cannot be a localized carrier swap: `SourceTestAlgebra` forces a full
`legacy : LegacyTestEquiv Test` bijection (Test ⇌ TestFunction), and
`CompactLogTest` is only a compact-support subset of `TestFunction`, so no
`LegacyTestEquiv CompactLogTest` exists.  **Seam B double-block verdict
(2026-08-04)**: BOTH repair conduits die at the concrete carrier layer and are
structurally rejected.  (ii) an operator/trace-class gate cannot be spliced
either: `concreteTestAlgebra` carries `Test := ConcreteTest := TestFunction`
(`AnalyticCoreBase.lean:3094,3119`, `legacy = concreteLegacyTestEquiv`,
encode/decode `= id`), while the HS-sandwich machine
(`windowedBoundaryDetector` = `A†A`, `windowedRootFactor`) lives on the
`CompactLogTest` domain — so the operator gate and the concrete carrier do not
type-match.  **A0 emptiness is the Heisenberg/band-time conflict in the gate's
own semantics, not a `(0,0)`-window artifact**: `supportInWindow g I =
supportCarrier g ⊆ windowCarrier I` (AnalyticCoreBase.lean:1441) and
`fourierSupportInWindow g I = fourierSupportCarrier g ⊆ windowCarrier I` (:1495),
so the single-point-window empty-producer result actually holds for **any bounded
window** (compact time-support ⇒ entire `𝓕g` (Paley–Wiener), an entire function
with compact real-axis Fourier support is zero).  Hence (i) the compact-support
equality carrier shell is **mathematically dead too**, not merely type-blocked.
Resolving A0 needs **the operator/trace-class gate**, whose only movable seam is
`SourceFourierSupportInvolutionGeometryData.fourierSupportInWindow`
(AnalyticCore.lean:678-681, a seed-supplied structure field), reinterpreted as an
`A†A`-operator predicate; it is a genuinely new band-limited operator estimate,
not a signature rewrite.

**Gate-3U 右能量对 inverse-Gram 界（2026-08-04，CCM25Concrete）**: 在
`canonicalRealGate3UAt` 正向上，`canonicalRealGate3UAt_of_completedKernelRightEnergy`
（`CCM24FiniteSCanonicalAdjointEnergyGate.lean:375`）把 Gate 归约到单一 premise
`hright : sourcePhysicalCoframeCompletedKernelRightEnergy ≤ fixedMajorant`。该右能量 =
`∑‖pair.right∘leak(basis i)‖²`，经 `tsum_normSq_precomp_le` 收紧为
`‖leak‖²·(右边 fixed majorant)`；唯一真新量是 `‖finiteEulerMetricCoframe‖`（未归一
Gram 逆，内含 `finiteEulerGramInv`）。scalar seam 给出 `‖metric coframe‖ ≤ 1/
suffixEulerSchurMarkovScalar(canonical)`,且该 scalar ≤1。因 consumer 只就固定
canonical family 求右能量，对**固定 owner** 这是**有限**（可能大于 majorant）的单算子
界, 不族统一 → 需具体计算核对 `1/suffix(canonical)` 因子系数 vs `fixedMajorant`，
    是该历史 Gate-3U lane 的 analytic bottom (condition-number 类, 防发散; 【859b/859c 推进（2026-08-08）：】定义域谓词 `MellinCriticalDefined.criticalDefined g := Integrable (logWeight (I/2) g)` 已建（axiom-clean）；`MellinBandGamma` 证得 band 测试 `t^a e^{-t}` 临界点 Mellin = `Complex.Gamma(a+i/2)` 且非零（`mellin_band_eq_Gamma` / `mellin_band_ne_zero`，axiom-clean）——sign 槽不再是空/零生产者。剩余 open：`Re[Gamma(a+i/2)^4] >= 0` 之相位上界（需 Gamma 渐近/Stirling，mathlib 尚缺），未证。

## 12. Coding And Review

Follow existing namespaces, naming, imports, and theorem layout. Make local,
reversible changes; extract helpers only to remove duplication or preserve a
same-object invariant. For a nontrivial change: state old weak path, add lower
data/API, prove projection/compatibility theorems, rewire the real consumer,
prove the old path is inactive, add negative guards for the removed shortcut.
Comments explain math ownership or a Lean elaboration hazard, not obvious code.

## 13. Documentation

`AGENTS.md` stores stable working rules; `MEMORY.md` stores the current route
snapshot and milestone evidence; plan docs store executable dependency trees.
Keep root docs concise; git history owns superseded chronology. Every plan must
state scope/non-goals, code evidence (file+line), source evidence (URL/manuscript
line), exact data-bearing APIs, consumer rewiring path, rejection guards,
smallest build and focused axiom audit, and success/partial/blocked/rejection
criteria.

## 14. Git And Public Hygiene

Imperative commit subjects ≤72 chars; commit/push only coherent milestones and
only when requested/authorized. Before commit/push:
`git status --short`, `git diff --check`, `git diff --cached --name-status`,
`git diff --cached --check`; inspect staged file ownership; scan for local
paths/private workflow artifacts. Do not stage private workflow files
(`AGENTS.md`, `MEMORY.md`, `RUNBOOK.md`, `HANDOFF.md`, `CONTEXT.md`, `WORKLOG.md`,
`.codex/`) unless the repo owns them. Public GitHub text must not contain Windows
or WSL absolute paths, temp verification dir names, private artifact names, JSON
escapes, or mojibake. After posting/editing public text, read back the rendered

**Default delivery lane (2026-08-08):** all routine work lands on main -- commit on main, push origin main. Do not spin up or keep extra local/remote branches for routine milestones; only branch for a genuinely isolated experiment that must not pollute main, and clean it up when done. When an internal convening asks to consolidate, ff-only into main and push, then remove the now-dead local branch. A GitHub-PR workflow is a separate, explicitly-requested exception, not the norm.
upstream body.

## 15. Handoff Standard

A milestone handoff must answer: result (good/partial/blocked/rejected); RH
status (unconditional or conditional); files changed; declarations added/changed;
active root removed/lowered; old weak path inactive evidence; build target and
result; import-facing audit result; focused axioms; remaining mathematical
bottom; next safe action. Do not claim "proved RH" from a successful build; that
requires plan 016 Phase 8 (`#print axioms unconditional_rh_skeleton` with no
project roots / `sorryAx`) plus the full repository verification gate.

## 16. Stable API / Build Facts

- Whole-line Schwartz convolution owner: `CC20Concrete/GlobalLogConvolution.lean`.
  Accepted build: `lake build ConnesWeilRH.Source.CC20Concrete
  ConnesWeilRH.Dev.GlobalLogConvolution`.
- Crossing owner: `CC20Concrete/GlobalConvolutionCrossing.lean`
  (`C_h† C_h` positive, `C_h† C_h J_b` crossing); keep separate from compact
  `pairData`. Accepted build: `... GlobalConvolutionCrossingAudit`.
- Legal HS cyclicity: `ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint`
  (`Tr_H(A†B)=Tr_G(BA†)`, absolutely summable two-basis expansion).
- Raw Gate 3U readout contract: `CCM24FiniteSCausalMarkovRawSourceOwnerTrace.lean`.
- Physical renewal support split (Proof 807):
  `CCM24FiniteSCausalMarkovRawRenewalSupportSplit.lean` +
  `Dev/CCM24FiniteSCausalMarkovRawRenewalSupportSplitAudit.lean`.
- Tail trace-bound contract (Direction A):
  `CCM24FiniteSCausalMarkovRawRenewalTailBound.lean` +
  `Dev/CCM24FiniteSCausalMarkovRawRenewalTailBoundAudit.lean`; builds clean,
  axioms `[propext, Classical.choice, Quot.sound]`. Holds the support+tail trace
  split, the abs gate = sum of piece bounds, the `canonicalRealGate3UAt_of_tailNormBound`
  closure, **and** the whole-tail operator-norm bound with its exponential decay
  chain (`norm_inverseLowerFactorPhysicalRenewalTailResponse_le_const`,
  `_le_const_exp`, `rawRenewalTailNormConstant`, `rawRenewalTailWeightDoubleSum_reassoc`).
- Brick G (CLOSED 2026-08-14, `Dev/C1XiGlobalZeroSum.lean`): global regularized
  zero sum `Σ (1/(s-ρ)+1/ρ)` — `regularizedZeroSummable` +
  `regularizedZeroTail_norm_shellSum_le` + consumer form
  `regularizedZeroTerm_norm_shell_le`. Route: docs/proofs/1012 §3, 1013.
- H-A0 (CLOSED 2026-08-14, `Dev/C1XiGlobalWeightedZeroSum.lean`):
  `weightedRegularizedZeroSummable` for
  `algebraMap ℝ ℂ (xiMultiplicity rho : Real) * regularizedZeroTerm s rho`.
  Norm-cast fact: `norm_algebraMap` + `Real.norm_eq_abs` — ℂ has NO
  `norm_ofReal` lemma; write the def with `algebraMap` literal.
  Route: docs/proofs/1013 (queue), next H-A1 = analyticity of the weighted
  sum via `Mathlib/Analysis/Calculus/SmoothSeries.lean`
  (`hasDerivAt_tsum_of_isPreconnected`).
- Name ownership for the zero-sum lane (`open` is NOT transitive; every
  consumer imports and `open`s each namespace itself):
  `sourceNontrivialZeroSet`, `dyadicShellIndex`, `lt_two_pow_succ_dyadicShellIndex`
  → `Source/CC20YoshidaNearZeros.lean`; `spectralMultiplicityConstant`,
  `spectralHeightMultiplicity_geometric_bound` → `Dev/C1SpectralSummability.lean`;
  `xiMultiplicity`, `spectralHeightShell(_partition/_finite)` → `Dev/C1SpectralWeil.lean`.



## 17. RH Axiom Guard (from 887 review, updated 2026-08-12)

Read `UnconditionalSkeleton.lean` before classifying its axioms. Two of them are
**RH-equivalent**, NOT "removable on a healthy carrier":
- `normalizedCoreCC20PropositionC1SourceCriterionRoot` (line 1564): its proposition is
  `<-> _root_.RiemannHypothesis` (lines 1555-1559).
- `normalizedSelectedYoshidaDetectorPolePairingNonnegativeCoreRoot` (line 5896): likewise
  `<-> RiemannHypothesis` (lines 5890-5894).
- `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot` is the active root
  of `unconditional_rh_skeleton`; `CC20RouteRealization` proves its proposition
  equivalent to `SourceRH` under the existing detector theorem.

Discharging either **IS proving RH**; you cannot swap in a healthy-carrier datum and claim
the axiom is "removed". Do not list C1-sign or Yoshida polarity under "provable lane".
Full inventory + four-lane classification (R / A / B / C): `docs/proofs/887_rh_axiom_ledger.md`.
`#print axioms` hook for the skeleton output (when built): a module + `#print axioms` on
`rhDefinitionBridgeToMathlibFromTheorems`; expected output still lists the `...Root` axioms.
