# Connes-Weil RH Proof

A Lean 4 project devoted to the Riemann hypothesis and the operator-theoretic
ideas surrounding the Connes-Weil explicit formula.

Toolchain: Lean 4.30.0 and Mathlib 4.30.0.

> **Status as of 2026-08-17.** This repository does not contain an
> unconditional proof of the Riemann hypothesis. The no-argument theorem
> `unconditional_rh_skeleton` consumes explicit project axioms, including
> `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`.
>
> The active constructive route is the C1 same-owner route. Physical Gate 3U is
> a separate diagnostic branch. The residual project-axiom ledger is recorded
> in [`RhOutputAxiomLedger.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/RhOutputAxiomLedger.lean).

## 1. The project

The Riemann hypothesis places every nontrivial zero of the Riemann zeta
function on the critical line:

$$
\zeta(s)=0,\quad 0<\mathrm{Re}(s)<1
\quad\Longrightarrow\quad
\mathrm{Re}(s)=\frac{1}{2}.
$$

This project studies the Connes-Weil route and formalizes its analytic and
operator-theoretic components in Lean 4. The project's final formal target is
Mathlib's
[`_root_.RiemannHypothesis`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LSeries/RiemannZeta.lean).

The route begins with a compactly supported test function g and its
convolution square

$$
F_g=g^{\ast}\ast g.
$$

The Weil explicit formula places zeta zeros, prime powers, and the
archimedean contribution in one distribution. A sufficiently rich family of
tests satisfying

$$
\sum_v W_v(F_g)\le 0
$$

would yield RH through the Weil criterion. The operator program seeks a
positive trace whose expansion equals this Weil expression. The delicate
point is ownership: the test function, convolution square, prime terms,
operator, and trace identity must refer to the same mathematical object.

Lean exposes each analytic obligation. A change of basis needs summability.
A trace cycle needs an absolutely convergent double series. An adjoint needs a
common Hilbert space. A limit needs a domain shared by every term. The current
route therefore tracks one test-space owner through coordinates, convolution,
arithmetic terms, the spectral sum, and the detector criterion.

| Route stage | Current state |
| --- | --- |
| CompactLog to positive-coordinate bridge | Closed |
| Same-owner pole, archimedean, and prime terms | Closed as definition/readback |
| Exact xi-zero index and spectral summability | Closed |
| Gate 2 arithmetic-to-spectral equality | Open |
| Gate 3 positive trace and Gate 4 detectors | Open |
| SourceRH to Mathlib RH | Conditional exit |

### 1.1 Representative lines of attack

1. Connes-Weil semilocal trace formulas

   This line combines a finite set of places S, Sonin spaces, semilocal
   Fourier theory, and the Weil explicit formula on one Hilbert space. The
   repository has formalized the exact prime-power coefficient of a single
   crossing and assembled finitely many crossings into a compact self-adjoint
   operator. This is a closed finite-prime subchain; its same-object
   identification with the load-bearing semilocal metric variation and its
   sign/RH consumer remain open.

2. Yoshida zero detectors

   Yoshida's method constructs Mellin test functions aimed at a prescribed
   zero off the critical line. The repository formalizes support budgets,
   convolution-power tail reduction, finite interpolation, and uniform
   quadratic decay on the critical strip. The existing detector theorem is
   attached to the older normalized test space; rebuilding or transporting the
   detector to the healthy C1 same-owner space remains open.

3. Xi-function zero counting

   The project controls the completed Xi function through Mathlib's theta
   kernel and reduces the zero-summability input to geometric ball bounds in
   the right half-plane. The current C1 layer also proves exact xi-zero index
   completeness, absolute spectral summability for every compact-log test, and
   finite contour/readback bricks. The arithmetic-to-spectral equality is still
   open. Quadratic Mellin decay requires shell growth below 4^n; the full
   Riemann-von Mangoldt asymptotic is stronger than this consumer needs.

4. Nyman-Beurling and Mobius blocks

   The repository investigates projected Mobius dyadic blocks, finite Gram
   matrices, Vasyunin dual systems, and fixed convolution directions. Exact
   computations show that the decisive lower bound restores an inverse-Gram
   non-cancellation problem of RH-level strength. The numerical and structural
   evidence remains useful as a record of this obstruction.

5. Prolate, Sonin, and positivity methods

   This direction studies time-frequency truncation, prolate wave operators,
   Wiener-Hopf crossings, and the CC20 decomposition involving -2I + K.
   Compactness controls the operator ideal; the desired Weil inequality also
   needs spectral sign information. The finite-band Route-A Gate is now an
   axiom-clean diagnostic result. The infinite-carrier Gate-3U cancellation
   identity remains open and is not the active RH root.

6. Operator-level falsification

   The project has tested Xi-nullspace corrections, log-Poisson positive
   operators, Fredholm/Fock Euler-log expansions, higher-order Q filters,
   adelic scalar compensation, and Clifford prime channels. Each rejected
   construction comes with a concrete coefficient, ideal-class, density, or
   domain obstruction. These records are historical route filters; they do not
   replace the current C1 Gate 2--4 work.

## 2. Formalized Lean 4 results

### 2.1 Hilbert-Schmidt trace cycles and nuclear expansions

Let A, B: H -> G satisfy the Hilbert-Schmidt summability conditions on a
Hilbert basis (e_i):

$$
\sum_i \Vert A e_i\Vert^2<\infty,
\qquad
\sum_i \Vert B e_i\Vert^2<\infty.
$$

The project first proves absolute summability of the two-basis coefficient
matrix:

$$
\sum_{i,j}
\left|
\langle A e_i,f_j\rangle
\langle f_j,B e_i\rangle
\right|<\infty.
$$

This estimate justifies the exchange of the two infinite sums and gives the
cross-space trace identity

$$
\mathrm{Tr}_H(A^{\ast}B)=\mathrm{Tr}_G(BA^{\ast}).
$$

Lean declarations:

- [`summable_cyclicCoefficients`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L307)
- [`ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L520)
- [`ordinaryTraceAlong_three_comp_eq_cycle`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L566)

The same module proves the nuclear expansion

$$
\begin{aligned}
A^{\ast}B
&= \sum_j
\mathrm{rankOne}(A^{\ast}f_j,B^{\ast}f_j).
\end{aligned}
$$

The series converges absolutely in the operator norm on continuous linear
maps. Each summand has finite rank, so closedness of the compact-operator
class gives Mathlib's `IsCompactOperator` predicate for A^*B.

- [`summable_norm_traceProductNuclearTerm`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L427)
- [`traceProduct_eq_tsum_nuclearTerm`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L445)
- [`traceProduct_isCompactOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L474)

### 2.2 Exact crossing traces for continuous kernels

For continuous kernels L and R on finite intervals, the project constructs
the corresponding L2 operators, proves Hilbert-Schmidt square summability,
and identifies the diagonal trace of L^*R with the integral of the
inner products of kernel sections:

$$
\begin{aligned}
\mathrm{Tr}(L^{\ast}R)
&= \int \langle L_s,R_s\rangle\,ds.
\end{aligned}
$$

- [`pairData_trace_eq_kernel_inner`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/ContinuousKernelHilbertSchmidt.lean#L316)

Applied to the selected convolution square F, this theorem yields the two
oriented crossing coefficients

$$
\mathrm{Tr}(L^{\ast}R)=bF(b),
\qquad
\mathrm{Tr}(R^{\ast}L)=bF(-b).
$$

- [`pairData_trace_eq_mul_convolutionSquare`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L289)
- [`reversePairData_trace_eq_mul_convolutionSquare_neg`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L320)
- [`eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L390)

For b = m log p, the Euler weight converts these traces into the prime-power
term of the explicit formula:

$$
\begin{aligned}
\frac{bF(b)+bF(-b)}{m\sqrt{p^m}}
&= \frac{\log p}{\sqrt{p^m}}
\left(F(\log p^m)+F(-\log p^m)\right).
\end{aligned}
$$

### 2.3 From compact crossings to the whole line

The compact kernel and the global convolution operator act on different
Hilbert spaces. The project constructs restriction S, zero extension E = S^*,
translation U_b, and the half-line projection P. It then
identifies the boundary translation with

$$
J_b=(I-P)U_bP.
$$

This is a formal crossing bridge. It does not by itself identify the smoothed
whole-line factorization with the semilocal metric variation, prove the global
sign gate, or provide an RH consumer.

The relevant declarations are:

- [`restrictedSetZeroExtension_eq_adjoint_restrict`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L210)
- [`globalBoundaryTranslationProjection_eq_singleCrossingOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1108)
- [`globalLogConvolution_involution_eq_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1788)

A trace cycle leaves a projection E E^* in the product. Lean first proves
that the relevant factor has range inside the range of E. The rectangular
three-factor trace theorem then transports the compact
trace to the whole line:

$$
\begin{aligned}
\mathrm{Tr}(L^{\ast}R)
&= \mathrm{Tr}(C_h C_{h^{\ast}}J_b),
\end{aligned}
$$

$$
\begin{aligned}
\mathrm{Tr}(R^{\ast}L)
&= \mathrm{Tr}(J_b^{\ast}C_h C_{h^{\ast}}).
\end{aligned}
$$

- [`leftKernelAdjoint_range_factorization`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1906)
- [`pairData_trace_eq_namedSourceCrossingProduct`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2072)
- [`reflectedWholeLineLeftFactor_summable`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2609)
- [`pairData_trace_eq_globalConvolutionCrossing`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2775)
- [`reversePairData_trace_eq_globalConvolutionCrossing_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2831)

### 2.4 A compact self-adjoint finite-prime operator

For a prime power (p, m), let T_(p,m) denote the whole-line crossing with
translation length m log p. The project defines

$$
\begin{aligned}
K_{p,m}
&= \frac{1}{m\sqrt{p^m}}
\left(T_{p,m}+T_{p,m}^{\ast}\right)
\end{aligned}
$$

and forms the finite sum before taking a trace:

$$
K_{\mathcal T}=\sum_{(p,m)\in\mathcal T}K_{p,m}.
$$

Every summand acts on the same global L2(R) space and uses the same
`SelectedWeilSquareOwner`. Lean proves four properties:

1. K_T is self-adjoint.
2. K_T is a compact operator in Mathlib's sense.
3. Its diagonal is absolutely summable along the named Hilbert basis.
4. Its ordinary trace equals the finite prime-power sum attached to the same
   convolution square.

$$
\begin{aligned}
\mathrm{Tr}(K_{\mathcal T})
&= \sum_{(p,m)\in\mathcal T}\mathrm{FP}(p^m).
\end{aligned}
$$

Here FP(p^m) denotes the selected finite-prime term.

This closes the finite-prime coefficient and compactness subchain. It is not a
positive-trace theorem: the same-owner identification with the C1 arithmetic
functional, the sign estimate, and the RH consumer remain separate obligations.

- [`eulerLogWeightedGlobalPairTraceOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2970)
- [`eulerLogWeightedGlobalPairTraceOperatorSum_isSelfAdjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3128)
- [`eulerLogWeightedGlobalPairTraceOperatorSum_isCompactOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3152)
- [`ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3187)

### 2.5 A global realization of the CC20 finite-window operator

The regular CC20 kernel begins on a finite Haar window. Let H_lambda denote
the finite-window operator and let E_lambda be zero extension into L2(R). The
project proves the exact conjugation identity

$$
\begin{aligned}
H_\lambda^{\mathrm{global}}
&= E_\lambda H_\lambda E_\lambda^{\ast}.
\end{aligned}
$$

Continuity and symmetry of the finite-window kernel give compactness and
self-adjointness. The conjugation identity carries both properties to the
global Hilbert space used by K_T.

- [`cc20GlobalLogWindowL2Operator_eq_zeroExtension_conjugation`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1629)
- [`isCompactOperator_cc20GlobalLogWindowL2Operator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1639)
- [`cc20GlobalLogWindowL2Operator_isSelfAdjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1649)

### 2.6 A translation quadratic form for prime terms

Let h belong to L2(R) and let U_b be global translation. Lean proves

$$
\langle h,U_bh\rangle=F_h(b).
$$

The project then defines the self-adjoint translation combination

$$
\begin{aligned}
D_{p,m}
&= \frac{\log p}{\sqrt{p^m}}
\left(U_{m\log p}+U_{-m\log p}\right)
\end{aligned}
$$

and obtains the finite-prime quadratic read-off on the same vector:

$$
\langle h,D_{p,m}h\rangle=\mathrm{FP}(p^m).
$$

- [`inner_sourceRootLp_translation_eq_convolutionSquare`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedPrimeTranslationQuadratic.lean#L32)
- [`primePowerTranslationOperator_isSelfAdjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedPrimeTranslationQuadratic.lean#L87)
- [`inner_primePowerTranslationOperator_eq_finitePrimeTerm_pow`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedPrimeTranslationQuadratic.lean#L109)

Translation preserves continuous spectrum, so this module supplies a
quadratic-form read-off. The crossing factorization in Section 2.4 supplies
compactness and an ordinary-trace read-off. The two constructions provide
independent checks on the finite-prime coefficient.

### 2.7 Yoshida support budgets and Xi tails

The Yoshida construction must interpolate prescribed Mellin values while
keeping its values at the remaining zeros small. In logarithmic coordinates,
the project uses the rescaling

$$
f_r(x)=r^{-1}f(x/r),
\qquad
\Phi_{f_r}(s)=\Phi_f(rs).
$$

It then takes an N-fold convolution with r = 1/N. The convolution power
reduces the Mellin tail while its total support stays inside the original
budget. A correction function in a disjoint residual window performs finite
interpolation and retains uniform quadratic decay on the strip.

- [`exists_residualWindow_correction_with_quadratic_decay`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaConvolution.lean#L323)
- [`exists_uniform_mellin_vertical_quadratic_decay`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaTail.lean#L283)
- [`exists_residualWindow_nearbyZero_assembled_distance_bound_lt`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaConvolution.lean#L1352)

For the completed Xi function, the project starts from a theta-kernel moment
bound and proves that right-half-plane ball estimates imply summability over
the source nontrivial zeros. Let N_n count the zeros in the n-th geometric
shell. The following estimate already matches the quadratic Mellin decay:

$$
N_n\le Kc^n,
\qquad c<4.
$$

The geometric ratio c/4 bounds the resulting shell sum.

- [`norm_completedRiemannXi_le_kernelMoment`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20ZetaCounting.lean#L239)
- [`sourceNontrivialZero_summable_of_xi_right_halfplane_ball_bounds`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20ZetaCounting.lean#L603)

The current C1 layer adds the following owner-preserving readbacks and status
boundaries:

| C1 component | State |
| --- | --- |
| Log coordinate to positive route test | Closed |
| Pole, archimedean, and visible prime terms | Closed as definition/readback |
| Absolute spectral summability for every test | Closed |
| Exact completed-xi zero index | Closed |
| Arithmetic value equals spectral value | Open |
| Positive trace and finite-vanishing criterion | Open |
| Yoshida detectors on the healthy owner | Open: rebuild/transport |

The convergence reduction is the exact statement

$$
\begin{aligned}
\operatorname{gate2ExplicitFormula}(F)
&\Longleftrightarrow
\operatorname{C1SameOwnerWeil.psi}(F)
= \operatorname{spectralWeilValue}(F).
\end{aligned}
$$

Finite `c = 1` prime-power readback and the center-2 Gamma_R reciprocal-series
normal form are also closed as local analytic bricks. They do not yet identify
the full archimedean term with `C1SameOwnerWeil.archimedeanTerm`, and they do
not close Gate 2 or RH.

- [`mellin_toPositiveRouteTest_eq_laplaceAt`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1LogPositiveBridge.lean#L127)
- [`spectralSummableProp`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1SpectralSummability.lean#L377)
- [`completedRiemannXi_eq_zero_iff_sourceNontrivialZero`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20ZetaCounting.lean#L396)
- [`normalized_integral_globalPrimePowerIntegrandSum_re_eq_finitePrimeSum`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1XiArithmeticPrimePowerAssembly.lean#L167)
- [`normalized_gammaR_centerTwo_eq_constant_sub_tsum_integrals`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1XiCenterTwoGamma.lean#L1559)

## 3. Current frontier

As of 2026-08-17, the finite-prime crossing chain is a verified infrastructure
subchain, while the active RH frontier is the C1 same-owner route. The C1 route
keeps one `CompactLogTest` owner through the coordinate bridge, the arithmetic
functional, the xi spectral index, and the remaining criterion gates.

| Frontier item | State | Scope |
| --- | --- | --- |
| CompactLog to positive-coordinate bridge | Closed | C1 coordinate ownership |
| Same-owner pole, archimedean, and prime readback | Closed | Definition/readback only |
| Exact xi-zero index and spectral summability | Closed | Every compact-log test |
| Arithmetic equals spectral expression | Open | Gate 2 |
| Positive trace and finite-vanishing criterion | Open | Gate 3, RH-level |
| Yoshida transport to the healthy owner | Open | Gate 4 |
| Finite crossing operator chain | Closed subchain | Coefficient and compactness checks |
| Infinite-carrier Gate-3U cancellation | Open diagnostic branch | Not the active RH root |

The current frontier separates four coupled points.

1. Crossing geometry

   The function-level formula for J_b confines the crossing to the exact
   interval [-b,0]. The source interval of the compact kernel therefore
   agrees with the global half-line projection. This settles the crossing
   geometry, not the later C1 arithmetic-to-spectral identity.

2. Trace-cycle legality

   The formal proof does not use an unrestricted identity of the form
   Tr(ABC) = Tr(BCA). Hilbert-Schmidt square sums,
   absolute summability of the two-basis matrix, and the rectangular
   three-factor theorem justify each cycle.

3. Compactness

   Absolute summability of one basis diagonal does not imply Mathlib's compact
   operator predicate. The rank-one expansion of A^*B converges in
   operator norm and gives compactness of each prime-power crossing and its
   finite sum.

4. A common carrier

   The finite-prime crossing sum and the regular CC20 window operator now act
   on the same global logarithmic Hilbert space. This removes one carrier
   mismatch inside the crossing subchain. It does not identify that subchain
   with the healthy C1 positive-trace owner.

### 3.1 The next mathematical problem

The next load-bearing statement is the C1 Gate 2 equality for one
`CompactLogTest` owner. Spectral convergence is already closed; the remaining
claim is the equality between the complete same-owner arithmetic functional and
the exact xi spectral expression:

$$
\begin{aligned}
\operatorname{gate2ExplicitFormula}(F)
&\Longleftrightarrow
\operatorname{C1SameOwnerWeil.psi}(F)
= \operatorname{spectralWeilValue}(F).
\end{aligned}
$$

The conditional contour spine is already assembled from finite-factor residue,
horizontal-limit, and right-line-limit consumers. Its missing inputs are a
global weighted log-derivative comparison, a quantitative cofactor bound, and
the same-owner arithmetic right-line readback.

| Contour or route brick | State | Limitation |
| --- | --- | --- |
| H-A0 weighted zero-sum convergence | Closed | Axiom-clean local brick |
| H-A1 weighted-sum analyticity | Closed | Does not compare globally with `xi'/xi` |
| H-A2 local removable-pole cancellation | Closed | Local extension only |
| Finite factor, residue, rectangle, and vertical fold | Closed | Finite or conditional consumers |
| H-A3 cofactor growth and H-A4 slope-zero input | Open | Needed for a global comparison |
| Horizontal contour limit | Conditional consumer | Requires a quantitative growth contract |
| Same-owner arithmetic right-line readback | Open | Needed for Gate 2 |
| Positive trace, finite vanishing, and Yoshida transport | Open | The remaining RH-level route |

The finite-prime crossing operator in Section 2.4 remains useful as a
coefficient and compactness check. It is not, by itself, the positive trace
needed by the C1 criterion. The intended implication after Gate 2 is

$$
\text{positive trace}
\Longrightarrow
QW(g,g)\ge 0
\Longrightarrow
\sum_v W_v(F_g)\le 0
\Longrightarrow
\mathrm{RH}.
$$

### 3.2 Representative obstructions

The route boundary is split into current blockers and historical rejected
constructions. The active blockers are the C1 Gate 2 equality, the
positive-trace/finite-vanishing criterion, and detector transport on the healthy
owner.

Current blockers:

| Route | Current gap | Record |
| --- | --- | --- |
| C1 Gate 2 arithmetic readback | The same-owner arithmetic functional is not yet identified with the spectral value | [proof 1006](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1006_gate2_spectral_summability_closure.md) |
| C1 global H-A1 comparison | Local analytic and removable-pole bricks do not provide a uniform cofactor growth bound | [proof 1013](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1013_c1_xi_global_hadamard_brick.md) |
| C1 minimum-modulus route | Raw quotient bounds remain exponential and do not imply the required horizontal decay | [proof 1014](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1014_c1_xi_growth_leg_circle_recon.md) |
| Healthy-owner positive trace and detectors | The positive-trace criterion and Yoshida transport are still open | [proof 1005](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1005_rh_route_after_psp_audit.md) |
| Infinite-carrier Gate-3U | The required physical cancellation identity is open; finite-band decay does not close the infinite carrier | [proof 1005](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1005_rh_route_after_psp_audit.md) |

Historical rejected routes:

| Route | Obstruction | Record |
| --- | --- | --- |
| Compact Xi-nullspace correction | Exponential zero density conflicts with the zero density of a compactly supported entire transform | [proof 110](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/110_xi_null_compact_support_zero_density_death.md) |
| Log-Poisson positive trace | Its positive coefficients do not reproduce the prime scalar in the explicit formula | [proof 111](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/111_log_poisson_positive_trace_readoff_death.md) |
| Compact Wiener-Hopf boundary repair | A compact perturbation cannot cancel the noncompact principal symbol | [proof 118](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/118_wiener_hopf_compact_boundary_cannot_cancel_symbol.md) |
| Fredholm/Fock Euler-log expansion | The required Euler-log derivative misses the target trace ideal | [proof 119](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/119_fredholm_euler_log_traceclass_death.md) |
| Higher-order Q filters | Differential weights strengthen the cusp principal part without producing the required sign | [proof 120](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/120_higher_q_filter_unbounded_cusp_rejection.md) |
| Adelic scalar compensation | Product-formula coefficients do not match the one-prime read-off | [proof 121](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/121_adelic_product_formula_scalar_mismatch.md) |
| Clifford prime channels | The Gram construction retains the original sign problem and adds channel cost | [proof 122](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/122_clifford_prime_channel_gram_cost.md) |

These records keep the route boundary explicit. A successful next construction
must preserve one C1 owner, prove the arithmetic-to-spectral equality, and then
establish the positive trace and detector criterion on that same owner.

## 4. Sources

The formal interfaces draw on the following papers.

1. Alain Connes and Caterina Consani, *Weil positivity and Trace formula: the
   archimedean place*,
   [arXiv:2006.13771](https://arxiv.org/abs/2006.13771).

   This paper supplies the archimedean trace formula, the Sonin/prolate
   framework, and the CC20 Weil criterion.

2. Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta Zeros and Prolate
   Wave Operators: Semilocal Adelic Operators*,
   [arXiv:2310.18423](https://arxiv.org/abs/2310.18423).

   This paper develops the semilocal space, modulus map, Fourier compatibility,
   and Sonin transport used to locate the finite-S operator problem.

3. Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta Spectral
   Triples*, [arXiv:2511.22755](https://arxiv.org/abs/2511.22755).

   This paper studies self-adjoint approximants and spectral triples. Its open
   convergence questions isolate further prolate spectral estimates.

4. The q-series/Jacobi model,
   [arXiv:2403.01247](https://arxiv.org/abs/2403.01247), and the finite
   Guinand-Weil dictionary,
   [arXiv:2607.02828](https://arxiv.org/abs/2607.02828).

   These works provide Jacobi matrices, finite-dimensional dictionaries, and
   tail orders. In this repository they document the finite-S and diagnostic
   branches; the active remaining problem is the C1 same-owner arithmetic,
   spectral, and positivity chain.

The term-by-term alignment between Burnol's compact-test explicit formula and
the repository's `SelectedWeilFormulaOwner` appears in
[proof 109](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/109_burnol_selected_weil_formula_alignment.md).

The current route ledger and status records are maintained in
[proof 1005](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1005_rh_route_after_psp_audit.md),
[proof 1006](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1006_gate2_spectral_summability_closure.md),
[proof 1007](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1007_xi_zero_index_completeness.md),
and [proof 1015](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1015_c1_xi_conditional_contour_spine.md).

## 5. Repository map

```text
ConnesWeilRH/
  Basic.lean                         Mathlib RH target and basic interfaces
  Source/
    CC20Concrete/                    continuous kernels, traces, global windows
    CCM25Concrete/                   selected squares, crossings, prime terms
    CC20Yoshida*.lean                Mellin detectors and support budgets
    CC20ZetaCounting.lean            Xi-kernel bounds and zero summability
  Route/                             conditional route composition
  Dev/                               premise audit and research boundary
    C1*.lean                         same-owner bridges, Xi contours, readbacks,
                                      and import-facing audits

docs/proofs/                         derivations, obstructions, milestones
docs/audits/                         source, quantifier, and axiom audits
formalization/                       interface and formalization notes
```

The root import is
[`ConnesWeilRH.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH.lean).
The conditional route composition is in
[`RouteTheorem.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Route/RouteTheorem.lean).
The RH-equivalence bridge is
[`normalizedRouteBackedCC20SquareRestrictedDetectorCriterionCoverage_iff_standardSourceRH`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Route/CC20RouteRealization.lean#L20270).
The premise audit for the no-argument root lives in
[`unconditional_rh_skeleton`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/UnconditionalSkeleton.lean#L8049).

Run `lake build ConnesWeilRH` for the root build. Import-facing audit files use
`#check`, `#print`, and `#print axioms` to inspect both theorem types and axiom
dependencies. A final theorem audit must also inspect explicit parameters,
implicit parameters, and typeclass parameters because an axiom report does not
detect ordinary premises.

## 6. License

Apache License 2.0. See
[LICENSE](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/LICENSE).
