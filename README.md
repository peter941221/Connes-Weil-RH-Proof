# Connes-Weil RH Formalization

<p align="center">
  <a href="#status-dashboard"><img alt="Research status: RH unproved" src="https://img.shields.io/badge/status-RH%20unproved-b42318?style=flat-square"></a>
  <a href="https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/lean-toolchain"><img alt="Lean 4.30.0" src="https://img.shields.io/badge/Lean-4.30.0-5c7cfa?style=flat-square"></a>
  <a href="https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/lakefile.toml#L15"><img alt="Mathlib 4.30.0" src="https://img.shields.io/badge/Mathlib-4.30.0-0f766e?style=flat-square"></a>
</p>

A Lean 4 proof-assistant formalization of the Connes-Weil approach to the
Riemann hypothesis. The repository separates checked Lean declarations from
conditional route interfaces and numerical reconnaissance, with evidence links
for each current claim.

## Status dashboard

> [!IMPORTANT]
> **Research status at [commit `ff83f7a`](https://github.com/peter941221/Connes-Weil-RH-Proof/commit/ff83f7a): 2026-09-01.**
> This repository does not contain an unconditional proof of
> the Riemann hypothesis. The output bridge
> [`rhDefinitionBridgeToMathlibFromTheorems`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/RhOutputAxiomLedger.lean#L24)
> still consumes five project axioms. The
> [`RhOutputAxiomLedger.lean`](ConnesWeilRH/Dev/RhOutputAxiomLedger.lean)
> audit names those axioms.

| Item | Status | Primary evidence |
| :-- | :-- | :-- |
| Current route map | Architecture, binding route ruling, and endpoint boundary | [route-map index](docs/map/README.md) |
| Mathematical mainline | B5-shaped, detector-specific route on the healthy `CompactLog` owner | [route ruling 1076](docs/map/003_b1_b5_minimal_exit_route_selection.md) |
| Output bridge | Five explicit project axioms remain | [`RhOutputAxiomLedger.lean`](ConnesWeilRH/Dev/RhOutputAxiomLedger.lean) |
| C2 detector pinning | Closed with five axiom-clean declarations | [proof 1080](docs/proofs/1080_c2_detector_pinning_exit.md) |
| C3 semi-local positivity | Root-window kernel (a) adjudicated numerically NEGATIVE (top of arch on the triple-vanishing subspace plateaus at -0.853, no positive direction at any resolution); carrier and transport routes closed, obligation re-anchored to certificate extension at the detector's orbit window | [proof 1087](docs/proofs/1087_c3_root_window_spectral_verdict.md), [proof 1081](docs/proofs/1081_c3_root_support_exit.md) |

### Lean 4 audit × Connes-Weil identity

Read the left panel as checked Lean implications with named premises. The
right panel states the Connes-Weil identity that joins zero, trivial, and
place terms. Write `RootGate` for
[`rootSupportedHealthyDetectorGate`](ConnesWeilRH/Dev/C1HealthyDetectorRootSupportExit.lean),
and `RootGate_right` for that gate over every right representative.

$$
\boxed{
  \begin{gathered}
  \text{LEAN 4 AUDIT} \\
  \mathrm{C2}\land h_{\mathrm{sign}}
    \xrightarrow{\ \mathrm{Lean}\,4\ }\mathrm{RootGate} \\
  \mathrm{RootGate}_{\mathrm{right}}\land h_{\mathrm{endpoint}}
    \xrightarrow{\ \mathrm{Lean}\,4\ }\mathrm{SourceRH} \\
  [\mathrm{propext},\mathrm{Classical.choice},\mathrm{Quot.sound}]
  \end{gathered}
}
\qquad
\boxed{
  \begin{gathered}
  \text{CONNES-WEIL IDENTITY} \\
  \sum_{\rho}\widetilde f(\rho)
    =\widetilde f(1)+\widetilde f(0)-\sum_v W_v(f) \\
  f=g\ast g^\sharp,\qquad
  \widetilde f\left(\frac12+it\right)
    =\left|\widetilde g\left(\frac12+it\right)\right|^2
  \end{gathered}
}
$$

Here `h_sign` is the strict archimedean inequality and `h_endpoint` is the
root-supported endpoint certificate. They remain open inputs, as do the five
project axioms in the output bridge. The right panel follows
[proof 1070](docs/proofs/1070_weil_q_hunting_level1.md).

### Active proof chain

```text
  ROOT-window CC20 local base
               |
               v
  C2: selected CompactLog detector                  [complete]
               |
               v
  C3: root-supported gate / RH-exit wiring           [formalized]
      root-window kernel (a) adjudicated negative    [1087 scan]
      re-anchored: orbit-window certificate growth   [open]
               |
               v
  SourceRH -> Mathlib RiemannHypothesis              [target]
```

For a pinned detector, write `F_g` for `g.convolutionSquare`. The RH exit
applies two incompatible sign statements to the same test:

$$
\underbrace{0\le q_w(g)}_{\text{CC20 endpoint certificate}}
\qquad\land\qquad
\underbrace{
  q_w(g)=\mathrm{spectralWeilValue}(F_g)<0
}_{\text{root-supported detector}}
\qquad\Longrightarrow\qquad
\bot.
$$

The Lean composition
[`sourceRH_of_rootSupportedGate_rightRep_and_endpointCertificates`](ConnesWeilRH/Dev/C1HealthyDetectorRootSupportExit.lean)
proves this same-owner contradiction.

The active mathematical interface is

$$
\underbrace{
  \begin{aligned}
  \mathrm{supp}(g)
    &\subseteq \left[-\frac{\log 2}{2},\frac{\log 2}{2}\right], \\
  \mathrm{laplaceAt}(g,\rho)&=-1, \qquad
  \mathrm{globalPrimeIndexSet}(F_g)=\varnothing
  \end{aligned}
}_{\text{C2: closed}}
\quad
\xrightarrow{\quad\text{C3 proof obligation}\quad}
\quad
\underbrace{
  0<\mathrm{archimedeanTerm}(F_g)
}_{\text{C3: open}}.
$$

C2 supplies the support, detector normalization, and visible-prime data. C3
requires the strict right-hand inequality on the same healthy owner; the
[`selectedDetectorArchimedeanGate`](ConnesWeilRH/Dev/C1HealthyDetectorPinning.lean#L113)
is its exact Lean statement. Record 1087 measured the whole root-window
feasible set of this inequality spectrally - the top of the archimedean form
on the triple-vanishing subspace plateaus at about -0.85 per unit mass, so
the displayed window admits no positive direction for any detector (and,
through the explicit-formula identity, producing one would be an off-line
zero witness, not a step toward RH). The open C3 obligation therefore moves
outward along the radius: extend the ROOT-local endpoint certificate to the
detector's orbit support with its finite visible-prime set, which the frozen
consumer wording already authorizes. See
[proof 1087](docs/proofs/1087_c3_root_window_spectral_verdict.md).

The universal B1 all-test campaign and the normalized additive B5 socket are
frozen. The active route seeks detector-specific positivity on the same healthy
owner.

### Verification protocol

The project promotes claimed formal results through this chain:

```text
published claim -> independent anchor -> exact or interval certificate
               -> Lean declaration + focused axiom audit -> build-log review
```

Floating-point calculations propose candidates. Lean declarations and their
axiom audits support formal claims. See
[the full mechanism view](RH_ROUTE_MECHANISM.md) for the complete protocol.

### Reading guide

- [The project](#1-the-project) introduces the mathematical target and route.
- [Formalized Lean 4 results](#2-formalized-lean-4-results) lists the proved
  infrastructure.
- [Current frontier](#3-current-frontier) states the remaining proof
  obligations and frozen alternatives.

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
| :-- | :-- |
| Same-owner analytic and arithmetic readback | Closed as axiom-clean infrastructure |
| Gate 2 arithmetic-to-spectral equality | Closed by the center-2 contour assembly |
| ROOT-window CC20 positivity | Shared local base; it is not an RH exit |
| C2 selected `CompactLog` detector and visible-prime set | Closed |
| C3 detector-specific semi-local positivity | Root-window branch numerically adjudicated negative ([1087](docs/proofs/1087_c3_root_window_spectral_verdict.md)); obligation re-anchored to orbit-window certificate extension |
| Universal B1 all-test globalization | Frozen |
| `SourceRH` to Mathlib RH | Conditional target after the healthy-owner exit |

### 1.1 Frozen historical lines of attack

The following routes are retained for provenance only. They are not an active
work queue; the dashboard and Section 3 summarize the healthy-`CompactLog`
mainline. [`RH_MAINLINE_FREEZE.md`](RH_MAINLINE_FREEZE.md) names the allowed
RH consumers.

1. Connes-Weil semilocal trace formulas

   This line combines a finite set of places S, Sonin spaces, semilocal
   Fourier theory, and the Weil explicit formula on one Hilbert space. The
   repository has formalized the exact prime-power coefficient of a single
   crossing and assembled finitely many crossings into a compact self-adjoint
   operator. This is a closed finite-prime subchain; its same-object
   identification with the load-bearing semilocal metric variation and its
   sign/RH consumer remain open.

   The paper-facing calculation brings the zero, trivial, and place terms into
   one explicit formula, documented in
   [proof 1070](docs/proofs/1070_weil_q_hunting_level1.md):

$$
\sum_{\rho}\widetilde f(\rho)
  = \widetilde f(1)+\widetilde f(0)-\sum_v W_v(f).
$$

2. Yoshida zero detectors (older normalized branch)

   Yoshida's method constructs Mellin test functions aimed at a prescribed
   zero off the critical line. The repository formalizes support budgets,
   convolution-power tail reduction, finite interpolation, translation/support
   transport, and uniform quadratic decay on the critical strip. The healthy
   C1 layer now has finite-node interpolation, translation/support transport,
   and a right-oriented detector construction with a conditional RH exit on
   the same owner. The older normalized detector route is retained only for
   provenance. The active route now carries its C2-to-C3 handoff on the
   healthy `CompactLog` owner.

   Its convolution square uses the Mellin identity. The critical-line term is
   therefore a square modulus; [proof 1070](docs/proofs/1070_weil_q_hunting_level1.md)
   derives this identity rather than assuming a shifted product.

$$
f=g\ast g^\sharp,
\qquad
\widetilde f(s)=\widetilde g(s)\widetilde g(1-s),
\qquad
\widetilde f\left(\frac12+it\right)
  =\left|\widetilde g\left(\frac12+it\right)\right|^2.
$$

3. Xi-function zero counting

   The project controls the completed Xi function through Mathlib's theta
   kernel and reduces the zero-summability input to geometric ball bounds in
   the right half-plane. The current C1 layer also proves exact xi-zero index
   completeness, absolute spectral summability for every compact-log test,
   finite contour/readback bricks, and the center-2 same-owner
   arithmetic-to-spectral equality. These results remain shared infrastructure
   for the healthy detector-specific route. The universal W4b campaign is
   frozen; C3 semi-local positivity is the active unresolved obligation.
   Quadratic Mellin decay requires shell growth below 4^n; the full
   Riemann-von Mangoldt asymptotic is stronger than this consumer needs.

4. Nyman-Beurling and Mobius blocks

   The repository investigates projected Mobius dyadic blocks, finite Gram
   matrices, Vasyunin dual systems, and fixed convolution directions. Exact
   computations show that the decisive lower bound restores an inverse-Gram
   non-cancellation problem of RH-level strength. The numerical and structural
   evidence remains useful as a record of this obstruction.

   The finite block exposes the obstruction through its Schur complement. The
   explicit Mobius coefficients do not remove `G_N^{-1}`; see
   [proof 020](docs/proofs/020_nyman_mobius_m4_first_verdict.md).

$$
\Vert w_N\Vert^2
  = a_N^{\mathsf T}
\left(B_N-C_N^{\mathsf T}G_N^{-1}C_N\right)a_N.
$$

5. Prolate, Sonin, and positivity methods

   This direction studies time-frequency truncation, prolate wave operators,
   Wiener-Hopf crossings, and the CC20 decomposition involving -2I + K.
   Compactness controls the operator ideal; the desired Weil inequality also
   needs spectral sign information. The finite-band Route-A Gate is now an
   axiom-clean diagnostic result. The infinite-carrier Gate-3U cancellation
   identity remains open and is not the active RH root.

   The Bessel bound marks the parameter boundary. The lower bound is rigorous
   but does not reach the paper scale. The
   paper-scale certificate needs an exceptional direction, a complement bound,
   and a rank-one repair; [proof 1050](docs/map/002_one_shot_rh_route_verdict.md)
   records that distinction.

$$
q_T(\xi)\ge(1-\lambda)\Vert\xi\Vert^2
\quad(\lambda<1),
\qquad
\lambda_{\mathrm{paper}}\simeq1.05158>1.
$$

6. Operator-level falsification

   The project has tested Xi-nullspace corrections, log-Poisson positive
   operators, Fredholm/Fock Euler-log expansions, higher-order Q filters,
   adelic scalar compensation, and Clifford prime channels. Each rejected
   construction comes with a concrete coefficient, ideal-class, density, or
   domain obstruction. These records are historical route filters; they do not
   replace the active healthy detector-specific mainline.

## 2. Formalized Lean 4 results

### 2.1 Hilbert-Schmidt trace cycles and nuclear expansions

Let A, B: H -> G satisfy the Hilbert-Schmidt summability conditions on a
Hilbert basis (e_i):

$$
\boxed{
  \begin{aligned}
  &\text{HILBERT-SCHMIDT TRACE CYCLE} \\
  &\sum_i \Vert A e_i\Vert^2 < \infty,\qquad
    \sum_i \Vert B e_i\Vert^2 < \infty \\
  &\Longrightarrow\quad
    \sum_{i,j}
    \left|
      \langle A e_i,f_j\rangle
      \langle f_j,B e_i\rangle
    \right| < \infty \\
  &\Longrightarrow\quad
    \mathrm{Tr}_H(A^{\ast}B)
    = \mathrm{Tr}_G(BA^{\ast})
  \end{aligned}
}
$$

The middle implication permits exchange of the two infinite sums; the last
line is the cross-space trace identity.

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
| Arithmetic value equals spectral value | Closed (center-2 contour) |
| Stage-3 positive-trace order consumer | Closed (conditional on `0 <= qw g`) |
| CC20 Archimedean log readback and rank-one error kill | Closed as dictionary/readback |
| W4b positivity on proper support classes | Closed historical local results |
| Universal W4b all-test globalization | Frozen |
| C2 pinned healthy detector | Closed |
| C3 detector-specific semi-local positivity | Open; root-window kernel (a) numerically negative definite ([1087](docs/proofs/1087_c3_root_window_spectral_verdict.md)), re-anchored outward |

The convergence reduction is the exact statement

$$
\begin{aligned}
\mathrm{gate2ExplicitFormula}(F)
&\Longleftrightarrow
\mathrm{C1SameOwnerWeil.psi}(F)
= \mathrm{spectralWeilValue}(F).
\end{aligned}
$$

Finite `c = 1` prime-power readback and the center-2 Gamma_R reciprocal-series
normal form are closed as local analytic bricks. The center-2 contour assembly
now proves the same-owner arithmetic-to-spectral equality as an axiom-clean
Lean theorem, closing Gate 2. The universal W4b campaign is frozen; the active
unresolved obligation is C3 detector-specific semi-local positivity, now
targeted at an expanded-radius (orbit-window) certificate: the root-window
branch of its kernel (a) was numerically adjudicated negative definite by
[proof 1087](docs/proofs/1087_c3_root_window_spectral_verdict.md). RH is not
claimed.

- [`centerTwo_arithmetic_eq_spectral`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L232)
- [`gate2ExplicitFormula_centerTwo`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L240)
- [`mellin_toPositiveRouteTest_eq_laplaceAt`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1LogPositiveBridge.lean#L127)
- [`spectralSummableProp`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1SpectralSummability.lean#L377)
- [`completedRiemannXi_eq_zero_iff_sourceNontrivialZero`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20ZetaCounting.lean#L396)
- [`normalized_integral_globalPrimePowerIntegrandSum_re_eq_finitePrimeSum`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1XiArithmeticPrimePowerAssembly.lean#L167)
- [`normalized_gammaR_centerTwo_eq_constant_sub_tsum_integrals`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1XiCenterTwoGamma.lean#L1559)
- [`cc20WRLog_eq_archimedeanTerm`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L39)
- [`cc20WInfinityLog_eq_neg_archimedeanTerm`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L47)
- [`CC20EndpointTraceCertificate`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L94)
- [`qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L133)
- [`cc20LemmaFirstForm_nonneg_iff`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20FiniteDimensional.lean#L158)
- [`cc20LemmaFirstForm_ge_epsilon`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20FiniteDimensional.lean#L189)
- [`cc20EndpointCoefficient_band`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20EndpointCoefficient.lean#L27)
- [`CC20EndpointOperatorTraceData`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20EndpointCertificateData.lean#L67)
- [`qw_nonneg_of_cc20EndpointOperatorTraceData`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20EndpointCertificateData.lean#L103)
- [`zeroTraceCertificate_of_nonnegative_wInfinity`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20EndpointCertificateData.lean#L161)
- [`posDef_of_ldlt`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1YoshidaLdlCertificate.lean#L101)
- [`witness_posDef`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1YoshidaLdlCertificate.lean#L181)
- [`cc20GapCoercivity_transfer`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20OperatorGap.lean#L64)
- [`cc20NegativeForm_le_rankOne`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20OperatorGap.lean#L79)
- [`qw_nonneg_of_vanishesOn_cc20Triple_of_boundary_square_support`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1SpectralW4bBoundary.lean#L329)
- [`qw_nonneg_of_vanishesOn_cc20Triple_of_refined_boundary_square_support`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1SpectralW4bBoundary.lean#L780)
- [`qw_nonneg_of_vanishesOn_cc20Triple_of_third_boundary_square_support`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1SpectralW4bBoundary.lean#L869)
- [`healthy_sourceRH_of_global_spectral_nonneg`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean#L554)

## 3. Current frontier

At [commit `9f9507b`](https://github.com/peter941221/Connes-Weil-RH-Proof/commit/9f9507b),
the project pursues the detector-specific, B5-shaped route selected in
[proof 1076](docs/map/003_b1_b5_minimal_exit_route_selection.md). C2 is
complete: Lean constructs a root-window detector with an explicit finite
visible-prime set. C3 remains open.

| Chain element | State | Scope |
| :-- | :-- | :-- |
| Same-owner analytic and arithmetic readback | Closed | Axiom-clean infrastructure |
| Gate 2 arithmetic-to-spectral equality | Closed | Center-2 contour assembly |
| Paper-scale ROOT-window CC20 base | Open | Shared local base, not an RH exit |
| C2 selected detector and visible-prime set | Closed | Root-window support and an empty visible-prime set |
| C3 detector-specific semi-local positivity | Open (root window closed) | One strict archimedean sign inequality; the root-window feasible set is numerically empty ([1087](docs/proofs/1087_c3_root_window_spectral_verdict.md)) - the remaining shape is the same inequality at the detector's orbit window |
| Detector certificate to `SourceRH` | Open | Healthy-owner contradiction theorem |
| Universal B1 all-test globalization | Frozen | It would require positivity for every compactly supported test |
| Normalized B5 coverage socket | Audit-only | Its additive convolution fails the Mellin product law |

The finite-prime crossing operator and the Gate 2 calculation remain verified
infrastructure. They do not establish the C3 positivity statement.

### 3.1 The Connes–Weil trace balance

On the healthy owner, the closed center-2 assembly identifies the same-owner
Weil functional with the zero-spectral value. This is the repository's formal
trace balance behind the [Connes–Consani trace-formula paper](https://arxiv.org/abs/2006.13771):

$$
\boxed{
  \begin{aligned}
  &\text{CONNES-WEIL TRACE BALANCE} \\
  \Psi(F)
    &= \mathrm{poleTerm}(F) - \mathrm{archimedeanTerm}(F) - \mathrm{finitePrimeSum}(F) \\
    &= \mathrm{spectralWeilValue}(F) \\
  \mathrm{poleTerm}(F_g)
    &= \mathrm{finitePrimeSum}(F_g)=0 \\
  &\Longrightarrow\quad
    \mathrm{spectralWeilValue}(F_g)
      = -\mathrm{archimedeanTerm}(F_g)
  \end{aligned}
}
$$

The selected triple-vanishing, prime-free square
`F_g = g.convolutionSquare` has zero pole and finite-prime terms. C3 must
establish the remaining strict archimedean sign. The three equalities come from
[`psi_eq_components`](ConnesWeilRH/Dev/C1SameOwnerWeil.lean#L199),
[`centerTwo_arithmetic_eq_spectral`](ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L232),
and
[`qw_eq_neg_archimedeanTerm_of_vanishesOn_cc20Triple_of_primeFreeSquare`](ConnesWeilRH/Dev/C1HealthyYoshidaDetector.lean#L127).

### 3.2 The next mathematical problem

C2 reduces the next station to one scalar inequality. For the pinned detector
`g : CompactLogTest`, the Lean handoff theorem
[`healthyDetectorData_iff_selectedDetectorArchimedeanGate`](ConnesWeilRH/Dev/C1HealthyDetectorPinning.lean#L119)
states that the full healthy-detector package is equivalent to

$$
0 < \mathrm{C1SameOwnerWeil.archimedeanTerm}(g^{\ast} \ast g).
$$

The next accepted result must prove this C3 gate for a selected detector on the
healthy owner. Records [1077](docs/proofs/1077_pinned_detector_sign.md)
through [1086](docs/proofs/1086_g3_carrier_design.md) searched for such a
detector inside the root window; [proof 1087](docs/proofs/1087_c3_root_window_spectral_verdict.md)
adjudicated the whole window: the top of the archimedean form on the
triple-vanishing subspace plateaus near -0.85 per unit mass, so no root-window
test can satisfy the displayed inequality (the trace balance above explains the
sign - at radius below log 2 the gate is an off-line-zero witness, not an RH
lemma). The surviving C3 shape is the same gate at the detector's orbit window,
reached by growing the ROOT-local endpoint certificate outward over a finite
visible-prime set. That proof may use a directed interval certificate or a
structured algebraic sign theorem, but it must land as a Lean theorem with its
own axiom audit; no theorem consumes the scan numbers.

| Requirement | State | Acceptance condition |
| :-- | :-- | :-- |
| C3 archimedean gate | Open (root window numerically closed by [1087](docs/proofs/1087_c3_root_window_spectral_verdict.md)) | Prove the strict inequality on a detector at an expanded-radius (orbit) window |
| Detector-specific semi-local positivity | Open | Derive the healthy-detector data on the same `CompactLog` owner |
| Contradiction to `SourceRH` | Open | Connect the detector certificate to the existing exit without using the coverage socket |

### 3.3 Route boundaries

The project keeps rejected and frozen routes visible so that a local theorem
does not get mistaken for an RH exit.

| Boundary | Why it cannot close the active route | Evidence |
| :-- | :-- | :-- |
| Universal B1 all-test positivity | ROOT-window positivity does not control mixed terms or newly visible prime powers | [proof 1076](docs/map/003_b1_b5_minimal_exit_route_selection.md) |
| Normalized additive B5 socket | Its convolution doubles a Mellin value rather than multiplying the required values | [proof 1076](docs/map/003_b1_b5_minimal_exit_route_selection.md) |
| Bare whole-line Hilbert-Schmidt premise | It fails for each nonzero test | [proof 1016](docs/proofs/1016_plain_window_trace_family_verdict.md) |
| Gate 3U and Lane R | The freeze policy archives them outside the healthy-owner chain | [`RH_MAINLINE_FREEZE.md`](RH_MAINLINE_FREEZE.md) |

The normalized B5 socket has an explicit Mellin counterexample:

$$
\boxed{
  \begin{gathered}
  \text{NORMALIZED B5: MELLIN OBSTRUCTION} \\
  \widetilde g(\rho)=1,\qquad
  \widetilde{g\star g}(\rho)=2\ne1=\widetilde g(\rho)^2 \\
  \Longrightarrow\quad
  \text{the Mellin product law fails on this owner.}
  \end{gathered}
}
$$

[`not_normalizedCC20MellinConvolutionLaw`](ConnesWeilRH/Source/CC20YoshidaConstruction.lean#L2727)
constructs the witness. The healthy `CompactLog` owner uses a genuine
Hermitian square, as
[`C1HealthyYoshidaDetector.lean`](ConnesWeilRH/Dev/C1HealthyYoshidaDetector.lean#L13)
records.

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

These records delimit the live campaign. New work must supply a named premise
of the healthy-owner chain: the paper-scale ROOT-local certificate, the C3
gate for a pinned detector, or the detector-certificate contradiction to
`SourceRH`. The
[`RH mainline freeze`](RH_MAINLINE_FREEZE.md) defines that boundary.

## 4. Sources

The formal interfaces draw on the following papers.

### Paper-to-interface map

Read each row from source to Lean interface to README panel. The source states
the mathematical object; the Lean declaration fixes the carrier and quantifiers
used here.

| Source | Mathematical object | Lean interface | README panel |
| :-- | :-- | :-- | :-- |
| [Connes–Consani (2020)](https://arxiv.org/abs/2006.13771) | Weil explicit formula and archimedean place | [`centerTwo_arithmetic_eq_spectral`](ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L232) | Section 3.1 Connes–Weil trace balance |
| [Connes–Consani–Moscovici (2023)](https://arxiv.org/abs/2310.18423) | Semilocal space and Fourier transport | [`CompactLogTest.convolutionSquare`](ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean#L114) | Healthy C2-to-C3 owner |
| [proof 1070](docs/proofs/1070_weil_q_hunting_level1.md) | Mellin square product law | [`not_normalizedCC20MellinConvolutionLaw`](ConnesWeilRH/Source/CC20YoshidaConstruction.lean#L2727) | Section 3.3 normalized B5 obstruction |

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
