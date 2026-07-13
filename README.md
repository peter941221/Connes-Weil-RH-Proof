# Connes-Weil RH Proof

A Lean 4 project devoted to the Riemann hypothesis and the operator-theoretic
ideas surrounding the Connes-Weil explicit formula.

Toolchain: Lean 4.30.0 and Mathlib 4.30.0.

## 1. The project

The Riemann hypothesis places every nontrivial zero of the Riemann zeta
function on the critical line:

```math
\zeta(s)=0,\quad 0<\mathrm{Re}(s)<1
\quad\Longrightarrow\quad
\mathrm{Re}(s)=\frac{1}{2}.
```

This project studies the Connes-Weil route and formalizes its analytic and
operator-theoretic components in Lean 4. The final target is Mathlib's
[`_root_.RiemannHypothesis`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LSeries/RiemannZeta.lean).

The route begins with a compactly supported test function g and its
convolution square

```math
F_g=g^{\ast}*g.
```

The Weil explicit formula places zeta zeros, prime powers, and the
archimedean contribution in one distribution. A sufficiently rich family of
tests satisfying

```math
\sum_v W_v(F_g)\le 0
```

would yield RH through the Weil criterion. The operator program seeks a
positive trace whose expansion equals this Weil expression. The delicate
point is ownership: the test function, convolution square, prime terms,
operator, and trace identity must refer to the same mathematical object.

Lean exposes each analytic obligation. A change of basis needs summability.
A trace cycle needs an absolutely convergent double series. An adjoint needs a
common Hilbert space. A limit needs a domain shared by every term.

<pre>
compact test g
     |
     v
convolution square F = g* * g
     |
     +-------------------+
     |                   |
     v                   v
prime-power values     archimedean operator
     |                   |
     v                   v
finite-S crossing sum  semilocal positive owner
     |                   |
     +---------+---------+
               |
               v
          Weil inequality
               |
               v
        Riemann hypothesis
</pre>

### 1.1 Representative lines of attack

1. Connes-Weil semilocal trace formulas

   This line combines a finite set of places S, Sonin spaces, semilocal
   Fourier theory, and the Weil explicit formula on one Hilbert space. The
   current route has formalized the exact prime-power coefficient of a single
   crossing and assembled finitely many crossings into a compact self-adjoint
   operator.

2. Yoshida zero detectors

   Yoshida's method constructs Mellin test functions aimed at a prescribed
   zero off the critical line. The repository formalizes support budgets,
   convolution-power tail reduction, finite interpolation, and uniform
   quadratic decay on the critical strip. The remaining question is whether
   these detectors enter the same semilocal positive-trace construction.

3. Xi-function zero counting

   The project controls the completed Xi function through Mathlib's theta
   kernel and reduces the zero-summability input to geometric ball bounds in
   the right half-plane. Quadratic Mellin decay requires shell growth
   below 4^n; the full Riemann-von Mangoldt asymptotic is stronger than this
   consumer needs.

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
   needs spectral sign information. The active problem is therefore an exact
   semilocal decomposition with a common domain and a controlled remainder.

6. Operator-level falsification

   The project has tested Xi-nullspace corrections, log-Poisson positive
   operators, Fredholm/Fock Euler-log expansions, higher-order Q filters,
   adelic scalar compensation, and Clifford prime channels. Each rejected
   construction comes with a concrete coefficient, ideal-class, density, or
   domain obstruction.

## 2. Formalized Lean 4 results

### 2.1 Hilbert-Schmidt trace cycles and nuclear expansions

Let A, B: H -> G satisfy the Hilbert-Schmidt summability conditions on a
Hilbert basis (e_i):

```math
\sum_i \Vert A e_i\Vert^2<\infty,
\qquad
\sum_i \Vert B e_i\Vert^2<\infty.
```

The project first proves absolute summability of the two-basis coefficient
matrix:

```math
\sum_{i,j}
\left|
\langle A e_i,f_j\rangle
\langle f_j,B e_i\rangle
\right|<\infty.
```

This estimate justifies the exchange of the two infinite sums and gives the
cross-space trace identity

```math
\mathrm{Tr}_H(A^{\ast}B)=\mathrm{Tr}_G(BA^{\ast}).
```

Lean declarations:

- [`summable_cyclicCoefficients`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L307)
- [`ordinaryTraceAlong_adjoint_comp_eq_comp_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L520)
- [`ordinaryTraceAlong_three_comp_eq_cycle`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/PositiveTrace.lean#L566)

The same module proves the nuclear expansion

```math
A^{\ast}B
=
\sum_j
\mathrm{rankOne}(A^{\ast}f_j,B^{\ast}f_j).
```

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

```math
\mathrm{Tr}(L^{\ast}R)
=
\int \langle L_s,R_s\rangle\,ds.
```

- [`pairData_trace_eq_kernel_inner`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/ContinuousKernelHilbertSchmidt.lean#L316)

Applied to the selected convolution square F, this theorem yields the two
oriented crossing coefficients

```math
\mathrm{Tr}(L^{\ast}R)=bF(b),
\qquad
\mathrm{Tr}(R^{\ast}L)=bF(-b).
```

- [`pairData_trace_eq_mul_convolutionSquare`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L289)
- [`reversePairData_trace_eq_mul_convolutionSquare_neg`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L320)
- [`eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L390)

For b = m log p, the Euler weight converts these traces into the prime-power
term of the explicit formula:

```math
\frac{bF(b)+bF(-b)}{m\sqrt{p^m}}
=
\frac{\log p}{\sqrt{p^m}}
\left(F(\log p^m)+F(-\log p^m)\right).
```

### 2.3 From compact crossings to the whole line

The compact kernel and the global convolution operator act on different
Hilbert spaces. The project constructs restriction S, zero extension E = S^*,
translation U_b, and the half-line projection P. It then
identifies the boundary translation with

```math
J_b=(I-P)U_bP.
```

The relevant declarations are:

- [`restrictedSetZeroExtension_eq_adjoint_restrict`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L210)
- [`globalBoundaryTranslationProjection_eq_singleCrossingOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1085)
- [`globalLogConvolution_involution_eq_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1765)

A trace cycle leaves a projection E E^* in the product. Lean first proves
that the relevant factor has range inside the range of E. The rectangular
three-factor trace theorem then transports the compact
trace to the whole line:

```math
\mathrm{Tr}(L^{\ast}R)
=
\mathrm{Tr}(C_h C_{h^{\ast}}J_b),
```

```math
\mathrm{Tr}(R^{\ast}L)
=
\mathrm{Tr}(J_b^{\ast}C_h C_{h^{\ast}}).
```

- [`leftKernelAdjoint_range_factorization`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L1842)
- [`pairData_trace_eq_namedSourceCrossingProduct`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2008)
- [`reflectedWholeLineLeftFactor_summable`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2545)
- [`pairData_trace_eq_globalConvolutionCrossing`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2711)
- [`reversePairData_trace_eq_globalConvolutionCrossing_adjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2767)

### 2.4 A compact self-adjoint finite-prime operator

For a prime power (p, m), let T_(p,m) denote the whole-line crossing with
translation length m log p. The project defines

```math
K_{p,m}
=
\frac{1}{m\sqrt{p^m}}
\left(T_{p,m}+T_{p,m}^{\ast}\right)
```

and forms the finite sum before taking a trace:

```math
K_{\mathcal T}=\sum_{(p,m)\in\mathcal T}K_{p,m}.
```

Every summand acts on the same global L2(R) space and uses the same
`SelectedWeilSquareOwner`. Lean proves four properties:

1. K_T is self-adjoint.
2. K_T is a compact operator in Mathlib's sense.
3. Its diagonal is absolutely summable along the named Hilbert basis.
4. Its ordinary trace equals the finite prime-power sum attached to the same
   convolution square.

```math
\mathrm{Tr}(K_{\mathcal T})
=
\sum_{(p,m)\in\mathcal T}\mathrm{FP}(p^m).
```

Here FP(p^m) denotes the selected finite-prime term.

- [`eulerLogWeightedGlobalPairTraceOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L2906)
- [`eulerLogWeightedGlobalPairTraceOperatorSum_isSelfAdjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3064)
- [`eulerLogWeightedGlobalPairTraceOperatorSum_isCompactOperator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3088)
- [`ordinaryTraceAlong_eulerLogWeightedGlobalPairTraceOperatorSum_eq_finitePrimeTerm_pow_sum`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingOperatorBridge.lean#L3123)

### 2.5 A global realization of the CC20 finite-window operator

The regular CC20 kernel begins on a finite Haar window. Let H_lambda denote
the finite-window operator and let E_lambda be zero extension into L2(R). The
project proves the exact conjugation identity

```math
H_\lambda^{\mathrm{global}}
=
E_\lambda H_\lambda E_\lambda^{\ast}.
```

Continuity and symmetry of the finite-window kernel give compactness and
self-adjointness. The conjugation identity carries both properties to the
global Hilbert space used by K_T.

- [`cc20GlobalLogWindowL2Operator_eq_zeroExtension_conjugation`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1629)
- [`isCompactOperator_cc20GlobalLogWindowL2Operator`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1639)
- [`cc20GlobalLogWindowL2Operator_isSelfAdjoint`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20Concrete/GlobalLogKernel.lean#L1649)

### 2.6 A translation quadratic form for prime terms

Let h belong to L2(R) and let U_b be global translation. Lean proves

```math
\langle h,U_bh\rangle=F_h(b).
```

The project then defines the self-adjoint translation combination

```math
D_{p,m}
=
\frac{\log p}{\sqrt{p^m}}
\left(U_{m\log p}+U_{-m\log p}\right)
```

and obtains the finite-prime quadratic read-off on the same vector:

```math
\langle h,D_{p,m}h\rangle=\mathrm{FP}(p^m).
```

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

```math
f_r(x)=r^{-1}f(x/r),
\qquad
\Phi_{f_r}(s)=\Phi_f(rs).
```

It then takes an N-fold convolution with r = 1/N. The convolution power
reduces the Mellin tail while its total support stays inside the original
budget. A correction function in a disjoint residual window performs finite
interpolation and retains uniform quadratic decay on the strip.

- [`exists_residualWindow_correction_with_quadratic_decay`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaConvolution.lean#L278)
- [`exists_uniform_mellin_vertical_quadratic_decay`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaTail.lean#L257)
- [`exists_residualWindow_nearbyZero_assembled_distance_bound_lt`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20YoshidaConvolution.lean#L780)

For the completed Xi function, the project starts from a theta-kernel moment
bound and proves that right-half-plane ball estimates imply summability over
the source nontrivial zeros. Let N_n count the zeros in the n-th geometric
shell. The following estimate already matches the quadratic Mellin decay:

```math
N_n\le Kc^n,
\qquad c<4.
```

The geometric ratio c/4 bounds the resulting shell sum.

- [`norm_completedRiemannXi_le_kernelMoment`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20ZetaCounting.lean#L239)
- [`sourceNontrivialZero_summable_of_xi_right_halfplane_ball_bounds`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Source/CC20ZetaCounting.lean#L531)

## 3. Current frontier

As of 2026-07-13, the finite-prime crossing chain runs from continuous kernels
to a global compact self-adjoint operator while preserving one selected
convolution square throughout.

<pre>
continuous kernels on finite intervals
               |
               v
       traces b F(b), b F(-b)
               |
               v
legal rectangular trace cycle
               |
               v
whole-line C_h C_h* J_b and its adjoint
               |
               v
Euler-log prime-power atom
               |
               v
finite-S compact self-adjoint K_S
               |
               v
trace(K_S) = selected finite-prime sum
</pre>

This chain settles four coupled points.

1. Crossing geometry

   The function-level formula for J_b confines the crossing to the exact
   interval [-b,0]. The source interval of the compact kernel therefore
   agrees with the global half-line projection.

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
   on the same global logarithmic Hilbert space. Future identities can compare
   their spectra without transporting signs between incompatible carriers.

### 3.1 The next mathematical problem

The next layer asks for a positive operator P_S(h) on the finite-S
semilocal space and an exact same-object decomposition

```math
\mathcal P_S(h)=K_S(h)+R_S(h).
```

The term K_S(h) must agree, summand by summand, with the crossing operator
formalized in Section 2.4. The remainder R_S(h) must share the domain, test
function, and Q action of P_S(h). A sign estimate or limiting
estimate for this remainder must then yield the Weil inequality. The intended
chain has the form

```math
\mathcal P_S(h)\ge 0,
\qquad
\mathcal P_S(h)=K_S(h)+R_S(h),
\qquad
R_S(h)\in\mathcal C_S.
```

Here C_S denotes the class of remainders satisfying the required
sign or limiting estimate.

After this operator layer, one quantifier problem remains: the route-generated
tests must detect every zero off the critical line. The desired implication is

```math
\mathcal P_S(h)\ge 0
\Longrightarrow
QW(h,h)\ge 0
\Longrightarrow
\sum_v W_v(F_h)\le 0
\Longrightarrow
\mathrm{RH}.
```

### 3.2 Representative obstructions

Each rejected route has a specific failure mechanism.

| Route | Obstruction | Record |
|---|---|---|
| Compact Xi-nullspace correction | Exponential zero density conflicts with the zero density of a compactly supported entire transform | [proof 110](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/110_xi_null_compact_support_zero_density_death.md) |
| Log-Poisson positive trace | Its positive coefficients do not reproduce the prime scalar in the explicit formula | [proof 111](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/111_log_poisson_positive_trace_readoff_death.md) |
| Compact Wiener-Hopf boundary repair | A compact perturbation cannot cancel the noncompact principal symbol | [proof 118](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/118_wiener_hopf_compact_boundary_cannot_cancel_symbol.md) |
| Fredholm/Fock Euler-log expansion | The required Euler-log derivative misses the target trace ideal | [proof 119](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/119_fredholm_euler_log_traceclass_death.md) |
| Higher-order Q filters | Differential weights strengthen the cusp principal part without producing the required sign | [proof 120](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/120_higher_q_filter_unbounded_cusp_rejection.md) |
| Adelic scalar compensation | Product-formula coefficients do not match the one-prime read-off | [proof 121](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/121_adelic_product_formula_scalar_mismatch.md) |
| Clifford prime channels | The Gram construction retains the original sign problem and adds channel cost | [proof 122](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/122_clifford_prime_channel_gram_cost.md) |

These obstructions constrain the next construction. It must provide an exact
finite-S trace read-off and control the post-Q remainder on one form domain.

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
   tail orders. The remaining operator problem is a uniform semilocal positive
   trace identity with a controlled remainder.

The term-by-term alignment between Burnol's compact-test explicit formula and
the repository's `SelectedWeilFormulaOwner` appears in
[proof 109](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/109_burnol_selected_weil_formula_alignment.md).

## 5. Repository map

<pre>
ConnesWeilRH/
  Basic.lean                         Mathlib RH target and basic interfaces
  Source/
    CC20Concrete/                    continuous kernels, traces, global windows
    CCM25Concrete/                   selected squares, crossings, prime terms
    CC20Yoshida*.lean                Mellin detectors and support budgets
    CC20ZetaCounting.lean            Xi-kernel bounds and zero summability
  Route/                             conditional route composition
  Dev/                               premise audit and research boundary

docs/proofs/                         derivations, obstructions, milestones
docs/audits/                         source, quantifier, and axiom audits
formalization/                       interface and formalization notes
</pre>

The root import is
[`ConnesWeilRH.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH.lean).
The conditional route reaches Mathlib RH in
[`RouteTheorem.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Route/RouteTheorem.lean#L3539).
The premise audit for the no-argument root lives in
[`UnconditionalSkeleton.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/UnconditionalSkeleton.lean#L8048).

Run `lake build ConnesWeilRH` for the root build. Import-facing audit files use
`#check`, `#print`, and `#print axioms` to inspect both theorem types and axiom
dependencies. A final theorem audit must also inspect explicit parameters,
implicit parameters, and typeclass parameters because an axiom report does not
detect ordinary premises.

## 6. License

Apache License 2.0. See
[LICENSE](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/LICENSE).
