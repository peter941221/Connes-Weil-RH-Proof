# 1736 - Detector sign: translation energy and the prime discrepancy

Date: 2026-09-20.

Status: PAPER derivations and candidate screening. No new Lean theorem,
numerical experiment, detector nonnegativity, or RH proof. The calculation
below retains the genuine CompactLog convolution square and its arithmetic
normalization. It does not promote a new route or an endpoint supplier.

## 1. Consumer and source audit

The consumer is
`C1HealthyYoshidaSpectralNegativity.healthy_sourceRH_of_right_detector_specific_qw_nonneg`.
For each hypothetical right-hand off-line zero, the existing construction
supplies a selected `g` with healthy detector data. The missing analysis must
prove `0 <= C1SameOwnerWeil.qw g` for that SAME `g`, using its raw construction
data and its actual visible prime powers. No sign conclusion is source data.

Source definitions:

- `Source/CCM25Concrete/CompactLogConvolution.lean`:
  `convolutionSquare_apply`, `convolutionSquare_neg`, and
  `convolutionSquare_zero_eq_integral_normSq`.
- `Dev/C1SameOwnerWeil.lean`: `archimedeanTerm`, `finitePrimeTermComplex`,
  `finitePrimeSum`, `psi`, and `qw`.
- `Dev/C1HealthyYoshidaDetector.lean`:
  `qw_eq_neg_archimedeanTerm_sub_finitePrimeSum_of_vanishesOn_cc20Triple`.
- `Dev/C1LaneRD3Root.lean`: `derivativeShift`,
  `laplaceAt_derivativeShift`, and `tripleVanishingRoot`.

For triple-vanishing tests the existing exact identity is

    qw(g) = -archimedeanTerm(F) - finitePrimeSum(F),
    F = g.involution.convolution g.

This is the target, rather than a sign assertion for an auxiliary trace.

## 2. An exact positive-energy decomposition with a negative mass term

Write

    M       = integral_R |g(x)|^2 dx,
    f(y)    = Re F(y),
    E_g(y)  = integral_R |g(x+y)-g(x)|^2 dx,
    w(y)    = exp(y/2)/(exp(y)-exp(-y)),       y > 0,
    a_n     = vonMangoldt(n)/sqrt(n),
    c       = log(4*pi) + EulerGamma.

The genuine square gives `F(y) = integral conj(g(x))*g(x+y) dx`.
Translation invariance of Lebesgue measure therefore gives

    E_g(y) = 2*M - 2*f(y).                                  (1)

Substitution into the committed archimedean formula gives

    archimedeanTerm(F) = K*M - integral_0^infinity w(y)*E_g(y) dy,
    K = log(8*pi) + EulerGamma + pi/2.                       (2)

Here the constant is evaluated, not dropped. With `u=exp(-y/2)`,

    integral_0^infinity 2*(exp(y/2)-1)/(exp(y)-exp(-y)) dy
      = 4*integral_0^1 1/((1+u)*(1+u^2)) du
      = log(2) + pi/2.

The partial fractions are

    4/((1+u)*(1+u^2)) = 2/(1+u) + (2-2*u)/(1+u^2).

All integrals in (2) converge: near zero,
`E_g(y) <= y^2*||g'||_2^2` and `w(y) = O(1/y)`; at infinity,
`E_g(y) <= 4*M` and `w(y) = O(exp(-y/2))`.

Let `I` be the actual finite visible prime-power index set of `F`. Then

    finitePrimeSum(F) = sum_(n in I) a_n*(2*M-E_g(log n)),

and, for a triple-vanishing test,

    qw(g) = integral_0^infinity w(y)*E_g(y) dy
              + sum_(n in I) a_n*E_g(log n)
              - (K + 2*sum_(n in I) a_n)*M.                (3)

The first two terms are nonnegative. Their nonnegativity does not bound
their sum below by the third term. Formula (3) is an exact reformulation,
not progress on the selected-detector sign estimate.

Adding an index with `F(log n)=0` changes neither side: (1) gives
`E_g(log n)=2*M`, so its added energy and mass charge cancel exactly.
Consequently an enlarged cutoff cannot create positivity by retaining the
energy and discarding the matching charge.

## 3. A quantitative counterfamily for a fixed arithmetic truncation

This subsection concerns a FIXED finite set `I` of integer indices >= 2,
not the support-dependent complete index set in (3). Define

    Q_I(g) = poleTerm(F) - archimedeanTerm(F)
               - 2*sum_(n in I) a_n*f(log n),
    C_I = K + 2*sum_(n in I) a_n,
    B_I = 18 + sum_(n in I) a_n*(log n)^2.

Both constants are finite and `C_I > 0`. The derivative estimate above and
Tonelli give

    integral_0^infinity y^2*w(y) dy
      = 16*sum_(k>=0) 1/(4*k+1)^3 <= 18.                   (4)

For the last inequality, separate `k=0` and bound the remaining decreasing
series by `integral_0^infinity (4*x+1)^(-3) dx = 1/8`.
Thus, on the triple-vanishing class,

    Q_I(g) <= B_I*||g'||_2^2 - C_I*||g||_2^2.              (5)

Choose any nonzero real `h` in `C_c^infinity(R)`, and put, for `L >= 1`,

    h_L(x) = h(x/L),
    g_L    = D*(D+1/2)*(D+1) h_L,
    A_j    = ||h^(j)||_2^2,                j = 1,2,3,4.

Integration by parts gives the exact Laplace identity

    laplaceAt g_L s = (-s)*(1/2-s)*(1-s)*laplaceAt h_L s.

Hence `g_L` satisfies the SAME three nodes `{0,1/2,1}` as the healthy
test space; no approximate moment cancellation is used. `A_1 > 0`, since
a nonzero compactly supported smooth function cannot be constant.

Expanding the derivative polynomial and integrating mixed derivative terms
by parts gives

    ||g_L||_2^2  = A_1/(4*L) + 5*A_2/(4*L^3) + A_3/L^5,
    ||g_L'||_2^2 = A_2/(4*L^3) + 5*A_3/(4*L^5) + A_4/L^7.

For example, `integral h'*h''' = -A_2`, while the mixed consecutive
derivative integrals vanish. These identities imply

    ||g_L'||_2^2 / ||g_L||_2^2 <= H/L^2,
    H = (A_2 + 5*A_3 + 4*A_4)/A_1.

Combining with (5) proves the following PAPER statement:

    L >= 1 and L^2 > B_I*H/C_I  ==>  Q_I(g_L) < 0.          (6)

This rejects a uniform nonnegativity proof for a frozen arithmetic
truncation even on the exact triple-vanishing class. It is not a
counterexample to `qw`: `I` in (6) is not the complete visible set.

Indeed, choose a prime `p` outside `I`. By (1) and the derivative bound,

    f_L(log p)/M_L >= 1 - (log p)^2*H/(2*L^2) > 0

for sufficiently large `L`. Thus `p` becomes an actual visible index.
The omitted arithmetic is not optional. Its TOTAL signed contribution is
not estimated here; the individual omitted terms need not improve the sign.

The same proof covers a fixed finite set of primes with ALL their powers.
For `r_p=p^(-1/2)`, replace the finite sums in the constants by

    sum_(p in S) log(p)*r_p/(1-r_p),
    sum_(p in S) (log p)^3*r_p*(1+r_p)/(1-r_p)^3,

respectively. Both converge. The actual evaluation for each compactly
supported square still contains only finitely many nonzero terms.

## 4. A direct prime-versus-continuum cancellation attempt

Define the right-continuous Chebyshev function and its log-coordinate error

    Psi(x) = sum_(2 <= n <= x) vonMangoldt(n),
    R(y)   = Psi(exp y) - (exp y - 1),
    H_g(y) = exp(-y/2)*f(y),                   y >= 0.

For a cutoff beyond the support of `F`, Stieltjes integration by parts is
exact. The endpoint terms vanish because `R(0)=0` and `H_g` is zero at
the outer cutoff. It yields

    finitePrimeSum(F)
      = 2*integral_0^infinity exp(y/2)*f(y) dy
          - 2*integral_0^infinity R(y)*H_g'(y) dy.

Hermitian symmetry also gives

    poleTerm(F)
      = 2*integral_0^infinity (exp(y/2)+exp(-y/2))*f(y) dy.

Therefore, on the SAME owner and with ALL visible indices included,

    qw(g) = Q_cont(g) + 2*integral_0^infinity R(y)*H_g'(y) dy,
    Q_cont(g) = 2*integral_0^infinity exp(-y/2)*f(y) dy
                  - archimedeanTerm(F).                   (7)

This identity uses no prime number theorem and assumes no zero location.

Replacing the arithmetic by its continuous main term sets `R=0`. That
model does not supply a positive form. Cauchy--Schwarz gives `f(y) <= M`;
(2) and (4) then imply

    Q_cont(g) <= (4-K)*M + 18*||g'||_2^2.

The explicit constant satisfies `K > 4`: `pi > 3`, `EulerGamma > 0`,
and `exp(3) < 24` give `K > log(24)+3/2 > 9/2`.
Consequently the SAME exact
triple-vanishing family satisfies

    L^2 > 18*H/(K-4)  ==>  Q_cont(g_L) < 0.                (8)

Thus dropping the discrepancy loses a necessary sign contribution. An
asymptotic statement about density does not itself bound the signed
integral in (7) for a selected detector of growing support.

### Actual arithmetic also prevents a termwise sign argument

One cannot repair this attempt by declaring the integrand in (7)
nonnegative on the triple-vanishing class. Its sign changes for the same
family `g_L`, using only the prime powers through 5.

For `0 < y < log 2`, `R(y)=-(exp(y)-1)<0`. Since `f` is even,
`H_g'(0)=-M/2<0`; the integrand is positive on a short interval to the
right of zero.

At the other end of this small arithmetic check,

    Psi(5) = log 2 + log 3 + log 2 + log 5 = log 60,
    R(log 5) = log 60 - 4 > 0.

The strict inequality follows from `exp(1)<11/4` and
`(11/4)^4=14641/256<60`. For completeness, the exponential series gives
`exp(1) <= 8/3 + 5/96 = 87/32 < 11/4`. There is therefore a nonempty
right-hand interval after `log 5` where `R>0` and `y<2`.

Put `r=||g'||_2^2/M`. Cauchy--Schwarz and (1) give

    |f'(y)|/M <= sqrt(r),
    f(y)/M >= 1-y^2*r/2,
    H_g'(y)/M <= exp(-y/2)*(sqrt(r)-1/2+y^2*r/4).

For `r <= 1/64` and `0 <= y <= 2`, the last parenthesis is at most
`1/8-1/2+1/64 < 0`. Taking `L^2 >= 64*H` supplies this condition for
`g_L`. The ACTUAL discrepancy integrand is thus negative on a nonempty
interval after `log 5` and positive near zero. Its integrated sign remains
unproved. This is a paper counterexample to pointwise positivity, not to
the aggregate inequality or to a detector-specific estimate.

## 5. Candidate cards and prior-art boundary

Generation operators: positive difference-square factorization and a
variational slow-test counterfamily; then elimination of the prime main
term by a signed Stieltjes identity.

Candidate SIGN-E:
  Target: the lower energy bound in (3) for the selected healthy detector.
  Proposed sign source: translation differences with positive weights.
  Falsifier: (6), if the support-dependent prime set is frozen or discarded.
  Verdict: NEEDS-ANALYSIS on the actual owner. Positive summands alone do
  not provide the required lower bound. The frozen-set variant has a paper
  counterexample; it is not promoted to a formal route-level no-go.

Candidate SIGN-R:
  Target: the same selected detector's value in (7).
  Proposed sign source: cancellation of the exponential prime main term.
  Falsifiers: (8) if the exact prime discrepancy is discarded; the
  prime-power calculation through 5 if its integrand is assigned a
  pointwise nonnegative sign on all triple-vanishing tests.
  Verdict: NEEDS-ANALYSIS. The missing new theorem is a one-sided estimate
  of the ACTUAL signed discrepancy integral against `H_g'`, strong enough
  to offset `Q_cont(g)`. Merely assuming that estimate would rename P2.

Prior art: record 063 already writes a localized pole-free Dirichlet form;
064/065 reject an inference from Perron structure to constrained positivity.
Map 004 section 8 and record 1417 already identify the phase-versus-density
problem. This record supplies explicit constants and one exact D3 family
for the two shortcuts above; it does not claim literature novelty for the
Dirichlet or Stieltjes representations.

Primary-source readback on 2026-09-20:

- Suzuki, *Weil's quadratic form via the screw function*,
  https://arxiv.org/html/2606.09096 : localized operator and variational
  theory; the all-window positive Hilbert-space specialization at zero
  energy assumes RH. It is not an unconditional producer for (3).
- *A probabilistic interpretation of Weil's explicit sums and arithmetic
  spectral measures*, https://arxiv.org/html/2311.08519 : covariance and
  spectral-integral representations; the required sign remains a criterion.

Prototype: ANALYTIC-ONLY. Equations (6) and (8) provide symbolic falsifiers;
finite numerical tests would add no evidence to those inequalities. The
counterfamily is a genuine admissible test family, NOT a hypothetical-zero
detector and NOT actual off-line zeta data.

## 6. Remaining core and acceptance

The selected-detector nonnegativity remains open. Neither S3 summability,
the existence of the positive terms in (3), nor the main-term cancellation
in (7) supplies it. A continuation must use raw information about the
selected orbit together with the actual signed prime correlations; it must
prove an estimate rather than package it as a field.

This record changes no Lean source and carries no build or axiom-audit
claim. Verification consists of the displayed substitutions, convergent
integrals, integration by parts, and exact polynomial norm calculations.
The route remains healthy-CompactLog B5; no universal B1 campaign opens.
