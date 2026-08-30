# Connes-Weil RH Proof

A Lean 4 project devoted to the Riemann hypothesis and the operator-theoretic
ideas surrounding the Connes-Weil explicit formula.

Toolchain: Lean 4.30.0 and Mathlib 4.30.0.

## Status dashboard

> **Updated 2026-08-30.** This dashboard describes commit
> [`16b5f96`](https://github.com/peter941221/Connes-Weil-RH-Proof/commit/16b5f96)
> (brick #1: unit-scale trace legality of the finite-S response, F2 proven,
> the single F1 crux isolated) together with the P2b closure recorded in
> [proof 1055](docs/proofs/1055_semilocal_p2b_verdict.md) and the
> 2026-08-30 analysis batch: [proof 1056](docs/proofs/1056_f1_semilocal_trace_scope_and_freeze_boundary.md)
> (F1 freeze-boundary rulings + brick #2 scope),
> [proof 1057](docs/proofs/1057_cc20_verbatim_delta_chain_and_numbering_map.md)
> (CC20 raw-tex delta pinning + exact numbering map),
> [proof 1058](docs/proofs/1058_alpha_chi_reconnaissance_verdict.md)
> (alpha reconnaissance: the endpoint profile is 11 terms deep),
> [proof 1059](docs/proofs/1059_2b_margin_revocation_and_lambda_convention_pin.md)
> (F1 brick-2b perturbation scheme REVOKED by its own pre-flight; the
> paper's lambda(n) convention PINNED to the c = 2 pi even branch),
> [proof 1060](docs/proofs/1060_gate1_delta_wiring_contract.md)
> (GATE 1 delta contract: the (141)-(143) chain is now a Lean structure
> feeding the endpoint certificate; delta is gated on gamma),
> [proof 1061](docs/proofs/1061_alpha_t1_lambda_table_and_data_map.md)
> (alpha campaign T1: the lambda(n) candidate table converges at 33-80
> stable digits and the contract's eigenvalue obligation splits),
> [proof 1062](docs/proofs/1062_alpha_t2t3_anchor_validation_and_lambda_sqrt_correction.md)
> (T2/T3 dictionary validated at 1e-33; the anchor test CORRECTED the
> 1059 pin: the paper's lambda(n) is the windowed-Fourier eigenvalue, the
> square root of the concentration table, with a sqrt(2) inner-product
> factor - and the endpointSlope identity then reproduces the paper's
> printed term list and the 22.9965 anchor digit for digit).
> **No unconditional proof of the Riemann hypothesis is claimed here.**

### Route map

Read it like a pilgrimage: the departure is at the top, RH lies at the
bottom; every station on the road carries its state.

```text

            THE ROAD TO THE RIEMANN HYPOTHESIS - JOURNEY MAP
        read downward: the departure is at the top, RH at the bottom

   ===================  LEG I - ALREADY BEHIND US  ====================

   DEPARTURE (July 2026): the Weil criterion is chosen as the road.
   If qw(g) >= 0 for EVERY admissible vanishing test g, then RH follows.

        |
        v  +-----------------------------------------------------+
           | STATION 1 - SAME-OWNER FOUNDATIONS     [CLEARED]    |
           | log-coordinate bridge; pole / archimedean / prime   |
           | readbacks; xi-zero index and spectral summability   |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | STATION 2 - GATE 2                    [CLEARED]     |
           | arithmetic-to-spectral equality on ONE owner;       |
           | center-2 contour assembly                           |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | STATION 3 - THE W-MOUNTAIN PASS       [CLEARED]     |
           | W1 online nonnegativity -> W2 vanishing bridge ->   |
           | W3 spectral split -> W4a conjugation -> W4b pairing |
           | (residual = 2 x Re(right-half sum)) -> real-test    |
           | reduction. Five days, five lemmas, axiom-clean.     |
           +-----------------------------------------------------+
        |
        |
        +------>  SIDE VALLEY - the budget-window ladder:
        |         three rungs carved, then PROVEN unreachable
        |         against the ROOT window: B(log 2) ~= +3.9 > 0.
        |                            ** TURNED BACK **
        |
   ============  LEG II - THE GREAT TURN (CC20 ROUTE)  ================

        v  +-----------------------------------------------------+
           | STATION 4 - OPERATOR FLOOR ON WINDOW I [BUILT]      |
           | [-log2/2, log2/2]: kernels -> L2 mass ladder ->     |
           | eq-(121) fold -> bounded operators applyKernelLp.   |
           | The pure-algebra key already fits too:              |
           | qw(g) = -arch(g^2) here (primes die by support,     |
           | pole dies by triple vanishing).                     |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | DETECTOR RIDGE - BOMBIERI/WIRTINGER   [CLEARED]     |
           | (8.13) wirtingerFull: Q(Z) splits into even/odd     |
           | envelopes plus a nonnegative remainder; (8.11) the  |
           | weighted K* Gram sum = ofReal S with S >= 0; the    |
           | reciprocal-eigenvalue sign 0 < lam, conditional.    |
           | DETECTOR only - never an unconditional GATE 1.      |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | CC20 FINITE-RANK INTERFACE            [BUILT]       |
           | eq-(115) profile difference chi - tau = K_I - T;    |
           | eq-(119) finite operator T; eq-(121) pairing bound, |
           | operator-norm gap, rank-one consumer; ROOT-local    |
           | Fact-1 alignment; paired plus/minus symmetry.       |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | EXTRACTED TABLE - PUBLISHED eq-(115) DATA [LANDED]  |
           | m = 1732 angles + coefficients, exact rationals,    |
           | SHA-256-pinned DOCX sources; n=0 plus the sign-paired|
           | nonzero index make eq-(119) complete and symmetric; |
           | concrete evenness + ROOT-window continuity; the     |
           | Fact-1 half-gap certificate ASSEMBLED concretely.   |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | GAMMA COERCIVITY - PAPER SCALE          [OPEN]      |
           | row-band AM-GM sandwich + 1732-branch coefficient   |
           | positivity are built. Bessel gives defect >=        |
           | (1-lam)||xi||^2 only for lam < 1. CC20 uses          |
           | lam ~= 1.05158 > 1, so exceptional direction +      |
           | complement spectrum + rank-one repair remain open.  |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | GATE 1 ASSEMBLY - CONDITIONAL CHAIN [WIRED]         |
           | one entry point for the concrete table: grid ->     |
           | eq-(121) operator gap -> Lemma-second rank-one ->   |
           | 13 < 4g/log 2 < 17 -> slope-matched residual.       |
           | Residue = alpha / beta / paper-gamma / delta.       |
           | Bessel discharges only a separate lam < 1 branch.   |
           +-----------------------------------------------------+
        |

   ##############  YOU ARE HERE  -  GATE 1 BASE CAMP  ################

        |  goal: arch(g^2) <= 0 for all ROOT-class tests [OPEN]
        |  the machinery is wired END TO END; the payloads:
        |
        |      (alpha) ENDPOINT PROFILE CHI ..... [T1-T3 DATA IN HAND]
        |          shape pinned (1057/1058): 11 modes suffice - the
        |          paper's own eq-(170) bounds the rest by 2.366e-12
        |          on [1,2], and probe 1058 reproduced that tail
        |          arithmetic exactly; CONVENTION CORRECTED (1062):
        |          the paper's lambda(n) is the SINGLE windowed-Fourier
        |          eigenvalue = (-1)^n sqrt(concentration table), NOT the
        |          concentration eigenvalue the 1059 s4 pin said; T1
        |          concentration table n=0..10 at dps 60, 33-80 stable
        |          digits M=44/56; T2/T3 CLOSED numerically (1062): the
        |          analyticMode sinc-extension validates at ODE residual
        |          1e-33 (x=1 continuation automatic), and the endpoint-
        |          Slope identity reproduces the paper's printed t(n) list
        |          (11.9719, 8.77574, ...) and anchor 22.9964756839 vs
        |          22.9965; eigenvalue obligation SPLITS: n>=2 by (983)
        |          (< 0.754 < 1), modes 0-1 need enclosures (corrected
        |          margins 5.72e-5 / 4.06e-2); remaining: B1-B3
        |          rigorization bricks + the innerltwoeven sqrt(2) lemma
        |
        |      (beta) JOINT GRID TABLE 2*int |chi - tau|
        |          <= epsilon1 ................ [DATA OPEN]
        |          certified L1 quadrature over the extracted
        |          table (consumer landed; blocked by alpha)
        |
        |      (gamma) PAPER-SCALE COERCIVITY .... [DATA OPEN]
        |          CC20 has lam ~= 1.05158 > 1, while the
        |          Bessel lower bound is only (1-lam)||xi||^2.
        |          Need an exact finite-section/Toeplitz
        |          certificate for the exceptional direction,
        |          complement frame bound, and rank-one repair.
        |          Constants tex-pinned (1057 s2): b ~ 0.05158,
        |          a ~ 0.064, eps2 ~ 0.00441, eps1 ~ 0.00122,
        |          <zeta|xi_0> ~ 0.94865, second gap c > 0.227784.
        |
        |      (delta) ARCHIMEDEAN COMPARISON .. [CONTRACT WIRED]
        |          trace - coefficient*rank <= W-infinity(g^2), the
        |          raw tex eqs (141)-(143) + E(f) chain (1057), is now
        |          a named Lean contract CC20ArchimedeanComparison
        |          whose fields ARE the three chain steps; the 1060
        |          leaf produces the EndpointTraceCertificate from it
        |          (standard-three axioms, no sorry) and composes to
        |          0 <= qw g; the 1057 s5 vanishing-node flag is
        |          resolved on the safe side - our triple set {0,
        |          1/2, 1} contains every candidate node; remaining:
        |          h142/hEchain/h143 discharge, now GATED ON GAMMA
        |
        |      (gapData) NON-PAPER BESSEL BRANCH [CLOSED]
        |          a = 1, epsilon1 = (1-lam)/2,
        |          epsilon2 = 1-lam under lam < 1; it cannot
        |          instantiate the published lam > 1 argument
        |
        |  PARALLEL THREAD - C1 BRICKS (Option-C semi-local bridge,
        |  1050 s4): brick #1 LANDED 16b5f96 - F2 proven, capstone
        |  holds modulo the single F1 crux + two compression-HS
        |  premises.  F1 scoped (1056): LEGAL for fixed lambda = 1
        |  model objects (outside the 1055 freeze; explicitly NOT a
        |  1055-P1 revival payment).  Brick #2 re-scoped (1059): the
        |  2b perturbation scheme was REVOKED by its own margin check
        |  (kappa(T_2) = 5.83 vs a qualitative source margin); F1
        |  stays the thread's named conditional premise (R2 default),
        |  2a Gram-corrected reduction proceeds as algebra, and the
        |  target-side angle lemma (R1) is a separate design record.
        |

   =====================  LEG III - STILL AHEAD  ======================

        |
        v  +-----------------------------------------------------+
           | STATION 5 - SEMI-LOCAL DETECTOR STEP  [AHEAD]       |
           | selected detector + its finite visible prime set;   |
           | prove the same-owner semi-local trace positivity    |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | STATION 6 - DETECTOR NONNEGATIVITY     [LAST GAP]   |
           | contradict the landed strict negative detector;     |
           | coverage-root is RH-equivalent, not a density lemma |
           +-----------------------------------------------------+
        |
        v  +-----------------------------------------------------+
           | STATION 7 - WRAPPER COMPOSITION       [LANDED]      |
           | coverage-root <-> SourceRH bridges plus the         |
           | conditional exits; proved once; no analysis inside  |
           +-----------------------------------------------------+
        |
        v
   ,---------------------------------------------------,
   |            R I E M A N N   H Y P O T H E S I S    |
   |            _root_.RiemannHypothesis (Mathlib)     |
   '---------------------------------------------------'

   ROADS NOT TAKEN (kept so nobody wanders back in):
     x  bare whole-line Hilbert-Schmidt premise - false for every
        nonzero test (proved)
     x  plain-window cutoff trace family - empty producer (proved)
     x  semilocal prolate asymptotic family - DEAD at the P2b gate
        (proof 1055): the cancellation has no mechanism (1054 exact
        counterexample) and no fixed-precision evaluation exists at any
        meaningful scale (precision wall); revival needs a proved
        self-adjoint realization plus an analytic one-crossing identity
     o  GATE 2 Titchmarsh square-form bridge - deferred by design;
        not needed for this first cut (Cartwright theory absent
        from Mathlib)
```

How to read the tags:

- `[CLEARED]` / `[BUILT]` / `[LANDED]` - proved in Lean and axiom-clean:
  every audited declaration reports exactly
  `[propext, Classical.choice, Quot.sound]`, never `sorryAx`.
- `[OPEN]` / `[AHEAD]` / `[LAST GAP]` - explicit outstanding obligations;
  nothing is hidden behind an axiom or a placeholder.
- `[NEXT]` - the brick under construction right now; `[DATA OPEN]` - the
  numeric side of a gate whose Lean interfaces already exist.
- `** TURNED BACK **` and the `x` roads - ruled-out paths, kept as signposts
  so nobody wanders back in; `[DEFERRED]` / `o` - postponed by a documented
  design decision, recorded in
  [proof 1043](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1043_first_cut_window_architecture.md),
  the living design record behind this map.

A milestone count is not an honest measure of distance to RH. The operator
floor, the detector ridge, and the published-data table have landed and audit
clean, but what remains is the hard analytic core: all four paper-scale GATE 1
payloads and a new detector-selected semi-local positivity theorem.  Proof
1055 closed the asymptotic prolate candidate that was supposed to supply the
second: its P2b gate has neither a mechanism nor a decidable evaluation, so
the semi-local step must now arrive from a NEW construction, and no
conditional Lean owner referencing `W_(lambda,S)` may be added.  ROOT
positivity cannot be lifted to arbitrary supports by density alone because
the mixed quadratic terms and newly visible prime powers are uncontrolled.
Ruled-out shortcuts are equally part of the record: the bare whole-line
Hilbert-Schmidt premise is false for every nonzero test, the plain-window
cutoff trace family is an empty producer, and the pure-analysis budget ladder
cannot reach the ROOT window (`B(log 2) ~= +3.9 > 0`).

### Commit timeline

```text
DATE         EVENT                                                COMMIT
------------------------------------------------------------------------
2026-07-09   repository baseline verification mirror            d0bdeed
2026-08-16   center-2 Fourier weight transform readbacks        a47723d
2026-08-17   Gamma reciprocal-series density identity           86af892
             center-2 Gate 2 route closed (arith = spectral)    f1f45d1
2026-08-19   Lane R reduced to real owners, then frozen         271b8fd
2026-08-21   FRONTIER-HS steps 3-9 closed, last sorry killed    8b93e8c
2026-08-24   bare whole-line HS premise refuted                 59f8ff8
             sign-attack plan docs/proofs/1040 defined          855a937
             W1: on-line spectral term of a square >= 0         20af271
             W2 vanishing bridge + W3 spectral split            1e69b31
2026-08-25   W4a: multiplicity survives conjugation             d79d86e
             W4b pairing = 2 x Re(right-half sum)               a7dcccc
             hqw collapsed to a single named inequality         3fdaaa1
             first broadly-quantified W4b class (narrow)        53520ac
             budget class widened by pure algebra               a4b0b75
             boundary-guided rung at exp(-7)                    98fd821
2026-08-26   second boundary rung at exp(-13/2)                 253d821
             direct-Euler boundary rung (third rung)            8a37b7e
             translation layer + root-support window ledger     f12b4fe
             pure-analysis ladder formally ruled out
             CC20 archimedean log-coordinate readback           74b94fa
             endpoint + Yoshida LDL^T algebraic layers          8b84704
             Hilbert Lemma first + spectral decomposition       3bbe82f
             kf_I L2 foundation: HS pointwise bound             62018f9
2026-08-27   Qepsilon endpoint kernel formula + guards          6967031
             kernel mass premises promoted to theorems          53f8cfa
             Yoshida interval-certificate engine                f36db49
             Bombieri 2000 logged as accessible source          c3e61f2
             paper-window kf_I boundedness brick                f149389
             translate-invariance pack (shift slot)             5173f21
             uniform displacement bound frees eq-(121)          2d26182
             weighted correlation fold: eq-(121) engine         1e9f0a1
             displacement-kernel owner bridge                   922a266
             integrability discharge + Fubini readback          6a23ea8
             pairing bound -> operator-norm gap adapter         5c0cff8
             HS kernels lifted to bounded quotient ops          13bae3d
2026-08-28   Wirtinger (8.13) flagship wirtingerFull             18b9b82
             Bombieri (8.11) K*Gram mass + conditional sign      1875953
             CC20 finite-rank gap interface                      429b747
             eq-(115) source reader + Fact-1 ROOT-local fix      553b30d
             profile symmetry producer                           f4eafad
             extracted eq-(115) table into Lean                  24f2dbe
             concrete Fact-1 certificate assembly                70983b6
             record of the certificate reduction                 f3abc6d
             Fact-1 mass-bound consumption layer                 84c133c
             GATE 1 conditional assembly                         01fa0a1
2026-08-29   gamma sandwich + 1732-branch positivity sweep       195d233
             Bessel theorem accepted only under lam < 1          ef44b4c
             Bessel discharge + concrete gap-data exhibit         d75186f
             dashboard refresh through Bessel discharge           39f0f81
             eq-(119) owner gains the central n = 0 term          5aafd9f
             paper-scale audit + guards, records 1050-1054        6eacb53
             dashboard/memory/norms refresh, 1055 round           40fd6f5
             P2b verdict: semilocal prolate family DEAD           d330e90
2026-08-30   brick #1: unit-scale trace legality, F1 isolated   16b5f96
             records 1056-1058: F1 scope, CC20 tex pins, alpha    9fc97ba
             .gitattributes: LF shell scripts for WSL2            74b6203
             record 1059: 2b REVOKED, lambda(n) pinned            0e787b0
             GATE 1 delta wiring leaf + record 1060               64482b6
             alpha T1 lambda(n) candidate table + record 1061     abd9a78
             alpha T2/T3 anchor validation + record 1062          (this commit)
               (1059 lambda(n) pin CORRECTED: windowed-Fourier sqrt)
------------------------------------------------------------------------
Code frontier at this writing:
https://github.com/peter941221/Connes-Weil-RH-Proof/commit/abd9a78
```

The narrative snapshot below is retained unchanged from the previous
(2026-08-26) revision. Its frontier tables in Section 3 remain accurate for
the items they list and predate only the CC20 window-operator chain summarized
above.

> **Status as of 2026-08-26.** This repository does not contain an
> unconditional proof of the Riemann hypothesis. The no-argument theorem
> `unconditional_rh_skeleton` consumes explicit project axioms, including
> `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`.
>
> The active constructive route is the C1 same-owner route. Gate 2
> (arithmetic-to-spectral equality) is closed via the center-2 contour
> assembly. The remaining RH-level gaps are: universal W4b positivity on
> vanishing tests, the concrete cutoff/remainder and same-owner readback
> producer, and the finite-vanishing criterion/coverage root. The Stage-3
> positive-trace consumer and the right-oriented Yoshida detector exit are
> closed only as conditional consumers of those gaps. Physical Gate 3U is a
> separate diagnostic branch. The residual project-axiom ledger is recorded
> in [`RhOutputAxiomLedger.lean`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/RhOutputAxiomLedger.lean).

> **Mainline freeze (2026-08-19).** Gate 3U, Lane R, numerical probes, and
> alternative physical routes are archived/frozen. New work must name a direct
> consumer of `normalizedSelectedFinalRouteDetectorCriterionCoverageRoot`.
> The standalone finite-band deliverable is under
> [`archive/diagnostic_gate3u/`](archive/diagnostic_gate3u/).
> Run `pwsh -File scripts/check_rh_mainline_freeze.ps1` before starting new
> work; it rejects edits to frozen route namespaces by default.

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
| Gate 2 arithmetic-to-spectral equality | Closed (center-2 contour assembly) |
| Gate 3 positive trace and finite-vanishing criterion | Open (RH-level) |
| Gate 4 right-oriented Yoshida detector exit | Closed (conditional) |
| Uniform detector-data / criterion coverage | Open (RH-level) |
| SourceRH to Mathlib RH | Conditional exit |

### 1.1 Frozen historical lines of attack

The following routes are retained for provenance only. They are not an active
work queue; the active C1 status is summarized in Sections 2--3. Use
`RH_MAINLINE_FREEZE.md` for the only allowed RH consumers.

1. Connes-Weil semilocal trace formulas

   This line combines a finite set of places S, Sonin spaces, semilocal
   Fourier theory, and the Weil explicit formula on one Hilbert space. The
   repository has formalized the exact prime-power coefficient of a single
   crossing and assembled finitely many crossings into a compact self-adjoint
   operator. This is a closed finite-prime subchain; its same-object
   identification with the load-bearing semilocal metric variation and its
   sign/RH consumer remain open.

2. Yoshida zero detectors (older normalized branch)

   Yoshida's method constructs Mellin test functions aimed at a prescribed
   zero off the critical line. The repository formalizes support budgets,
   convolution-power tail reduction, finite interpolation, translation/support
   transport, and uniform quadratic decay on the critical strip. The healthy
   C1 layer now has finite-node interpolation, translation/support transport,
   and a right-oriented detector construction with a conditional RH exit on
   the same owner. The older normalized detector route is retained only for
   provenance; the active remaining issue is the global sign and criterion
   coverage input needed to make the conditional consumers unconditional.

3. Xi-function zero counting

   The project controls the completed Xi function through Mathlib's theta
   kernel and reduces the zero-summability input to geometric ball bounds in
   the right half-plane. The current C1 layer also proves exact xi-zero index
   completeness, absolute spectral summability for every compact-log test,
   finite contour/readback bricks, and the center-2 same-owner
   arithmetic-to-spectral equality. The positive-trace producer, universal
   W4b sign, and finite-vanishing coverage remain open, while the right-oriented
   detector construction is available as a conditional consumer. Quadratic
   Mellin decay requires shell growth below 4^n; the full Riemann-von Mangoldt
   asymptotic is stronger than this consumer needs.

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
   replace the current C1 Gate 3 and coverage work.

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
| Arithmetic value equals spectral value | Closed (center-2 contour) |
| Stage-3 positive-trace order consumer | Closed (conditional on `0 <= qw g`) |
| CC20 Archimedean log readback and rank-one error kill | Closed as dictionary/readback |
| W4b positivity on proper support classes | Closed (narrow class and boundary rungs) |
| Universal W4b positivity and finite-vanishing criterion | Open (RH-level) |
| Right-oriented Yoshida detector construction | Closed (conditional exit) |

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
Lean theorem, closing Gate 2. The positive-trace and finite-vanishing
criterion (Gate 3) and universal W4b positivity remain open; RH is not claimed.

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

As of 2026-08-26, the finite-prime crossing chain is a verified infrastructure
subchain, and the C1 same-owner route has closed Gate 2. The active RH
frontier is now explicit: prove the endpoint trace/sign estimate behind the
universal W4b inequality, construct the genuine cutoff/remainder/readback
producer, and discharge the finite-vanishing criterion/coverage root.

| Frontier item | State | Scope |
| --- | --- | --- |
| CompactLog to positive-coordinate bridge | Closed | C1 coordinate ownership |
| Same-owner pole, archimedean, and prime readback | Closed | Definition/readback only |
| Exact xi-zero index and spectral summability | Closed | Every compact-log test |
| Gate 2 arithmetic-to-spectral equality | Closed | Center-2 contour assembly |
| Positive-trace order consumer (Stage-3 P3-a) | Closed | Rank-one correction, conditional on `0 <= qw g` |
| CC20 Archimedean readback + rank-one error kill | Closed | Endpoint certificate interface only |
| CC20 finite-dimensional trace/determinant algebra | Closed | Shifted coercivity brick; no spectral/trace estimate |
| CC20 endpoint coefficient arithmetic band | Closed | `13 < 4γ/log 2 < 17` from explicit gamma bounds; spectral source open |
| Yoshida finite-node interpolation + right-oriented detector | Closed | Same-owner conditional exit |
| W4b positivity on narrow class + boundary rungs | Closed | Proper support classes (`exp(-7)`, `exp(-13/2)`, `exp(-63/10)`) |
| W4b universal positivity over all vanishing tests | Open | RH-level |
| Concrete cutoff remainder/readback producer | Open | Stage-3 remainder and same-owner trace estimate |
| Finite-vanishing Weil criterion on the same owner | Open | Gate 3, RH-level |
| Detector-data / criterion coverage root | Open | RH-level coverage axiom is still consumed by the skeleton |
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

Gate 2 is closed: the center-2 contour assembly proves the same-owner
arithmetic-to-spectral equality as an axiom-clean Lean theorem
([`gate2ExplicitFormula_centerTwo`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L240)).
The next load-bearing statement is the W4b universal positivity

$$
0 \le \mathrm{C1SameOwnerWeil.qw}(g)
\qquad
\text{for every vanishing test } g.
$$

The Stage-3 windowed trace (Program P step 2) reduces the positive-trace
criterion to this single premise:
[`positiveTracePairLimitFamily_of_rankOneCorrection`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1Stage3WindowedTraceP3a.lean#L379)
assembles a full `PositiveTracePairLimitFamily` for each test, conditional on
`0 <= qw g`. This is a sign-transparent consumer, not an analytic proof of
that premise. The CC20 Archimedean readback closes the log-coordinate
dictionary and kills the rank-one error under triple vanishing; its
[`CC20EndpointTraceCertificate`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L94)
still requires a nonnegative endpoint trace and the bound
`trace - c * |g-hat(0)|^2 <= W-infinity(g-square)`. Supplying that certificate
is the remaining Archimedean sign/trace theorem.

W4b is closed on a narrow class (triple vanishing + bounded Hermitian-square
support) and on three boundary-guided rungs
(`exp(-7)`, `exp(-13/2)`, and `exp(-63/10)`), plus the earlier algebraic
`widerArchRadius` rung
([`qw_nonneg_of_vanishesOn_cc20Triple_of_budget_window`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1SpectralNarrowW4b.lean#L171)).
The reduction
[`qw_nonneg_of_forall_real_vanishing`](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/ConnesWeilRH/Dev/C1SpectralRealPair.lean#L658)
collapses the universal obligation from complex to real vanishing tests; the
sign bound on real vanishing tests remains the open W4b gap. The published
root-support window `Icc(-log 2 / 2, log 2 / 2)` is still much wider than these
rungs; the endpoint theorem is the first-cut target. A square-support version
would additionally need a Titchmarsh convolution bridge, which is deliberately
deferred.

| Route brick | State | Limitation |
| --- | --- | --- |
| Gate 2 center-2 contour assembly | Closed | Axiom-clean, `4147/4147` |
| Stage-3 rank-one correction (Program P step 2) | Closed | Conditional on `0 <= qw g`; no analytic producer |
| CC20 Archimedean readback + rank-one error kill | Closed | Endpoint trace certificate still required |
| W4b narrow-class instance | Closed | Proper support class, not universal |
| W4b boundary-guided rungs (`exp(-7)`, `exp(-13/2)`, `exp(-63/10)`) | Closed | Each a proper support class |
| W4b reduction to real vanishing tests | Closed | Sign bound on real tests still open |
| W4b universal positivity over all vanishing tests | Open | RH-level; endpoint sign theorem |
| Concrete cutoff remainder/readback producer | Open | Stage-3 remainder and same-owner trace estimate |
| Finite-vanishing Weil criterion on the same owner | Open | RH-level |

The finite-prime crossing operator in Section 2.4 remains useful as a
coefficient and compactness check. The intended implication after W4b and the
remainder are closed is

$$
0 \le \mathrm{C1SameOwnerWeil.qw}(g)
\Longrightarrow
\text{positive trace}
\Longrightarrow
\sum_v W_v(F_g)\le 0
\Longrightarrow
\mathrm{RH}.
$$

### 3.2 Representative obstructions

The route boundary is split into current blockers and historical rejected
constructions. The active blockers are W4b universal positivity, the concrete
cutoff remainder/readback producer, and the finite-vanishing Weil criterion on
the same owner. Gate 2 and Yoshida detector construction are now closed.

Current blockers:

| Route | Current gap | Record |
| --- | --- | --- |
| W4b universal positivity | The endpoint trace estimate / Archimedean sign theorem is not proved; the narrow class and boundary rungs cover only proper support classes | [proof 1040](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1040_hqw_sign_attack.md), [proof 1043](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1043_first_cut_window_architecture.md) |
| CC20 endpoint trace certificate | The log-coordinate readback and rank-one error-kill consumer are proved, but the nonnegative endpoint trace and `trace - error <= W-infinity` bound are still analytic obligations | [proof 1043](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1043_first_cut_window_architecture.md) |
| Concrete cutoff remainder/readback | The Stage-3 positive-trace consumer is closed only conditionally on `0 <= qw g`; the cutoff remainder estimate is not supplied | [proof 1038](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1038_positive_trace_producer_design.md), [proof 1016](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1016_plain_window_trace_family_verdict.md) |
| Bare whole-line HS obstruction | The bare whole-line HS premise is false for every nonzero test; only a windowed or renormalized detector can remain viable | [proof 1016](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1016_plain_window_trace_family_verdict.md) |
| Finite-vanishing Weil criterion on the same owner | The same-owner finite-vanishing criterion is an RH-level gap; Gate 3 positive-trace remains open | [proof 1005](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1005_rh_route_after_psp_audit.md) |
| Infinite-carrier Gate-3U | The required physical cancellation identity is open; finite-band decay does not close the infinite carrier | [proof 1005](https://github.com/peter941221/Connes-Weil-RH-Proof/blob/main/docs/proofs/1005_rh_route_after_psp_audit.md) |

The cutoff gap is structural, not a missing `trace-class` annotation. The bare
whole-line Hilbert--Schmidt owner is ruled out for every nonzero test, and the
canonical finite-window trace has a linearly growing bulk. The insertion defect
has only a uniform compression bound, while the window-to-response defect can
have an unbounded real trace even for a bounded response. A viable producer
therefore needs an explicit finite-part/renormalized or otherwise new detector
owner, together with a genuine remainder and same-owner readback estimate.

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
must preserve one C1 owner and the closed arithmetic-to-spectral equality, then
fill the endpoint certificate, establish universal W4b positivity, and supply
the concrete cutoff remainder/readback needed by the positive-trace consumer.
The finite-vanishing criterion and detector-coverage root must then be discharged
on that same owner before the conditional `SourceRH` exit can become an
unconditional theorem.

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
