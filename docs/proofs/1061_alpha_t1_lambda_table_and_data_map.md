# 1061 - Alpha campaign slice T1: the lambda(n) candidate table converges, and the contract's eigenvalue obligation splits

Date: 2026-08-30.  Follows 1058 (shape), 1059 (convention pinned), 1060
(delta contract wired).  Probe:
`docs/proofs/1061_alpha_lambda_t1_probe.py`, runner
`scripts/run_1061_probe.sh`, log `/home/peter/cc20/probe1061.log`.

Result up front: **GOOD.**  The 11 candidate eigenvalues of the paper's
lambda(n) (even branch, c = 2 pi, convention 1059 s4) are computed in
mpmath at dps 60 with 33-80 digits of cross-truncation stability
(M = 44 vs M = 56), and the Lean contract `CC20EndpointSpectralData`
(EndpointKernelFormula.lean:38) turns out to need far less than a full
enclosure campaign for its eigenvalue part: the obligation
`eigenvalue_sq_lt_one` SPLITS into {n >= 2: discharged by the paper's own
bound (983) < 0.754 < 1, monotone} + {n = 0, 1: numerically enclosed with
margins 1.145e-4 and 7.957e-2, i.e. 26 orders above the numerical noise}.
This is the first slice where the alpha long pole has concrete data targets
with concrete error budgets.

## 1. The contract -> data-target map (what the instance must supply)

Read from `ConnesWeilRH/Source/CC20Concrete/EndpointKernelFormula.lean`:

```text
+---------------------------------------------------------------------+
| target | contract object            | what it is          | status  |
+--------+----------------------------+-------------------+----------+
|  T1    | eigenvalue : Nat -> Real   | lambda(n), paper   | THIS    |
|        |  + eigenvalue_sq_lt_one    | lambda_{2n}^{2pi}  | RECORD  |
|--------+----------------------------+-------------------+----------|
|  T2    | analyticMode n x           | xi_n^an(x) and     | OPEN   |
|  T2'   | analyticModeDeriv n x      | (xi_n^an)'(x) on   | (ODE   |
|        |                            | [1/2, 2], incl.    | slice) |
|        |                            | continuation of    |        |
|        |                            | the prolate SL ODE |        |
|        |                            | ACROSS x = 1 (a    |        |
|        |                            | regular-singular   |        |
|        |                            | point; PS is the   |        |
|        |                            | regular solution)  |        |
|--------+----------------------------+-------------------+----------|
|  T3    | endpointSlope              | epsilon'(1+) =     | OPEN   |
|        |  + endpointSlope_eq_spectral| tsum weight*mode(1)^2 | (needs T2) |
|        |  + endpointSlope_pos       | published anchor   |        |
|        |                            | 22.9965 (tex:219)  |        |
|--------+----------------------------+-------------------+----------|
|  T4    | endpointSlope_summable     | weight_n =         | HALF-  |
|        |                            | lambda^2/(1-lambda^2)| OPEN |
|        |                            | dominated by (169):|        |
|        |                            | weight_11 ~ 2.4e-65|        |
|        |                            | vs published tail  |        |
|        |                            | majorant 2.353e-12 |        |
+--------+----------------------------+-------------------+----------+
```

Mode dictionary for T2 (tex:997-1049, devil0): xi_n = P_1 phi_n /
‖P_1 phi_n‖ with phi_n the even prolate angular functions PS_{2n,0}(2pi, .)
and P_1 = chi_{[-1,1]}; the SL eigenvalues chi_n the ODE consumes are in
section 3 below.

## 2. T1 candidate table (dps 60, cross-M stable >= 33 digits)

```text
n   lambda(n)            weight_n = l^2/(1-l^2)   1 - lambda^2
0   0.999942753354       8733.386168              1.144900146e-4
1   0.959390345448       11.56752451              7.957016506e-2
2   0.274666026625       8.159723820e-2           9.245648e-1
3   3.478238071580e-3    1.209828645e-5           9.999879017e-1
4   7.465620360490e-6    5.573548737e-11
5   5.820371501360e-9    3.387672441e-17
6   2.072073566870e-12   4.293488867e-24
7   3.851190779710e-16   1.483167042e-31
8   4.100679551890e-20   1.681557279e-39
9   2.680155263000e-24   7.183232234e-48
10  1.134386458490e-28   1.286832637e-56
```

Evidence quality:
- cross-truncation agreement M=44 vs M=56: max |diff| = 4.98e-60 at the
  top modes; per-mode stable digits [80, 80, 58, 58, 57, 53, 50, 46, 42,
  38, 33];
- external anchor: 1058 block B2 float64 M=800 values agree to 9.7e-8
  relative for n <= 5;
- (983) verified on the branch for all n = 0..10;
- ALL modes (even the float64-invisible n = 8..10) decay as the (169)
  comparison requires: the last measured ratio lambda_10/lambda_9 =
  4.23e-5, and the paper's (169) term_11 = 2.353e-12 MAJORIZES the true
  weight_11 ~ 2.5e-65 by 50+ orders - the published tail is extremely
  conservative, which is good news for the enclosure budget.

## 3. The SL spectrum for T2's ODE (commutant, float64, positivity fixed)

The commutant L = -d/dx((1-x^2)d/dx) + (2pi)^2 x^2 has an EXACT sparse
Legendre-basis matrix; its even-branch eigenvalues (the chi_n the angular
ODE needs) are

```text
chi_n (n=0..5) = [5.494094, 26.834164, 42.916034, 63.158589,
                  92.517013, 130.238912]
```

Sanity: chi_0 = 5.494 matches the large-c asymptotic c - 0.789 at c = 2pi,
and the operator is positive on the branch.  First-attempt note (honesty
ledger): a hand-written x^2-Legendre coefficient formula mis-signed beta_0
and produced chi_0 = -13.4 (negative eigenvalue of a positive operator);
the probe now builds x^2 as the SQUARE of the multiplication-by-x
tridiagonal from the Bonnet recursion - no closed forms, and the positivity
check is a hard gate.  A second first-run artifact: a module-level constant
`OMEGA = 2*pi` frozen at import-time dps 15 silently capped every kernel
evaluation and faked a 5e-18 eigenvalue plateau for n >= 6; fixed by
evaluating 2*pi inside the kernel.  Both are AGENTS 7c-style fidelity laws
reasserting themselves: every "surprising saturation" in a validated
pipeline is a bug report from the numerics, not data.

## 4. What T1 rigorization still needs (Lean side, next bricks)

```text
B1  eigenvalue_sq_lt_one for n >= 2: formalize the paper's bound (983) in
    Lean (gamma/factorial ratio machinery already exists in the (169)
    comparison file family) and a monotonicity/norm_num lemma that
    bound(2) < 1 and bound decreases.  Pure arithmetic, no numerics.
B2  lambda(0), lambda(1) enclosures: certified interval eigenvalue
    (interval Taylor on the collocation matrix or a Kato-temple style
    bracket from the commutant) with radius < 5e-5 (mode 0) - the first
    real validated-numerics certificate of the campaign.
B3  the eigenvalue FIELD itself: lambda : Nat -> Real is given by a closed
    definition (concentration eigenvalue of P_1 F P_1 on L^2(R)_ev), so
    B1/B2 are theorems ABOUT that definition, not assertions of numbers;
    the definition brick comes before B1.
```

T2 (modes + continuation across the regular-singular point x = 1) is the
next probe slice: it needs the interval-Taylor machinery (yoshida_intervals
pattern) pointed at the angular prolate ODE with the chi_n above, and the
dictionary xi_n = P_1 phi_n / ‖P_1 phi_n‖ in positive coordinates.
T3/T4 then follow from T2 + (169)/(170).

## 5. Sources

```text
ConnesWeilRH/Source/CC20Concrete/EndpointKernelFormula.lean:38-135
  (the contract, read verbatim this session)
CC20 tex:214-219 (epsilon series + eps'(1+) ~ 22.9965), 967-983
  (lambda(n) convention + (983) bound, 1059), 997-1049 (devil0 mode
  dictionary), 2239-2250 (eq-(169)/(170) tail, 1057 s3)
probe log: /home/peter/cc20/probe1061.log (deterministic, rerun via
  scripts/run_1061_probe.sh)
docs/proofs/1058 (collocation floor history), 1059 s4 (convention pin)
```

## AMENDMENT (record 1062, same day) - the table survives, the mapping is by SQUARE ROOT

Section 1-2's candidate table is the concentration spectrum lam_c(n) =
the paper's lambda(n)^2 (not lambda(n) itself - 1059 s4's mispin
inherited here); section 2's weight column (lam_c^2/(1-lam_c^2)) is NOT
the contract weight, which is mu^2/(1-mu^2) = lam_c/(1-lam_c); the
"enclosure margins 1.1449e-4 / 7.957e-2" are the SQUARE-ROOT-SCALED
margins (true 1-mu^2 margins: 5.7247e-5 / 4.0610e-2).  The eigenvalue
split SURVIVES in corrected form: |mu(n)| <= (983) bound(n) with
bound(2) = 0.75394 < 1 monotone discharges eigenvalue_sq_lt_one for
n >= 2, leaving modes 0-1.  Section 3's chi_n table and section 4's B1-B3
plan stand (B2's error budget tightens to < 5.7e-5).  The T2/T3
continuation and anchor layers were then closed numerically by 1062
(endpointSlope = 22.9964756839, per-term t(n) matched to the paper's
printed list, ODE residual 1e-33 validating analyticMode and sqrt2
normalization).  See
docs/proofs/1062_alpha_t2t3_anchor_validation_and_lambda_sqrt_correction.md.
