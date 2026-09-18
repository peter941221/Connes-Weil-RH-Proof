# 1634 — O1 opened: the defect is a one-sided convolution vanishing, and the asymptotic proportionality law (Erratum G on 1633's tail law)

Date: 2026-09-18. Round: item `O1` of the 1633 hand-off, first stage. No Lean
brick; two scripts land (`scripts/carrier_rational_1634.py`,
`scripts/carrier_limit_1634.py`).

Read with: 1633 (the hand-off and law F53, now demoted), 1630 (the probe),
1632 (the ε-gap), 1627 (no finite-type witness), 1629 (the Toeplitz form).

## 1. Verdict block

```text
(A) EXACT       The defect is a one-sided convolution vanishing.  With
    REFORMULATION  v = F^{-1}(m(-.) Hhat) = K * h,  K = F^{-1}(m(-.)),

                D^2(lambda, H) = INT_{-inf}^{c} |v(y)|^2 dy / INT |v(y)|^2 dy,
                c = 2 log lambda,

                carrier(lambda) != {0}  <=>  exists h != 0 in L^2((-inf,0])
                with (K * h) vanishing on (-inf, c).

                Pure change of variables (y = x + c), no approximation.
                Model m := 1: K = delta and the condition is "supp h in
                [c, 0]" -- the finite-type witness.

(B) ERRATUM G   1633's tail law (F53: the defect is governed by the Hhat tail
                above xi_c = lambda^{-2}) is REFUTED.  On the rational family
                the measured real exponent equals the MODEL exponent
                2 - 2(k-1)/|c| to two decimals (k = 3: 1.78/1.78, 1.80/1.80,
                1.82/1.82, 1.83/1.83; k = 4: 1.68/1.67, 1.70/1.70, 1.72/1.72,
                1.74/1.74) while the tail law predicts 2k-1 = 3 and 5 and 7.
                The 1633 "slope match" compared two different quantities that
                happen to have the same order of magnitude inside the window.

(C) LAW F56     PROPORTIONALITY.  D_real / D_model -> c = 0.080, and c is
                k-INDEPENDENT: k = 3 reads 0.0806 constant over five scales,
                k = 4 reads 0.0794 -> 0.0801, k = 2's resolved rows read
                0.0815 - 0.0836.  Numerically c is close to 1/(4 pi) = 0.0796
                (CONJECTURE, not claimed).  So the multiplier m(-xi) acts
                asymptotically as a CONSTANT-AMPLITUDE version of the free
                shift; it is not a new obstruction (consistent with 1633's
                F54, real < model floor, c < 1).

(D) MODEL EXACT The model defect is exactly  Gamma(2k-1, 2|c|)/Gamma(2k-1)
                (squared), verified against the grid to 1.5e-16 at k = 1 and
                to quadrature accuracy (<= 3e-3) at k = 2, 3, 4; asymptotics
                D_model ~ lambda^2 |c|^{k-1}/sqrt(Gamma(2k-1)).

(E) RIG LIMIT   The compact-support (finite-type) residual is NOT resolvable
    F57         by an FFT-modulation rig: the MODEL itself reads 1e-9 (W = 1)
                and 1e-15 (W = 4) there, i.e. the fractional-shift aliasing
                floor of non-band-limited data, not zero.  Conclusion: the
                1627 obstruction must be probed with rational families
                (algebraic spectrum, live model floor), never with bumps.

(F) OBLIGATIONS O1' is now the POSITION form: prove
                D_real(H, lambda) <= (c + o(1)) sqrt(mass of h on (-inf, 2log lambda))
                + (H-dependent, lambda-uniform error), an FIO localization
                estimate for the shear y = x + (2 pi)^{-1} gamma'(-xi).
                O2 (uniformity) and O3 (kernel forcing) unchanged.
```

## 2. The reformulation, in one line of calculus

With F(h)(ξ) = ∫h(x)e^{−2πixξ}dx and u = F⁻¹(U_λĤ), U_λ(ξ) = e^{2πicξ}m(−ξ):

```text
u(x) = INT m(-xi) Hhat(xi) e^{2 pi i (x + c) xi} dxi = v(x + c),
v    = F^{-1}(m(-.) Hhat) = K * h,        K = F^{-1}(m(-.)).
```

So the defect — the mass of u on x < 0 — is the mass of v on x + c < 0, i.e.
on y < c:

```text
D^2 = INT_{-inf}^{c} |v(y)|^2 dy / ||v||^2,      c = 2 log lambda.
```

Everything in 1633 (the "landing of frequency ξ at x = −(log|ξ| + 2logλ)")
was a stationary-phase reading of this single identity. The identity itself
needs no stationary phase, and it makes the carrier a statement about a
convolution vanishing on a half-line — the form in which the classical
"one-sided convolution equation" tools can be brought to bear.

## 3. The rational family and the measurement

Trial functions with an ALGEBRAIC spectral tail (the C^∞ bump's tail is
super-exponential and was eaten by the |ξ| ≤ 64 window, which is what made
1633's slopes window-limited):

```text
Hhat_k(xi) = (1 - 2 pi i xi)^{-k},    h_k(x) = e^x x^{k-1}/(k-1)! 1_{x<0},
||Hhat_k||^2 = (1 + 4 pi^2 xi^2)^{-k},  tail ~ xi_c^{1-2k}   (algebraic),
D_model^2 = Gamma(2k-1, 2|c|) / Gamma(2k-1)   (exact, verified).
```

Translate direction matters: the model defect of h(·−s) is the mass of h on
(−∞, c−s), which DECREASES in s. The first draft used a leftward-only family
and its k = 2 row broke at |c| ≈ 14; the committed rig shifts right,
s ∈ {0, 1, …, 8}, and reports both the family minimum and the single vector
s = 0.

```text
k = 3   +---------+---------+--------------+--------------+----------+---------+---------+
        | lambda  |  |c|    |  D_model     |  D_real      | ratio    | p_model | p_real  |
        +---------+---------+--------------+--------------+----------+---------+---------+
        |  0.0100 |   9.210 |   8.5826e-06 |   6.9217e-07 |   0.0806 |     -   |    -    |
        |  0.0050 |  10.597 |   2.4938e-06 |   2.0109e-07 |   0.0806 |   1.78  |  1.78   |
        |  0.0020 |  12.429 |   4.7907e-07 |   3.8619e-08 |   0.0806 |   1.80  |  1.80   |
        |  0.0010 |  13.816 |   1.3613e-07 |   1.0970e-08 |   0.0806 |   1.82  |  1.82   |
        |  0.0005 |  15.202 |   3.8383e-08 |   3.0925e-09 |   0.0806 |   1.83  |  1.83   |
        +---------+---------+--------------+--------------+----------+---------+---------+

k = 4   ratio 0.0794, 0.0797, 0.0799, 0.0800, 0.0801;  p_model = p_real
        at every row (1.68/1.67, 1.70/1.70, 1.72/1.72, 1.74/1.74).

k = 2   the family MINIMUM is contaminated by the aliasing floor (~1e-6, the
        first rows have ratio 1.32 / 0.95 / 2.62 while D_real hovers at 1e-6);
        the single vector s = 0 is clean for |c| <= 12.4 and reads
        0.0815, 0.0816, 0.0836, then drifts as D_real reaches the floor.

k = 1   excluded: h_1 jumps at x = 0, and the DFT fractional shift of a
        discontinuous datum carries an O(fractional part) error, so its small
        readings are artefacts (visible as D_real at lambda = 0.02 exceeding
        the exact model value).
```

Two independent readings agree on the exponent law:

```text
p_model = d log D_model / d log lambda = 2 - 2(k-1)/|c|     (exact asymptotics)
measured p_real = p_model to two decimals on 8 of 8 clean rows.
```

## 4. What the law means, and what it does not

Means: for every FIXED h ∈ L²((−∞,0]) the real defect is asymptotically the
free-shift position defect — the mass of h below the receding threshold
c = 2logλ — times a universal constant ≈ 0.080 < 1. Hence

```text
inf over H of D_real(H, lambda)  ->  0    as lambda -> 0,
```

quantitatively, with an explicit rate λ²|c|^{k−1} on the rational families.
The carrier's "angle" is 0; the multiplier contributes a constant loss, not a
growth. This strengthens 1633 (D) from a qualitative collapse to a rate law.

Does NOT mean: attainment. The proportionality is measured on families with
UNBOUNDED support, where the model defect itself tends to 0. On compactly
supported h the model defect is exactly 0, so a proportionality law of this
shape says nothing about the residual — and 1627 proves that residual is
nonzero at every λ. The gap between "the model defect is 0" and "the real
defect is 0" is exactly the ε-gap; nothing in this round moves it, and the
finite-type residual is below the rig floor (E). No claim about the carrier,
the gate, or RH.

## 5. Laws added / amended

```text
F56  PROPORTIONALITY.  D_real(lambda, h_k)/D_model(lambda, h_k) -> c = 0.080
     (k-independent for k = 2, 3, 4, constant to four digits over five scales
     at k = 3).  The multiplier is asymptotically a constant-amplitude free
     shift on these families.  Numerically c ~ 1/(4 pi) = 0.0796: CONJECTURE.
F57  An FFT-modulation rig cannot resolve the compact-support residual: the
     model reads the fractional-shift aliasing floor (1e-9 at W = 1, 1e-15 at
     W = 4), not zero.  Probe the finite-type obstruction with RATIONAL
     families (algebraic spectrum + live model floor), never with bumps.
F58  A translate family must shift in the FAVOURABLE direction (rightward for
     this defect: the model defect is the mass of h on (-inf, c - s), which
     decreases in s).  A leftward-only family reports the family's badness,
     not the object's.

ERRATUM G  1633's F53 (critical-frequency TAIL law) is REFUTED: the decay
     follows the position law lambda^2 |c|^{k-1}, and the measured exponent
     equals the model exponent, not 2k-1.  F52, F54, F55 of 1633 stand; the
     xi_c = lambda^{-2} identity remains a correct stationary-phase READING of
     the reformulation but is NOT the decay mechanism.
```

## 6. Obligations, revised

```text
O1'  Position/FIO form.  Prove, for h in L^2((-inf,0]),
         D_real(lambda, h) <= (c0 + o(1)) sqrt(mass of h on (-inf, 2 log lambda))
                             + E(h, lambda),
     where the canonical relation of T = F^{-1} M_{m(-.)} F is the shear
     y = x + (2 pi)^{-1} gamma'(-xi) = x + log|xi| + O(1)  (monotone in xi),
     c0 is the amplitude constant the rig measures at 0.080, and E is
     lambda-uniform in the sense of O2.  This is a localization estimate for
     a Fourier integral operator of shear type, not a tail estimate.
O2   Uniformity of E: decide whether E can be made o(1) uniformly over the
     unit sphere of H^2(C_+) as lambda -> 0.  Uniformity converts the base
     into a small-perturbation problem (O3); non-uniformity IS the epsilon-gap.
O3   Only under O2: force a nonzero kernel of P_- U restricted to H^2(C_+).
```

## 7. Next steps

1. Fit the constant c0 on more families (different decay rates; two rational
   families superposed) to test universality and the 1/(4π) conjecture.
2. Prove the amplitude constant: the shear FIO's leading symbol evaluated at
   the stationary point gives a closed-form candidate for c0 — compare with
   0.080.
3. Test O2 numerically: measure sup over a family of D_real/(model defect)
   as λ ↓ 0 and look for a non-uniform blow-up (the ε-gap's signature).