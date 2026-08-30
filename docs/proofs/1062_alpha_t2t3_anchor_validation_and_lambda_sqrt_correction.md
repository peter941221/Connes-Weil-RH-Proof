# 1062 - The T2/T3 anchor test failed on purpose and found the real convention: lambda(n) is the WINDOWED FOURIER eigenvalue, the square root of everything 1061 computed

Date: 2026-08-30.  Follows 1059 (convention pin - now CORRECTED by this
record), 1061 (T1 table - raw data still valid, interpretation amended).
Probe: `docs/proofs/1062_alpha_t2t3_mode_anchor_probe.py`, runner
`scripts/run_1062_probe.sh`, log `/home/peter/cc20/probe1062.log`.

Result up front: **GOOD, with a correction of record.**  The probe set out
to validate the mode dictionary against the contract's own
`endpointSlope_eq_spectral` identity.  The ODE falsification gate passed
at 1e-33 (the sinc-extension really is the paper's `analyticMode`, with
continuation across the regular-singular x = 1 automatic - the integral
representations E1 = (1/lam) int K(x-y) xi(y) dy and E2 = (1/lam) F xi
coincide because both are entire and agree on the window).  But the anchor
sum came out **5.37903498198, not the published 22.9965** - and chasing
that mismatch through the raw tex found that the 1059 pin was a
square-root off:

```text
THE CORRECTION (tex:967-983 re-read verbatim):
  prolateeq   int_{-1}^{1} PS_{2n,0}(2pi,x) e^{i 2 pi x w} dx = lambda(n) PS_{2n,0}(2pi,w)
  cosalphan   P_1 FOURIER P_1 phi_n       = lambda(n)   P_1 phi_n     <-- SINGLE Fourier
  cosalphan1  P_1 P^_1  P_1 phi_n          = lambda(n)^2 P_1 phi_n     <-- the SQUARED one
  The collocation kernel sin(2 pi (x-y))/(pi (x-y)) of 1058/1061 is the
  kernel of P F P F (the composition), so the 1061 "lambda(n)" table is
  the paper's lambda(n)^2.  Paper list (tex:972-975):
  lambda = [0.999971, -0.979485, 0.524086, -0.0589766, 0.00273233, -7.63e-5]
         = (-1)^n * sqrt(the 1061 concentration table)   - exact match n<=5
  innerltwoeven (tex:249): <eta|xi> = 1/2 int_R = int_0^oo, so the paper's
  unit-norm xi is sqrt(2) x the standard-L2 xi computed by the probe.
```

With those two factors, contract term t(n) = (mu^2/(1-mu^2)) * xi^an(1)^2
= [lam_c/(1-lam_c)] * 2 * xi_probe(1)^2 reproduces the paper's own printed
term list digit for digit, and the sum hits the anchor.

## 1. Corrected table (dps 60, M = 44; anchor stability |S44-S56| = 2.9e-56)

```text
n   mu(n) = (-1)^n sqrt(lam_c)   weight_p = mu^2/(1-mu^2)   t(n)         paper's t(n)
0   +0.999971376267              17467.27232                11.97193235  11.9719    (rel 2.7e-6)
1   -0.979484734668                  23.6246862              8.775743151   8.77574   (rel 3.6e-7)
2   +0.524085896228                   0.378675254            2.205276321   2.20528   (rel 1.7e-6)
3   -0.0589765891824                  0.003490378439         0.04339828243 0.0433983 (rel 4.1e-7)
4   +0.00273232874312                 7.465676096e-6         1.254589747e-4 0.000125459 (rel 2.0e-7)
5   -7.62913592837e-5                 5.820371535e-9         1.216555164e-7   -
...  (to n=10; t decays below 1e-14 by n=7)
    SUM n<=10 = 22.9964756839   vs published eps'(1+) ~ 22.9965   [MATCH]
```

Independent float64 leg (numpy eigh, M=600) reproduces the same anchor
5.379035 in the old convention; cross-M stability of the sum is 2.9e-56.
(The A3 "worst relative disagreement 2.0" line is an eigenvector SIGN
flip of xi_3 between M=44/56 - vacuous for squared quantities.)

## 2. What survived and what changed from 1061

```text
+--------+--------------------------------------------------------------+
| 1061   | status after 1062                                            |
+--------+--------------------------------------------------------------+
| the    | UNCHANGED - the concentration eigenvalues lam_c(n) ARE the   |
| table  | paper's lambda(n)^2; the dps-60 candidate table remains the  |
|        | raw data of the campaign                                     |
| weight | SUPERSEDED - contract weight is lam_c/(1-lam_c), not the     |
| column | printed lam_c^2/(1-lam_c^2); mode-0 weight 17467.3 not 8733.4|
| margins| HALVED at mode 0: eigenvalue_sq_lt_one needs 1-mu^2 =        |
|        | 1-lam_c: mode 0 margin 5.7247e-5 (was quoted 1.1449e-4 =     |
|        | 1-lam_c^2), mode 1 margin 4.0610e-2                          |
| (983)  | RE-VERIFIED for |mu| directly (probe F3, n<=5 all hold;      |
| split  | bound(2)=0.75394<1 monotone => n>=2 discharged by (983)      |
|        | alone exactly as before, now applied to the right quantity)  |
| T2/T3  | CLOSED numerically: extension = analyticMode (ODE residual   |
|        | 1e-33), continuation across x=1 automatic, anchor validated  |
+--------+--------------------------------------------------------------+
```

## 3. The falsification machinery that made the mismatch trustworthy

Three independent gates had to pass before the anchor mismatch could be
read as "convention bug" rather than "numerics bug" - and they all did:

- (C) SL ODE residual ((1-x^2)y')' + (chi - c^2 x^2)y = 0 on the extension
  at x = 0.5, 1.5, 2 for n = 0,1,2: max relative 4.4e-32.  This pins the
  eigenvectors, the sqrt2 pairing, the chi_n commutant table (MP rebuilt,
  basis 28, matches 1061 float64 to all shown digits), and the extension
  formula simultaneously.
- (A2) anchor sum cross-M stability 2.9e-56 - the 5.379 was not noise.
- (D) float64 independent implementation agrees to 7 digits.

The paper's own per-term list (tex after (Rokh)) then confirmed the
correction unambiguously: t(3) = 0.0433983 reproduced to 4e-7 relative.

## 4. Consequences for the campaign plan

- The contract instance's `eigenvalue : Nat -> Real` is the SIGNED mu(n) =
  (-1)^n sqrt(lam_c(n)); the enclosure bricks B2 target
  1 - mu(0)^2 > 0 with margin budget < 5.7e-5 (not 1.1e-4) and the n>=2
  brick B1 quotes (983) at |mu| (bound(2) = 0.75394 < 1).
- analyticMode data for T3 is now in hand for the slope layer: the
  endpointSlope value itself is validated (22.9965); what remains for a
  Lean instance is the enclosure package (interval radii for lam_c and
  xi(1), the (983)^2-free route via |mu| <= b(n) < 1, and the
  innerltwoeven normalization as an explicit identity lemma).
- (Rokh) |xi_n(1)| <= sqrt(2n+1/2) (tex:1377, from Rokhlin Thm 12) holds
  on every computed value (max 2.4933 at n=3 vs bound 2.5495) - a
  ready-made structural bound for the summability brick T4.
- The 1059 pin and the 1061 interpretation get AMENDMENT sections pointing
  here; neither record is deleted (the 1059 lesson - test derived
  quantities before booking a convention - is what produced this catch:
  the mismatch 5.379 vs 22.9965 was findable the moment the anchor was
  wired to the contract identity, which is exactly what 1061 s1
  prescribed and this probe executed).

## 5. Sources

```text
weil-compo.tex (sha256 b01d353b..., 1057 s0 pin) lines:
  940-995   prolateeq/cosalphan/cosalphan1 + the printed lambda(n) list
  249       innerltwoeven normalization
  997-1060  devil0 mode dictionary
  1340-1412 propQe, sonineQ/sonineQbis, the epsilon' lemma, the printed
            t(n) list and 22.9965, quadform/opkf
probe log: /home/peter/cc20/probe1062.log (rerun: scripts/run_1062_probe.sh)
docs/proofs/1059 s4 (the pin being corrected), 1061 (raw table)
```
