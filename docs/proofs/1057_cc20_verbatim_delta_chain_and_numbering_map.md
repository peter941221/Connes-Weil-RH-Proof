# 1057 - CC20 verbatim pass: the delta chain, the numbering map, and the appendix that de-risks alpha

Date: 2026-08-30.  Follows 1044, 1046, 1049-B, 1056.  Primary source: the raw
arXiv e-print of arXiv:2006.13771, `weil-compo.tex`, fetched this session
(`scripts/fetch_cc20.sh`), replacing the 1049-B HTML sweep with the literal
tex source.

Status:

```text
GOOD NEWS (1): the repo's equation-number references are EXACTLY right on
the raw tex source.  Independent count of numbered equation environments:
total 170; eq-(115) = `computerverif` (tex:1556); eq-(119) = `opT`
(tex:1614); eq-(121) = `opTbound` (tex:1628).  No off-by-one risk remains.

GOOD NEWS (2): alpha's tail is self-funded by the paper.  Appendix lem
`lemesti`, eqs (169)-(170) (tex:2239-2250) give Q epsilon(rho) as an
ELEVEN-TERM explicit series plus a closed-form remainder <= 2.366e-12 on
rho in [1,2].  The Fact-1 justification (tex:1566-1568) says explicitly
that chi may be replaced "without any loss" by the first 11 terms.  The
alpha brick is therefore an 11-mode validated-ODE campaign, not an
infinite-spectral revival.  Probe verdict in docs/proofs/1058.

FLAG: the intro theorem and the final theorem state DIFFERENT vanishing
conditions (section 5 below).  The GATE 1 assembly must match the one it
consumes.
```

Provenance:

```text
e-print sha256   771a004b70fb0c36cae11351bd29cec50b3da13896bb1ef5015bbdd68beadb6d
weil-compo.tex   b01d353b0423b6fedee373c3c33fe3678eea733f62049810750f6c64ef20f3fc
title            "Weil positivity and Trace formula the archimedean place" (tex:69)
```

## 1. Numbering map (label -> rendered number -> tex line)

| Label | Eq # | tex line | Role on our route |
| --- | --- | --- | --- |
| `quadform` | 103 | 1405 | Proposition propcompact quadratic form |
| `opkf` | 104 | 1409 | K_I definition |
| `Eprimeqq` | 105 | 1437 | discrete form Q_q(xi) |
| `toeplitzQ` | 106 | 1449 | Toeplitz matrix of Q epsilon(q^k) |
| `tableangles` | 109 | 1484 | first 25 alpha_j (alpha_1 = 1.33371 exceptional) |
| `tableds` | 112 | 1517 | d(1) = 1.17111, d(2) = 1.12443, ... -> 1 |
| `approx0` | 114 | 1548 | tau(lambda, alpha, d, m) trigonometric profile |
| `computerverif` | **115** | 1556 | `2 * integral_0^{log 2} |tau - chi| ~ 0.00122` |
| `opT` | **119** | 1614 | `T = lambda * sum_{n in Z} (p_n - d(|n|) p_{alpha_n})`, alpha_{-n} = -alpha_n, d(0) = 0, tail convention alpha_n = n, d(n) = 1 for n > m |
| `opTbound` | 121 | 1628 | operator-norm gap consumer |
| `G` | 128 | 1779 | `G := sum_n d(|n|) p_{alpha_n}` |
| `spectral0` | 134 | 1875 | `|| K_I - T || <= epsilon_1` |
| `posconds` | 138 | 1905 | rank-one split positivity conditions |
| `posconds2` | 139 | 1909 | numeric instance of the second condition |
| `negativeNI` | 140 | 1933 | coercivity of `-N_I` with rank-one correction |
| `maininequ` | **141** | 1959 | THE delta display (section 2) |
| `sonine1thm` | 142 | 1964 | trace decomposition |
| `sonine1thm1` | 143 | 1967 | k = Y * g transport identities |
| `computersafe` | 169 | 2244 | closed-form 11-term tail bound for Q epsilon |
| `computersafe1` | 170 | 2248 | remainder <= 2.366e-12 on [1,2] |

Cross-check against repo usage: `cc20Eq115_gate1hT` (GATE 1 assembly), the
`eq-(119)` central-n=0 owner fix (`5aafd9f`, AGENTS 7d bullet 1), and the
`eq-(121)` norm-gap consumer (1044) all land on the intended displays.

## 2. The delta chain, verbatim from the tex

Final theorem (thm `mainthmfine`, tex:1958-1962):

```text
Let g in C_c^infty(R_+^*) have support in [2^{-1/2}, 2^{1/2}] and Fourier
transform vanishing at -i/2.  Then

(141)  W_infty(g*g*) >= Tr(rep(g) S rep(g)*) - c * |ghat(0)|^2,
       c = 4*gamma/log 2.
```

The comparison engine (tex:1963-1990, eqs 142-143 and the unnumbered chain):

```text
(142)  tr(rep(f) S) = W_infty(f) + integral f(rho^-1) epsilon(rho) d*rho
     = W_infty(f) + E(f),   f = g*g*.
(143)  Q(k*k*) = g*g* = f,  khat(0) = -2 ghat(0),
     k(u) = u^{1/2} int_0^u v^{-1/2} g(v) d*rho, support k subset [2^-1/2, 2^1/2]
     via 0 = ghat(-i/2) = int_0^infty v^{-1/2} g(v) d*rho.
chain  E(f) = E o Q(k*k*) = <xi | N_I xi>
       <= gamma * |<xi_0 | xi>|^2 = (gamma/log 2) |khat(0)|^2
       = (4 gamma/log 2) |ghat(0)|^2.
```

This is exactly the GATE 1 delta field of 1046: "trace - coefficient * rank
<= W-infinity(g^2)" with the |ghat(0)|^2 rank-one term.

The paper-scale coercivity block (gamma payload territory), tex:1933-2005:

```text
(140)  <xi | (id - K_I) xi> + a |<xi_0 | xi>|^2 >= (epsilon_2 - epsilon_1) ||xi||^2
       (after multiplying the (138/139) condition by -2 e'(1_+))
numerics:  lambda_max = 1.05158,  b = lambda_max - 1 ~ 0.05158,
           <zeta | xi_0> ~ 0.94865,  c > 0.227784   (second eigenvalue gap)
           a ~ 0.064,  epsilon_2 ~ 0.00441,  epsilon_1 ~ 0.00122 < epsilon_2
rem remlowc (tex:1989-2005):  the first eigenvalue of K_I satisfies
           |lambda_1(K_I) - 1.05158| <= 0.00122, and a constructed g gives
           E(g*g*) >= 0.1 e'(1_+) |<xi_0|xi>|^2 > 13 |ghat(0)|^2, hence
           W_infty(g*g*) < Tr(...) - 13 |ghat(0)|^2, so the BEST constant
           in (141) obeys  13 < c < 17.
```

The 13<c<17 band is the paper-side anchor of the README gamma row
("13 < 4*gamma/log 2 < 17"); with c = 4*gamma/log 2 this is the consistency
condition `gamma in (2.2527, 2.9459)`, and the 1049 exhibit band
`294/100 < gamma < 2944/1000` (gamma = 2*ePrime) sits inside it at the
upper end.  No contradiction, but the two bands must not be conflated.

## 3. The alpha discovery: eq (170) self-funds the tail

Fact 1's own proof (tex:1566-1568):

```text
"To justify (115), one first uses (170) of Appendix to replace, without any
loss, the function chi(x) := (Q epsilon)(exp(x)) / (2 epsilon'(1+)) using
the contribution of the first 11 terms of the series (169) defining
Q epsilon."
```

(169)/(170), lem `lemesti` (tex:2239-2250):

```text
| Q epsilon(rho) - sum_{k=0}^{N} lambda(k)/sqrt(1 - lambda(k)^2) T_k(rho) |
    <= sum_{n=N+1}^infty term_n,
term_n = 2^(2n+2) pi^(2n+3/2) p(n) ((2n)!)^2 / ((4n)! Gamma(2n+3/2)),
p(n) = 16 n^2 + 8(1+3 pi) n + (4+sqrt 2) sqrt(4n+1) + 32 pi^2 + 24 pi + 2,
N = 10:  sum_{11}^infty term_n <= 2.366e-12  for all rho in [1, 2].
```

Consequences for the alpha brick (supersedes 1044's open-ended framing):

1. The `endpointSlope_summable` / `eigenvalue_sq_lt_one` premises of
   `CC20EndpointSpectralData` are provable from the same (169) mechanism:
   the paper's proof IS a ratio-test summability argument (nu_n comparison,
   nu_35 <= 5e-81, geometric tail).  Probe 1058 reproduces this arithmetic
   bit for bit.
2. The `hchi` enclosure on e^|v| in [1,2] needs only 11 modes: exact
   interval-ODE data for lambda_n and the analytic-continuation modes
   xi_n^an, plus the published 2.366e-12 tail.
3. The `hmass` certified L1 quadrature of |chi - tau| over the 3464 paired
   Fourier terms therefore runs against an 11-term enclosed chi, in the
   intended `yoshida_intervals` pattern (1044).
4. This is FIXED-depth, FIXED-scale work: no lambda -> infinity, no
   W_(lambda,S), so it does not touch the 1055 freeze (see 1056 rulings).
   It does NOT fund the 1055 revival; Ruling 2 of 1056 applies.

## 4. The tau table inputs are already committed

`tableangles`/`tableds` are the paper's SAMPLE tables; the full m = 1732
(angles, coefficients) inputs are the hash-pinned DOCX files already under
`scripts/cc20_eq115/data/` (1044), and the exact-rational Lean table is
`C1CC20Eq115Table.lean` with the n = 0 correction of `5aafd9f`.  The opT
(119) conventions `alpha_{-n} = -alpha_n`, `d(0) = 0`, `n > m: alpha_n = n,
d(n) = 1` are verbatim confirmed this pass.

## 5. Flag: intro-vs-final vanishing conditions differ

```text
mainthmintro  (tex:125-133, eqs (6)-(7)):  g supported in
  [2^{-1/2}, 2^{1/2}] AND ghat vanishing at BOTH +i/2 AND 0:
      W_infty(g*g*) >= Tr(rep(g) S rep(g)*) - c |ghat(0)|^2
      (with the c-term; the no-c version eq (5)-style needs both vanishings)
mainthmfine   (tex:1958, eq (141)):        g supported AND ghat(-i/2) = 0
  only; the |ghat(0)|^2 rank-one term STAYS (that is what (143)'s
  khat(0) = -2 ghat(0) transport is for).
```

The two statements are not literally the same theorem: the final theorem
replaces the second vanishing by the rank-one penalty with c = 4 gamma /
log 2.  Our GATE 1 assembly (1046: "Lemma-second rank-one" and the
"triple-vanishing kill" of the rank-one error) consumes the FINAL form; the
detector/triple-vanishing tests upstream must be checked against exactly
which vanishing set is in scope.  This is a pinning obligation on the
detector side, recorded here, not a defect.

## 6. Reproduction

```text
scripts/fetch_cc20.sh                      # e-print + unpack (WSL2)
sha256sum x/weil-compo.tex                 # must match section 0
grep -n 'label{computerverif}\|label{opT}\|label{maininequ}' ...   # map spot-check
docs/proofs/1058_alpha_chi_reconnaissance_probe.py                 # tail arithmetic
```

## 7. Sources

```text
arXiv:2006.13771 source, weil-compo.tex (sha256 above).
Repo: 1044 (extracted table + reduction), 1046 (payload table),
1049-B (HTML sweep superseded by this tex pass), 1050 (route shape),
1056 (F1 scope + freeze rulings), scripts/cc20_eq115/ (data + extractors).
```
