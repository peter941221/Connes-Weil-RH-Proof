# Record 2030 - Determinant certification margin on the converged gate rows

Date: 2026-09-27.

Status: DERIVATION FROM COMMITTED ARTIFACTS. No theorem, no new run, no RH
claim. This is the P2 follow-up registered in
[2029](2029_coupling_scan_outcome.md) section 7.

Instrument: `scripts/fourpoint_determinant_margin_2030.py` (exact
`Fraction` arithmetic, no floating point in the certificate solve). Artifact:
`results/2030_determinant_margin.json`. Input: the `dxi = 0.02` gate rows of
`results/2028_coupling_scan.json` (good to `<= 7.3e-7` relative -- see 2029
section 3).

## 1. Question, and the answer

Question: which half of the map-106 section 4 certificate is the real
obstruction on the converged rows -- the determinant `detUpper < 0`, or the
sign pair `Clo > 0`, `blo > 0`?

Answer, first line: **the determinant half is not the obstruction; the sign
half is, and it is not a precision question at all.** On the certified rows
`n = 1..4` the centers themselves have `C0 < 0` and `b0 < 0`, so
`Clo = C0 - eC <= C0 < 0` for every nonnegative error `eC`: the registered
certificate is unreachable there for every precision, at every cost.

The determinant half, by contrast, is comfortably reachable even with a loose
uniform relative budget.

## 2. Exact solve

Map 106 section 4, with one number `eps` for all three moments
(`eC = eps*|C0|`, `eU = eps*|U0|`, `eV = eps*|V0|`):

```text
U0 = b0 - a*C0
V0 = D0 - 2*a*b0 + a^2*C0
det = C0*V0 - U0^2                       (a-invariant; equals C0*D0 - b0^2)
Q   = |C0*V0| + U0^2
E   = (eps^2 + 2*eps) * Q
detUpper = det + E
Clo = C0 - eps*|C0|                       > 0  <=>  eps < 1   (if C0 > 0)
blo = b0 - eps*(|a|*|C0| + |U0|)          > 0  <=>  eps < 1   (if b0 > 0)
```

`eps_det` in the table below is the exact root of `det + E = 0`. Two centering
frames are reported: `a = 0` (uncentered, `U0 = b0`, `V0 = D0`) and the
vertex-centered frame `a = round((b0/C0) * 2^20) / 2^20` (a rational, stated
exactly; its own quantization is booked inside `U0` and `V0`, not discarded).

```text
 n  route  cert   eps_det (a=0)   eps_det (vertex)   |det|/Q (a=0)   C0>0   b0>0
 0  B      yes    8.9948e-03      4.1421e-01         1.8071e-02     true   true
 1  B      yes    3.1923e-02      4.1421e-01         6.4865e-02     false  false
 2  B      yes    3.8198e-03      4.1421e-01         7.6541e-03     false  false
 3  B      yes    3.3074e-02      4.1421e-01         6.7241e-02     false  false
 4  B      yes    9.0252e-02      4.1421e-01         1.8865e-01     false  false
 5  A      no     4.1421e-01      4.1421e-01         1.0000e+00     true   false
 6  A      no     4.1421e-01      4.1421e-01         1.0000e+00     true   true
```

Vertex frame residuals on the certified rows: `|U0|` in
`4.0e-04 .. 1.9e-01`, i.e. the center rounds the vertex to `<= 1e-5` relative
in `a`.

## 3. Reading

```text
1.  detUpper < 0 is reachable on EVERY certified row, including the rows whose
    sign half fails.  Worst certified requirement is eps < 3.8e-3 (n = 2);
    loosest is eps < 9.0e-2 (n = 4).  Centering the moment about the vertex
    rational lifts the requirement to eps < sqrt(2) - 1 = 0.4142 uniformly,
    because E ~ 2*eps*|det| once |U0| is small.
2.  The n = 0 row satisfies the FULL registered pattern (C0 > 0, b0 > 0,
    det < 0) with eps < 9.0e-3 on the determinant and eps < 1 on the signs, so
    the certificate is not vacuous: it is a per-n statement, and it holds
    exactly where the signs hold.
3.  For n = 1..4 the two sign clauses are unreachable, not tight: the centers
    are on the wrong side of zero.  No refinement, no interval method and no
    saddle-point bound changes that; only a different gate row does.
4.  Rows n = 5, 6 (route A, uncertified) have |det|/Q = 1 exactly, i.e. NO
    cancellation in the determinant at all, and eps_det = 0.4142 even
    uncentered.  Their route-A prime-channel error is 1e-2 .. 1e-1, which is
    below 0.4142 but not below the certified routes' own requirement.
```

## 4. Cross-lane price comparison

Route A's hard inequality is the health witness `C > 0`, which record 2010 /
2013 price as a cancellation of order `f = mm/A`: the required relative
accuracy on the signed masses is `eps < 1/(1+f)`.

```text
 lane   obligation        own required relative accuracy          source
 A      C > 0            1/(1+f): 1.16e-5 .. 1.96e-2            records 2010/2013
 B      detUpper < 0     eps_det : 3.82e-3 .. 9.03e-2 (a = 0)    this record
 B      detUpper < 0     0.4142 (vertex-centered)                this record
```

So on the conditioning axis the B-lane determinant is priced 1x to 15x looser
than the A-lane health witness uncentered, and 7x to 3.6e4x looser once the
moment is centered. The two are different obligations on different owners and
this is not a proof of either; it is the correct pricing of the remaining work.

## 5. Non-claims and follow-ups

- The centers are float numbers, not certified intervals. `eps_det` is the
  precision the map-106 (eC, eU, eV) certificate would need, not a claim that a
  certificate exists.
- Nothing here changes the 2029 verdict: `n` is still not a currency, and the
  live Cut-2 obligation is still an admissible `n >= 1` gate row with the
  registered signs.
- Consequence for route accounting: if a future seed/owner produces a certified
  row with `C0 > 0`, `b0 > 0`, `det < 0`, the determinant is the CHEAP half of
  the pair (<= 1e-2 relative, or 0.41 centered), and the remaining work in
  Route B sits in R-B1 (the all-strip `q` bound) and R-B0 (the complete owner),
  not in R-B2.
