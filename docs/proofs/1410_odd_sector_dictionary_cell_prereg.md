# 1410 — Prereg: the odd-sector dictionary cell (closing the last leg of 1407)

Date: 2026-09-14. Zero-digit record. Prereqs: 1407/1408 (even cell =
PLUS_ONE), 1406 kill (b) (tier-1 owners are exactly ODD, so the
chain's owners live in the odd sector), main.tex section 4 /
`eq:oddlower` (the paper certifies the odd sector:
`Q >= 8.2e-15 ||f||^2`, real odd `f`, `supp <= 0.8`). Model-level only
(law 65). No Lean. RH not claimed.

## 1. What is decided here, and nothing else

1408 section 5 marked the dictionary "confirmed ... up to the untested
odd-sector leg". That leg is now load-bearing: 1408 section 6 kills
the radius-shrink route (attack (a) on the wall) only IF psi = Q on
ODD real windowed tests, because the chain's produced owners are
odd-equariant (1406 kill (b): targets `(1,-1,0x5)` force
`h(-x) = -h(x)`). One odd bump cell decides whether the last proposed
shortcut into the wall is measured-dead or reopened. No other content
is claimed either way.

## 2. Structural reading BEFORE digits (paper + register algebra)

For real odd `f`, `C(s) = int f e^{sx}` is odd in `s`:
`C(-s) = -C(s)`, so `C(s)C(-s) = -C(s)^2`. The register pole is
parity-blind in its FORM:

```
poleTerm F = lapAt F(1/2) + lapAt F(-1/2) = 2 C(1/2)C(-1/2)
             = +2C^2  (f even)      [matches their  2 Fhat(i/2)^2]
             = -2C^2  (f odd)       [matches their  -2 (int f_o sinh(x/2))^2 ]
```

(their `2F(i/2)^2` line is the even-`f` form; section 4's sign flip is
the SAME formula evaluated on odd `f`, since `Fhat(i/2) = C(-1/2)`.
The y-side `F = f~star f` is EVEN for both parities, so the arch and
prime channels of psi are literally unchanged evaluators.) The
Plancherel channel `(1/2pi) int |Fhat|^2 cos(t x) dt = (f~star f)(x)`
is parity-blind by derivation. Expectation is PLUS_ONE; the cell
exists because expectation is not measurement, and because 1406's
whole escalation started from a "structurally obvious" reading that
numbers later overruled.

## 3. The cell (locked design)

Test: `f_o(x) = (x/L) * exp(-1/(1-(x/L)^2))` on `|x| < L`, `L = 1/2`;
odd, C-infinity, flat at boundary; comb: `n = 2` visible,
`n = 3` excluded (identical window class to 1407, so Chuk's `0.8`
certificate DOES reach it). Left side: the 1407 rev3 register
machinery verbatim with `g_of` replaced by the odd autocorrelation
`g_o(y) = int f_o(v-y) f_o(v) dv` (even, computed on overlap `(y-L,L)`
by the same dense-panels rule; amplitude scale of `f_o` near 0 is
finer — panel cap tightened to 0.0025 for `g_o` inputs, disclosed in
the script header, gate classes unchanged). Right side:

```
fhatO(t)  = 2 int_0^L f_o(u) sin(t u) du        (Fhat_o = i * fhatO)
pole_o    = -2 * (2 int_0^L f_o(u) sinh(u/2) du)^2   (= -2 C(1/2)^2)
Q_o       = pole_o + (1/pi) int_0^T fhatO(t)^2 Psi_L(t) dt + tail
Psi_L     = same locked symbol as 1407 (n=2 comb)
```

## 4. Gates (classes IDENTICAL to 1407 rev3: 2e-4 abs / 1e-8 rel /
1e-8 rel / 1e-14) and verdict classes

| id | statement |
|----|-----------|
| O0 | script-identity tie: the shared `A_gen` transcription still reproduces committed tier-1 `A = -17.3431099115819` (abs 2e-4) |
| O1 | odd Plancherel convention: `(1/pi) int_0^T fhatO^2 cos(t log 2) dt` vs `g_o(log 2)` directly (rel 1e-8) |
| O2 | dual-path float64 vs 200-bit summation for Q_o and psi_o parts (rel 1e-8) |
| O3 | tail budget `fhatO(T)^2 * |Psi(T)| <= 1e-14 * max(1, |Q_partial|)` (1e-14), T printed |

Verdict on `rho_o = Q_o / psi_o`: `PLUS_ONE` `|rho_o - 1| <= 1e-6`;
`MINUS_ONE` `|rho_o + 1| <= 1e-6`; `RESCALED` classical constants
`{2,4,1/2,1/4,pi,2pi,1/pi,1/2pi}` (rel 1e-6); `OTHER` otherwise with
the three-term decomposition printed on both sides; `DEGENERATE-TEST`
if `|psi_o| < 1e-6`.

F16 reachability audit: both poles carry the SAME `-2C^2` form, but
the psi-side pole is computed from the y-side `g_o` integral
(`4 int g_o cosh`) — its agreement with `-2C^2` is a real numerical
claim, not a type fact; O1's channel is a different integrand
(`sin`-squared); and the odd Q floor is positive by `eq:oddlower`
only if the dictionary holds — MINUS_ONE/OTHER remain live a priori
(a sign flip here would mean psi is NOT the paper's odd-sector form
and 1406's sector story must be rebuilt). No branch vacuous.

## 5. Readings (locked)

* `PLUS_ONE` (+ O-gates pass): the odd dictionary leg holds at this
  cell => 1408's route-(a) closure stands at measurement level: the
  chain's counterexample class (odd owners, radius >= ~2^gamma) is
  provably disjoint from every fixed-L certificate, and NO shrink of
  the production radius can reach `<= 0.8` without contradicting
  Yoshida/Chuk through a measured dictionary. Outcome record 1411
  also closes the Chuk species file and the campaign's executable
  queue for the third time, now by mathematical necessity rather
  than exhaustion of ideas.
* `MINUS_ONE` / `RESCALED` / `OTHER`: psi is parity-sensitive relative
  to Q (or the even-cell match was a coincidence of conventions);
  1406-1408 sector reasoning reopens; the odd certificate leg of the
  1408 dissolution does NOT bind our owners; record what breaks,
  and route (a) is NOT closed — re-price honestly.
* Degenerate/failed-gate handling per law 7j/42 (rig-only fixes may
  touch quadrature only, never classes).

## 6. Kill scope

One cell again. It cannot falsify `eq:oddlower`, the chain, or the
sup-law. It prices exactly one branch condition. No Lean funded.
RH not claimed in either direction.

## 7. Next steps

1. `scripts/run_1410_odict.py`: reuse rev3 functions by import
   (`run_1407_dict`), new odd evaluators, same main structure; commit
   before digits.
2. Run on the Linux-side verification environment; outcome record
   1411 + 1409 recon (route-(a) closure) + register closure wave.
