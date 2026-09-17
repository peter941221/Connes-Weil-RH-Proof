# 1570 — T0 wave: quantitative digamma asymptotics with explicit constants

Date: 2026-09-17.

**Status: PAPER DERIVATION + EXACT-RATIONAL NUMERIC SENTINEL. Zero Lean.**
This record delivers the pre-registered entry fee of the phase wave
(record 1568 §2): the pair (T0a)/(T0b) with explicit absolute constants,
derived from the committed phase transcription
`theta'(xi) = -2*pi*(Re psi(1/4 - pi*i*xi) - log pi)` (record 1511 §6, via
`logDeriv_GammaR_eq_log_pi_add_digamma`). It also carries the F22 correction
of record 1568's T0b transcription (below). No gate is advanced: (★), B4,
rho5 all stay open. RH not claimed.

## 1. Correction of the 1568 T0b sign slip (F22 duty)

Record 1568 §2 pinned `|theta''(xi) - 2*pi/xi| <= C2/xi^2`. Deriving from the
committed theta' formula (not from prose): theta'(xi) ~ -2*pi*log|xi| is
DEcreasing, so theta'' ~ -2*pi/xi, and the correct anchor is

```text
|theta''(xi) + 2*pi/xi|          (plus, not minus)
```

with the sharper true rate O(xi^-3) shown below. The 1568 entry remains on
disk as the pre-registration; this section supersedes its T0b line.

## 2. The two tools (cited, with their honest scope)

(a) Stieltjes expansion with remainder (DLMF §5.11, eqs. 5.11.2 and the
error-bound paragraph of §5.11(ii); fetched 2026-09-17,
`https://dlmf.nist.gov/5.11`):

```text
psi(z)  ~ log z - 1/(2z) - sum_{k>=1} B_{2k}/(2k z^{2k})
psi'(z) ~ 1/z + 1/(2z^2) + sum_{k>=1} B_{2k} z^{-(2k+1)}
```

terminating at k = n-1, the remainder for real z > 0 is bounded by the first
omitted term with the same sign; for complex z it is bounded by
`sec^{2n+1}((1/2) ph z)` times the first omitted term (DLMF 5.11(ii),
5.11.2-case; for psi' the general reference is Nemes 2013b). On our vertical
line `z = 1/4 + i*tau` we have `|ph z| < pi/2`, so the worst factor is
`sec^5(pi/4) = 4*sqrt(2) ~ 5.66` at n = 2. The sec-factor is NOT omitted from
the constants below (law F18: cite premises verbatim, use what the citation
actually gives). Bernoulli values used: `B2 = 1/6`, `B4 = -1/30`,
`B6 = 1/42`, so the k=1 remainder scale is `|B4|/(4 r^4) = 1/(120 r^4)` and
the psi' k=1 remainder scale is `|B4| r^{-5} = r^{-5}/30`.

(b) Elementary rational inequalities (no citation needed): `log(1+t) <= t`,
and for `r^2 = tau^2 + 1/16`: `Re(1/z) = (1/4)/r^2`,
`Re(1/z^2) = (1/16 - tau^2)/r^4`, `Im(1/z) = -tau/r^2`,
`Im(1/z^2) = -tau/(2 r^4)`, `Im(1/z^3) = (tau^3 - 3*tau/16)/r^6` (real
arithmetic in exact Fractions; the odd-power real parts are
`Re(1/z^{2k+1}) = O(tau^{-2k-2})` which is why the real part on the vertical
line jumps to order tau^{-2}, as previewed in 1568 §2).

## 3. (T0a): the pinned first-derivative bound

Set `tau = pi*|xi|`, `z = 1/4 + i*tau` (conjugation invariance makes
`Re psi(1/4 - i*tau) = Re psi(z)`), `xi >= 2` so `tau >= 2*pi > 6`.
Decomposing `Re psi(z) - log tau` with tool (a) at n = 2 (keep k=1 term,
first omitted `1/(120 r^4)`, sec-factor `<= 4*sqrt(2)`):

```text
row  term                                   | bound (tau >= 6)
---  -------------------------------------   ----------------------
 1   |log|z| - log tau| = (1/2)log(1+1/(16 tau^2))        (1/32) tau^-2
 2   |Re 1/(2z)|           = 1/(8 r^2)                    (1/8)  tau^-2
 3   |Re 1/(12 z^2)|       = (tau^2 - 1/16)/(12 r^4)      (1/12) tau^-2
 4   |Re R_2| <= 4*sqrt(2)/(120 tau^4)   (tau >= 2pi)     (sqrt2/(120 pi^2)) tau^-2
     ------------------------------------------------------------
     sum                                             (17/96 + sqrt2/(120 pi^2)) tau^-2
```

Since `theta'(xi) + 2*pi*log|xi| = -2*pi*(Re psi(z) - log tau)`:

```text
(T0a)  |theta'(xi) + 2*pi*log|xi||  <=  C1 / xi^2,      C1 = 17/(48*pi) +
       sqrt(2)/(60*pi^3)  <  0.1138                    for |xi| >= 2.
```

Sharp sign fact kept for the wave: rows 1-3 have signed sum
`(+1/32 - 1/8 + 1/12) tau^-2 = -tau^-2/96`, hence

```text
theta'(xi) = -2*pi*log|xi| + (1/(48*pi)) xi^-2 + O(xi^-4)     (positive drift).
```

The leading drift 0.00663/xi^2 sits 17x inside the pinned bound; the
`4*sqrt(2)` sec-slack contributes only row 4's 0.7%.

## 4. (T0b): the pinned second-derivative bound (xi^-3 rate)

`theta''(xi) = 2*pi^2 * Im psi'(z)` (from §1's differentiation; sign-checked
twice: `d/dxi Re psi = pi Re(i psi'(z)) = -pi Im psi'(z)` and
`theta' = -2*pi Re psi(...)` compose to `+2*pi^2 Im psi'`). Expanding
`psi'(z) = 1/z + 1/(2z^2) + 1/(6z^3) + R_3`, `|R_3| <= 4*sqrt(2)/(30 tau^5)`
(n = 2 again on the sec-factor, first omitted `|B4| tau^-5 = tau^-5/30`):

```text
row  term                                   | bound (tau >= 6)
---  -------------------------------------   ----------------------
 1   |1/tau - tau/r^2| = (1/16)/(tau r^2)                 (1/16) tau^-3
 2   |tau/(4 r^4)|                                        (1/4)  tau^-3
 3   |(tau^3 - 3 tau/16)/(6 r^6)|                         (1/6)  tau^-3
 4   |Im R_3| <= 4*sqrt(2)/(30 tau^5)  (tau >= 2pi)       (sqrt2/(60 pi^2)) tau^-3
     ------------------------------------------------------------
     sum                                              (23/48 + sqrt2/(60 pi^2)) tau^-3
```

Hence, with `2*pi/xi = 2*pi^2/tau` already pulled to the left:

```text
(T0b')  |theta''(xi) + 2*pi/xi|  <=  C2 / |xi|^3,   C2 = 23/(24*pi) +
        sqrt(2)/(30*pi^3)  <  0.3067                for |xi| >= 2;
(T0b)   in particular  <= (C2/2) / xi^2  <= 0.154 / xi^2,
```

which is the form 1568 priced (with the §1 sign correction). Sharp signed
sum of rows 1-3: `+1/16 - 1/4 + 1/6 = -1/48`, i.e.

```text
theta''(xi) = -2*pi/xi - (1/(24*pi)) xi^-3 + O(xi^-5),
```

and this is exactly the xi-derivative of §3's signed expansion - the two
rows cross-validate.

## 5. Numeric sentinel (exact rational, WSL, PASS 8/8)

`scripts/t0_digamma_sentinel/d2_stieltjes_sentinel.py` validates the
Bernoulli-coefficient chain on the positive real axis (where the series
telescopes exactly at integers, `psi(m) = H_{m-1} - gamma`, so no floating
point and no series truncation is involved): with the 50-digit stored gamma
bracket and `log 2 = 2*atanh(1/3)` derived from its rational series, the
exact-interval check of

```text
D2(x) := psi(x) - log x + 1/(2x) + 1/(12 x^2),   0 < D2(x) <= 1/(120 x^4)
```

PASSES at x = 2, 4, 8, 16, 32, 64, 128, 256 (measured widths ~1e-44), and
`D2(x)*120*x^4` equals the two-term prediction `1 - (120/252)/x^2` to within
7e-6 already at x = 16:

```text
m=2    ratio=0.903337  pred=0.880952  PASS     m=16   ratio=0.998147  pred=0.998140  PASS
m=4    ratio=0.972001  pred=0.970238  PASS     m=32   ratio=0.999535  pred=0.999535  PASS
m=8    ratio=0.992678  pred=0.992560  PASS     m=64   ratio=0.999884  pred=0.999884  PASS
m=128  ratio=0.999971  pred=0.999971  PASS     m=256  ratio=0.999993  pred=0.999993  PASS
```

Scope note, honestly stated: the sentinel checks the coefficient chain and
the constant structure on the real axis (where the DLMF bound is exactly the
sec-free one); the vertical-line passage is pure tool-(a)+(b) algebra with
the 4*sqrt(2) factor paid in rows 4. No Lean consumer may quote the sentinel
as a proof (generator-grade evidence, same policy as the yoshida engine's
docstring).

## 6. What the wave may now spend on

Per the 1568 §4 gate ("no Lean brick on T1+ until T0a/T0b exist on paper
with error terms"): the entry fee is PAID with explicit constants. The next
step (record 1571) is the T1 exponent ledger; T-B4 may also instantiate its
consumer now that theta' and theta'' carry named bounds. The constants
`C1 = 0.1138`, `C2 = 0.3067`, drift `+1/(48 pi xi^2)`, curvature
`-1/(24 pi xi^3)` are the wave's pinned analytic inputs.

## 7. Boundary

RH not claimed; nothing in this record touches (★), B4, rho5, or R4 status.
