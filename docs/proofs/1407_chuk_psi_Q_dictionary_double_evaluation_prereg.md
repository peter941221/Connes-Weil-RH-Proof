# 1407 — Prereg: the psi-vs-Q_Chuk dictionary as a scalar double-evaluation cell

Date: 2026-09-14. Zero-digit record: locked specification, no
measurement. Prereqs: 1405 (bridge framing), 1406 (outcome: COVERS by
double structural kill; residual = this dictionary). Model-level only
(law 65). No Lean. RH not claimed.

## 1. What is decided here, and nothing else

1406 section 5 reduced the Chuk bridge (arXiv:2608.24827) to ONE
scalar question: is the register's `psi` the paper's `Q` as a functional
on a REAL windowed test, with which sign and factor? Cross-term
objection (dead per 1406 kill (a)) and parity objection (dead per
paper section 4) are both settled; what remains is the normalization
and the archimedean-side convention.

## 2. Paper facts, quoted from the RAW LaTeX source (law F17 applied to literature)

Downloaded this session from arXiv `e-print/2608.24827` (Windows-side
fetch; WSL direct egress is dead behind the NAT proxy); the paper
source `main.tex` extracted, quoted verbatim (lines 178-192):

```latex
Q(f)\;=\;2F(i/2)^2
+\frac1{2\pi}\int_{\R}|F(t)|^2\,\Psi_L(t)\,dt,
...
\Psi_L(t)\;=\;\Rey\,\psi\Bigl(\tfrac14+\tfrac{it}2\Bigr)-\log\pi
-\sum_{\log n<2L}\frac{2\Lambda(n)}{\sqrt n}\,\cos(t\log n),
```

with `\hat f(r) = \int f(u) e^{iru} du` (section 1), `f` even real
continuous supported in `[-L,L]`; and the zeros-side identity (5):
`Q(f) = sum_rho ghat((rho - 1/2)/i) =_{RH} sum_{gamma>0} 2|fhat(gamma)|^2`,
`g = f star f~`. Parity section 4 verbatim: "the pole term of
Q(f_o) changing sign to -2(int f_o sinh(x/2) dx)^2" — the register's
paired-`laplaceAt` convention reproduces that odd-sector sign
structurally (1406). "Positivity ... for every L > 0 is equivalent to
RH. For fixed L it is a finite, unconditional statement" +
"Yoshida proved positivity for 2L <= log 2".

## 3. Structural term-by-term reading (paper algebra, no computation)

Under the identification `their f = our owner g`, `their g = our test F = g~star g`:

* POLE matches structurally: their `2F(i/2)^2 = 2C(-1/2)^2` against
  ours `poleTerm F = lapAt F(1/2) + lapAt F(-1/2)` with
  `lapAt F(s) = C(s)C(-s)`, `C(s) = int f e^{s x}`; for EVEN f,
  `C(-s) = C(s)` ⇒ both are `2C(1/2)^2`. (For odd f,
  `C(-s) = -C(s)` ⇒ theirs `(2)`-form does not apply and section 4's
  `-2s^2` equals ours `-C(1/2)^2 - C(-1/2)^2 = -2s^2` ✓.)
* PRIMES match structurally IF AND ONLY IF the Plancherel pair
  `(1/2pi) int |F(t)|^2 cos(t log n) dt = Fg(log n)` holds with the
  paper's conventions — gate D1 below audits exactly this, because a
  convention error here would masquerade as a dictionary result.
* ARCHIMEDEAN is the live unknown: their `(1/2pi) int |F|^2
  (Re psi(1/4+it/2) - log pi) dt` vs the register's
  `(log 4pi + gamma)F(0) + int_0^inf [e^{y/2}(F(y)+F(-y)) - 2F(0)] /
  (2 sinh y) dy`. Sign/factor = what this cell measures.

## 4. The cell (locked design)

Test: `f(x) = exp(-1/(1-(x/L)^2))` on `|x| < L`, 0 otherwise;
`L = 1/2`. Even, real, C-infinity, flat at boundary (their hypothesis
class exactly). Chosen so the prime comb is nonempty but tiny:
`2L = 1.0` contains `log 2 = 0.6931` (n=2, coefficient
`2 log 2 / sqrt 2`) and excludes `log 3 = 1.0986 > 1.0` — one comb
term on both sides, so the primes channel is actually TESTED (unlike
the tier-1 cell of 1405/1406 where the support radius sat exactly at
log 2 and the sum was empty).

Left side (`register`), on `F = f~star f` (radius 2L = 1):

```
psi(F) = poleTerm F - arch F - primeSum F
poleTerm F = 4 int_0^{2L} F(y) cosh(y/2) dy         (bilateral pair)
arch     F = (log4pi+gamma)F(0) + int_0^{2L}[2 e^{y/2}F(y)-2F(0)]/(e^y-e^-y) dy
           + F(0) * log(tanh L)                     (analytic tail beyond 2L)
primeSum F = 2*(log 2)/sqrt(2) * F(log 2)           (n=3+ invisible)
```

The `arch` line is the VERBATIM transcription of `run_1398_rig.compute_A`
with `Rg = L` and an empty kink set (this test is C-infinity), only the
`F_at` call site substituted — law F17. Gate D0 below is the
parent-agreement check that the generalization reproduces the
committed tier-1 number before any dictionary digit is read.

Right side (`Chuk`), on the same f:

```
Fhat(t)   = 2 int_0^L f(u) cos(t u) du
Q(f)      = 2 Fhat(i/2)^2 + (1/pi) int_0^{TMAX} Fhat(t)^2 Psi(t) dt + tail
Psi(t)    = Re digamma(1/4 + i t/2) - log pi - (2 log2/sqrt2) cos(t log 2)
tail gate = |Fhat(TMAX)|^2 * |Psi(TMAX)| / max(1,|Q_partial|) <= 1e-14
```

`TMAX` is chosen adaptively INSIDE the run to satisfy the tail gate
(the CLASS is locked here, the value is artifact data — no pre-fixed
digit, no dead branch: C-infinity flat decay guarantees a finite such
TMAX). Inner `Fhat(t)` quadrature: frequency-adaptive 16-node
Gauss-Legendre panels, node density `max(8 * t * L / (2pi), 1)`
panels — the probe's own panel rule, transcribed.

## 5. Gates (all branches reachable — F16 audit)

| id | statement | class |
|----|-----------|-------|
| D0 | parent agreement: generalized arch functional reproduces the committed tier-1 `A = -17.3431099115819` (via the 1405 rev2 `A_float` path, owner evaluator, Cg grid) | abs 2e-4 |
| D1 | Plancherel convention check: `(1/2pi) int |Fhat|^2 cos(t log 2) dt` vs `F(log 2)` directly | rel 1e-8 |
| D2 | dual-path agreement (float64 vs 200-bit summation) for psi, Q, and all printed parts | rel 1e-8 |
| D3 | tail budget: `Fhat(TMAX)^2 * |Psi(TMAX)| <= 1e-14 * max(1, |Q_partial|)`, TMAX printed | 1e-14 |

Sentinels:
`DONE gates=D0:...,D1:...,D2:...,D3:...` and
`VERDICT dictPsiQ=PLUS_ONE|MINUS_ONE|RESCALED|OTHER q_ratio=... psi=... Q=...`

Verdict classes on `rho_r = Q / psi` (psi printed nonzero-guarded; if
`|psi| < 1e-6` the cell prints `DEGENERATE-TEST` and no branch fires —
reachable by design since the test is a single fixed function):

* `PLUS_ONE`  `|rho_r - 1| <= 1e-6`
* `MINUS_ONE` `|rho_r + 1| <= 1e-6`
* `RESCALED`  `rho_r = c(1+eps)` with `c` in `{2, 4, 1/2, 1/4, pi, 2pi, 1/pi, 1/2pi}` and `|eps| <= 1e-6`
* `OTHER`     otherwise (includes term-wise mismatch: the record prints
  the three-term decomposition table on both sides regardless, so
  OTHER is diagnostic, not empty).

F16 audit (branch reachability, not just satisfiability): the sign of
the arch-side channel is not determined by any formula-level argument
we possess (section 3: it is the ONLY unmatched channel after pole and
primes matched structurally), so PLUS_ONE, MINUS_ONE and OTHER are all
live a priori; RESCALED covers the classical 2-branching of the
Plancherel constant; DEGENERATE is reachable only through a broken
test choice and self-reports. No branch is vacuous.

## 6. Readings (locked BEFORE digits, per law 42)

* `PLUS_ONE`: the register's psi IS the classical geometric side,
  model-confirmed. Then the 1406 triangle resolves with the DICTIONARY
  TRUE, and the escape must lie in the other two vertices: the paper
  says fixed-L positivity is a FINITE FRAGMENT (not the wall), so the
  rung-5 wall must quantify over owners whose support exceeds every
  fixed L — this becomes a FORMAL-SIDE VERIFICATION DUTY (grep the
  register class: is the tower's owner class support-unbounded? if it
  were entirely windowed at log2/2, a 1992 theorem would already settle
  the wall, which is impossible-by-history; find the hypothesis that
  separates the wall class from the Yoshida class). Also: pillar A's
  death acquires a classical citation (Yoshida via their eq. 2) instead
  of only 107 measurements. No Lean, no claim either way.
* `MINUS_ONE` or `RESCALED`: the register's psi differs from the
  classical form by a locked sign/factor convention; pillar A's
  negativity census maps onto classical positivity with the recorded
  factor; Chuk's certificate is NOT consumable as a psi-bound (wrong
  functional); the species closes as a pillar-B supplier per the 1405
  section 7 reading, and the 1406 triangle dissolves.
* `OTHER`: term-by-term decomposition decides which channel
  (arch / primes / pole) breaks the identification; report, close the
  species, no further dictionary probe of this paper (law F14: one
  mechanism per class).

## 7. Kill scope

One model cell, one fixed test function. It cannot falsify the chain,
Yoshida, or Chuk; it measures a normalization identity. A PLUS_ONE at
one cell is model evidence, not a theorem (sup-law + law 65):
formal consumption would require a Lean bridge theorem for psi = Q,
which nobody is funding from one bump. No Lean. RH not claimed.

## 8. Next steps

1. Write `scripts/run_1407_dict.py` implementing section 4 exactly
   (self-contained; the arch generic transcribed per F17 and gated by
   D0 against the committed tier-1 value before any dictionary read).
2. Commit BEFORE any digit; run on the Linux-side verification
   environment; outcome record 1408 with sentinels verbatim +
   decomposition table + the formal-side duty located if PLUS_ONE.
