# 2263 — Arb ball certification of the census non-zero pins (the 2245 kill-list non-zero side)

Date: 2026-09-30

Consumer: the 2245 owner-count brick decomposes the 30/33/36 node totals
as 21/24/27 true in-ball critical-line zeros plus 6 non-zero pins per
candidate: 2 off-line functional-equation points (`0.945 - i gamma`,
`0.055 - i gamma`), 3 real-axis pins (`0.5`, `1.0`, `1.5`), and the
non-zero kill pin at the false `gamma_4` ordinate `27.67032193035704`.
Record 2259 certified the 72 zero brackets and the kill pin; the remaining
pins were classified only by mpmath. This record certifies `xi(z) != 0`
at every non-zero pin with Arb ball arithmetic.

Verdict: **all 18 non-zero pin instances at the three candidates are
certified non-vanishing (15 by Arb `acb` balls with the smallest lower
bound `9.227272168362652e-13`, 3 at the pole point `s = 1` by the
classical exact `xi(1) = 1/2`). The distinct geometry is
`3 real-axis + 6 off-line + 1 kill pin`; the off-line margins come in
functional-equation mirror pairs (`xi(s) = xi(1-s)`), and the certified
`xi(0.5) = 0.4971207781883137` reproduces the classical `Xi(0)`. The kill
pin is re-certified with `|xi| >= 3.8781880974656257e-07`, consistent
with the 2259 Hardy-Z bound `|Z| >= 2.8451013491344974` (ratio equals the
certified prefactor modulus). The 2259 extension is complete: zeros by
certified brackets, non-zero pins by certified lower bounds — the census
classification is ball-checked end to end.**

## Method

`xi(z) = (1/2) z (z-1) pi^{-z/2} Gamma(z/2) zeta(z)` evaluated with
python-flint (`acb.gamma`, `acb.zeta`, `arb.pi`) at 200 bits; nodes enter
as exact floats (`arb(float)`); the certified object per pin is the
positive lower bound `|xi(z)| >= m` (ball modulus `mid - rad`, float
conversion padded 8 ulp). The classification rule is the committed 2247
one (mpmath `siegelz < 1e-9` at 60 dps), applied only to decide which pin
gets which certificate; the certificates are independent of it. All
count assertions verified: `21/24/27` zeros, `1` critical-line non-zero
(kill) pin, `2` off-line, `3` real-axis, node totals `30/33/36` per
candidate.

Boundary case: the real-axis pin `s = 1` is `zeta`'s pole; `acb.zeta` at
a ball containing `1` is indeterminate and interval arithmetic cannot
cancel `(s-1) zeta(s)` at the boundary point. That pin (one instance per
candidate) is recorded with the classical exact value `xi(1) = 1/2` (the
entire completion normalization) and named as such in the artifact — a
documented classical input, not an `acb` computation.

## Results

```text
gamma               39.25244858548658   42.12289614653125   45.66611208104108
nodes               30                  33                  36
zeros               21                  24                  27
kill pin            1                   1                   1
off-line pins       2                   2                   2
real-axis pins      3                   3                   3
min acb pin margin  5.547830231357397e-11  4.354577967736868e-12  9.227272168362652e-13
```

Distinct certified points (10 = 3 + 6 + 1):

```text
0.5                |xi| >= 0.4971207781883137   (= classical Xi(0))
1.0                xi(1) = 1/2                  (classical, pole point)
1.5                |xi| >= 0.5087310387263231
0.055 - i gamma_k  |xi| >= 5.5478e-11 / 4.3546e-12 / 9.2273e-13
0.945 - i gamma_k  mirror pair (same margins, xi(s) = xi(1-s))
0.5 + 27.67032193035704 i  kill pin |xi| >= 3.8781880974656257e-07
```

## Nonclaims

- the `xi` evaluation certifies non-vanishing at the committed float node
  coordinates (`arb(float)` is exact); the critical-line zero side remains
  the 2259 brackets (72 certified);
- the pin at `s = 1` uses the classical exact value (see Method);
- the classification rule (mpmath `siegelz < 1e-9`) is the committed 2247
  rule, not a certified object;
- no producer GO, no gate sign change, no RH claim.

## Provenance

- script: `scripts/routea_weighted_zero_census_arb_2263.py`;
- artifact: `results/2263_census_arb.json`
  (md5 `f01dfccb302f009ad72da8e582901671`);
- machinery: `scripts/routea_weighted_zero_separation_input_2247.py`
  (`assemble_owner`, classification rule); python-flint venv;
- predecessor: `docs/proofs/2259_routea_weighted_zero_brackets_arb.md`;
- consumer: `docs/proofs/2245_routea_weighted_zero_owner_count_brick.md`.