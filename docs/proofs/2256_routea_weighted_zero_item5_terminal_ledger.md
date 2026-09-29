# 2256 — Terminal item-5 ledger at the transfer-free standing; stored-solve residual audit

Date: 2026-09-30

Consumer: the terminal item-5 ledger — the 2249 certified margin, the 2253
count-free full-tail charge, and the 2255 gap charge, assembled and frozen
for the Lean strict-margin theorem.

Verdict: **the terminal ledger holds: margin `1675396046388.2737`, gap
charge `6537949.749302972`, full-tail charge `4968695278.066621`, reading
`0.00296569559081069`, `eps0 = 1670420813160.4578`; the stored operands
solve the reconstructed construction to relative residual `2.3e-29`
(backward consistency); the Lean constants freeze at tail
`4894093747.764274`, known `74601530.30234718`, gap `1e7`, slack
`1.67e12`, with strict arithmetic slack `417351110.20703125`.**

## The terminal ledger

```text
margin_2249 (=-q_hi, 2249)          1675396046388.2737
total gap charged (2255)                6537949.749302972
margin, gap-adjusted                1675389508438.5244
charge (full tail 2248 + known 2109) 4968695278.066621
reading terminal                    0.00296569559081069
eps0 terminal                       1670420813160.4578
```

The charge is the 2253 fallback: the count-free Lean high-shell bound
`4 * mult * B` plus the 2109 known-error sum; the `owner/62` transfer
factor stays withdrawn.

## Lean constants frozen

```text
highShellTail2248    4894093747.764274
knownError2109          74601530.30234718
gapCharge2255                 10000000   (measured 6537949.749302972 rounded up)
eps0FullTail2249     1670000000000
strict slack for transfer_free_charge_le_margin_sub_slack:
  margin2249 - eps0 - tail - known - gap = 417351110.20703125 > 0
```

`ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` carries
`transfer_free_charge_le_margin_sub_slack` and
`a005_item5_strict_signed_margin_full_tail` at these constants, both by
`norm_num`.

## Stored-operand residual audit (convention A closure)

The 2230 convention A defines the stored binary64 operands as exact; the
float-solve-vs-exact-solve gap is a convention, not a charge. What remains
checkable is that the stored operands are a genuine solution of the stored
system:

```text
residual base (inf)        6.4676997486962715e-15   |base| inf  2.7756775344869828e14
residual corr (inf)        1.1417431493021041e-11   |corr| inf  5.6875117346762605e17
relative base              2.3301336946878703e-29
relative corr              2.0074563404256314e-29
condition number of a_mat  265373.1999607843
```

Scope, stated exactly: this certifies BACKWARD consistency (the residual
is at the solve's guaranteed order relative to the coefficient
magnitudes), not forward accuracy — the forward amplification
`cond * u ~ 5.9e-11` relative is precisely the solve gap that convention A
defines away. The reconstruction also cross-checks the node set: the 2234
build cache and the rebuilt owner nodes agree, or the corr residual would
be enormous.

## Nonclaims

No producer GO, no gate sign change, no RH claim. The Lean repricing is
the arithmetic only; the numeric inputs (2249 enclosure, 2245/2250 counts,
2109 ledger, 2255 gap charge) remain artifact-level facts. The ideal-to-
discrete gaps beyond the 2255 measured refinements are not independently
derived.

## Provenance

- script: `scripts/routea_weighted_zero_item5_terminal_ledger_2256.py`;
- artifact: `results/2256_item5_terminal_ledger.json`
  (md5 `ee255507712cf24a59680ebed7935059`);
- inputs: `results/2249_l1_enclosure.json`,
  `results/2255_l1_gaps.json`, `results/2234_build_cache.npz`;
- Lean: `ConnesWeilRH/Dev/C1RouteAItem5Arithmetic.lean` (+ probe).