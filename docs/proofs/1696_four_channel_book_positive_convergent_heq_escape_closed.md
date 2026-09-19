# 1696 — the committed four-channel book converges to +1.663, positive and window-stable; the cross channels book +0.0048 each (positive): the "cross channels carry the sign" escape hatch from 1695 is closed with data

Date: 2026-09-19.

Status: one rig on the COMMITTED object
(`scripts/four_channel_ledger_1696.py`, run in WSL2; results
`results/1696_four_channel_ledger.json`).  Companion to record 1695; RH is
not claimed.

## Object (all definitions read from the tree before rigging, F27/F28)

The endpoint operator of the G8 lane is `J† K† G K J` with
`G = (id + S†)† ∘ D ∘ (id + S†)`, `S` = pulled shear ALONE
(`C1G8AdjointShearGram.lean:59-66`), `D` = detector `C†C`.  The cutoff
family windows with `B_n` = `fullBoundaryPositiveOperator g (cutoffLower n)
(cutoffUpper n)` — symmetric windows of radius `supportRadius(g) + n + 1`
(`C1PositiveTraceCutoffAdapter.lean:31`), modeled as reflect-and-window on
the grid.  Four channels (`:1069-1100`): base `B†DB`, cross `B†SDB`,
adjoint-cross `B†DS†B`, fourth `B†S†DSB`, all traced along the carrier
basis (the 1694 v4 meet, m-orientation).

## Verdict

```text
  N=1024, r_n = 0.42 + n + 1;  qw = -0.912628
  hcore (W-channel, no window) = +0.885784
  n= 0 r= 1.42: base=+0.927000 cross=+0.004767 across=+0.004767 fourth=+0.739975  BOOK=+1.676510
  n= 2 r= 3.42: base=+0.888243 cross=+0.004783 across=+0.004783 fourth=+0.777683  BOOK=+1.675492
  n= 4 r= 5.42: base=+0.885784 cross=+0.004768 across=+0.004768 fourth=+0.767473  BOOK=+1.662792
  n= 8 r= 9.42: base=+0.885784 cross=+0.004768 across=+0.004768 fourth=+0.767489  BOOK=+1.662809
  n=12 r=13.42: (identical to n=8)  BOOK=+1.662809
  n=16 r=17.42: (identical to n=8)  BOOK=+1.662809
  direct no-window readback tr(Qc† G Qc) = +2.151668
```

1. **The book is positive and window-stable**: converged by `n = 4`
   (radius 5.42 already swells past the carrier window) to `+1.6628`, with
   the brick's prediction `BOOK ≥ 0 ∀n`
   (`C1G8P4ReadbackSocketVacuity`) confirmed on the committed object.
2. **The escape hatch is closed.**  For `heq` to hold at this test, the
   limit book would have to read `qw = −0.913`; the missing `≈ −2.58`
   would have to come from the cross channels.  Measured: `+0.0048` each —
   positive and three orders of magnitude too small.  There is no
   channelwise reweighting of this book that reaches a negative `qw`.
3. **Window limit ≠ no-window object**: the book converges to `+1.663`
   while the direct `G` readback is `+2.152` — the window family converges
   to the reflected limit (`B_n → Ref`), not to the unwindowed operator.
   The committed readback ties to the B_n-family limit; the distinction is
   real and must be respected in any future identification (it is the
   1695 operator-object caveat, seen from the second side).
4. Combined with 1695's difference-form reading (`+0.021`): every
   positive-trace reading in the committed vocabulary — shear-alone book,
   difference-form aggregate, annular Gram column energies — sits at
   `≥ 0`, while `qw < 0` at the test.  Map 046's structural verdict stands
   triple-sealed (formal brick + two rigs): **the sign face has no carrier
   in any single positive trace of the committed vocabulary.**

Next (unchanged from 1695 §3): the sign must be consumed where it is
proven — the committed spectral bridge
(`qw_eq_spectralWeilValue_centerTwo`) — or a genuinely indefinite
identification (a signed difference of positive traces with a proven
trace-class gap).  Both are new-lane decisions; stop word unchanged: gate
certificate.
