# 926 - Gate-3U: closure vs refutation assessment (evidence-based, NOT a proof)

Date: 2026-08-10. Type: decision-support verdict. No `sorry`, no new `axiom`.
RH NOT claimed.

## 0. Purpose

The active Gate frontier is the single analytic operator identity `L = 0` on
non-empty finite-prime families (Piece 1), plus the trace/seam build (Piece 2).
This memo separates the two possible resolutions - CLOSURE (L = 0) vs
REFUTATION (L != 0) - from the evidence in hand and gives a recommendation.
It is not a proof of either branch.

## 1. The Gate and what is already proven

`canonicalRealGate3UAt` on the full (infinite) carrier is `|D_S| <= 1`, which by
the proven sharp step is equivalent to `L = 0`, where

```
L = sourceActualBandForwardCoframe + sourcePhysicalCoframeLeakage
  = F + (D - J) = 0,        F in (range J)^perp, (D-J) in (range J)^perp.
```

Already proven (axiom-clean): `J^+ D_S = I`, `P D_S = J`, the sharp
`|D_S|<=1 <-> L=0`, the pointwise/operator energy ledgers `D_S^*D_S = I + L^*L`,
and the forward norm bound `|F| <= 1` (`norm_sourceActualBandForwardCoframe_le_one`).

The forward covariant `F` is bounded (<=1), the metric residual `(D-J)` is
numerically ~0.61-0.62 (probe 884, this session, exact anchor), so both lie in
the same off-Sonin subspace at comparable scale - cancellation is at least
dimensionally consistent, but nothing forces it.

## 2. Closure branch (L = 0)

- Biorthogonality + `P D_S = J` hold a priori and are required of any right
  inverse of `J^+`; they do not force the off-Sonin cancellation.
- The `nil` family closes (trivial); it is degenerate.
- No in-repo theorem forces `(I-P)F = -(I-P)D`.

Score: no positive control mechanism is in-repo.

## 3. Refutation branch (L != 0)

- The legal channel (outer metric residual) is robustly non-zero at ~0.61-0.62,
  scale-stable - but it is only the `(D-J)` factor, not the full sum.
- No non-empty family is proven annihilating in Lean.
- A formal refute is BLOCKED: `F` contains the exact Sonin projector `R0` which
  no finite grid can reach, so the metric side can't be promoted to a proof that
  `F + (D-J) != 0`.

## 4. Bottom line + recommendation

- Evidence leans toward REFUTE for the infinite-carrier form; closure has no
  supporting mechanism and adversarial numerics. But neither is a proof.
- Finite-band form stays closed (docs/860; `card rho`-scaled, finite bands only).
- Recommendation: (1) do not bet on "prove L=0" first; (2) pursue the authorized
  carrier re-point (Piece 2) to make the Gate realizable on a Hilbert/trace-class
  carrier uniform in the band factor; (3) if Piece 2 cannot be uniform, the gate
  is not closable by truncation and the design must face an exact `F` cancellation
  that its definitions do not supply.

RH NOT claimed. decision-support only.



> Superseded note (2026-08-10): 927 - the 'carrier re-point (Piece 2)' branch recommended here CANNOT by itself close the infinite-carrier Gate (support term does not decay; op is not trace-class there). Only Piece 1 (the analytic (I-P)F=-(I-P)D identity) is load-bearing. See docs/proofs/927_gate3u_piece2_correction.md.

