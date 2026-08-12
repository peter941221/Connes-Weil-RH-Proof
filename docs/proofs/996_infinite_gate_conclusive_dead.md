# 996 - Infinite-carrier Gate-3U: precise conclusive-dead verdict on the canonical gate

Date: 2026-08-11. Status: precise conclusive-dead-by-definitions decision (repo-verified,
no Lean edit, mirror dirty). Scope: the canonical infinite-carrier Gate-3U readout ONLY.
It does NOT claim dead for the finite-band Route-A gate (closed) nor for RH. RH NOT claimed.

## What "conclusive-dead" means here (per the no-stop rule)

A path ends when a named guard / counterexample / structure-level impossibility is shown.
The infinite-carrier Gate is conventionally dead at THREE independent, definition-level
levels, so no further work short of a genuinely new continuous/effective structure is
spent on the canonical gate as currently defined:

## L1 - Support trace diverges (docs/927, route/definition)
On the infinite carrier the Gate bound would read `(card rho)*(||Support|| + ||Tail||)`.
- Tail: ||Tail|| ~ exp(-B/4) decays;
- Support: ||Support|| does NOT decay in the band cut B; it sums the displacement-B
  indices with fixed operator norm, so `(card rho)*||Support||` -> inf as rho -> whole carrier.
=> no finite upper bound on the infinite-carrier support trace; the canonical Gate
cannot be a proved finite-trace bound there.

2. L2 no trace-class on the raw tail (docs/860, object layer)
The raw renewal tail is `tsum` over an infinite Nat mult-index (PUnit | Nat * ...) around
the detectorOperator = A^t A, an L2 Fourier multiplier - neither compact, nor
Hilbert-Schmidt, nor trace-class on the uncompressed (infinite-dim) carrier.  No
`IsTraceClassAlong` certificate exists (repo guard also bans trace/support interchange,
Proof 807). Note docs/860 also corrects: the prolate lane is a SEPARATE semi-infinite
band with its own machinery - claimed dead here is the renewal tail / canonical Gate.

3 - `(*)` operator front reduces to `F = J - D`; necessary `(I - (R0-S))(J-D) = 0`
(docs/995). Numerics 824/884 (outer ~0.61, scale-stable) + support-non-decay lean NEGATIVE
for non-empty families, but the off-band mass needs the exact Sonin intersection R0
(unreachable). So this last front stays OPEN in the identity sense but cannot help the
defined Gate (killed at L1/L2 regardless): the identity `F=J-D` would not rescue a
non-summable support trace even if it held on some family.

## Net route

- canonical Gate-3U = finite-band Route-A (route/closed). 
- infinite-carrier Gate keeps its real analytic identity (docs/872 `(*)`/995 `F=J-D` D)
  but it neither needs to be closed for the canonical deliverable, nor can its finite-bound
  form be certified (L1/L2).
- Remaining genuinely-open maths unrelated to the canonical gate: `(I-P)F=-(I-P)D` for
  non-empty families (docs/872/995/Burnol). RH not claimed.

RH not claimed.
