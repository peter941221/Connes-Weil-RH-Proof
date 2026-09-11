# Record 1335 — Corridor capacity verdict: `hcolumn` is inconsistent with the committed archimedean model (truncation level)

Date: 2026-09-11.
Status: VERDICT RECORD for the official record-1334 run
(`docs/proofs/1334_probe_results.json`), all gates green. Paper analysis of
consequences; authorizes nothing new. MODEL-twin numerics: no statement
about the formal `ran P_S`, no vanishing, no `qw` sign, no `SourceRH`, no
RH conclusion. RH is not claimed.

## 1. Registered verdict, verbatim outcome

```text
KERNEL   = CONFIRMED   (R1 = 387/388.9 = 658/661.2 = 952/955.2 = 0.995+-,
                        all three cells inside the [0.95, 1.05] band;
                        cliffs sharp: 38 / 14 / 7.0 x; all other gates 0 err)
CAPACITY = FALSIFIES   (decisive cell L=48: min_tau A_tau = 1.995 >= 1.20)
```

## 2. What was established (model level)

(i) **The carrier is far from empty.** The near-kernel sector of the
discrete Toeplitz model of `T_phi w = P_+(phi w)` has dimension equal to the
symbol winding `|W(L)| ~ 2 L log L`, matching to 0.5% at every domain, and
the winding diverges. The mechanism is the Fredholm index, corroborated by
the sign controls (unit +shift has kernel {0}; phi = 1 is unitary). C0a is
resolved in the nontrivial direction, and the earlier record-1331 worry
that the radial pipe might be EMPTY is empirically retired: the pipe is
full — the problem is what flows through it.

(ii) **The kernel diagonal cannot hide in the corridors.** The corridor
capacity of the near-kernel sector, `A_tau` of record 1334 section 1
(normalized `(2 + 2cos)` energy per sector dimension), is
`1.995 - 2.012 ~ 2` for every prime lag `tau = log p`, p in {2,3,5,7,11},
at every domain — the value a generic (non-hiding) span has by averaging.
The `hcolumn` series (record 1329 section 1: `E_col = sum_j (2 +
2 Re<f_j, U_tau f_j>`) converges only if the carrier's kernel-diagonal mass
sits asymptotically inside the zero corridors of every prime-log lattice;
the measurement says the near-kernel sector contributes the FULL average
defect `~ 2` per direction, and the sector dimension `|W(L)|` diverges. So
the 1329 section 8 necessary condition (vanishing-exclusion counting must
dominate the non-antiperiodic mode count) fails at capacity zero: the
committed archimedean-only phase carries no exclusion mechanism at all.

## 3. Consequence for G8 P1 (map update)

```text
+---------------------------------------------------------------+
| 1330 brick          : stands (conditional, vacuously useful)  |
| 1324-1328 chain     : premises empirically inconsistent with  |
|                       the committed HT model at truncation    |
|                       level -> NO further formal investment   |
|                       in the radial hcolumn leg is justified  |
|                       on this model.                          |
| 1331 branch table   : outcome row 2 (¬hcolumn) is the live    |
|                       direction; rows 1 and 3 empirically     |
|                       closed.                                 |
| G1 (nondegeneracy)  : empirically TRUE (huge kernel); still   |
|                       no formal nonzero carrier element.      |
+---------------------------------------------------------------+
```

The divergence source is now identified structurally: `arg phi(x) ~
-4 pi x log x` — the archimedean phase winds with density `~ 2 log|x|`, so
`W` is populated by index directions whose antiperiodicity defect at every
prime lag is O(1) each and whose count diverges. For `hcolumn` to have any
chance, the model phase must stop winding generically and start winding
ONLY where zeros exclude mass — i.e. the phase must carry the zeta side
(completed `xi` quotient) rather than the pure `Gamma_R` quotient. That is
the record-1332 section 3 "C4 model-upgrade" memo, and this record
sharpens it: **C4 is the only surviving path to a satisfiable `hcolumn`;
every other radial-leg investment is spent.**

## 4. What this record does NOT establish

- No formal theorem: the probe is a twin; the Lean premise `hcolumn` is
  about `ran P_S`. A formal ¬hcolumn needs explicit carrier SEQUENCES
  (each an entire function with the forced lower-lattice zeros of record
  1332 section 2, two-sided weighted in L2) with the prime-defect series
  diverging — a construction campaign (and its formalization needs the G2
  RKHS package). Cost estimate: multi-record; benefit: kills or
  legitimizes the radial leg at the theorem level.
- No statement about any model that includes zero data.
- No RH claim of any form. RH is not claimed.

## 5. Decision requested (nothing is self-authorized)

```text
Option H  HOLD: accept the truncation-level inconsistency, freeze the
          radial leg exactly as 1331 directed, bank C0 as closed, and
          spend future effort on non-radial G8 legs only.
Option K  CONSTRUCT: open the ¬hcolumn attack as a paper campaign
          (explicit carrier sequences from the index mechanism; probe-
          guided; each numerics step needs its own prereg).
Option M  MODEL: commission the C4 memo — precise definition of a
          zero-carrying scattering phase, what it does to W, to G1, and
          to hcolumn feasibility — analysis only, no Source changes.
```

Recommended order: M first (cheapest, and it is the decision the campaign
actually faces), then H or K per M's findings.

RH is not claimed.
