# 1411 — Odd-sector dictionary cell = PLUS_ONE; the radius-shrink route to the wall closes at measurement level; Chuk species file sealed

Date: 2026-09-14. Outcome record for the prereg committed at
`docs/proofs/1410_odd_sector_dictionary_cell_prereg.md` (prereg
UNTOUCHED; gate classes identical to 1407 rev3; law 42 — this wave ran
VALID on the FIRST invocation, the first such since the rev3 rules
were earned). No Lean was written. Nothing was falsified.
RH not claimed, in either direction.

## 1. Verdict up front

`scripts/run_1410_odict.py` inv1, 13.9 s. Sentinels, verbatim:

```
DONE gates=O0:PASS,O1:PASS,O2:PASS,O3:PASS
VERDICT dictPsiQodd=PLUS_ONE q_ratio=0.999999986946 psi=0.000167580082437 Q=0.000167580080249
sha256 docs/proofs/1410_odict_results.json = 75a18188a681fd4cd3bce96e87ee9b9ea92c4d05aed2a43e05d4e2135e413b41
```

The dictionary leg that 1406-1408 left untested — real ODD windowed
tests, the class where the chain's owners live (kill (b):
EvenOddPair targets force `h` odd) — now measures PLUS_ONE as well:
`Q_o / psi_o = 1 - 1.3e-8`, every gate inside its class. And the cell
is structurally informative, not just agreeable:

| channel | register (y-side) | Chuk (paper form) | check |
|---------|-------------------|-------------------|-------|
| pole | -1.55086199015e-4 | -2C(1/2)^2 = -1.55086199015e-4 | ODD-SECTOR SIGN FLIP measured: pole negative, matching paper section 4, and BOTH sides agree to 1e-12 |
| arch | +0.000929368326408 (subtracted) | -0.000929368328596 (in Q) | ~2e-9 abs |
| primes | -0.00125203460786 = +(2log2/sqrt2) g_o(log2), with g_o(log2) < 0 (odd autocorrelation negative at log 2) | +0.00125203460786 via O1 | O1 rel within class |
| total | psi_o = +1.67580082437e-4 | Q_o = +1.67580080249e-4 | 1 + (-1.3e-8) |

Q_o > 0 sits consistent with the paper's certified odd floor
(`eq:oddlower`, 8.2e-15, window `<= 0.8` — our `L = 0.5` is inside it
for BOTH parities); O0 re-tied the shared `A_gen` transcription to the
committed tier-1 `A = -17.3431099115819` before any odd digit.

## 2. What this closes: the last proposed shortcut into the wall

Attack (a) on rung 5, as proposed at the 1408 close, was: shrink the
production radius (`R >= 2^(n0+1)`, height-dominated, 1408 section 6)
toward the root window, where a fixed-L certificate would then bind.
The chain of implications, with each link's status stated:

    +------------------------------------------------------------+
    | L1  psi = Q for EVEN windowed tests:   MEASURED (1407,     |
    |     one cell, all gates PASS)                              |
    | L2  psi = Q for ODD  windowed tests:   MEASURED (this      |
    |     record, one cell; pole sign flip confirms sector form) |
    | L3  chain owners (EvenOddPair family) are ODD real-equivalent|
    |     to r~star r + m~star m: STRUCTURAL (1406 kill (a)+(b), |
    |     model-level lemma argued at formula level)             |
    | L4  Q >= 0 on all real tests (any parity) with supp <= 0.8:|
    |     PUBLISHED (Chuk thm:L08 even 8.9e-18; eq:oddlower odd  |
    |     8.2e-15; unrefereed) / classical for 2L <= log 2       |
    |     (Yoshida, peer reviewed)                               |
    +-----------------------------+------------------------------+
                                  |
    +-----------------------------v------------------------------+
    | CONCLUSION (MODEL level, law 65): a root-supported (<=      |
    | log2/2 < 0.8) healthy owner with qw < 0 CANNOT coexist with|
    | L1-L4. The radius-shrink route is closed: not by absence of|
    | an engineering idea, but because its target is provably    |
    | empty — small windows are exactly where positivity holds.  |
    +------------------------------------------------------------+

Honest load-bearing caveats: (i) L1/L2 are each ONE bump cell — the
dictionary is an algebraic identity claim whose verification between
`L = 0.5` and the owner family is not done; (ii) L4's stronger
(`<= 0.8`) form is unrefereed — but the classical `2L <= log 2`
(Yoshida/Connes-Consani) already suffices, because root-supported
owners sit at `L = log 2 / 2` inside the closed classical window;
(iii) everything here is MODEL: no Lean obligation was touched, and
none CAN be touched by these measurements (law 65). The conclusion is
therefore stated as: **the route-(a) program has no measurable
support and contradicts published theorems on its own target class —
it is closed; reopening it requires first breaking L1/L2/L4 at
measurement, and no such break was found where we looked.**

## 3. Final position of the wall

With (a) closed, the register's map of the remaining distance to RH
is complete at paper level:

* `B0b`: `(forall healthy g, 0 <= qw g) <-> SourceRH` — machine
  checked. The left side quantifies over EVERY radius, and by the
  paper's own equivalence sentence ("positivity for every L is
  equivalent to RH"), no fixed-L certificate can supply it: the wall
  is exactly the classical Weil criterion in the register's normal
  form, and its general proof IS the millennium problem, not an
  engineering backlog.
* What the campaign has genuinely added around it (all still true):
  a machine-checked counterexample mechanism (1081 exit + 1375 F3:
  `¬RH` => height-dominated-radius owner with strict detector sign),
  the iff bridge (1343/B0b), 107/107 sign-consistent numerics, the
  exact geometry of why the tower cannot shortcut through small
  windows (1402 repartition + this record), and a fully adjudicated
  external-certificate species (1405-1411: reach, blind-spot kill,
  dictionary both parities, radius disjointness, route closure).

The executable queue is now empty for the third time, and this time by
MATHEMATICAL NECESSITY (every named finite surface has run AND the
last structural escape has been measured closed), not by exhaustion of
appetite. Anything further toward "breaking through" is a new proof
idea for full-quantifier positivity, i.e. new mathematics, or an
explicitly authorized multi-day formal campaign that changes what the
wall IS (e.g. formalizing the dictionary itself as a Lean bridge
theorem `psi = Q` — publishable register content, zero progress on
RH). Both are Peter's decisions; neither is a task I can complete on
standing instructions without one.

## 4. Kill scope honored

One model cell, one route-closure argument (L1-L4 with statuses
labelled), no falsification of the chain, Yoshida, Chuk, or the
sup-law; no Lean funded; no claim about RH in either direction. The
Chuk species file (arXiv:2608.24827) is SEALED at 1405-1411.

## 5. Next steps

1. Register closure wave: map item 37, root project log, frontier
   card, dead-routes archive line ("radius-shrink route: closed
   1411"), commit + push. Done in this commit.
2. Peter's fork, now cleanly two-valued: (F1) freeze the mainline at
   its proven normal form (my recommendation: every finite surface is
   exhausted, and the remaining statement equals RH); or (F2) fund a
   decision-grade formal project with a DIFFERENT goal — formalizing
   the dictionary bridge (`psi = Q` for even windowed tests in Lean,
   ~multi-day, publishable, zero RH progress) or a genuinely new
   positivity idea, which nobody can commit to on a checklist.
3. If F2-dictionary is chosen: prereg first (law 42 applies to formal
   campaigns too), and the odd-sector lemma of 1406 kill (a) would be
   its first free brick.
