# Record 2717: P5 n=3 probe — channel flip budgets and two-grid honest joint

**Verdict: PROBE GREEN — THE GATE SIDE OF BOTH n=3 CANDIDATE ROWS IS
DISCHARGEABLE BY A %-GRADE CERTIFIED ENCLOSURE.**  At the sampled-grade
channel decomposition of the stored record-2032 rows, a single channel
box of relative width

```text
eps_unified = 3.36%   discharges sign(C) AND sign(det) at (gamma_1, N=4, n=3)
eps_unified = 2.92%   discharges sign(C) AND sign(det) at (gamma_2, N=5, n=3)
```

certifies the exact gate branch (rays / all respectively), and the joint
lambda interval then follows from the record-2716 honest constants
(grid-independent).  The two stored grids (dxi = 0.02 / 0.01) agree on
every coefficient to 1e-9..1e-10 — eight orders below the budgets.  This
is the priced certification target for the interval rig (swing 2b): the
rig does NOT need 1e-12 enclosures; it needs ~1% enclosures, a factor
~1e6 looser than the pipeline's own float precision.

This is a sampled-grade margin ledger, not a certificate: the enclosure
itself is not built here, and the stored owner remains the record-1980
model (under-approximation).

## Task card (bounded-progress gate)

```text
consumer    riemannHypothesis_of_four_point_span_contradiction_producer,
            via the record-2708 contract P5 duty at n = 3
owner       the stored record-1980 trial owners (gamma_1, N=4) and
            (gamma_2, N=5) at index n=3 (27- and 56-node models)
premise     the gate-branch signs (C < 0; det sign) at the candidate rows
            are sampled floats of unknown robustness
criterion   exact worst-case flip budgets eps such that ANY channel
            enclosure of relative width < eps certifies the branch, plus
            two-grid joint survival
budget      paper arithmetic on stored artifacts (2032/2033/2716); 30-dps;
            no rig, no build
stop        verdict recorded
```

## Channel decomposition (record-2032 gate_row, recovered exactly)

The stored artifact carries the archimedean integrals `arch[0..2]` and
the sums, so the prime channels are recovered exactly:
`pr[i] = sum_i - arch[i]` (rational subtraction of stored binary64
values).  All six channels of both candidate rows at both grids:

```text
(gamma_1, N=4, n=3)  -- rays branch (C<0, det<0 => Delta>0)
  arch0 = -4.6832e+04   pr0 = -9.8387e+04   (both NEGATIVE: reinforcing)
  arch1 = -6.9629e+07   pr1 = -2.4141e+08
  arch2 = -1.1355e+11   pr2 = -4.6870e+11
  C = -1.452195e+05  b = -3.110370e+08  D = -5.822451e+11
  det = -1.219067e+16   lambda(vertex) = 2141.8   L+ = 1381.5

(gamma_2, N=5, n=3)  -- all branch (C<0, det>0 => Delta<0)
  arch0 = -4.0392e+04   pr0 = +3.1901e+04   (C is a cancellation)
  arch1 = -1.0833e+08   pr1 = +8.8352e+07
  arch2 = -3.1996e+11   pr2 = +2.0128e+11
  C = -8.491123e+03  b = -1.998117e+07  D = -1.186764e+11
  det = +6.084493e+14   lambda(vertex) = 2353.2   (gate holds everywhere)
```

## Flip budgets (exact worst-case boxes)

Definitions (script header carries the derivations): `eps_C =
|C|/(|arch0|+|pr0|)`; `eps_Delta = |sqrt(C*D) - |b|| / (sqrt(C*D)+|b|)`
for C*D > 0 (unbounded for C*D <= 0); `eps_unif = min(eps_C, |det| /
(|D| S0 + |C| S2 + 2|b| S1))` with `S_i = |arch_i| + |pr_i|`.

```text
+----------------+------+---------+--------+--------+--------+---------+
| row            | grid | branch  | eps_C  | eps_D  | eps_1  | joint@  |
|                |      |         |        |        | (unif) | new geom|
+----------------+------+---------+--------+--------+--------+---------+
| (14.1347,4,3)  | .02  | rays    | 1.0002 | 0.0337 | 0.0336 | YES     |
| (14.1347,4,3)  | .01  | rays    | 1.0002 | 0.0337 | 0.0336 | YES     |
| (21.0220,5,3)  | .02  | all     | 0.1175 | 0.2274 | 0.0292 | YES     |
| (21.0220,5,3)  | .01  | all     | 0.1175 | 0.2274 | 0.0292 | YES     |
+----------------+------+---------+--------+--------+--------+---------+
```

(eps_1 = eps_unified: ONE channel box of that width certifies both signs
simultaneously.  (gamma_1,4,3)'s C-sign budget exceeds 1 because both
channels reinforce — the sign is un-flippable by any sub-total
perturbation; its binding budget is the determinant's 3.36%.)

Reading: **any certified enclosure of the six channels at relative width
below eps_unif certifies the branch, and the branch determines the joint:**

```text
(gamma_1,4,3): rays [L+, inf) with L+ = 1381.5  vs Ltail = 0.683 (2716)
               -> joint lambda in [1381.5, inf), certified-free above L+
(gamma_2,5,3): all-branch gate vs Ltail = 15.86 (2716)
               -> joint lambda in (15.86, inf), gate side VACUOUS
```

On the unbounded branches the gate side contributes no upper constraint,
so the joint interval needs no lambda certification at all — the whole
P5 gate duty reduces to the two sign certificates.

## Two-grid and sensitivity controls

- The 0.02 -> 0.01 grid refinement moves every coefficient by
  1e-10..6e-9 relative (C: 2.9e-10 / 1.1e-10 at the candidates; det:
  1.9e-9 / 2.3e-9) — EIGHT orders below the budgets.  The record-2028
  convergence ladder (<= 1.4e-13 at dxi <= 0.005) says the residual grid
  slack is far smaller still.
- Both candidates keep the honest joint at the 2710 geometry on BOTH
  grids, and under the record-2354 sensitivity eps^2 = (3/2)A.
- Anchors (in-run, all green): (a1) the 2033 stored rows are BITWISE the
  2032 primary-grid rows (0 mismatches over 35x4 fields); (a2) stored
  lambda == float(b/C) bitwise on all 90 gate entries; (a3) the record-
  2716 A_n fields (both geometries, all 35 rows) reproduce EXACTLY from
  the committed constants via the 2716 module (imported, not copied).

## What the interval rig (swing 2b) must enclose — priced plan

The rig certifies SIX channel integrals on one grid (dxi = 0.02
suffices; the budget dwarfs the refinement slack):

1. **Prime channels pr[i]**: kp = sum over the 2532 prime powers
   (cutoff log 10) of (2 log p / sqrt(k)) cos(2 pi xi log k) — directed
   one-sided-guard summation per node (record-2262 pattern), 2501 nodes
   x 2532 terms; then the trapezoid combination with the f_i boxes.
2. **Archimedean channels arch[i]**: needs W = |lb|^{2(n+1)} |lc|^2 with
   lb/lc cardinal transforms over the 27/56-node owner.  Atoms: node
   products (interval polynomials — easy), the seed Laplace transform
   (GL-800 with a certified remainder via the record-2056 ellipse
   pattern; the seed is analytic on a stadium, convergence is
   geometric), and the digamma weight sigma (the 1918 series: 8
   harmonic terms + 6 Bernoulli corrections — interval series evaluation,
   record-2305 precedent).
3. **Power amplification**: |lb|^{2(n+1)} = |lb|^8 at n=3 widens boxes
   by the power — the ~0.4% relative box on |lb| needed for a 3%
   W box is ~4 orders looser than the GL floor (record-2053: t-
   independent ~e^{-2K} floor inside the trust horizon).
4. **Trapezoid remainder**: the record-2270 Euler-Maclaurin corrected
   form (T_h + (h^2/12)(|f'(a)|+|f'(b)|) + (h^4/720) int |f''''|) with
   coarse majorants — the 3% budget absorbs what a 1e-12 rig could not.
5. **Branch and joint assembly**: signs from the certified boxes; L+ by
   monotone propagation (its worst-case box end enters the ray start);
   the tail constants are the committed 2716 values (m = 1 floor,
   Cspec = 128.65).

The rig certifies the GATE side at trial-owner model grade.  The tail
side keeps its own premise: the decay constants C4/C2 are sampled
(record-2033 height-grid maxima) — that is P3/G4 territory, unchanged.

## Nonclaims

- No certificate is issued here: this record prices the margins, it does
  not build the enclosure.  "Dischargeable by a %-grade enclosure" is a
  plan statement, not a gate witness.
- The stored owner is the record-1980 model: known zeros in the formal
  ball + orbit + healthy targets (UNDER-approximation, 19/48 known
  zeros at the two candidates).  The COMPLETE-owner gate (rung ii)
  additionally needs G2 (the full closed-ball zero-set identification)
  and re-measurement on the complete owner.  The flip budgets protect
  against ENCLOSURE error of a FIXED owner's integrals; they say
  nothing about owner perturbation (adding zeros changes the channels,
  possibly at O(1)).
- The decay constants remain sampled (P3 open); m = 1 floor; no
  multiplicity input.
- No map-103 reopening: the freeze lifts only when the named probe —
  now THIS rig plus the complete-owner rung — produces the
  complete-owner gate certificate.  This record sharpens the probe and
  proves its target is loose (percent-grade), which is the difference
  between a multi-session 1e-12 instrument and a bounded one.
- No producer GO, no SourceRH, no RH claim; paper arithmetic only.

## Evidence

- `scripts/g1_p5_n3_probe_2717.py` (anchors a1-a3, exact budget
  formulas, imports the 2716 module verbatim for branch/joint semantics)
- `results/2717_p5_n3_probe.json` (45-row x 2-grid ledger, candidate
  focus blocks, two-grid joint table, source sha256)
- Inputs: `results/2032_gate_row_search.json`,
  `results/2033_gate_tail_pairing.json`,
  `results/2716_g1_joint_acceptance_repricing.json`,
  `docs/proofs/2716_g1_joint_acceptance_repricing.md` (honest joint),
  `docs/proofs/2708_joint_acceptance_contract.md` (section-5 branches),
  `docs/proofs/2710_high_shell_geometry_verified.md` (d = 169/16).
