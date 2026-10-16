# Record 2720: P3 certified strip-decay constants and joint repricing
at the two n = 3 candidate rows

**Verdict: P3 GREEN AT MODEL GRADE -- the tail constraint (P3 premise)
closes at row B (gamma_2, N=5) at its own stored index n = 3 with the
certified contraction pair (T = 64, q* = 2.5e-16), lambda_min = 3.2e-19,
compatible with the record-2718 gate certificate (lambda > 15.86).  Row A
(gamma_1, N=4) does NOT close at n = 3 (lim = 1.74e10) but closes at
n = 4 (lim = 0.256).  The certified-constants run carries a zero-fail
coverage bugcatch on BOTH rows (envelope dominates the L300 pipeline
cardinal on the full 972-point grid, worst headroom ratio 6.0e-4 /
3.3e-4).**

## Task card (bounded-progress gate)

```text
consumer    selectedOwner_fullOrbitSpan_fourthOrderSpectralTail_of_q
            (C1FourPointHighShellTail.lean): the three forall-strip
            hypotheses hbaseContract / hbaseQuartic /
            hcorrectionQuadratic were satisfiable only by the SAMPLED
            record-2033 constants; P3 replaces them with certified
            envelopes at the two candidate rows
owner       the stored record-1980 binary64 owners (27 / 56 nodes) at
            (14.134725141734693, N=4) and (21.022039638771556, N=5);
            seed object = the L300 pipeline cardinal
            [int e^{(s/2)x} f(x)dx]^{10}, f = smooth_seed_raw
premise     "P3 certified C4/C2 strip decay constants" (named in
            records 2718/2719 as the remaining analytic brick)
criterion   certified (q*(T), C4*, C2*) with the coverage bugcatch at
            zero fails per row, plus the joint repricing table
budget      one WSL run (51 s) + this record
stop        verdict recorded (this record)
```

## Certified seed-derivative table (S1)

IBP ladder on the seed factor L1(v) = int e^{vx} f(x) dx over
[-2, 2] (boundary-flat: f^(j)(+-2) = 0 for all j):

```text
+-----+----------------+------------+------------+
|  k  | D_k (certified)| closed form| encloses   |
+-----+----------------+------------+------------+
|  1  | 2.004632472964 | 2          | yes        |
|  2  | 8.125733214369 | 8          | yes        |
|  3  | 8.3412e+01     | --         | --         |
|  4  | 1.5351e+03     | --         | --         |
|  5  | 6.0789e+04     | --         | --         |
|  6  | 5.6102e+06     | --         | --         |
|  7  | 1.1030e+09     | --         | --         |
|  8  | 3.4356e+11     | --         | --         |
|  9  | 1.4474e+14     | --         | --         |
| 10  | 7.7329e+16     | --         | --         |
| 11  | 5.0710e+19     | --         | --         |
| 12  | 3.9953e+22     | --         | --         |
+-----+----------------+------------+------------+
```

Method: one mpmath.iv jet (order 12) per cell over 4096 cells on
[1/4096, 1/2], D_k = 4 int_0^{1/2} |T^(k)| du (the flat middle
contributes zero; the two ramp halves are equal by the T-symmetry),
sliver (0, 1/4096] charged neighbor-sup x 8 x width.  Binomial-product
jets (the jet-algebra law: derivative-sequence products need
math.comb, not Taylor-coefficient convolution -- the run-1 D_2 = 4.06
defect).  Sliver evidence scan: worst observed fraction of the charged
bound 0.000e+00 at 1024 points x k in {2, 6, 12}.

## Certified strip constants (S2/S3) and inflation factors

```text
+---------+-------------+-------------+-------------+-------------+
| row     | C4* (base)  | C2* (corr)  | q*(32)      | q*(64)      |
+---------+-------------+-------------+-------------+-------------+
| gamma_1 | 1.538e+07   | 8.401e+06   | 3.836e-06   | 5.432e-18   |
| F vs    | 1.006e+05   | 1.228e+04   |             |             |
| gamma_2 | 6.052e+07   | 2.816e+07   | 4.903e-03   | 2.525e-16   |
| F vs    | 9.692e+04   | 1.472e+04   |             |             |
+---------+-------------+-------------+-------------+-------------+
```

F = certified/sampled (sampled = record-2033 grid values 152.96/683.9
and 624.5/1913.3).  The ~1e4-1e5 inflation is the seed-10th-power
amplification of the mass-piece floor: near the interpolation nodes
the envelope uses Psi = 3 e^{r_z} per factor (r_z = max(Re z,
1 - Re z)), and Psi^10 amplifies the per-factor slack by 10 orders.
Both certified contractions at T = 2^(N+1) are far STRONGER than the
sampled 2^-14: q*(32)/2^-14 = 6.3e-2 (row A), q*(64)/2^-14 = 4.1e-12
(row B).

Envelope structure (all certified, no observational premises):
sigma eliminated by endpoint maxima per factor (ds_w =
max(|Re w|, |1-Re w|)); continuum cover by INTERVAL cells (coarse
0.1 overlaid by 0.005 fine cells near active heights, tail ladder
x1.05 to 600, both signs); per-term bound
|c_z| MQ_z(t) Psi_z^{10} with Psi_z = min(3 Ez_z,
min_k Ez_z D_k 2^k / tau^k), tau = |t - Im z|, MQ_z the endpoint-max
product over ALL owner nodes; c_z = y_z / (prod_{w!=z} (z_w - z) *
3^10) in absolute value with outward pads.

## Joint repricing (S5; 2033 formulas verbatim)

Two lanes.  PAIR: the certified (T = 2^(N+1), q*(T)) pair -- the
contraction premise is the certified q*, priced at q*^{2n}.  KEEP-Q:
the sampled contraction 2^-14 kept, certified C4* C2* priced against
the 2033 F_max budget.

```text
Row A (gamma_1, N=4, T_pair = 32, q* = 3.836e-06):
+-----+-----------+-----------+-------------+----------------+
|  n  | F_total   | F_max     | lim_pair    | joint (PAIR)   |
+-----+-----------+-----------+-------------+----------------+
|  3  | 1.236e+09 | 2.324     | 1.742e+10   | False          |
|  4  | 1.236e+09 | 3.808e+04 | 2.564e-01   | True (lmin 8.9e+04) |
|  5  | 1.236e+09 | 6.240e+08 | 3.773e-12   | True (lmin 0.17)    |
|  6  | 1.236e+09 | 1.022e+13 | 5.552e-23   | True           |
+-----+-----------+-----------+-------------+----------------+

Row B (gamma_2, N=5, T_pair = 64, q* = 2.525e-16):
+-----+-----------+-----------+-------------+----------------+
|  3  | 1.427e+09 | None      | 9.499e-49   | True (lmin 3.2e-19) |
|  4  | 1.427e+09 | 1.698e+03 | 6.055e-80   | True           |
|  5  | 1.427e+09 | 2.781e+07 | 3.860e-111  | True           |
|  6  | 1.427e+09 | 4.557e+11 | 2.461e-142  | True           |
+-----+-----------+-----------+-------------+----------------+
```

(F_max = None at row B n = 3 means the SAMPLED constants already fail
the tail constraint there -- lim_sampled = 93.2 >= 1; the certified
pair is what turns row B on.)

Reading: the record-2716/2717/2718 gate row family has TWO live n = 3
candidates; the tail side (this record) closes at row B's own index
with eight orders of lambda headroom (3.2e-19 vs the gate's 15.86),
and at row A after ONE shell-index bump (n = 4, lam_min 8.9e4).  In
the conservative KEEP-Q lane (sampled contraction retained) both rows
close only at n = 6.  The inflation absorption dial is the shell
index, exactly as the pre-run analysis anticipated.

## Coverage bugcatch (S4) -- the instrument's own falsifier

The envelope must dominate the L300 pipeline cardinal
(op.cardinal_transform) on the 2033-style grid: 3 sigmas x 81 heights
x 2 signs x 2 channels per row, relative pad 1e-9.  Final run:
fails = 0 on BOTH rows (row A worst sampled/envelope ratio 6.049e-4,
row B 3.302e-4 -- the envelope is tightest near the nodes, as
expected from the mass-piece floor).  This bugcatch caught or
confirmed every defect below; it is the reason the certified numbers
are quotable.

## Instrument defects found and fixed en route (all six)

```text
D1  IBP denominator transcription: 2^k/(2 tau)^k instead of
    2^k/tau^k -- a 2^-k UNSOUND (too-small) bound; the min-ladder
    then picked invalidly small pieces and the coverage ratios read
    6e54.  Run 2's constants were invalid; the bugcatch fired.
D2  Correction channel built over the 3 active nodes only: c_z and
    every product must run over the FULL 27/56-node owner list (the
    sampled object's own convention); only the +-1 nodes contribute
    terms.
D3  Tail Lipschitz correction with dPsi = max over all 12 IBP-piece
    derivatives: sound but inflates the tail by ~1e10 near node
    heights (row B corr sup 2.17e16 vs profile max 1.07e6), because
    the k = 12 piece's derivative explodes as tau -> 0 while never
    being the min.  Removed: the interval-cell bound needs no
    derivative machinery (each factor is bounded at its cell-worst
    point; the mass piece floors Psi near nodes).
D4  Cell-merge teleport: the coarse loop jumped to the next FINE
    breakpoint, creating a 10-unit cell [2, 12.13] (base sup
    8.17e7).  Fixed by overlapped covers (coarse + fine), which are
    sound because the sup takes the max over all cells.
D5  Non-strict clamp loop: "while t <= END: t2 = min(t + step, END);
    t = t2" spins FOREVER when t lands exactly on END (t2 == t, no
    progress, condition still true).  Hung two runs (10-19 min
    silent CPU).  Fix: strict "<" at every clamped ladder.  Found by
    a per-stage FILE-logged timing probe after two profiler probes
    died in stdio buffers (the "| tail" pipe prints only at EOF --
    log-not-pipe, third incident this quarter).
D6  Coverage-side bugs: (a) an ABSOLUTE 1e-9 pad demanded envelope >=
    1e-9 at deep-decay points (envelope 1e-40 ABOVE the sample 1e-61
    still "failed"); relative-only pad.  (b) The envelope was
    evaluated at |t| while the sample sat at -t -- on an asymmetric
    owner (the base target set has no conjugate of rho + 0.5) the
    two sides differ; row B corr read 23 phantom fails at t = -95.
```

## Nonclaims

- Model-grade owner constants (stored binary64 nodes; the
  node-radius transfer brick stays open).  The identification of the
  Lean `laplaceAt base/correction` with the pipeline cardinal is the
  P2/seam duty, unchanged.
- Numeric certified enclosures, not Lean theorems; the Lean
  forall-strip absorption (instantiating the three hypotheses at
  these constants) is a separate brick, as is the lambda-side gate
  absorption of records 2717/2718.
- The PAIR lane's T = 2^(N+1) uses the P4 shell-threshold cap as a
  hypothesis; P4's shell inequalities in Lean are unchanged.
- Row A at n = 4 is an absorption reading, NOT a new gate row: no
  gate-sign analysis exists at n = 4 and none is claimed.
- No producer GO, no map-103 reopening, no SourceRH, no RH claim.

## Evidence

- `scripts/p3_certified_strip_constants_2720.py` (self-contained
  instrument; `__main__` guarded; writes the artifact)
- `results/2720_p3_certified_strip_constants.json` (D table, sliver
  scan, per-row constants, q* ladders, coverage including worst
  points, full n-tables, provenance sha256s)
- `results/2720_p3_run.log` (the run log; 51 s WSL)
- Inputs: `scripts/fourpoint_actual_owner_1980.py` (owner builder),
  `scripts/fourpoint_powered_seed_1981.py` (L300 seed pipeline),
  `scripts/fourpoint_gate_tail_pairing_2033.py` (joint formulas
  reproduced verbatim), `results/2032_gate_row_search.json` (sampled
  constants and row metadata)
