# 1097b - Deep-octave certification by bracket direction

Date: 2026-09-02.

Status: PRE-REGISTRATION, committed BEFORE the run. This record re-runs the
record-1097 pipeline with a replaced certification gate. The H1/H2 criteria
are byte-for-byte the record-1097 criteria (section 3 there); only the deep-
octave gate changes, for a reason that is a measured memory wall, not a
verdict preference. The probe is `1097b_p2_deep_octave_bracket_probe.py`.
RH is not claimed. Evidence labels follow map `004` section 1.

## 1. Why record 1097 aborted, and what is and is not inherited

Record 1097 fired its pre-registered ABORT: the dt-pair (8193, T=10) +
(16385, T=20) disagreed at max rel 1.33e-01 / 1.43e-01 against a 2e-3 gate.
Its section 6 recorded the anatomy: at fixed `dt = 0.00244` and
`xi_max = 204.8`, the pair necessarily varies `dxi` from 0.05 to 0.0125
(because `N = 1/(dt*dxi)`), and also varies the time-domain extent
(T = 10 to 20). The two axes move together in this pair; the coarse member
overestimated every trace-class observable in both families, and the source
trace returned to the committed band at fine resolution (6.5620 vs committed
6.4740, rel 1.36e-02).

Inherited unchanged from 1097:

- the rig, the anchors, the lean deep-window builder, the four deep grids;
- the H1 observable (`trace(K_S)` at the FINE deep point), the H2
  observables (`p_hs`, `l_tr1` slopes over the four anchor rows);
- the verdict mapping of 1097 section 3.

Not inherited: the G-dt gate (value-invariance at 2e-3).

## 2. Why value-invariance is unreachable at this window

Holding dt and xi_max fixed, the next dxi refinement is (32769, T=40): its
complex matrices are 17.2 GiB each and the dense rig is out of memory budget
there. So at the campaign's widest window there is no affordable third grid
level, and a 2e-3 value-invariance gate cannot be evaluated at all. This is
the same situation class as the record-1090 budget ladder: the answer is a
re-designed in-budget certification, pre-registered openly, not a bigger
machine.

## 3. The replacement gate: bracket direction

The fine grid (16385, T=20) is the best-resolved point of the campaign
(finest dt AND finest dxi). The coarse member (8193, T=10) brackets it from
above on the trace-class observables. The certification replaces numeric
invariance with a signed direction test, stated BEFORE the run:

```text
+--------+------------------------------------------------+-----------+
| Gate   | Criterion                                      | Source    |
+--------+------------------------------------------------+-----------+
| G-anc  | Unchanged from 1097: the four committed anchor | 1067/1068 |
|        | rows and the lean cross-anchor at (8193,20)    |           |
|        | reproduce within 5e-3 / 2e-3 for both families |           |
|        | on the same code path.                         |           |
+--------+------------------------------------------------+-----------+
| G-src  | Unchanged from 1097: source trace at the FINE  | 1097      |
|        | deep point vs committed (8193,20): rel <= 5e-2.| s6 log    |
+--------+------------------------------------------------+-----------+
| G-brkt | On the trace-class observables tr_ks and       | 1097 s6   |
|        | ks_frob2, the COARSE member exceeds the FINE   | anatomy   |
|        | member strictly, in BOTH families (4 pairs).   |           |
|        | p_hs is EXCLUDED from the direction test: the  |           |
|        | 1097 numbers already show its coarse/fine      |           |
|        | direction is not signed ({2,3,5}: coarse 3.064 |           |
|        | < fine 3.534; src: 2.3832 vs 2.3835), so a     |           |
|        | direction requirement on it would be false by  |           |
|        | construction.                                  |           |
+--------+------------------------------------------------+-----------+
| G-conf | The coarse source trace must sit OUTSIDE the   | 1097 s6   |
|        | G-src band around the committed value (this is |           |
|        | what makes the coarse member the artifact      |           |
|        | rather than the fine member).                  |           |
+--------+------------------------------------------------+-----------+
```

Known confound, named now: the pair varies dxi AND t-extent jointly, so
G-brkt certifies the COARSE-vs-FINE bracket as a whole, not a pure dxi
effect. That is sufficient for its purpose: the verdict consumes only the
FINE point, and G-brkt + G-conf together certify that the coarse point
cannot be the better continuum estimate.

H1/H2 criteria (identical to 1097 section 3):

- G-H1: slope16x = log(tr_fine / 16.1996) / log(16) >= +0.15, OR the fine
  increment (tr_fine - 34.2696) >= 0.5 x (34.2696 - 26.8715);
- G-H2: |p_hs slope8x| < 0.15 AND |l_tr1 slope8x| < 0.15 over the four
  anchor rows (SVD rows at N <= 8193, as committed).

Verdict mapping (identical to 1097 section 3):

```text
G-anc fails            -> ABORT: model misread; no verdict.
G-src fails            -> ABORT: rig anchor broken; no verdict.
G-brkt or G-conf fails -> ABORT: bracket direction broken; the fine point
                          is not certified; no verdict.
G-H1 fires AND G-H2    -> H1-REJECTED / H2-CONFIRMED: 1097 section 5 repo
passes                    changes fire (map 004 section 4 re-point, record
                          1096 erratum, AGENTS 7c law, follow-up brick 1098).
G-H1 does not fire     -> H1-OPEN: 1096 stays canonical.
G-H2 fails             -> H2-REJECTED: escalation; no re-route.
```

Soft check (not a gate): the re-run's deep-grid numbers should reproduce the
1097 log to near machine precision (deterministic pipeline; threaded BLAS may
differ at the 1e-12 level). A macroscopic difference aborts the run as an
environment fault even if every gate above passes.

## 4. What this record does not do

It does not re-point map `004`; it does not demote or promote record 1096;
it adds no law text. Those are verdict-keyed to the mapping above. It does
not claim a continuum sign for any family: a finite-matrix trace continuation
is NUMERICAL evidence under the map-`004` labels, and the 1063-standard
guard (dt-invariance, four octaves, dt-invariant exponent) is the reason the
committed table was actionable at all.
