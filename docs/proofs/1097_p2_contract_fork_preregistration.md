# 1097 - The S2 primitive fork: is A-in-HS schedulable, and what replaces it?

Date: 2026-09-02.

Status: PRE-REGISTRATION. This document is committed BEFORE the probe run.
The probe script `1097_p2_contract_fork_probe.py` is committed in the same
batch; the verdict section (section 6) is appended after the run, unedited
elsewhere. RH is not claimed. Evidence labels follow map `004` section 1.

## 1. The conflict this record resolves

Record 1096 discharged the record-1095 sandwiched nuclearity to a single
primitive

```lean
targetProlateRemainderFactorHS : Summable fun i => norm (A e_i)^2   (A in HS)
```

with A the target prolate remainder factor and `K_S = A^dagger . A`. Since
`Summable (norm (A e_i)^2)` along an orthonormal basis is exactly
`Tr K_S < inf`, this primitive is the RAW-F1 quantity class:

- the consuming leaf's own header
  (`C1ProlateResponseTraceLegalityUnitScale.lean:78-80`) says the leaf "makes
  no raw Hilbert-Schmidt assertion about it: record 1063 guards against
  scheduling the corresponding raw target";
- record 1063 falsified the raw class in the model: the nonmeet angle mass
  grows like `xi^0.4` over four octaves, dt-invariant, top angles never
  decay - K_S is not even compact there;
- record 1067 measured the same quantity directly and pre-registered the fork
  GROWTH vs SATURATION; GROWTH fired: `Tr(K_S)_model` runs
  16.1996 -> 20.1700 -> 26.8715 -> 34.2696 over `xi_max` 12.8 -> 102.4 with
  INCREASING increments and no bend;
- record 1096's docstring describes this same table as "growing but finite,
  16 -> 34" and calls the primitive "strictly narrower". The narrowing is
  valid as an implication, but the surviving primitive is the falsified
  class, not a weaker one. No-bend growth over four octaves is divergence
  evidence under the 1063/1067 standard, not finiteness evidence.

On the finite carrier `finiteSCarrier` every operator is HS, so the 1096 Lean
implication is correct as stated; the conflict is about which primitive the
CONTINUUM owner transfer may schedule.

## 2. What record 1068/1090 already measured (committed evidence)

The law-16 obligation set (leaf lines 125-138, AGENTS 7c law (16)):

```text
D K_S = C^dagger K_S C  +  C^dagger [C, K_S],
D = C^dagger C,  C = selected convolution root.
```

- (a) `Tr(C^dagger K_S C) = norm(A C)^2_HS` (the positive sandwich): measured
  `p_hs_sq` 3.5661 -> 3.5356 over four octaves, DECREASING (record 1068
  s5.1, k = 1);
- (b) `norm([C, K_S])_nuclear`: measured `l_tr1` 1.3462 -> 1.2850,
  DECREASING (record 1068 s5.1); the PROBE-P2 per-term nuclear norms
  (`ck_tr1`/`kc_tr1` ~ 4.63, flat) are the record-1090 witnesses;
- control: `norm(K_S)_F^2 = Tr(K_S^2)` grows mildly 8.35 -> 11.42 (record
  1090 control row) - the square-summable class is NOT yet adjudicated.

So the D-weighted quantities are O(1) while the raw trace is not - exactly
the 1063 F1' verdict. The question this probe settles is only whether the
four committed octaves under-detect a bend.

## 3. Pre-registered fork

H1 (the 1096 primitive is schedulable on the continuum):
`Tr K_S` converges; the window sweep must BEND beyond the committed window.

H2 (the law-16 set is the right primitive): obligations (a) and (b) stay
O(1) flat at deeper windows; the S2 analytic core routes through them, NOT
through A-in-HS.

Decision criteria (fixed now, before the run):

```text
+--------+------------------------------------------------+------------------+
| Gate   | Criterion                                      | Source           |
+--------+------------------------------------------------+------------------+
| G-anc  | At N <= 8193 the committed 1067 table          | COMMITTED_1067   |
|        | (Tr path) and 1068 table (l_hs_sq/l_tr1, and   | COMMITTED_1068   |
|        | the p_hs endpoints 3.5661/3.5356) reproduce    | (byte-identical  |
|        | within 5e-3 / 2e-3; m-symmetry and Q_S gates   | 1068 module);    |
|        | hold on the same code path; the lean deep-     | lean cross-rig   |
|        | window builder reproduces COMMITTED_1067 at    | anchor           |
|        | (8193, T=20) within 5e-3 for both families.    |                  |
+--------+------------------------------------------------+------------------+
| G-dt   | New-window dt-invariance pair (8193/T10 vs     | law (15)         |
|        | 16385/T20: same dt, same xi_max 204.8) agrees  |                  |
|        | to rel <= 2e-3 on every H1/H2 observable.      |                  |
+--------+------------------------------------------------+------------------+
| G-src  | Source family (S = []) trace stays flat at the | 1067 anchor      |
|        | new octave (rel change <= 5e-2 vs N=8193).     |                  |
+--------+------------------------------------------------+------------------+
| G-H1   | Tr(K_S) at 16385 continues the committed       | 1063/1067        |
|        | power law: log-log slope >= +0.15 over the     | standard         |
|        | 16x span 12.8 -> 204.8, OR the 16385 increment |                  |
|        | is >= 0.5x the previous increment (no bend).   |                  |
+--------+------------------------------------------------+------------------+
| G-H2   | p_hs (obligation a) and l_tr1 (obligation b    | 1068/1090        |
|        | witness, SVD rows at N <= 8193) have           |                  |
|        | |log-log slope| < 0.15 over the full sweep.    |                  |
+--------+------------------------------------------------+------------------+
```

Verdict mapping:

```text
G-anc fails                     -> ABORT: model misread; re-audit, no verdict.
G-dt fails                      -> ABORT: grid artifact; no verdict (law 15).
G-src fails                     -> ABORT: rig anchor broken; no verdict.
G-H1 fires AND G-H2 passes      -> H1-REJECTED / H2-CONFIRMED:
        the 1096 A-in-HS discharge route is CLOSED for continuum scheduling
        (numerical guard, 1063-standard; it does not prove a continuum
        negation - NUMERICAL label).  The canonical S2 primitive set becomes
        (a) AC in HS + (b) commutator-remainder trace legality; record 1095's
        sandwiched nuclearity stays the canonical consumer contract; record
        1096's discharge is demoted to a valid-but-unschedulable implication.
        A follow-up Lean brick (1098) wires 1095 from (a)+(b) via the leaf's
        own decomposition, and law text is added to AGENTS 7c.
G-H1 does not fire (bend)       -> H1-OPEN: 1096 stays canonical; schedule
        its discharge as the next producer brick.
G-H2 fails                      -> H2-REJECTED: escalation with numbers; no
        re-route without a new pre-registration.
```

## 4. Probe design

- Rig: import the committed `1068_root_commutator_ledger_probe.py` module
  (which reuses the 1067 rig byte-identically); family `{2,3,5}` (deciding)
  and source family `[]` (anchor); k = 1 Gaussian symbol, as committed.
- Grids: committed anchors (1025/2049/4097/8193 at T = 20) plus the NEW deep
  octave (16385 at T = 20, `xi_max = 204.8`, same dxi-family discipline) and
  the dt-invariance pair (8193 at T = 10 and 16385 at T = 20 share dt and
  xi_max).
- H1 observable: `trace(K_S).real` (equals the 1067 `Tr M - d` path up to the
  committed 2.6e-11 three-path agreement; the anchor gate pins it).
- H2 observables: `p_hs = trace(C^dagger K_S C)` (= `norm(A C)_HS^2`),
  `l_tr1 = norm([C, K_S])_nuclear` (SVD), and the signed-term witnesses
  `ck_tr1`/`kc_tr1` (record-1090 comparability).
- Pre-registered deviations at N = 16385 only (memory/runtime):
  1. `E` is applied by column broadcasting the 0/1 vector instead of
     building a dense diagonal matrix (identical values, exact);
  2. the Q_S idempotence/self-adjoint gates run in FROBENIUS norm with the
     printed residual (the spectral-norm SVD of a 16k matrix is out of
     budget); the positivity gate and the meet projection stay eigh-based;
  3. no SVD rows at 16385 (`l_tr1`/`ck_tr1`/`kc_tr1` absent there; their
     verdicts ride on N <= 8193);
  4. one internal identity gate replaces 1067's three-path rig at 16385:
     `K_S` Hermitian (Frobenius residual printed), `R_S` idempotent, and
     `trace(K_S) = trace(M) - d` verified directly.
- Runtime/memory budget: N = 16385 complex matrices are 4.3 GiB; the lean
  path with aggressive frees stays under ~24 GiB peak on the 35 GiB mirror.
  Runtime estimate ~1-2 h total on 16 threads, run as a heavy background
  task through the resource runner.

## 5. What each branch changes in the repo

- H1-REJECTED: map `004` section 4 note (P2/S2 producer primitive re-pointed
  to (a)+(b)); record 1096 doc gains an erratum block (its own numbering);
  AGENTS 7c gains the law "a discharge chain that lands on a previously
  falsified quantity class must re-run that quantity's guard before the
  primitive is called narrower" (the 1096 lesson);
- H1-OPEN: record 1096 stays canonical; the discharge probe/proof is
  scheduled as the next P2 brick;
- either way, records 1089/1095 shapes are untouched (the gate object and
  the consumer contract are primitive-agnostic).

## 6. Verdict (appended after the run)

**ABORT — G-dt failed; no fork verdict; no section-5 repo changes fire.**

The run is log `build-logs/1097_fork_probe3.log` (acceptance by flushed log,
not exit code). All stage-1/2 gates were green: the four committed anchors
reproduced `COMMITTED_1067`/`COMMITTED_1068`/the `p_hs` endpoints, and the
lean deep-window builder reproduced the committed cross-rig points for both
families — `{2,3,5}` trace 34.2696 (rel 1.08e-06), `p_hs` 3.5356,
`ks_frob2` 11.4231; source trace 6.4740 (rel 6.88e-06).

Decision table (log lines 84-93):

```text
+-----------+--------------------------------------------------+--------+
| item      | Measurement                                      | Result |
+-----------+--------------------------------------------------+--------+
| G-anc     | anchors + lean cross-anchor (both families)      | PASS   |
| G-src     | src trace 6.5620 at (16385,20) vs 6.4740         | PASS   |
|           | committed (8193,20), rel 1.36e-02 <= 5e-2        |        |
| G-dt      | {2,3,5} max rel 1.33e-01; src max rel 1.43e-01   | FAIL   |
|           | (tr_ks, ks_frob2, p_hs, gate 2e-3)               |        |
+-----------+--------------------------------------------------+--------+
| H1        | tr_ks 16.1996 -> 20.1700 -> 26.8715 -> 34.2696   | fires  |
|           | -> 41.0499; slope16x +0.335; inc ratio 0.917     | (unc.) |
| H2        | p_hs slope8x -0.004; l_tr1 slope8x -0.022        | passes |
|           | (both |slope| < 0.15)                            | (unc.) |
+-----------+--------------------------------------------------+--------+
```

Per the pre-registered mapping, G-dt failure fires

```text
ABORT: G-dt/G-src failed (dt max rel {2,3,5: 1.33e-01, src: 1.43e-01},
src rel 1.36e-02) - grid artifact; no verdict (law 15).
```

so the H1/H2 pattern above is RECORDED but NOT CERTIFIED, and the fork is
UNRESOLVED. Records 1095/1096 stay canonical; map `004` section 4 is not
re-pointed; no AGENTS law fires from section 5.

Anatomy of the failure (for the follow-up record): the pre-registered
dt-pair (8193, T=10) + (16385, T=20) holds dt = 0.00244 and xi_max = 204.8
fixed, but since `N = 1/(dt*dxi)` it necessarily varies dxi from 0.05 to
0.0125 (a factor of 4). The measured pair disagreement is therefore the
dxi-axis sensitivity at the deep octave, not a rig fault:

```text
+-----------+-------+----------+-----------+---------+----------+
| grid      | dt    | dxi      | xi_max    | tr_ks   | src tr_ks|
+-----------+-------+----------+-----------+---------+----------+
| (8193,10) | 0.0024| 0.05     | 204.8     | 42.5025 | 7.6327   |
| (16385,20)| 0.0024| 0.0125   | 204.8     | 41.0499 | 6.5620   |
+-----------+-------+----------+-----------+---------+----------+
```

The coarse-dxi member overestimates every trace-class observable in BOTH
families, and at fine resolution the source trace returns to the committed
band (6.5620, within 1.4e-02 of the committed 6.4740) — the +18 percent
coarse-grid excursion was the artifact, and the fine (16385,20) grid is the
best-resolved point of the campaign. The next dxi refinement at this window
(32769, T=40) needs 17.2 GiB per complex matrix and is out of memory budget,
so deep-octave certification cannot ride on value-invariance; it must ride on
a pre-registered bracket-direction design. That re-registration is a separate
record; the H1/H2 criteria there are unchanged from section 3.

Provenance: the run copy of `1097_p2_contract_fork_probe.py` had md5
`d5516f8ff0a055289cba8e3f304424cc`; the committed copy differs from it ONLY
in the run-block comment lines (a local absolute path dropped for public-repo
hygiene). No executable line differs.
