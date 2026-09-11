# Record 1329 — G8 P1 column-energy premise: antiperiodicity probe (preregistration)

Date: 2026-09-11.
Status: PRE-REGISTRATION, committed BEFORE any numerical run in this
campaign (law 42).  Peter's A+C decision of 2026-09-11 authorizes route A
(continue the conditional mainline chain) and route C (this cheap
plausibility probe of the single named analytic premise).  RH is not
claimed anywhere below; nothing in this record proves or refutes the Lean
premise — all numerics are MODEL-twin statements (law 65).

Subject premise (verbatim, records 1324-1328 lineage):

```text
hcolumn p :  Summable fun i => ‖newFrameAntiresonantColumn λ p S (newSuffixFrame† (u_i))‖²
```

Everything P1 currently delivers (the two-channel transport, the 1328
quantitative ledger, and downstream cutoff identification / endpoint / P2
/ P3) is conditional on this one premise.  Route C asks, on cheap
discretized twins only: *is the premise plausible in any vanishing-
condition model of the frame range, or does the model evidence push the
other way?*

## 1. Stage-0 reduction (paper, before any digit)

From committed definitions:

```text
newFrameAntiresonantColumn λ p S = (primeEulerAmbientLossFactor p)† ∘L newSuffixFrame
primeEulerAmbientLossFactor p    = lossScale p • (I + U_{-log p})      (lossScale p > 0 finite)
newSuffixFrame                   = parameterizedSoninPolarFrame λ 1 S  (isometric)
```

Since an isometry `F` satisfies `F ∘L F† = P_range(F) =: P_S`, the column
operator composing with `F†` is

```text
C_p := lossScale p • (I + U_{±log p}) ∘ P_S          (sign of the shift: see below)
```

and `hcolumn` is `‖C_p‖²_HS < ∞` along any carrier basis.  By the
adjoint/basis invariance just proved in record 1328
(`hsNormSq_adjoint_invariance`), the energy is independent of which
Hilbert basis of `ran P_S` is used, and

```text
E_col(p) = lossScale p² · ∑_j ‖(I + U_t) e_j‖²,   t = ±log p, {e_j} any ONB of ran P_S
         = lossScale p² · ∑_j ( 2 + 2 Re⟨e_j, U_t e_j⟩ ).        (‖e_j‖ = ‖U_t e_j‖ = 1)
```

The sign convention: `1328 §4` records the operator with `U_{-log p}`;
`(lossFactor p)†` carries `U_{+log p}`.  The probe is immune to the
convention: a vector is t-antiperiodic (`U_t v ≈ -v`) iff it is
(-t)-antiperiodic, because the alignment value `-1` is real, and both
signs are measured and compared by gate G5 below.

So the premise says (positively finite scalar `lossScale p²` dropped):

```text
PREMISE(p)  <=>  ∑_j (2 + 2 Re⟨e_j, U_{log p} e_j⟩) < ∞
           <=>  the frame range is ASYMPTOTICALLY p-ANTIPERIODIC with a
                summable defect, along every/any ONB.
```

A single term is small exactly when the vector inverts under shift by
`log p`.  The identity part alone contributes `2·rank(P_S)` and
`rank(P_S) = ∞`, so nothing converges unless the shift part cancels it:
the whole content of the premise is antiperiodicity, nothing else.

Multi-prime compatibility note (paper, registered here, not probed to a
verdict): the same `ran P_S` must serve every visible prime.  If
`U_a e_j → -e_j` and `U_b e_j → -e_j` with `a = log p`, `b = log p'`,
then `U_{a-b} e_j = U_a U_b† e_j → e_j`; differences `log p - log p'`
generate a dense subgroup of `R`, so joint summability over all visible
primes forces the range to become asymptotically translation-INVARIANT
(spectral concentration at frequency 0 in the log coordinate, the
critical-line direction in Mellin language).  The probe's J1 model tests
the two-prime instance numerically.  This note is a structural
observation for the analytic lane; the probe claims no consequence from
it.

## 2. Measured quantity and window model

Discretization: the log coordinate periodicized on a torus of length
`L_p := 2 log p` (per-prime self-contained grid, so `U_{log p}` is an
exact grid roll by `M/2`), `M` points, complex128.  `U_t` = cyclic roll;
`P_S` = orthogonal projection onto the kernel of `K` explicit linear
constraint rows (the Mellin-vanishing twin: rows are Fourier-mode
evaluation vectors `v_n = (1/√M)·(ω^{nk})_k`, exactly the discretized
"vanish at node s = in/L_p" condition used by the 1212/1225 rigs).
`{e_j}` = any ONB of `ker A` (SVD null space).

Primary statistic at resolution `M` and model `X`:

```text
E_M(X, p) := ∑_{j=1}^{M-K} ‖(I + U_{log p}) e_j‖²        (full discrete HS energy)
γ_M(X, p) := d log E / d log M over consecutive dyadic M  (divergence exponent:
              γ = 1 linear divergence, γ = 0 bounded)
Joint:      E_M(J1) := E_M(M1, 2) + E_M(M1, 3)            (two-prime compatibility)
```

Registered models (four; each with its first-principles expectation
fixed NOW, before any digit):

| id | range model `ker A` | expected |
|---|---|---|
| M0 | no constraints (`K=0`), full torus space | `E_M = 2M` exactly, γ ≡ 1 (sanity: identity part contributes 2 per vector, off-diagonal shift has zero trace) |
| M1 | generic triple vanishing, `K=3` off-lattice Fourier rows (the 1212 healthy-triple twin, nodes non-resonant) | `E_M = 2M − O(1)`, γ → 1: a finite-codimensional vanishing range does not antiperiodize |
| M2 | POSITIVE CONTROL: exclusion of ALL even modes (`K = M/2`) | `E_M = 0`, registered γ = 0 (bounded band): the kernel is exactly the antiperiodic half of the Fourier basis, so the statistic CAN report convergence; a rig that never reports it is broken |
| M3 | RESONANT-LATTICE vanishing: `K ∈ {3, 9, 33}` symmetric modes at multiples of the antiperiodic spacing (nodes `n = 1..K/2` in `L_p` units keep the lattice resonant with `log p`), both parities present | γ → 1: half of every resonant band is non-antiperiodic; finite-density lattice vanishing does not save the premise |
| J1 | M1-twin simultaneously at `p = 2` and `p = 3` (`E` summed) | grows linearly at coefficient ≥ that of each part; the dense-invariance note predicts NO summable joint defect at finite K |

Note on what is NOT modeled: `ran P_S` of the true polar frame is not a
finite-codimension Fourier-kernel; the models above are vanishing-
condition TWINS in the 1212 lineage.  If premise-plausible behavior
needs infinite-density, parity-selective vanishing (M2's structure at
K = M/2, or its growing-window analogue), that necessary shape is the
finding this probe is designed to deliver as a CONDITION, not a
disproof of the formal premise.

## 3. Controls and abort gates (all registered before any digit)

```text
G1  unitarity:      max_j |‖U_t e_j‖ − 1| <= 1e-12
G2  two-formula:    E_M == 2·(M−K) + 2·Re tr(P_S U_t)  to 1e-8·max(1,E)
                    (tr P U computed from the SVD null basis; independent path)
G3  basis-invariance (numerical audit of the 1328 invariance):
                    SVD null basis vs QR(null(A) @ random-unitary) give
                    |E1 − E2| <= 1e-8·max(1,E)
G4  control anchors: M0 matches 2M to 1e-8·M; M2 reads E <= 1e-10
G5  sign convention: E_M(X, +t) and E_M(X, −t) agree to 1e-8·max(1,E)
any G-failure on any invocation -> ABORTED-UNINFORMATIVE (rig finding,
zero verdict weight; 1097 protocol; remedy needs a fresh amendment
committed before any re-run)
```

## 4. Registered branch semantics (law 42; exhaustive, no post-hoc branch)

Adjudicated on the fitted γ over the dyadic ladder `M ∈ {512, 1024, 2048, 4096}`,
per model, at primes `p ∈ {2, 3, 5, 7, 11}` (J1 at `p ∈ {2, 3}`):

```text
SOME-MODEL-CONVERGENT   γ <= 0.15 for a repo-lineage model M1 or M3 at any p
  -> the premise is plausible in a finite-density vanishing twin;
     route A (cutoff identification, endpoint, P2, P3) continues as the
     mainline conditional chain with plausibility support on record.

LINEAR-DIVERGENT         γ >= 0.85 for every M1/M3 run
  -> premise NOT plausible in any finite-density vanishing twin; the
     registered necessary condition is infinite-density parity-selective
     vanishing (M2-shape); the freeze card marks the column-energy premise
     "probe-negative at finite density" and the analytic lane decides
     whether the true ran P_S carries that structure (fresh prereg for
     any formal falsification attempt; this record authorizes none).

SUBLINEAR-UNRESOLVED     otherwise
  -> one registered extension step only: repeat at M = 8192 once and
     refit γ at the top dyadic pair; γ then adjudicates by the two bands
     above; if still in (0.15, 0.85), record conservatively as
     LINEAR-DIVERGENT with the unresolved values printed verbatim.
```

The probe NEVER claims: the premise true/false, RH-facing content, or
any statement about the formal `ran P_S` — only about its vanishing-
condition twins.

## 5. Implementation and budget

```text
script   docs/proofs/1329_column_energy_antiperiodicity_probe.py   (new file;
         committed 1212/1225 style; no edit of any committed script or JSON)
env      .venv-probe (numpy only; no scipy needed — dense roll + SVD)
outputs  docs/proofs/1329_probe_results.json + run log
         1329_probe_results.log (repo-side copy of the verdict table only)
scale    M <= 8192 (only via the registered SUBLINEAR extension),
         K <= M/2, five primes; runtime cap 10 min; single invocation,
         resource-lock wrapper class heavy per the 1225 A9 protocol
verdict  post-run addendum in THIS record after the commit of the run's
         script + JSON (house pattern of 1225 sections 7-8); no verdict
         is valid before its gates appear in the log
budget   one implementation pass + one official invocation + one
         registered-extension pass (SUBLINEAR branch only)
```

Lane note (A9): this record is the mainline (this session) lane; the NM
lane with the companion session is untouched.  Route A continuation
(next conditional brick: cutoff identification) proceeds in parallel and
does not wait on this probe.

RH is not claimed.

## 6. Amendment A1 - invocation-1 ledger and registered code fix (2026-09-11, BEFORE invocation 2)

Invocation 1 ran committed code `c50bb5b` (log
`1329_probe_results.log`, mirror side) and DIED SILENTLY mid-run: the log
stops after 20 lines (inside M3-9 at p=2, M=2048), no verdict line, no
results JSON, while the wrapping shell reported exit 0.  This matches the
documented WSL-instance first-run death class (1225 A7c).  Score:
ABORTED-UNINFORMATIVE, zero verdict weight.  Post-run audit of the
invocation-1 log found a second, independent DEFECT (caught before any
number was adjudicated): the M3 cell names were parsed with
`model[2:]`, which keeps the dash — `int("-3") = -3` yields an empty
symmetric-mode list, so every M3 run silently executed K=1 (mode-0
exclusion only) instead of the registered K in {3, 9, 33}.  M0/M1/M2
cells were correctly shaped in the captured lines (M1 K=3, M2 K=M/2,
E values matching the closed forms 2M-6+tiny, 0, 2M-4).

Registered fixes before invocation 2 (law-42 compliant: fixes make the
code implement the ALREADY-committed prereg section 2; no registered
quantity, band, gate, or branch is changed):

```text
F1  M3 parsing: model.split("-")[1]; the K in {3,9,33} cells now run the
    registered symmetric resonant-lattice mode sets {0,+-1}, {0,..,+-4},
    {0,..,+-16}.
F2  new KSHAPE guard (the invocation-1 defect class is promoted to a
    gate): every cell asserts the realized K equals the registered K
    (M0:0, M1:3, M2:M/2, M3-K:K) before energies are used; a breach is
    an ABORTED-UNINFORMATIVE gate failure.
F3  A9 rule-2 hygiene: invocation 2 writes to a NEW log path
    1329_probe_results_inv2.log; the invocation-1 log is preserved
    untruncated as the defect evidence; launch is detached and polled
    rather than foreground-coupled.
```

Invocation-1 numbers carry no weight, but their captured cells
independently confirm the rig's closed-form behavior (M0 anchor exact at
2M, M1 2M-6+O(1) at p=2, M2 positive control exact 0 through K=2048, G3
basis-invariance deltas <= 1.6e-10 on every captured cell).  RH is not
claimed.
