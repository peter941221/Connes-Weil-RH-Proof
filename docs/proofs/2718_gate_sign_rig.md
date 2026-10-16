# Record 2718: model-grade P5 gate sign rig at n = 3 (G1 swing 2b)

**Verdict: RIG GREEN — THE FIRST MODEL-GRADE P5 GATE SIGN CERTIFICATE.**
All four sign claims at the two n = 3 candidate rows are certified:

```text
+----------------+--------------+-------------+---------------+----------+-----------+
| row            | claim        | margin      | allowance at  | slack    | E_crit /  |
|                |              |             | premises      |          | E_obs     |
+----------------+--------------+-------------+---------------+----------+-----------+
| (14.1347,4,3)  | C < 0        | 1.452195e+5 | 3.62e-2       | full     | 4.02e+07  |
| (14.1347,4,3)  | det < 0      | 1.219067e16 | 7.163e+10     | 1.219e16 | 1.73e+06  |
| (21.0220,5,3)  | C < 0        | 8.491123e+3 | 1.38e-2       | full     | 6.16e+06  |
| (21.0220,5,3)  | det > 0      | 6.084493e14 | 4.341e+09     | 6.084e14 | 1.41e+06  |
+----------------+--------------+-------------+---------------+----------+-----------+
```

The gate BRANCH is robust at every premise corner: (gamma_1,4,3) stays
`rays` at all 8 corners (L+ moves < 6e-3: [1381.5309, 1381.5367], joint
lambda >= 1381.53 vs Ltail = 0.683); (gamma_2,5,3) stays `all` at all 8
corners (gate side vacuous, joint lambda > 15.86).  The sign structure
that the record-2716/2717 paper pricing identified is now certified at
model grade, and the certificate is NOT leaning on its observational
premises: with both premises set to ZERO, the certified roundoff classes
alone leave margins of 1.7e8 (row A det) and 8.9e7 (row B det).

## Task card (bounded-progress gate)

```text
consumer    riemannHypothesis_of_four_point_span_contradiction_producer,
            via the record-2708 contract P5 duty at n = 3 -- the named
            map-103 reopen probe (sharpened by records 2716/2717)
owner       the STORED record-1980 trial-owner models at (gamma_1,N=4,3)
            and (gamma_2,N=5,3); node constants are the stored floats,
            taken as the owner definition (model grade, G2 pending)
premise     the gate-branch signs at the candidate rows were supported
            only by sampled floats + two-grid agreement
criterion   per sign claim: margin |C| (resp. |det|) against allowance =
            certified non-seed classes + A*E_seed + M*grid, with E_seed
            and grid as NAMED premises (10x observed spreads); report
            critical E_L per claim
budget      one shadow-rig run in WSL, both candidates, primary grid;
            seed three-order study (300/600/1200) at the rig's own
            evaluation points; ran 6.3 s
stop        verdict recorded (this record); bitwise anchor failure would
            trigger environment diagnosis, never producer patching
```

## Method (forward-error shadow, record-2249 law)

The exact record-2032 pipeline is rebuilt from the committed modules
(verbatim call order) and BITWISE-anchored against the stored rows;
every error class is then certified separately and propagated linearly
to the claims:

```text
R_sigma  float sigma_vec vs mpmath dps-35 digamma: EXACT per-node deltas
         (max 1.332e-14); kills the series-truncation question by
         measurement, no analytic bound needed
R_cos    prime-kernel cos/argument rounding: per-term |da| <= 4U|a| + 1 ulp
         with |a| <= 2*pi*25*10, charged as 1e-12 * wsum * trapz|f|
         (wsum = 588.0, the exact sieve weight sum)
R_trap   trapezoid accumulation: 16U * trapz(|integrand|)
R_float  cardinal/power roundoff: generous 1e-11 * trapz scale
E_seed   NAMED premise: |dL| <= E_seed uniform at every evaluation point.
         Propagation through the cardinal terms (both entry points of the
         seed: each L(s - z_j) AND the constant L(0) in the denominators):
         |dterm_j| <= |c_j||Q_j| E (1 + |L(u_j)|/|L(0)|), so
         |dlb| <= E*S_b, |dlc| <= E*S_c,
         |dW| <= E*G,  G = 8|lb|^7|lc|^2 S_b + 2|lb|^8|lc| S_c,
         A_i = trapz((|sig|+|kp|) |P|^i G) per channel, and
         A_det = |D|A_0 + |C|A_2 + 2|b|A_1  (worst-case correlation)
M_grid   NAMED premise: the trapezoid functionals T_0.02 approximate the
         continuum integrals; charged as 10x the observed 0.02-vs-0.01
         per-channel movement (row A: M_det = 9.74e8; row B: 1.65e+07),
         propagated with the same |D|/|C|/2|b| weights.  The analytic
         Euler-Maclaurin remainder (record-2270 form) is deferred.
```

E_seed = 10 x 4.797e-7 = 4.80e-6, where 4.797e-7 is the max |L_1200 -
L_300| over the rig's evaluation points (s - z_j for both cardinals).
The 600-vs-300 spread (3.506e-7) sits just under it: the observed
differences are dominated by the order-300 residue, consistent with
geometric GL convergence.

## Anchors (in-run, all green)

```text
a1  both candidate rows rebuilt BITWISE vs the stored 2032 artifact at
    BOTH grids (C, b, D, det, lambda, arch[0..2]: 0 mismatches); the W
    identity (build_density vs direct cardinal recombination) is bitwise
a3  seed0 bitwise == the committed 1981 laplace_at_zero
a4  |L300(0) - 3^10| = 1.4125e-07 <= E_obs: at the ONE point where the
    true seed transform is known exactly (laplaceAt smoothSeed 0 = 3,
    hence seed0 = 59049; the committed float 59048.99999985875 is pure
    GL quadrature error), the observed spread covers the true error
```

Anchor a4 is the independent corroboration of the seed-premise scale: it
is not circular (59049 is exact arithmetic, the 1.41e-7 gap is the
order-300 quadrature error measured against closed-form truth).

## Certificate statement

Certified object: the record-2032 pipeline AS CODE on the stored float
node constants at dxi = 0.02 -- i.e. the trapezoid functionals T_0.02 of
the stored-model B5 gate coefficients C, b, D, det.  Claims:

```text
(gamma_1, N=4, n=3):  sign(C) = -1 and sign(det) = -1 certified
                      => branch rays, L+ in [1381.5309, 1381.5367]
                      => gate lambda in [1381.53, inf); with Ltail = 0.683
                         (2716 constants) the joint lambda interval is
                         [1381.53, inf)
(gamma_2, N=5, n=3):  sign(C) = -1 and sign(det) = +1 certified
                      => branch all (gate holds for every lambda > 0)
                      => joint lambda in (15.86, inf), gate side vacuous
```

Binding structure: the det allowance at the premises is dominated by the
seed class (A_det * E_seed = 7.06e10 at row A), with the grid premise
adding ~1e9 and the certified non-seed classes contributing 7.2e7.  The
critical seed error is E_L = 0.83 (row A) / 0.68 (row B): the seed
transform could be off by an ABSOLUTE 0.7-0.8 (relative ~1.2e-5 of the
59049 scale) before any det sign flips -- the observed scale is 4.8e-7.

## Reading

1. **The P5 gate duty at n = 3 has its model-grade rung.**  The
   record-2717 flip budgets (3.36% / 2.92%) assumed a %-grade enclosure
   was buildable; this rig builds it -- and the realized margins are not
   percent-grade but 5.5-to-8-order grade, because the sampled signs sit
   on reinforcing channels (row A) or on cancellations the certified
   classes barely move (row B).

2. **The certificate survives total mispricing of its premises.**  Both
   named premises are observational (three-order seed study; two-grid
   movement) with 10x inflation, and both would have to be wrong by
   5-7 ORDERS for any claim to flip.  The analytic versions (a
   stadium/ellipse GL remainder for the smooth seed, an Euler-Maclaurin
   |f''| bound for the trapezoid) remain open and are now BOUNDED work
   with known targets, not feasibility questions.

3. **Supersession note on record 2030.**  Its "the sign half is the
   obstruction" verdict answered the map-106 PATTERN certificate
   (C > 0, b > 0, det < 0); under the record-2708 section-5 branch-exact
   reading the C < 0 rows are admissible and 2030's obstacle dissolves.
   Its vertex-centered determinant budget (0.4142) does NOT transfer to
   a channel-box rig: the centering constant a = lambda(vertex) ~ 2141
   amplifies |dU0| >= |a| dC, making the centered frame WEAKER than the
   direct 3.36% channel box.  The 2717 budgets were the correct targets.

4. **What remains for the named map-103 reopen probe.**  The probe has
   two rungs: (i) a gate certificate, (ii) the COMPLETE owner.  This
   record closes rung (i) at model grade.  Still open: G2 (the full
   closed-ball zero-set identification, so the owner stops being an
   under-approximation) and re-measurement on the complete owner (the
   flip budgets protect against ENCLOSURE error of a FIXED owner only --
   adding zeros changes the channels at O(1)); plus the tail-side P3
   (certified C4/C2; the stored decay constants are sampled) and the P4
   shell identification.  The freeze stands until the complete-owner
   rung fires.

## Nonclaims

- Model grade ONLY: the certified owner is the stored record-1980
  under-approximation (known zeros in the ball + orbit + healthy
  targets).  No complete-owner claim; no G2 progress.
- E_seed and M_grid are NAMED OBSERVATIONAL premises, not theorems; the
  certificate is conditional on them (with 5-7 orders of headroom).
- The certified object is the dxi = 0.02 trapezoid functional; the
  grid-to-continuum lift is the M_grid premise.
- The tail side keeps its own premises: C4/C2 remain sampled (P3/G4),
  m = 1 floor, no multiplicity input; P4 remains a necessary-condition
  screen.
- No map-103 reopening, no producer GO, no SourceRH, no RH claim.
- The joint lambda intervals consume the record-2716 honest constants
  (Cspec = 128.65, d = 169/16) exactly as committed there.

## Evidence

- `scripts/g1_gate_sign_rig_2718.py` (shadow rig; imports the committed
  1980/1981/1918/1959/2028 producers and the 2716 module verbatim)
- `results/2718_gate_sign_rig.json` (full ledger: per-channel error
  classes, seed term details, G profiles, masses, corner branches,
  claims with critical values; source sha256)
- `results/2718_rig_run.log` (the run log)
- Inputs: `results/2032_gate_row_search.json` (bitwise-anchored rows),
  `results/1981_powered_seed_underapprox.json` (seed0 anchor),
  `docs/proofs/2716_g1_joint_acceptance_repricing.md` (branch/joint
  semantics + honest constants),
  `docs/proofs/2717_p5_n3_probe.md` (flip budgets being discharged),
  `docs/proofs/2030_determinant_certification_margin.md` (superseded
  pattern-frame reading, Reading 3).
