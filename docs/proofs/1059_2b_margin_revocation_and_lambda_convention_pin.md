# 1059 - 2b pre-flight fires: the perturbation scheme for F1 is REVOKED; the paper's lambda(n) convention is PINNED

Date: 2026-08-30.  Follows 1056 (GO with pre-flight), 1057 (verbatim delta
chain), 1058 (alpha reconnaissance probe).  No Lean change; the Dev leaf keeps
its single sorry at `C1ProlateResponseTraceLegalityUnitScale.lean:121`.

Results up front, one good one bad:

```text
(1) BAD for the cheap route: the 1056 brick-2b plan (target angle bound as a
    PERTURBATION of the source angle bound through the Euler transport) is
    REFUTED by the pre-flight margin check, already at S = {2}:
    closing it would need the source leakage constant delta >= 0.98517,
    while the source file proves only 0 < delta <= 1 qualitatively, and the
    prime pool {p : 1 < p} is unbounded so no family-uniform repair exists.
    F1's angle strictness is therefore its OWN transversality statement on
    the transported pair, not a table lookup.  This is the one revocation
    condition 1056 s4 explicitly reserved; it fired on day one.

(2) GOOD for alpha: the open convention item 1058 s3.4 is CLOSED from the
    raw tex (lines 967-983): the paper's lambda(n) IS Wang's lambda_{2n}^c
    at c = 2 pi - the EVEN-parity branch of the (window [-1,1], kernel
    e^{2 pi i x omega}) concentration spectrum.  Probe block B2 measures
    that branch and verifies the paper's own decay bound (983) on it.
    It also corrects 1058 s2: the row labelled "c = 2 pi" there was
    computed at collocation bandwidth omega = pi, not 2 pi; the corrected
    even-branch values and the MP/ARB onset (n >= 6) are below.
```

## 1. What 1056 asked, and the evidence gathered

The 1056 pre-flight: "Pin the numerical margin of
`norm_unitProlateFactor_lt_one` against the worst S the visible-prime setup
allows. If margin < transport bound at some allowed S, the scheme needs a
sharper angle argument and F1 is NOT free."  Three ingredients:

```text
(a) the source margin - CCM24UnitScaleStrictAngle.lean:1403-1413:

      noncomputable def unitLeakageLowerBound : ℝ :=
        unitLeakageReconstructionBound⁻¹

      theorem unitLeakageLowerBound_pos : 0 < unitLeakageLowerBound
      theorem unitLeakageLowerBound_le_one : unitLeakageLowerBound ≤ 1

      noncomputable def unitProlateAngleBound : ℝ :=
        Real.sqrt (1 - unitLeakageLowerBound ^ 2)

    The only facts about delta := unitLeakageLowerBound are 0 < delta <= 1.
    No numeric floor exists anywhere in the file; the source strictness is
    qualitative (a reconstruction bound being finite), not a constant.

(b) the transport size - CCM24EulerTransport.lean:

      abbrev CCM24VisiblePrime := {p : ℕ // 1 < p}
      ccm24PrimeEulerCoefficient p = 1 / Real.sqrt p
      ccm24PrimeEulerContraction p = c_p • cc20GlobalLogTranslation (- log p)
      theorem norm_ccm24PrimeEulerContraction_lt_one : ‖...‖ < 1

    ‖c_p • Shift‖ = c_p exactly (translation is an isometry); the pool is
    ALL primes > 1 with no family bound: FinitePrimePowerFamily.terms is an
    arbitrary Finset (ℕ × ℕ), and c_2 = 2^{-1/2} = 0.70711 is already large.

(c) the factor being bounded - ProlateTraceReduction.lean:38-40:

      prolateFactor U = cc20TransportedHalfLineProjection U
                          ∘L supportComplementProjection U

    both factors are orthogonal projections, so ‖prolateFactor U‖ ≤ 1 is
    AUTOMATIC for every U; the entire content of `hangle` is STRICTNESS,
    i.e. angle < pi/2 between the two ranges.  A norm-continuity argument
    through T_S cannot deliver strictness uniformly because kappa(T_S) is
    unbounded across families and the source margin is not a number.
```

## 2. The revocation arithmetic

The 2b scheme would conclude ‖F_S‖ < 1 from ‖F_src‖ = sqrt(1 - delta^2) < 1
via conjugation by the Euler transport T_S.  Conjugation costs the condition
number; even for the smallest allowed nonempty S = {2}, using
‖T_2‖ ≤ 1 + c_2 and ‖T_2⁻¹‖ ≤ 1/(1 - c_2) (Neumann, since c_2 < 1):

```text
+-------------------------------------------------------------------+
| quantity                                | value                   |
+-----------------------------------------+-------------------------+
| c_2 = 2^{-1/2}                          | 0.707107                |
| kappa(T_{2}) = (1+c_2)/(1-c_2)          | 5.828427                |
| closure needs kappa * sqrt(1-delta^2)<1 |                         |
|   => required delta                     | > 0.985166              |
| proven about delta                      | 0 < delta <= 1 only     |
| uniform repair across S                 | impossible: pool is     |
|                                         | {p : 1 < p}, no bound   |
+-----------------------------------------+-------------------------+
```

There is no theorem giving delta > 0.985, and the source leakage constant is
the ASYMPTOTIC-quality quantity of that file - staking F1 on a numeric floor
for it is exactly the move the source proof never makes.  Verdict:

```text
REVOKED: 1056 brick-2b "target angle bound by perturbation of the source
angle bound" does not exist as a uniform argument.  The GO of 1056 s3
stands only for the parts that never used 2b: the freeze rulings and the
reclassification of F1 as estimate certificates rather than plumbing.
```

## 3. Re-scoped F1 (decision recorded, not silently taken)

What survives and what the replacement options are:

```text
STILL VALID groundwork:
  2a  generic Gram-corrected reduction (targetProlateRemainder_eq_factor /
      targetSoninProjection_eq_gramCorrected generalized along T_S):
      independent of any angle estimate; it is algebra.  Build it.

REPLACEMENT for 2b (pick one; both stay outside the 1055 freeze -
fixed-scale model objects, no W_(lambda,S), no asymptotics):
  R1  target-side uniform angle/leakage lemma (RECOMMENDED as the real
      target): prove ‖prolateFactor (T-conjugated configuration)‖ < 1 by
      the SAME mechanism the source file uses - additive-kernel
      identification + support geometry - not by norm continuity.  The
      geometric fact that makes this plausible and cheap at the level of
      structure: in log coordinates the window has length log 2 and every
      shift log p >= log 2, so T_S - I moves the window off itself; the
      strictness should come from kernel decay across that gap, uniformly
      in S.  This is genuine analysis (weeks), not a table.
  R2  honest fallback (zero cost, ship-able today): keep F1 as the named
      conditional premise it already is - the Dev leaf capstone is proven
      modulo F1 + the two compression-HS premises, and the Gate-2 readback
      already carries `hresponse`-style premises.  Nothing regresses; the
      sorry just stays documented instead of becoming a theorem.

ORDERING DECISION: R2 by default (F1 stays the thread's single open premise),
2a proceeds as unconditional algebra, and R1 is opened only as its own design
record when alpha/beta/gamma/delta (the GATE 1 mainline) hand off.  F1 is NOT
the shortest path right now - the pre-flight was precisely to learn that, and
it learned it.
```

Anti-conflation reminder (1056 Ruling 2, AGENTS §7d) still holds: none of
R1/R2 pays any 1055 revival debt.

## 4. The lambda(n) convention, pinned from raw tex

`weil-compo.tex` (arXiv:2006.13771, sha256 `b01d353b...20f3fc` per 1057 s0),
lines 967-969 and 983:

```text
  \int_{-1}^{1} PS_{2n,0}(2\pi,x) e^{i 2\pi x\omega} dx
      = \lambda(n)\, PS_{2n,0}(2\pi,\omega)
  "The eigenvalue \lambda(n) is \lambda_{2n}^{c} (c=2\pi) in the
   notation of Wang"   [Rokhlin reference]

  (983)   |\lambda(n)| <= 2^{2n} pi^{2n+1/2} ((2n)!)^2
                        / ((4n)! Gamma(2n+3/2))
```

So the operator is P_[-1,1] F P_[-1,1} with the e^{2 pi i x omega} Fourier
kernel and band |omega| <= 1: in the probe's parameterization the collocation
kernel is sin(Omega (x-y)) / (pi (x-y)) at **Omega = 2 pi**, and because
PS_{2n,0} has even parity, the paper's lambda(n) is every OTHER eigenvalue of
the full (even+odd alternating) descending spectrum - the even-branch subset
lambda_full(0), lambda_full(2), lambda_full(4), ...

Probe 1058 block B2 (`docs/proofs/1058_alpha_chi_reconnaissance_probe.py`,
re-run 2026-08-30, log `/home/peter/cc20/probe1058.log`) measures exactly
this, with parity detected from the eigenvectors rather than assumed:

```text
parity-even full-spectrum positions: [0, 2, 4, 6, 8, 10, 12, ...]
(the alternation degrades past position ~12 where float64 noise takes over)

lambda(n) = even branch, n = 0..5:
  [0.9999428, 0.9593903, 0.2746660, 3.478238e-3, 7.465620e-6, 5.820371e-9]

tex-(983) bound check (all within, and tracking the measured values):
  n=0  9.999428e-01 <= 2.000000e+00   True
  n=1  9.593903e-01 <= 3.509193e+00   True
  n=2  2.746660e-01 <= 7.539449e-01   True
  n=3  3.478238e-03 <= 6.307385e-02   True
  n=4  7.465620e-06 <= 2.804286e-03   True
  n=5  5.820371e-09 <= 7.731240e-05   True

pairing coefficients p(n) = lambda(n)/sqrt(1 - lambda(n)^2) of tex:214:
  p(0) ~ 93.5, p(1) ~ 3.401, p(2) ~ 0.2857, p(3) ~ 3.4782e-3,
  p(4) ~ 7.4656e-6, p(5) ~ 5.8204e-9
```

Consequences, written down where alpha work will read them:

```text
1. CORRECTION to 1058 s2: the row labelled "band c = 2 pi" was computed at
   collocation Omega = pi.  The decay-shape conclusions survive (superexpo-
   nential decay, ratio limit pi^2/(16 n^2), tail arithmetic independent of
   the spectrum), but the VALUE TABLE of the paper's lambda(n) is the B2
   even branch above, not the old B row.
2. MP/ARB onset moves earlier: on the even branch, lambda(6) already sits
   at the float64 collocation floor; validated eigenvalues/modes for the
   11-term campaign need arbitrary precision from n = 6 (was: n >= 7 on
   the mislabeled scale).
3. The tightest enclosure in the whole alpha campaign is mode 0:
   1 - lambda(0)^2 ~ 1.144e-4 is the small denominator of p(0) ~ 93.5.
   Certifying eigenvalue_sq_lt_one for lambda(0) needs error < 1e-4 on
   lambda(0) itself (easy for MP, but it must be the FIRST certificate
   produced, not an afterthought).
4. The repo's unitAdditiveFourierKernel (Omega = 1, e^{i x y}) scale is
   confirmed to be a DIFFERENT spectrum (old B row 2: lambda_0 = 0.5726)
   and must not be identified with the paper's lambda(n).
```

## 5. What changed elsewhere

```text
1056: amendment appended at s4/s5 - brick 2b marked REVOKED-BY-1059;
      brick ordering now "2a algebra + R2 conditional premise; R1 by
      separate design record".
1058: verdict s3 item 4 struck as RESOLVED-BY-1059; s2 value table
      annotated with the Omega = pi labeling error; probe gains block B2.
AGENTS 7d: alpha clause updated (convention pinned: even branch of the
      c = 2 pi pair, Omega = 2 pi collocation kernel; do NOT reuse the
      Omega = pi row).  New clause: the target angle strictness is NOT a
      perturbation of the source angle bound (kappa(T_2) = 5.83 vs a
      qualitative delta; ‖prolateFactor U‖ <= 1 is automatic, strictness
      is the whole content).
README C1 panel: brick #2 line rewritten to the R2 default + 2a.
```

## 6. Sources

```text
CC20 raw tex: /home/peter/cc20/x/weil-compo.tex lines 967-969, 983, 214
  (fetch + sha256 provenance per 1057 s0 and scripts/cc20_pin.sh)
ConnesWeilRH/Source/CCM25Concrete/CCM24UnitScaleStrictAngle.lean:1403-1419
  (delta definition + qualitative bounds)
ConnesWeilRH/Source/CC20Concrete/CCM24EulerTransport.lean
  (visible prime pool, coefficients, contraction norms)
ConnesWeilRH/Source/CC20Concrete/ProlateTraceReduction.lean:38-40
  (prolateFactor = composition of two projections)
docs/proofs/1058_alpha_chi_reconnaissance_probe.py block B2, log
  /home/peter/cc20/probe1058.log (deterministic; reproduce via
  scripts/run_1058_probe.sh)
docs/proofs/1056 s3-s4 (the reserved revocation condition), 1057 s5
  (alpha tail context)
```

## AMENDMENT (record 1062, same day) - section 4's convention pin is a SQUARE ROOT off

The pin "lambda(n) = even-parity branch of the concentration spectrum" is
WRONG as stated: tex:967-983 re-read verbatim shows the paper's lambda(n)
is the eigenvalue of the SINGLE windowed Fourier operator P_1 F P_1
(prolateeq / cosalphan, with ALTERNATING signs), and the concentration
operator P_1 F P_1 F (cosalphan1) has eigenvalue lambda(n)^2.  The
collocation kernel sin(2pi(x-y))/(pi(x-y)) used in s4 computes the
SQUARED operator, so the s4 value list [0.99994, 0.95939, ...] = the
paper's lambda(n)^2, and the paper's actual list is
lambda(n) = (-1)^n sqrt(s4 list) = [0.999971, -0.979485, 0.524086, ...]
exactly matching tex:972-975.  Corrected margins for the contract:
1 - lambda(0)^2 = 5.7247e-5 (not 1.1449e-4), mode 1 = 4.0610e-2 (not
7.957e-2); the (983) bound applies to |lambda(n)| directly.  The mode-0
p(0) ~ 93.5 scale in s4 is also superseded (tau(0) = mu/sqrt(1-mu^2) ~
132.2).  Discovery route and corrected anchor validation (sum t(n) =
22.9964756839 vs paper 22.9965, per-term match to <= 2.7e-6) in
docs/proofs/1062_alpha_t2t3_anchor_validation_and_lambda_sqrt_correction.md.
The rest of 1059 (the 2b revocation, R1/R2 re-scope) is untouched.
