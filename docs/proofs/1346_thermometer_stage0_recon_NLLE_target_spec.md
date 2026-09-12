# Record 1346 - Thermometer STAGE-0 recon: the C7 bone census and the NLLE target spec

```text
+---------------------------------------------------------------------+
| VERDICT QUALITY: STAGE-0 RECONNAISSANCE (paper-only, MODEL grade).   |
| Constants PLACEHOLDER-grade where used (structural conclusions are   |
| O(1)-robust; numeric ones are flagged).  No official digit, no       |
| verdict band consumed.  Supersedes the 1345 s5 band wording per      |
| law 42 (bands refined BEFORE any official run).                      |
| READOUT: assault on the N1 line = COLD-STRUCTURAL;                   |
|          harvest (target spec + conditional theorem + simulator)     |
|          = WARM and recommended.                                     |
| RH NOT claimed.                                                      |
+---------------------------------------------------------------------+
```

## 0. Trigger

Owner question (2026-09-12): "C7是不是唯一的不确定的骨头?那能否先探测C7,看看
值不值得打这条线?" - i.e. execute the F6 ranging shot at the missing bone
BEFORE funding the line. This record is that shot. A1/A3 independence
checked: the stage-0 consumes only committed algebra + located literature;
it needs no A1 digit and blocks on nothing.

## 1. Bone census - exactly where the uncertainty lives

```text
 C1 Paley-Wiener type from support          MECHANICAL (classical)
 C2 strip growth |G(+-w)| <= e^{R|delta|}   MECHANICAL (classical)
 C3 node density via explicit S(T)          MECHANICAL (parse Trudgian primary)
 C4 multiplicity m <= 10 log T              MECHANICAL (rederive Jensen,
                                            Titchmarsh 9.2; MoE 514655)
 C5 verified base 3e12                      FREE (Platt-Trudgian 2021)
 C6 explicit sampling/frame LOWER bound     SECOND BONE: exists
    on the (adversarially thinned) zero     non-explicitly (Beurling-
    sequence                                Malliavin/Olevskii); explicit
                                            only for lattices (Kadec 1/4).
                                            Explicitization = research-
                                            adjacent, quantifiable.
 C7 NLLE near-line local exclusion          FIRST BONE: absent theorem.
                                            This record SPECS it (s4) and
                                            audits reachability (s3).
 C0 my own algebra                          META-BONE: mitigations =
                                            member-counting recheck (s2),
                                            delta=0 -> W1 sanity, every
                                            constant sourced, stage-0
                                            flagged, official run rederives.
```

Answer to the owner's first question: **C7 is the only MISSING bone; C6 is
a second, smaller UNCERTAINTY bone (explicitness, not existence); C1-C5 are
mechanical.** Both C6 and C7 are probed below.

## 2. Verified contest algebra (member-counted, correction chain closed)

With `G(s) = laplaceAt g s`, real g of support in (-sigma, sigma),
sigma = log 2 on the full prime-free class (G7: first prime log 2),
`F = convolutionSquare g`, `laplaceAt F s = G(s) G(-s)` (1345 s1):

- On-line zero 1/2+iy: term = mult * |G(iy)|^2 >= 0 (W1 sanity at
  delta=0: PASSED).
- Quartet {beta+-i*y0, (1-beta)-+i*y0}, w = delta+i*y0, delta = beta-1/2:
  s-coordinates {w, conj w, -w, -conj w}; Schwarz reflection folds
  G(-w) = conj(G(-delta+i*y0)) back to height +y0; all four members carry
  the SAME real part Re[G(w)G(-w)] (1345 s1, reverified by explicit
  member counting).
- Quartet total = 4 * m * Re[G(w)G(-w)], and the quartet contains 4m zeros.

**The factor-4 cancellation (stage-0's first structural result):** loss per
off-line zero = |G(w)G(-w)| <= e^{2 sigma delta} * (on-line energy scale at
the same height) <= 2 * scale for delta <= 1/2 (sigma = log 2); gain per
on-line zero = mult * |G(iy)|^2 = 1 * scale. The quartet factor 4 is
exactly consumed by the 4 quartet members, so for an attacker concentrated
in one Nyquist window (width W = pi/sigma ~ 4.53; kernel-type G, tails at
adjacent-window nodes ~ sinc^2 ~ 0 by Nyquist geometry):

```text
 (**)  contest holds in the window  <=>  N_on >= e^{2 sigma delta} * N_off
       (multiplicity-weighted counts)  =>  off-line fraction f < 1/2
       as delta -> 0, and f < 1/3 uniformly for all delta <= 1/2.
```

Frame caveat (the C6 bone, stated honestly): (**) treats per-node energies
at face value (density ansatz). The rigorous version needs the explicit
frame lower bound converting "N_on nodes present" into "gain >= A *
energy"; A is where C6 lives. Structural conclusion (**) is O(1)-robust;
the exact threshold f* is C6-dependent and belongs to the official run.

## 3. The adversary configuration, audited against EVERY named unconditional constraint

Configuration A: at some height y0 > 3e12, fill one Nyquist window with
near-line quartets (delta_k ~ 1/log T), on-line count in the window driven
to a minority; attacker G = reproducing kernel at the window, projected
into the vanishing class (codimension-3m constraints are low-frequency
moments; kernel energy at y0 ~ 3e12 loses ~epsilon under projection - the
1342 nullspace construction Z is the numerical precedent).

| constraint | does it block A? | evidence |
|---|---|---|
| integrated density N(sigma,T) << T^{A(1-sigma)} log^C T | NO - budget at delta ~ 1/log T is ~0.26*T*log^C, window needs only ~0.7 log T | Ingham-class; 1345 s3 crack |
| explicit S(T) window occupancy | NO - it BOUNDS A: window total in [~0.50, ~0.94]*log T (PLACEHOLDER constants), adversary fits inside | Trudgian (parse pending) |
| explicit zero-free region | NO - delta = 1/log T is far inside beta < 1 - c/log T | Mossinghoff-Trudgian line |
| multiplicity bounds | NO - per-quartet m <= 0.23 log T needed at worst; Jensen gives <= 10 log T (crude) / ~log T/log log T (small-disk sharpened) | MoE 514655; Ivic 1999 |
| large sieve (explicit Montgomery-Vaughan) | NO - it requires SEPARATED point sets; A clusters freely inside the window | separation hypothesis of the sieve |
| pair correlation / zero repulsion | NO unconditional block located - Montgomery-type pair correlation is RH-conditional or on-line-only; DH repulsion exists only near Re=1 (and for zeta itself there is no exceptional-zero analogue) | 1345 s3-s4 searches; Benli 2410.06082 |
| horizontal clustering bans (two zeros within c/log^k T) | NO - even a spacing floor c/log^k T leaves room for >> 0.7 log T quartets across a width-4.53 window | Jensen-counting argument, s3 |

**Stage-0 conclusion (the ranging readout):** configuration A is consistent
with every unconditional theorem this session located. Therefore (★) is NOT
derivable from any located named technology: the missing input is a genuine
missing theorem, not a constant-tuning gap. Reachability classes (declared
BEFORE any official run, law 42 + new F7): the N1 ASSAULT is
**COLD-STRUCTURAL** (baseline technology set for local majority exclusion =
void; a ratio-to-void band is meaningless - this refines 1345 s5, whose
"<= ~2x of existing" wording presumed a non-void baseline). The line's
HARVEST is **WARM**: the recon itself produced the first quantitative spec
(s4) plus two provable artifacts (s6).

Sweep caveat (epistemic honesty): "no located technology" is the result of
this session's targeted searches, NOT a systematic technology sweep. The
official thermometer's task 1 is exactly that sweep (candidates: explicit
short-interval density, half-isolated zeros arXiv:2206.11729, Gonek-type
clustering, Goldston-Gonek-Ozluk-Snyder pair-correlation unconditional
fragments, Carneiro-Milinovich-Soundararajan zero-repulsion line).

## 4. The NLLE target spec (first explicit quantification of the missing input)

```text
+---------------------------------------------------------------------+
| NLLE (near-line local exclusion), stage-0 spec:                      |
|   There exist explicit eps(T) > 0 and T0 such that for every         |
|   Nyquist window [y, y + pi/sigma] at height >= T0: the              |
|   multiplicity-weighted count of zeros with |beta - 1/2| < eps(T)    |
|   is < 1/3 of the multiplicity-weighted count of ALL zeros in the    |
|   window.   (Zeros with |beta - 1/2| >= eps(T) are handled instead   |
|   by classical integrated density, which is STRONG away from the     |
|   line - the two-regime split; the entire crack lives in the         |
|   ultra-near-line regime.)                                           |
| Status: NLLE => RH via the committed chain (1345 s2 + s3 assembly);  |
|   RH => NLLE vacuously (no off-line zeros).  NLLE is therefore        |
|   equivalent to RH - but quantitatively specified: window width,     |
|   fraction, regime, and explicit constants, which "all zeros on the  |
|   line" is not.  No located technology proves it (s3).               |
+---------------------------------------------------------------------+
```

## 5. Band refinement (law 42: refined BEFORE any official run; supersedes 1345 s5 wording)

Old bands ("X <= ~2x of existing => HOT") presumed a non-void baseline -
meaningless when existing technology gives NO local control at all (F7
lesson banked). Operational bands for the official thermometer:

```text
 X := (best local off-line-fraction control derivable from the swept
       named technologies) / (required f* from s2 with explicit C6)
 HOT   - X <= 4   AND baseline non-void: required input is constant-
                    tuning inside published explicit technology
 WARM  - 4 < X <= 32: one genuine new lemma with a nameable proof route
 COLD-STRUCTURAL - baseline void (no named technology gives ANY local
                    control) or X > 32
```

Stage-0 places the line in COLD-STRUCTURAL for assault, with the sweep
(s3 caveat) as the only upgrade path - cheap, and the FIRST task of the
official run if funded.

## 6. Harvest items (WARM, each provable/publishable without NLLE)

- **H1 - target-spec memo**: s4 as a standalone note: "RH follows
  (machine-verified equivalence chain) from explicit near-line majority
  exclusion" - the first quantitative spec of what the field must prove;
  systematic technology sweep attached.
- **H2 - conditional theorem**: "RH holds unless, at some height > 3e12,
  ultra-near-line zeros achieve local majority in a Nyquist window" -
  assembled from C1-C5 + best-available C6 (explicit frame bound flagged
  where non-explicit); paper-grade first, Lean-izable second.
- **H3 - A1c simulator**, repurposed with a sharp objective: visualize the
  majority-attack margin D(f, delta, m) on the G8-faithful dictionary
  (difficulty map, not truth map - expectation management per 1345 s5.2).

## 7. Portfolio consequences (owner decision input)

1. N1 ASSAULT: NOT recommended for funding at this time (COLD-STRUCTURAL;
   the ranging shot just saved the assault budget - F6 working as
   designed). N1 stays REGISTERED PENDING with the s4 spec attached; the
   upgrade path is the s3 sweep.
2. P1 (A1 capacity exponent, task #7) and P2 (A3 audit of
   arXiv:1703.03827v14, task #8) are UNAFFECTED and proceed - they probe
   different bones (net-program capacity; external-claim adjudication).
3. Task #9 (official thermometer) rescoped: (a) systematic sweep, (b)
   primary-source constant parse, (c) explicit C6 frame bound sufficient
   for H2. Funding optional; H1/H2 harvest does NOT require it.

## 8. What this record does NOT claim

- No official digit; PLACEHOLDER constants used only where flagged; every
  structural conclusion stated with its O(1)-robustness caveat (s2 frame
  caveat, s3 sweep caveat).
- COLD-STRUCTURAL is a statement about LOCATED technology after targeted
  searches, not about all possible technology; the sweep may upgrade it.
- NLLE's equivalence to RH makes it as hard as RH; the spec's value is
  operational (it tells a prover exactly what to prove, at what strength,
  with which regime split), not a difficulty reduction.
- RH not claimed; all grades MODEL/paper per repo law.
