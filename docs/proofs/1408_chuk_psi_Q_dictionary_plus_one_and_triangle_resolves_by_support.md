# 1408 — 1407 dictionary double-evaluation outcome: PLUS_ONE; the 1406 triangle resolves by SUPPORT RADIUS, and the separating hypothesis is located inside the register

Date: 2026-09-14. Model-level outcome record for the prereg committed at
`docs/proofs/1407_chuk_psi_Q_dictionary_double_evaluation_prereg.md`
(prereg file UNTOUCHED; gate classes UNCHANGED across all three
revisions; law 42). No Lean was written. Nothing was falsified.
RH is not claimed, in either direction.

## 1. Verdict up front

`scripts/run_1407_dict.py` rev3, invocation 3. Sentinels, verbatim:

```
DONE gates=D0:PASS,D1:PASS,D2:PASS,D3:PASS
VERDICT dictPsiQ=PLUS_ONE q_ratio=1.00000000216 psi=0.000926518704814 Q=0.000926518706811
sha256 docs/proofs/1407_dict_results.json = 3c39472c385e10aa1b3299d1c0b74c09497d5f1f5e8b6af8fa634795ee9bbc4c
```

The register's `psi` IS the paper's `Q` as a functional on real windowed
tests, with sign `+` and factor 1: `Q/psi = 1 + 2.16e-9` at the locked
flat-bump cell (`L = 1/2`, prime comb nonempty: `n = 2` visible,
`n = 3` excluded), every gate passing at 5-15 orders of margin inside
its class. Per the prereg section 6 `PLUS_ONE` reading, this record then
discharges the mandated formal-side verification duty — and the duty's
answer DISSOLVES the 1406 collision triangle: the chain's `¬RH` owner
class is NOT windowed (section 6 below), so no fixed-L certificate,
Chuk's or Yoshida's, ever reaches it. The paper's own sentence
(main.tex:194-199, "For fixed L it is a finite, unconditional statement
... Yoshida proved positivity for 2L <= log 2") was, and remains, the
whole story.

## 2. Invocation ledger (law 7j disclosure)

| inv | state | outcome |
|-----|-------|---------|
| inv1 | rev1 | crash `TypeError: dict - mpf` (return-tuple unpack order at the mp call site; rig-only fix commit `6a3b80c`); D0 line printed pre-verdict (allowed: D0 is tied to the pre-locked committed reference, not to any dictionary digit). Log kept: mirror `docs/proofs/1407_dict_run.inv1.log` |
| inv2 | rev2 | VALID RUN, FALSE FAIL: `D1:FAIL` at rel 1.74e-5 vs class 1e-8, `q_ratio` 0.9999967 missing `PLUS_ONE` at 3.3e-6. Root cause: evaluator quadrature, not dictionary (section 3). Artifact archived renamed: `docs/proofs/1407_dict_results.inv2.json` (sha256 `9755ba11...`), log mirror `1407_dict_run.inv2.log` |
| inv3 | rev3: `bump_edges()` panels resolve BOTH flat-bump amplitude (`<= 0.005`) and half-period oscillation; TERM-DECOMP chuk channels switched from the y-side `g_log2` substitution to the actual D1 t-integral `planch` (diagnostic honesty; gate classes untouched) | VALID, 11.2 s, verdict above |

## 3. Diagnosis of inv2's failure (mpmath-50bit reference diagnostic)

The prereg's D1/D2 classes were SATISFIABLE but not achievable by the
rev1-rev2 evaluator — law F12 (pre-run achievability) applies to gate
*implementations*, not just gate statements; inv2 discovered at runtime
what a pre-run noise prediction would have caught. Diagnostic
(`scripts/_diag_1407_quadrature.py`, run on the mirror):

| quantity | rel err, 1-panel GL16 (inv2) | rel err, dense panels | reference |
|----------|------------------------------|----------------------|-----------|
| `C = 2 int_0^L f cosh(x/2)` | **8.8e-7** | 6.2e-16 | mp 50-bit |
| `fhat(11)` | 5.4e-6 | 1.1e-15 | mp |
| `g_of` (register side, 0.02 subpanels) | ~1e-13 | — | dense |
| pole identity: register `4 int g cosh` vs `2C^2` (mp) | **agrees to 3e-17** | | |

`R._panels` is purely oscillation-density driven
(`per = freq*L/(2pi)`), so a non-oscillatory flat bump on `[0,L]` got
ONE 16-node panel; its feature scale ~0.1 was unresolved at ~1e-6, which
squared into the 1.76e-6 pole-path split and integrated into D1's
1.74e-5. The register side was accurate all along, and the inv3
measurement confirms the algebra identity itself (no convention error
was ever present; the pole "mismatch" was pure Chuk-side quadrature).

Post-fix gate margins: D1 rel 9.1e-15 (class 1e-8), D2 max 1.7e-17,
D3 tail_rel 5.3e-16 at `T = 400` (8160 nodes; class 1e-14), D0
|diff| 1.4e-12 vs committed tier-1 `A = -17.3431099115819` (class 2e-4).

## 4. Measured dictionary cell (locked design of 1407 section 4)

| channel | register (y-side, F = f~star f) | Chuk (t-side, Fhat = fhat) | abs diff |
|---------|--------------------------------|----------------------------|----------|
| pole    | 0.09954340257320513            | 0.09954340257320515        | 2e-17 |
| archimedean | +0.0959658012132 (subtracted) | -0.0959658012112 (integrated into Q) | 2e-12 |
| prime comb (n=2) | -0.00265108265523 (= -(2log2/sqrt2) F(log2)) | -(2log2/sqrt2) x D1-integral | D1 rel 9.1e-15 |
| **total** | psi = +9.26518704814e-4 | Q = +9.26518706811e-4 | **ratio 1 + 2.2e-9** |

The residual 2e-9 sits in the arch channel's float-path quadrature
floor (2e-12 absolute on a 0.096 term, amplified by the cancellation
`pole - arch - primes` down to 9.3e-4) — three orders inside the
`PLUS_ONE` class, no unexplained structure.

## 5. What PLUS_ONE buys, and what it cannot

Model-level (law 65): a functional identity confirmed at ONE even
generic cell, with parity-blind Plancherel structure and a
structurally-matched odd-sector pole sign (1407 section 3: for odd `f`
both conventions give `-2s^2`). It confirms there is NO sign, factor,
or pole-convention discrepancy between the register's `psi` and the
classical geometric side — pillar A's negativity census and all 107
measurements are now known to be, up to the untested odd-sector leg, a
census of classical `Q`-positivity, i.e. of a theorem
(Yoshida 1992 / Connes-Consani 2021 for `2L <= log 2`, per the paper's
own citations). That citation upgrade is real: pillar A's exit (1081,
closed as campaign at 1402-1404) now rests partly on published
positivity, not only on measurement. It funds no Lean and proves
nothing: one bump cannot establish a functional identity, and the
sup-law keeps its veto.

## 6. The triangle dissolves: the separating hypothesis is support radius

1406 section 5 posed T1 x T2 x T3: at most two vertices can hold, or RH
falls. The prereg's `PLUS_ONE` reading demanded the formal-side duty:
"grep the register class: is the tower's owner class support-unbounded?
... find the hypothesis that separates the wall class from the Yoshida
class". Executed. **Correction first (law F18, section 7):** T1 as
typed in 1406 ("exists owner g (smooth, supp g in +-(log2)/2) with
qw g < 0") OVERSTATED the formal chain. The support field is not there.
The actual statements:

```lean
-- C1HealthyYoshidaSpectralNegativity.lean:568-571 (the F3-style right
-- producer; the public conclusion carries NO support bound):
theorem exists_healthyDetectorData_of_sourceNontrivialZero_right
    (rho : sourceNontrivialZeroSet) (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    ∃ g : CompactLogTest, HealthyYoshidaDetectorData rho.1 g

-- :535 + :543, the produced radius, height-dominated:
let R : Real := (2 : Real) ^ (n0 + 1) + 2 + dist (2 : Complex) rho.1
have himLt : |rho.1.im| < (2 : Real) ^ (n0 + 1)
```

and the root-supported form is explicitly conditional elsewhere in the
same register:

```lean
-- C1HealthyDetectorRootSupportExit.lean:78-81 (header): "The
-- orbit-detector theorem does not supply this support field, so this
proposition remains a conditional alternative ...":
def rootSupportedHealthyDetectorGate (rho : Complex) : Prop :=
  ... Function.support g.test ⊆
        Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2)
```

    +--------------------------------------------------------------+
    | CORRECTED T1:  not-RH  ==>  exists owner g with             |
    |   radius R(rho) >= 2^ceil(log2 |Im rho|)   [NO fixed window |
    |   -- grows unboundedly with the zero's height]  and qw g < 0 |
    +------------------------------+-------------------------------+
                                   | psi = Q  (PLUS_ONE, model)
    +------------------------------v-------------------------------+
    | T2:  Q(f) >= 0 ONLY for supp f <= 0.8 (Chuk, unrefereed;   |
    |    even sector) / odd sector 8.2e-15 (eq:oddlower), and    |
    |    2L <= log 2 (Yoshida, classical)                        |
    +--------------------------------------------------------------+

A zero at height 14.13 (the first one) already forces `R >= 18 > 0.8`;
every taller zero pushes further out. The certificate's window and the
counterexample's support are DISJOINT hypotheses — no collision, no
escalation, the chain and every published positivity theorem coexist.
And the wall, restated with full precision, is exactly the missing
radius-shrink: turn the produced owner's `R(rho) ~ 2^gamma` window into
the root-supported gate `support <= log 2 / 2`. That step CANNOT be
outsourced to any fixed-L certificate, by the paper's own
`lambda_min(L)` equivalence sentence: positivity for EVERY fixed L is
what RH means; each finite certificate sits strictly inside the wall.
Consuming Chuk at `L <= 0.8` would supply `0 <= qw` for exactly those
healthy tests already known positive by Yoshida — which is, per section
5's census, all the root-supported family numerics has ever shown.

## 7. Law (promoted to AGENTS.md section 7)

- (F18) CITE THE FORM PREMISE VERBATIM, ESPECIALLY YOUR OWN. The 1406
  triangle was sharp only because T1's support field was paraphrased
  from memory instead of transcribed from the producer's statement —
  the register's own `exists_healthyDetectorData_of_sourceNontrivialZero_right`
  has NO support bound, and the root-supported gate file SAYS the orbit
  theorem does not supply it. F17 (transcribe, never reconstruct)
  applies to logical premises as much as to code: before a dichotomy or
  collision is priced, the exact statement text (file:line) of every
  formal vertex must be quoted in the record; a paraphrased vertex can
  manufacture a crisis that the kernel never proved.

## 8. Kill scope honored

One model cell; one correction; one structural observation about radii
already implicit in 1402's wall-repartition ("what remains is the
single `0 < arch h.convSq`" — now seen to be the same missing
radius-shrink, viewed from the sign side). It cannot falsify the chain,
Yoshida, or Chuk; proves no gate; funds no Lean; claims nothing about
RH, which remains exactly the wall: `B0b` iff `SourceRH`, open.

## 9. Next steps

1. Register closure for the 1405-1408 wave (map item 36, root project
   log, frontier card): the Chuk species is now FULLY adjudicated —
   bridge framed (1405), cross-term covered by double structural kill
   (1406), dictionary PLUS_ONE (1407), triangle dissolved by support
   radius with the separating hypothesis formally located (1408).
2. Campaign queue after law F15 re-audit: empty, with stronger grounds
   than at 1404 — the last external-literature surface is now measured
   and closed, and the wall restated as the radius-shrink step.
   What remains is a proof idea (Peter's decision), not an executable
   paper or rig item.
3. If formal consumption is ever wanted (it buys nothing per section 6,
   and this record recommends against it): a Lean `psi = Q` bridge
   theorem would be a multi-day campaign requiring explicit approval —
   do not start without asking.
