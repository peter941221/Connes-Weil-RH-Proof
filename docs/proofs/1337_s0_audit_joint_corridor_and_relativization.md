# Record 1337 — S0 audit: per-prime hcolumn, the joint corridor, and the relativization reading

Date: 2026-09-11.
Status: READ-ONLY AUDIT (paper only: no Lean brick, no numerics, no Source
change). It answers the Stage-0 question that record 1336 section 6 left
implicit — does the G8 readback need `hcolumn` for EVERY visible prime or for
ONE — and derives the consequences for what C4 (record 1336) would actually
have to satisfy. It authorizes nothing by itself; the numerical decision it
licenses (fund M1-prime) is executed under record 1338's own preregistration.
MODEL/paper analysis; RH is not claimed.

## 1. The S0 answer: EVERY prime, not one (from committed Lean)

Consumer chain, read back from source:

```text
ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSActualSchurCascade.lean:48-57
  oldSuffixFrame lambda p S = parameterizedSoninPolarFrame lambda 1 (p :: S)
  newSuffixFrame lambda S   = parameterizedSoninPolarFrame lambda 1 S

ConnesWeilRH/Source/CCM25Concrete/CCM24FiniteSCompletedJuliaRawPhysicalOldCarrier
  AntiresonantRadialSplit.lean:55-59
  newFrameAntiresonantColumn lambda p S =
      (primeEulerAmbientLossFactor p)^dagger ∘L newSuffixFrame lambda S
```

The frame objects are indexed by a prime LIST: `oldSuffixFrame` carries the
head prime `p` against the suffix list `S`, and the Euler cascade advances
through the visible-prime list one prime per step (records 1324-1328 state
every P1 bound for a fixed `(p, S)` step; the record-1328 ledger theorem
`p1BoundaryEnergyLedger_of_fullCarrierColumnEnergy` is stated at
`C1G8P1ColumnEnergyQuantitativeAlignment.lean:314` with
`(p : CCM24VisiblePrime) (S : List CCM24VisiblePrime)` in its hypothesis
list). The family-level boundary defect is the assembled product of the
per-step defects (record 1251 four-channel ledger; records 1326-1328 merge),
so the summability the readback consumes is the sum of the per-step column
energies. For a healthy detector `g` the visible-prime set is
`{p prime : p <= exp(R_g)}` and contains at least {2, 3} for every nonzero
support radius used in the campaign. **Answer: `hcolumn` must hold at every
cascade step, i.e. simultaneously at every visible prime.** The S0 question
from the session map is closed in the unfavorable direction: the two-prime
analysis below is BINDING, not optional.

## 2. The joint corridor lemma (paper, elementary, zero RH content)

Stage-0 reduction (record 1328 section 4 / 1329 section 1): at lag
`tau = log p`,

```text
E_col(p) converges  <=>  sum_j ||(I + U_tau) e_j||^2 < infinity  over any ONB
                         of ran P_S,  U_tau f(t) = f(t + tau) on L^2(R)
                         (= finiteSCarrier, CCM24FiniteSProjectionTrace.lean:73,
                            GlobalLogHaar.lean:30).
```

Each summand is nonnegative, so convergence forces
`||(I + U_{log p}) e_j|| -> 0` along the tail: the carrier must
asymptotically live in the (-1)-eigenspace geometry of EVERY prime
translation. Fourier side: `(I + U_tau)` is multiplication by
`1 + e^{2 pi i tau xi}`, so the single-prime corridor symbol and its zero
set are

```text
s_p(xi) = 2 + 2 cos(2 pi xi log p) >= 0
zero set L_p = { (2k+1) / (2 log p) : k in Z }      (a lattice, spacing 1/log p)
```

Two-prime joint symbol (what section 1 forces):

```text
s_{p,q}(xi) = s_p(xi) + s_q(xi) = 4 + 2cos(2 pi xi log p) + 2cos(2 pi xi log q)
```

Lemma (disjointness). `L_p ∩ L_q = ∅` for primes `p ≠ q`:
`(2k+1)/(2 log p) = (2m+1)/(2 log q)` iff `q^{2k+1} = p^{2m+1}`, impossible by
unique factorization. Hence **`s_{p,q} > 0` on all of R**: the joint corridor
has an EMPTY zero set, while each single corridor has positive density.

Lemma (near-minima). `log p / log q` is irrational (`p^b = q^a` impossible),
so by Kronecker the lattices come arbitrarily close: `inf s_{p,q} = 0` is not
attained. Near a crossing of `L_p` and `L_q` the two corridors intersect
transversally (different spacings), so the joint `{s < eps}` region has
measure `O(eps)` per crossing while each single-prime region has measure
`Theta(eps)` already saturated — i.e. the k-prime carrier must hide its
spectral measure in a target that is thinner than ANY single-prime corridor
by an eps^{k-1}-type factor at resolution eps.

Consequence for the record-1334 verdict. The joint corridor is a SUBSET of
every single corridor, so IF the Γ-only model's single-corridor capacity
reading of record 1334 (`A_tau ≈ 2.0`) stands, the joint condition fails a
fortiori as well. QUALIFICATION (added the same day) — NOW DISCHARGED:
during record-1338 implementation it was found that 1334's capacity block
was selected from the WRONG end of the singular-vector list (largest-`sigma`
sector instead of the preregistered `sigma < 1e-6` near-kernel sector; full
corrigendum in record 1338 section 0), so the `A_tau ≈ 2.0` number was
measured on a generic span where 2.0 is trivial, making this paragraph's
force conditional. Record 1338's control statistic S0unc RE-MEASURED the
capacity on the CORRECT near-kernel block at N = 8192 and got
`A_tau in [1.997, 2.013]` (FALSIFIES at every cell and both flavors;
record 1339 section 2): the condition is satisfied, the a-fortiori force
of this paragraph stands, and 1335's headline survives the corrigendum.

## 3. The relativization reading (what C4 must survive logically)

The G8 route assumes an off-line zero `rho = beta + i gamma` (that is the
hypothesis) and must derive `0 <= qw(g)`; if the strengthened `hcolumn` on
`W_zero` were to REQUIRE all zeros on the line, the premise would be false
under exactly the hypothesis that needs it — a 1225-F1-style bundling trap
would be present at the model level. Check:

```text
1336 imposes vanishings at the REAL points xi_n = gamma_n / (2 pi).
A single off-line quadruple {rho, 1-rho, rho-bar, 1-rho-bar} has N(T)-count
2 (two members with imaginary part +gamma) but supplies only ONE real
constraint point gamma/(2 pi): the factor-2 mismatch shows up as finitely
many extra surviving carrier directions.
A finite number of extra O(1)-defect directions added to a convergent
nonnegative series keeps it convergent.
```

So: for the hypothesis actually in force (the route needs at most the
witnessed off-line zero, finitely many), `hcolumn`-on-`W_zero` is NOT
obviously self-contradictory under the assumption — no 1225-style trap fires
at this level. This is a REHABILITATION of the C4 architecture relative to
the worst-case fear, with two honest caveats:

- Caveat R1 (unbounded off-line sets): if the off-line sector were
  unreasonably large the surviving dimension grows with its counting
  function and the tail question reopens. The route never needs this case;
  the carrier definition must simply not be allowed to depend on an
  unproved off-line sparsity statement. Record for M2's definition stage.
- Caveat R2 (data access): any numerical probe can only use CERTIFIED
  ON-LINE zero data (the law-34 certifier / mpmath Gram search both probe
  the line). The probe therefore tests the S-sector tail under RH-typical
  data and the FINITE-perturbation reading above handles the witness;
  a probe PASS establishes "not cheaply dead", never "provable", and never
  anything about models with infinitely many off-line zeros.

## 4. What survives of record 1336's M1 (and what must change)

1336 section 6 M1 = index-cancellation check (expect dim W_zero(L) ~ O(S)).
Section 2 above sharpens the target: constraints are imposed at the ±lattice
of zero images (each zero line `±gamma_n` is a distinct real point, so the
model uses `2 N(2 pi L)` functionals on a sector of measured dimension
`r = |W(L)|`), and the BINDING statistic is the surviving fraction plus the
corridor capacity OF THE SURVIVORS, not the raw count. The joint-corridor
subset argument (section 2) says the SAME single-prime statistic `A_tau`
measured on the constrained sector is a valid NECESSARY test — no new joint
symbol machinery is needed in the probe. So M1 is kept but re-scoped to
M1-prime with two statistics:

```text
S1  index cancellation:      r'  = dim(ker E) ,  E[n,j] = v_j(xi_n) on the
                             1334 near-kernel sector basis {v_j}, constraints
                             at ±xi_n = ±gamma_n/(2 pi), gamma_n <= 2 pi L.
                             Report r'/r against the rank bound
                             r' >= r - 2N(2 pi L) and the band below.
S2  corridor capacity:       A_tau of the CONSTRAINED sector exactly as
                             record 1334 section 1 (unchanged statistic,
                             unchanged bands), decisive cell L = 48.
```

Verdict bands (pre-committed in 1338; stated here so the reading of 1338 is
self-contained): `THINS` iff `r'/r <= 0.20`; `NO-THIN` iff `r'/r >= 0.60`;
else `INCONCLUSIVE`. Capacity as 1334: `CONCENTRATES` iff `max_tau A_tau <=
0.30`; `FALSIFIES` iff `min_tau A_tau >= 1.20`.

Prediction table (what each outcome licenses):

```text
+------------+------------+-------------------------------------------------+
| S1         | S2         | reading                                         |
+------------+------------+-------------------------------------------------+
| THINS      | CONCENTRATES| C4 lives: fund M2 (G2 strip-RKHS package ->      |
|            |            | W_zero + evaluation, per 1336 section 6)         |
| THINS      | FALSIFIES  | thin but still no hiding -> Option H permanent;  |
|            |            | radial leg closed at model level twice over      |
| NO-THIN    | *          | 1336's own index bookkeeping refuted at          |
|            |            | truncation level (survivor fraction does not     |
|            |            | fall below independence floor) -> C4 as stated   |
|            |            | dies cheaply; pivot to L4 Fork B + A4 + NM       |
|            |            | registry rows (map 006)                          |
| INCONCLUDE | *          | amend + rerun once (law 42), not arbitrate       |
+------------+------------+-------------------------------------------------+
```

## 5. What this record does NOT establish

No Lean theorem, no numeric datum, no statement about the formal carrier,
no vanishing, no `qw` sign, no `SourceRH`, no RH claim. The section-2 lemmas
are elementary real facts with committed-source definitions behind them
(reported with file:line); they could later be Lean-ized as a standalone
arithmetical brick if the campaign ever needs them formally. The
rehabilitation in section 3 is a paper reading of the constraint geometry
under finite off-line sets; it is not a proof that a `W_zero` definition
avoids the trap for every legal carrier parameterization — M2's definition
stage must discharge that at the statement level.

## 6. The convention discovery: the instrument's winding is 2x the zero count

The 1334 script's phase is `arg phi(x) = -2 Im [ -(s/2)ln pi + logGamma(s/2)
+ logGamma((s+1)/2) ]`, `s = 1/2 + 2 pi i x` — a product of TWO gamma
factors (a GL(1,C)-flavor archimedean completion; Legendre duplication
`logGamma(s/2)+logGamma((s+1)/2) = log(2^(1-s) sqrt(pi) Gamma(s))` reduces
it to a single `Gamma(s)` with constants). Its winding has the closed form

```text
|W_LC(L)| = 2 L (ln pi + 2 ln L - 2)
            L=32: 388.9 | L=48: 661.2 | L=64: 955.2
            (1334 measured windings: match exactly)
```

while the zero-count identity used by record 1336 section 3 is the
GL(1,R)-flavor one:

```text
N(T) = theta_R(T)/pi + S + 7/8,  theta_R(2 pi L)/pi = L (ln L - 1)
     => 2 N(2 pi L) ~ 2 L (ln L - 1)        (± constraint set: one per sign)
     => |W_LC(L)| / (2 N(2 pi L)) = 2 (1 + (ln pi / 2)/(ln L - 1))  ->  2
```

Check on measured cells (M counted at the 1338 margin `gamma <= 2 pi (L-3)`):
L=48: r=658 vs 2N(2 pi 45) = 2*127 = 254, ratio 2.59 versus the closed form
`2 (1 + 0.572/(ln 48 - 1)) = 2.40` — both approximations bracket the finite-L
regime; the probe will use the exact counts. Consequence: on the
COMMITTED-twin (two-gamma) model the truncated index sector is
asymptotically TWICE the number of available ± point-vanishing functionals,
so the survivor fraction cannot fall below `f0 = 1 - 2N/|W| -> 0.50`: the
record-1336 claim "N(T) vanishings cancel the winding to leading order" is
FALSE on this convention, and the failure is exactly a factor 2 of
archimedean flavor — not a subtler mechanism. A single-Gamma_R-flavor phase
would have `|W_LR(L)| = 2 L (ln L - 1) = 2 N(2 pi L) (1 + o(1))` — thinning
to O(S)-scale survivors becomes arithmetically POSSIBLE (still requiring
constraint independence and a capacity test for the survivors).

Reading: C4 is not dead; the MODEL PHASE FLAVOR is the binding variable. The
record-1338 probe therefore measures BOTH flavors — the committed two-gamma
twin (for continuity with 1332-1335) and a single-Gamma_R variant — with S1
(index cancellation) and S2 (survivor corridor capacity) reported per
flavor. If ONLY the Gamma_R-flavor cells thin and concentrate, the finding
is a model-convention decision for the owner (which archimedean factor is
the intended carrier model), and it must be reconciled against the
committed Lean `ccm24ArchimedeanScatteringPhase` definition BEFORE any Lean
re-parameterization is contemplated; this record makes no claim about what
the Lean phase's asymptotic flavor is — that check is registered as the
first step of M2 if M2 is ever funded. (The Lean check is bounded:
`Source/CC20Concrete/CCM24HardyTitchmarsh.lean` pins the phase by
definition.)

RH is not claimed.
