# Record 1364 (W0 READOUT, closes task #14) - Connes math/9811068 dictionary: Q1 theorem numbers landed, Q2 subclass-positivity = NO, Q3 his-delta is NOT our-delta but his elimination MECHANISM is Fork-B's own design

```text
+---------------------------------------------------------------------+
| Wave W0 (B-route recon) of the 1358 direct-attack charter. Verdict  |
| up front: NEITHER good nor bad for breaching - the survey is a MAP  |
| result. All quotations raw from arxiv.org/pdf/math/9811068v1,       |
| question-scoped reads this session (API-names-are-DATA law applied  |
| to primary text). Deliverable = B-blueprint v1 as charter s3        |
| promised. RH NOT claimed.                                           |
+---------------------------------------------------------------------+
```

## 1. Q1 - the exact theorem inventory (number fields, characteristic zero)

The paper's own section map (verbatim): "I Quantum chaos ... II
Algebraic Geometry and global fields of non zero characteristic. III
Spectral interpretation of critical zeros. IV The distribution trace
formula for flows on manifolds. V The action (λ,x) → λx of K* on a
local field K. VI The global case, and the formal trace computation.
VII Proof of the trace formula in the S-local case. VIII The trace
formula in the global case, and elimination of δ. Appendix I, Proof of
theorem 1."

Load-bearing items:

1. THEOREM 1 (section III, proof in Appendix I via Weil's distribution
   reading [W2] of Tate-Iwasawa): the operator D_chi from the R*_+
   action on H_chi has DISCRETE spectrum, "Sp D_chi ⊂ iR is the set of
   imaginary parts of zeros ... which have real part equal to 1/2;
   ρ ∈ Sp D ⇔ L(chi~, 1/2 + ρ) = 0 and ρ ∈ iR", multiplicity rule
   stated, and "When the zeros of L have multiplicity and δ is large
   enough the operator D is not semisimple and has a non trivial
   Jordan form". CRITICAL: the spectrum sees ONLY the 1/2-line zeros
   (absorption spectrum); noncritical zeros "appear as resonances and
   enter in the trace formula through their harmonic potential with
   respect to the critical line" (intro, verbatim).
2. Equation (34): "Trace"(U(h)) = hat-h(0) + hat-h(1) − Σ_{L(chi,ρ)=0,
   Re ρ = 1/2} hat-h(chi,ρ) + ... with the on-record caveat: "the trace
   on the left hand side of (34) only makes sense after a suitable
   regularisation since the left regular representation of C_k is not
   traceable ... similar to the one encountered by Atiyah and Bott".
3. Equation (15) passage: the formal trace, "when restricted to the
   hyperplane h(1) = 0, [is] the distribution obtained by André Weil
   [W3] as the synthesis of the explicit formulas" - THE SAME SPECIES
   as our machine-checked gate (d767a1d formalizes exactly this
   distribution on a truncated test class). 1359 s2.1 stands, now with
   the locus pinned: his vanishing test = h(1)=0 (vanishing at the ONE
   identity point); ours = cc20TripleFiniteVanishingSet (vanishing on
   a finite triple class). Same axis, different discretization.
4. Section VIII: L2(X) := L2_delta(X) at "the trivial value delta = 0
   which of course eliminates the unpleasant term", Q_Lambda =
   projection onto B_Lambda = span of f in S(A) "which vanish as well
   as their Fourier transform for |x| > Lambda", and the GLOBAL
   FORMULA (16): Trace(Q_Lambda U(h)) = 2 h(1) log' Lambda + Σ_v
   integral' h(u^-1)|1-u| d*u + o(1), where 2 log' Lambda is the
   ideles annulus mass. His own admission (verbatim): "We can prove
   directly that (16) holds when h is supported by C_{k,1} but are NOT
   ABLE TO PROVE (16) DIRECTLY FOR ARBITRARY h ... What we shall show
   however is that the trace formula (16) IMPLIES the positivity of the
   Weil distribution, and hence the validity of RH for k. Remember
   that we are still in positive characteristic where RH is actually a
   theorem of A. Weil." Theorem 5 = the positive-characteristic
   equivalence a) (16) holds  <->  b) RH for all Grossencharakter
   L-functions.
5. Weil distribution (formula (17)): Delta = log|d^-1| delta_1 + D −
   Σ_v D_v. Positivity of Delta on the h(1)=0 hyperplane = Weil's
   RH criterion = the classical statement whose Lean formalization is
   our committed iff (d767a1d). The wall has a NAME on both sides of
   the dictionary and it is the SAME name.

## 2. Q2 - is there a subclass-positivity lemma we can restrict into?

Answer: NO, on the located text. Every positivity-adjacent result
found is either (i) an implication from the trace formula to
positivity (nothing unconditional), or (ii) an equivalence certified
in positive characteristic, where RH is already Weil's theorem and
positivity is imported from the geometry of curves, not proved by the
framework. The only h-class where (16) is actually PROVED is "h
supported by C_{k,1}" - a SUPPORT-near-identity class, and there the
formula is a computation, not a positivity statement, and it does not
cover the test functions a positivity proof would need.
Consequence per charter s3: the B-blueprint does NOT collapse to a
pullback exercise. The expectation stated at 1359 s0 ("expectation
low") is now confirmed at zero. The Goldfeld passage (p.50, verbatim)
says it for him: "the positivity of the inner product is of course
equivalent to the positivity of the Weil distribution (and by the
result of A. Weil to RH) but this DOES NOT GIVE ANY CLUE HOW TO PROVE
THIS POSITIVITY" - a fifth independent source confirming the wall's
location (1346 s3 audit, 1352, 1355, 1358-charp, now 1364).

## 3. Q3 - his delta vs our delta: different animals, but his ELIMINATION is our Fork-B design pattern

His delta (verbatim): "an unnatural parameter delta which plays the
role of a Sobolev exponent and allows to see the absorption spectrum
as a point spectrum" - a WEIGHT EXPONENT on L2_delta(X) controlling
growth ||W(g)|| = O(log|g|)^{delta/2}. Our delta (1345 s1): distance
from the critical line in the contest geometry. SAME GREEK LETTER,
DIFFERENT OBJECT - flagged here because conflating them would be a
register-vs-text error of the 1352 species.

The transferable part is the ELIMINATION MECHANISM (section VII-VIII):
he removes the weight-singularity by MOVING THE CUTOFF INSIDE THE
PAIR: the object is never U(h) alone (not trace-class) but
Q_Lambda U(h) with Q_Lambda a two-sided Fourier-annihilating
projection, and the leftover bulk is exactly one scalar term
2 h(1) log' Lambda + o(1). That is structurally OUR L4 Fork-B
requirement (1340: "the counterterm must live INSIDE the pair"; 1211:
any bounded moving response is cofinally unbounded) expressed in
adelic coordinates: his B_Lambda is our windowed carrier C_n, his
log' Lambda bulk is our Re Tr(windowedBoundaryDetector_n) (1224's
identification), his "projection onto span of {f, f-hat both vanish
beyond Lambda}" is the adelic twin of the double-localization spaces
our G8/Gram machinery manipulates. Where the dictionary STOPS: his
framework needs the trace formula (16) itself as the conjecture whose
validity would give positivity; he never supplies a positivity
certificate for any fixed h-class - so migrating our corridor into
adelic coordinates relocates the wall (from CompactLogTest windows to
C_k test functions) without shortening it.

## 4. B-blueprint v1 (charter s3 deliverable; the object to invent, stated once, honestly)

```text
+---------------------------------------------------------------------+
| B-TARGET (the adelic twin of our gate): produce, for the committed  |
| log-lattice test class, the analogue of Connes' (16) as an          |
| ESTIMATE rather than a formula: a cutoff family Q_n with (i)        |
| two-sided annihilation inside the pair (Fork-B geometry, committed  |
| 1211 obstruction forces it), (ii) bulk = one scalar log-term with   |
| coefficient sign-known, (iii) the remainder o(1) dominated BELOW by |
| nothing - i.e. positivity of the remainder-limit on the vanishing   |
| hyperplane. This is literally the gate (0 <= qw g) relabeled:       |
| (i)+(ii) we have in machine-checked form (1224 ledger + L1 brick    |
| 1363), (iii) IS the wall. Blueprint verdict: the adelic dictionary  |
| supplies COORDINATES, not FORCE. Distance added by W0: zero;        |
| clarity added: the wall is the same single sentence in two          |
| languages.                                                          |
+---------------------------------------------------------------------+
```

Mapping table (charter W0.1/W0.2/W0.3, now answerable):

    his object                      our committed twin              status
    C_k test h, h(1)=0              vanishing class, d767a1d        mapped
    Delta (Weil distribution)       qw g                            mapped (1343)
    Q_Lambda / B_Lambda             windowed C_n + G8 cutoffs       partial (no f-hat side)
    (16) spectral trace identity    L4 Fork-B convergence           OPEN both worlds
    2 h(1) log'Lambda bulk          detector bulk, 1224             identified
    absorption spectrum Sp D        spectralTerm zeros-side         mapped (1359 s2.3)
    noncritical = resonances        offLineSpectralTerm residual    mapped (W3/W4b)
    positivity Delta >= 0           0 <= qw g [THE GATE]            OPEN both worlds
    char-p proof of equivalence     - none (no geometry side)       no lever

W0 REGISTER LINE: recon CLOSED with deliverable B-blueprint v1 above.
No breach, no harvestable lemma; the fourth (fifth with Goldfeld's
remark) independent confirmation that the wall = distributional
positivity, stated now with exact theorem numbers and his own
limitation quote. Task #14 CLOSED. A-route (1363: corridor complete
to the single L2 face) remains the only lane where formal progress was
made this wave; both routes' maps now agree on the wall's identity.

## 5. Next actions

1. Owner decision stands open and is now maximally informed: the two
   live attack lanes are (B) commission the L2a/C6 charter - localized
   frame sampling on the committed kernel, weeks-scale science with no
   located technology (1361 mechanism table + 1364 both certify the
   absence); or (C) 1355-style deep pass on adjacent paper claims.
   Option D (thermometer) and this option (W0) are DONE.
2. If B is chosen: first deliverable = design record making 1353 s5's
   prolate/ceiling arithmetic rigorous at the ONE-window level (L2a),
   with L2b gluing budgeted second (sinc^2 tails, 1346 s4) and L2c
   definitions-side (realize A(I)/N(I) for the committed kernel at
   W = pi/log2) attempted first as the cheapest formal face.
3. Either way the harvest lane keeps the artifacts shipping: records
   1360-1364 + bricks 1343/1356/1363 are the public progress surface;
   the stop word is untouched - gate Lean certificate or nothing.
