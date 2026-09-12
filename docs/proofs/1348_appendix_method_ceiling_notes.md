# 1348 appendix - method-ceiling notes: where 2/3 is born, and the measured moment-floor gap

Working notes (MODEL grade; exploratory reanalysis of the COMMITTED A1
spectrum digits in 1344_a1_results.json; produces NO new probe digits and
binds NO 1348 branch - the branch rule is locked in the 1348 prereg and
waits for its own numbers). Written while batch 1548 runs, as ammunition
for whichever next prereg the A1b outcome selects.

## 1. The Alpoege-Furman ceiling is a MOMENT constant, floor-blind by construction

Chain of constants as read from arXiv:2608.13637v2 (quotes below):

- Objects: G~ = (aL^2)^{-1} sum_rho m_rho v_rho v_rho^T + E, d x d, with
  v_rho = (phihat(gamma_rho - alpha_k))_{k<d} on the sample grid
  alpha_k = T + 2pi k/L, d = N(T,2T) + O(L) (s2.2-2.3). Same species as
  our B-matrix: a finite compression of Weil's form; their dimension
  counts the HEIGHT GRID, ours counts the TEST-NET.
- Zero side (Prop 4.1 + Cor 4.5): tr P + 2 n_+(Q) <= N(I) + O(sqrt(T)logT);
  the factor 2 is on-line/double-counting bookkeeping of off-line pairs.
- Linear algebra (Lemma 3.2): rank P_1 >= 2 tr P_1 - r... - 4 tr Q_- type
  bookkeeping via x^2 >= 2x - 1 summed over eigenvalues - i.e. ONLY tr
  and the HS second moment enter.
- Prime side (Thm 5.7): ||G~||_HS^2 = (R(psi) + o(1)) N, and (Prop 4.2)
  tr G~ = (1 + o(1)) N, with R(psi) the window functional reduced to the
  Montgomery-Vaughan mean value (the 3/4 entry).
- Conclusion (proof of Theorem A, part ii):
  2(s_1 + s_2 + p) >= (3 - R(psi) - o(1)) N.
  For psi_0 = 1_[-1/2,1/2] this gives R = 5/3 and proportion 2/3; the
  Montgomery-Taylor window cos(sqrt2 s) tunes R(psi) to give 0.6725.

The ceiling is therefore literally "3 - R(psi)" - a statement about the
FIRST AND SECOND SPECTRAL MOMENTS of the compression. The only operator-
norm input (Lemma 3.4/Weyl) bounds the ERROR perturbation E (||E|| <<
T^{-1/2}); the floor of the main block is never required. The method
cannot SEE near-zero directions - it averages over them. This is what
"proportion, not ALL" means mechanically.

## 2. What the committed A1 ladder says about the floor, for free

From 1344_a1_results.json eig_spectrum (log-parsed, no rerun):

```text
 m   dim=m-3  lam_min      mean=tr/d    lam_max    mean/lam_min  lam_max/lam_min  dim/participation
 24    21     3.083244e-03 6.075369e-03 6.776815e-03   1.97          2.20            1.0295
 48    45     1.559255e-03 3.951436e-03 4.375626e-03   2.53          2.81            1.0290
 96    93     7.833532e-04 2.457697e-03 2.707331e-03   3.14          3.46            1.0253

 exponents (log-log over the three committed tiers):
   mean        ~ m^-0.6528
   lam_min     ~ m^-0.9884          (= A1's alpha, consistent by identity)
   mean/lam_min ~ m^+0.3355         MOMENT-FLOOR GAP exponent (gamma, provisional)
   lam_max/lam_min ~ m^+0.3265
   dim/participation ~ m^+0.0030    ~ FLAT: the spectrum never concentrates
```

Two structural readings (MODEL, species-level):

1. FLAT SPECTRUM: the participation ratio stays ~1.03 of full dimension -
   no outlier low directions, no hidden collapsing subspace. The floor
   separates from the bulk only polynomially and mildly: the worst
   direction is m^{1/3}-type below the mean by m=96. So on this ladder
   the missing ingredient for ALL (vs proportion) is TAIL FLOOR CONTROL,
   and it is a small, quantified, structureless gap - the best possible
   news for a future floor-bound proof, and exactly the quantity their
   moment method is blind to.
2. THE UNIFORM-CONSTANT TARGET TRANSLATES: "lambda_min >= kappa * (tr/d)"
   fails like m^{-0.336} at these tiers; the honest conjectural form the
   next prereg must aim at is
       lambda_min(G_m) >= c_eps * m^{-1/3 - eps} * mean(G_m)
   (or with the exponent replaced by whatever the 192/384 rungs measure -
   see s4 on what 1348 does/doesn't save).

## 3. Rails and non-transfer (restated loudly)

Their G~ acts on the height-sample space (d ~ N(T,2T), fixed T); our Gm
acts on the test-net space (d = m-3, vanishing class, prime-free window).
The moment-vs-floor contrast in s1-s2 is a STATEMENT ABOUT METHOD
FAMILIES, not a theorem connecting the two matrices. No implication
between R(psi_0)=5/3 and gamma=0.3355 is asserted. Nothing here touches
the validity of their Lean-verified result. RH NOT claimed.

## 4. Data-completeness note for the next run (rig, not outcome)

1348 saves eig_low = first 6 eigenvalues only (prereg-locked; the branch
rule needs just lambda_min and does NOT change). To extend the gamma
ladder to the 192/384 tiers, tr is required - so the FULL spectrum dump
becomes a named field of the 1348b/next-probe spec. This is an amendment
to a FUTURE prereg, never to 1348 mid-flight (law 42).
