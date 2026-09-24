# 1957 - Plan B re-audit and the shortest same-owner execution contract

Date: 2026-09-24.

Status: SOURCE AUDIT and PAPER algebra / proposed work order. No new Lean
theorem, numerical experiment, unconditional sign bound, or RH claim.
No binding route change. Subordinate to maps 003 and 103.

## Owner, consumer, assumptions, and stop condition

Owner: `g_n = (selectedOwner base correction n).sourceTest`,
`u_n = fullFunctionalEquationOrbitAnnihilator g_n rho`, and
`h_n = annihilatorDetectorSpanVector u_n g_n lambda_n`.
Keep the support-derived finite prime-power owner of this span throughout.

Consumer: the actual span parabola and finite-prefix transport in
`C1FourPointSpanGateCertificate`, the bound in `C1FourPointHighShellTail`,
then `witness_of_gate_and_tail` and the existing SourceRH / Mathlib exit.

Assumptions: hypothetical right off-line `rho`; base interpolation and strip
contraction; a fixed finite spectral prefix; correction interpolation; the
all-index construction's scalar admissibility conditions. These must be
instantiated, not hidden in a new certificate structure.

Remove: the actual-owner determinant sign and its joint tail margin.
Failure: a checked obstruction for the specified owner/parameter class, or
failure to bound the complete moment remainder below the proposed margin.
A failure of one estimate is not a no-go for RH or for all coarse methods.

## Corrections to records 1953-1956 and the original map-105 proposal

1. Record 1955 proves a two-point difference bound under
   `190 <= gamma^2-delta^2`. It does not prove a cluster-mean gap, a uniform
   positive-region variance bound, or `hdom`; its transfer theorem assumes
   both `hgap_le` and `hdom`. The height condition also remains an input.
2. `5700^2 = 32490000`; the quoted ratio to `1980000` is about 16.41, not 30.
   With these bounds the sufficient mean-gap-only test needs
   `r = Cminus/Cplus > 1980000/(32490000+1980000)`, about 0.05744.
   The proposed bound `r >= 0.05` does not establish that test.
3. The original map-105 displayed ANOVA expression is **minus** the
   determinant. The correct identity is
   `det = -Cplus*Cminus*gap^2
          +(Cplus-Cminus)*(Cplus*varPlus-Cminus*varMinus)`.
4. A negative n=2 cosine term does not prove negativity of the full kernel.
   Local kernel signs do not provide quantitative selected-owner Fourier
   mass bounds. Two intervals do not exhaust the three gate moments.
5. `exists_pos_lambda_quadratic_neg_of_macro_atom_bounds` is a finite-sum
   theorem with internal oscillation, cross-separation, mass, and domination
   assumptions. An interval-to-moment bridge with internal variances and
   complement contributions is required to apply it to actual integrals.
6. Record 1953 certifies arithmetic on four literal rational tuples. The
   tuple structure contains no certified relation to a `CompactLogTest` or
   its integrals. This is not yet an actual-owner determinant certificate.
7. `riemannHypothesis_of_gate_determinant_neg` takes an existential gate AND
   `qw(span) < 0` producer. Its name does not remove the spectral-tail premise.

Existing evidence already favors keeping the negative variance. In the
first case of `results/1951_macro_atom_bounds.json`, the full sign-split mean
gap is about 1544, not 5700, and `varMinus` is about 100720000. These are
floating-point observations on the rig: the script calls `rig.bump(c)`;
it does not construct the all-index interpolated selected owner. They may
motivate an estimate but cannot certify that owner.

## The shortest joint acceptance test

Use the actual gate values

```text
C_n = ICgate(g_n.square) > 0
b_n = (ICgate(u_n.involution.convolution g_n)
       + ICgate(g_n.involution.convolution u_n))/2
D_n = ICgate(u_n.square)
lambda_n = b_n/C_n
H = 3 + norm(rho)
```

For each hypothetical rho, it suffices to construct one admissible `n` with

```text
b_n > 0
D_n*C_n - b_n^2 < 0
A_rho * 4^(-n) * (1 + H^4/lambda_n)^2 < xiMultiplicity(rho),
```

where, for the fixed shell cutoff `s`,

```text
A_rho = 4 * spectralMultiplicityConstant * (3/4)^s
        * H^4 * (2*pi)^12 * (C4*C2)^2.
```

The last line is exactly the existing sufficient tail budget divided by
`lambda_n^2`; it is not an additional empirical sign principle. Choose
`epsilon^2` strictly between the tail bound and the prefix allowance and
apply the existing assembly. Retain the prefix, height, vanishing, and
all-index admissibility premises in this application.

Quantifier order: fix rho; choose base and its contraction threshold; choose
the shell prefix covering that threshold and rho; choose correction for that
prefix; obtain fixed decay constants; select `n` and its vertex together.
Do not enlarge the shell prefix after fixing correction without proving the
new interpolation conditions.

There is no requirement that all rho share constants or a common n.
There is also no requirement that every n work. A useful sufficient analytic
target is: for a fixed rho and this fixed base/correction, there is
`ell_rho > 0` and arbitrarily large admissible n with
`det_n < 0` and `lambda_n >= ell_rho`.
Then

```text
(1 + H^4/lambda_n)^2 <= (1 + H^4/ell_rho)^2
```

and the geometric tail closes along those indices. In particular, an upper
bound on lambda is unnecessary for this relative-tail argument. The lower
bound and the arbitrarily-large-index sign assertion are OPEN, not supplied
by the current all-index construction. A direct one-index joint certificate
would be enough and should be preferred if available.

## Revised coarse method: complete centered moments

For an arbitrary real centering value `a_n`, define algebraically

```text
U_n = b_n - a_n*C_n
V_n = D_n - 2*a_n*b_n + a_n^2*C_n.
det_n = C_n*V_n - U_n^2
lambda_n = a_n + U_n/C_n.
```

These identities preserve the exact owner and exact vertex. The centering
value is not a replacement span coefficient. Under a proved same-owner
continuous kernel readback, they become the three full-line moments of
`1`, `P-a_n`, and `(P-a_n)^2` against `K_n*W_n`.
Record 1919 is a paper/probe source for that representation; the finite
ANOVA Lean identity alone is not its continuous formal proof. Do not assume
the selected complex test has even Fourier energy without a proof.

Partition the actual integrals into finitely many intervals and a complement.
Retain complete signed interval moments or certified enclosures, including
negative-region spread. On uncertain-sign cells use valid signed enclosures;
do not declare an entire cell positive/negative from one prime term. There
is no need to locate every zero of K exactly. The complement must be bounded
for all three weighted integrands, especially the degree-eight one.

For central values `(C0,U0,V0)` with absolute errors `(eC,eU,eV)`, a valid
determinant error bound is

```text
E = abs(V0)*eC + abs(C0)*eV + eC*eV + 2*abs(U0)*eU + eU^2.
```

Thus `C0-eC > 0` and `C0*V0-U0^2+E < 0` certify the determinant.
Also certify `a_n*C_n+U_n >= ell_rho*C_n` for the coefficient lower bound,
or certify the joint relative-tail inequality directly. This is a proposed
error budget, not an available analytic producer; coarse enclosures may fail
when the true margin is thin. No precision claim follows from the 5700 bound.

## Execution priority

1. Identify a quantitative base/correction construction inside the existing
   all-index class. Existing existential interpolation alone supplies no
   interval energy or moment constants. Any chosen representative must prove
   the same interpolation/support contract; a bump surrogate is insufficient.
2. Screen that actual family against the complete centered determinant and
   relative-tail budget. Any probe must name the parameter class, finite
   prime owner, decision threshold, and reproducible provenance. This audit
   performs no new probe.
3. Prove one decisive actual-owner signed bound, retaining negative variance
   and the complement. Formalize continuous readback only as needed by that
   bound. A generic bridge by itself is infrastructure, not core progress.
4. Extend to each hypothetical rho with the correct existential quantifiers;
   then consume the existing gate/prefix/tail assembly and run the axiom and
   root build ladder. Do not add another conditional RH exit.

The revised coarse method remains a candidate within map 103. Its missing
ingredient is quantitative control of the actual interpolated owner, not
another algebraic certificate. No claim of original mathematics or of a
known complete path to RH is made by this audit.
