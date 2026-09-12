# 1371 - HBridge P0: sampling residual, anchor cost, and discrepancy estimates

Date: 2026-09-12. Owner instruction: execute the proposed paper analysis and
update map 008. Class: PAPER DERIVATION / PROJECT CANDIDATE, with separately
identified FORMAL SOURCE READBACK. No Lean certification or numerical run.

Consumer: D1/D4/D5/D6 of [map 008](../map/008_l2_hbridge_bone_attack_plan.md),
then D8/D9 for the SAME selected healthy `CompactLogTest` and its finite
visible-prime owner. CB-HB1 stays NEEDS-ANALYSIS; no D2/D3 zero-data producer
or D8 sign is supplied. This is the paper-only P0 continuation of record
1370, not a new universal positivity or frozen finite-positive-owner campaign.
All new estimates below have proofs, but their evidence level is PAPER, not
FORMAL. They are necessary constraints and candidate inputs, not RH progress
certificates by themselves.

## 1. Exact owner and notation

Fix ONE hypothetical right-hand source zero `rho`, and retain the raw
construction witnesses `base, correction, n` for its selected healthy test
`g = (selectedOwner base correction n).sourceTest`. This retention matters:
`HealthyYoshidaDetectorData` alone does not expose the normalized values used
below. The construction theorem in
[C1HealthyYoshidaSpectralNegativity](../../ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean),
`exists_healthyDetectorData_of_fixedWindows_nearbyZero_spectral_neg`, actually
constructs these witnesses internally. Re-exporting their conjunction with
support and the same square/tail owner is still a D0 Lean API obligation;
independent existential witnesses must never be mixed.

Write `rho = 1/2 + d + i*t0`, with `d > 0`. Choose a proved support radius
`R > 0` for this SAME g, so `support(g) subset [-R,R]`. The pinned construction
uses `R = n+2`; square support is within `[-2R,2R]`, and the visible
prime-power cutoff is `q < exp(2R)`. See
[C1P2DefectControl](../../ConnesWeilRH/Dev/C1P2DefectControl.lean),
`exists_healthyDetectorData_with_pinned_support`.
R here is a physical log-support radius, not the interpolation closed-ball
radius, the ordinate-window width W, or a spectral height cutoff.

Use the actual positive-character transform

```text
G(z) = integral_[-R,R] g(x) exp(z*x) dx.
```

By [C1HealthyTestSpace](../../ConnesWeilRH/Dev/C1HealthyTestSpace.lean),
`healthyMellinReadoff`, and
[CC20RHExit](../../ConnesWeilRH/Source/CC20RHExit.lean), the healthy triple is
`G(0) = G(1/2) = G(1) = 0`. Do not replace these by a symmetric triple.
The raw construction uses its shifted nodes before `sourceTest` is formed.

The proof of `selectedOwner_horizontalDefect_anchor_eq_two_mul_multiplicity`
in [C1P2SpectralHorizontalDefect](../../ConnesWeilRH/Dev/C1P2SpectralHorizontalDefect.lean)
reads back, under the actual raw target equations,

```text
G(d+i*t0) = 1,  G(-d+i*t0) = -1.
pairedMass(g,rho) = m(rho),  horizontalDefect(g,rho) = 2*m(rho).
```

These are FORMAL SOURCE READBACK, not newly built declarations. All following
applications to the normalized detector retain these explicit hypotheses.

## 2. P0-R1: exact visible/invisible sampling decomposition

Let H be complex `L2([-R,R], dx)` with inner product linear in the SECOND
argument, and let

```text
k_z(x) = exp(conj(z)*x),           G(z) = <k_z,g>,
H_V = {h in H : <k_c,h> = 0 for c in {0,1/2,1}},
Q = orthogonal projection H -> H_V,  u_z = Q k_z.
```

All evaluations are bounded on H by Cauchy--Schwarz; H_V is therefore closed.
For a finite weighted list of real sample ordinates, with `m_j > 0`, define

```text
S : H_V -> C^J,        (S h)_j = sqrt(m_j) <u_(i*gamma_j),h>,
E = range(S*) = span{u_(i*gamma_j)},
P = orthogonal projection H_V -> E.
```

**Paper proof.** The finite-dimensional E is closed and
`E^perp = kernel(S)`: being orthogonal to all sample representers is exactly
vanishing of every sampled coordinate. Thus `S(I-P)=0`, `Sg=S(Pg)`, and
`Sg=0 iff Pg=0`. No sampling density hypothesis is needed for these identities.

If `E != {0}`, define the genuine finite-range lower constant

```text
lambda = min { ||S p||^2 : p in E, ||p||=1 } > 0.
```

The unit sphere is compact and S is injective on E, proving strict positivity.
This is existence of a constant on a finite range, NOT a quantitative lower
bound uniform over zero configurations. The zero-range case is handled
separately with P=0 and no division by lambda. Repeated nodes do not increase
rank; positive weights may be combined at identical ordinates.

Orthogonal decomposition and Cauchy--Schwarz now give, for every `g in H_V`,

```text
G(z) = <P u_z,Pg> + <(I-P)u_z,(I-P)g>,
|G(z)| <= ||P u_z||/sqrt(lambda) * ||Sg||
           + ||(I-P)u_z|| * ||(I-P)g||.                 (R1)
```

The second term cannot be omitted. R1 is an estimate of the original test's
transform. Pg and (I-P)g are auxiliary L2 vectors; neither is asserted to be
smooth after zero extension or supplied to `qw` as a `CompactLogTest`.
Any later split of `qw` across those vectors needs its own form domain and
continuity theorem; small L2 error alone is not such a theorem.

### Specialization to the construction's killed prefix

Take the sample list to consist ONLY of on-line source zeros within the
construction's controlled finite prefix. The closed-prefix theorem
`selectedOwner_laplaceAt_convolutionSquare_eq_zero_of_source_mem_closedBall_not_mem_orbit`
in [C1HealthyYoshidaClosedPrefix](../../ConnesWeilRH/Dev/C1HealthyYoshidaClosedPrefix.lean)
and the square law imply `|G(i*gamma_j)|^2=0`: an on-line zero is outside the
off-line anchor orbit. The actual square-zero version used by the negativity
construction gives the same conclusion, treating fixed target nodes via their
zero raw values as in that source's prefix proof. Hence `Sg=0` and `Pg=0`.
This does not assert that samples outside the controlled prefix vanish.

Put `v = u_(d+i*t0) - u_(-d+i*t0)` and `w=(I-P)v`. Then

```text
<w,g> = 2,    4 <= ||w||^2 ||g||^2.                    (R2)
```

In particular w is nonzero, and the entire anchor difference is in the
unobserved direction. A finite-range certificate with excellent lambda says
nothing about its size. R2 is the matched detector falsifier for any claim
that the complement is negligible merely because finite samples are numerous.

### Sharper finite Gram target, without a positivity claim

Let `w_+ = (I-P)u_(d+i*t0)`, `w_- = (I-P)u_(-d+i*t0)` and
`K_ab = <w_a,w_b>`. For a vector h in kernel(S) inside H_V, the two anchor
constraints are `Lh=y`, where `y=(1,-1)`. Then `L L*=K`. Feasibility implies
`y in range(K)`; using its Moore--Penrose inverse,

```text
minimum ||h||^2 subject to Lh=y = y* K^dagger y.       (R3)
```

Indeed `h_min=L* K^dagger y` has Lh_min=y, squared norm `y* K^dagger y`, and
is orthogonal to kernel(L); every other solution differs by a kernel vector.
This is a relaxation to L2, giving a necessary norm bound for smooth detectors.
It is not a construction of a new smooth detector or a same-owner positive
finite quadratic form for `qw`. This Gram matrix measures interpolation cost.

## 3. P0-R2: sharp two-anchor support/normalization cost

For `R,d > 0` set

```text
a_R(d) = sinh(2*d*R)/d,
B_R(d) = 2*sinh(2*d*R)/d - 4*R > 0.
```

The full-space difference representer is
`k_(d+i*t0)-k_(-d+i*t0)=2*sinh(d*x)*exp(-i*t0*x)`. Direct integration gives

```text
||k_(d+i*t0)-k_(-d+i*t0)||^2
  = 4 integral_[-R,R] sinh(d*x)^2 dx = B_R(d).
```

Thus every normalized two-anchor test, and in particular the retained
construction owner, satisfies

```text
||g||_2^2 >= 4/B_R(d).                               (R4)
```

Proof: apply Cauchy--Schwarz to its difference value 2. Projection is
contractive, so R2 can strengthen R4. The bound R4 is sharp in the unrestricted
L2 two-anchor problem: its Gram matrix is

```text
[[a_R(d), 2R], [2R, a_R(d)]],
g_min = (k_(d+i*t0)-k_(-d+i*t0))/(a_R(d)-2R).
```

Both prescribed evaluations hold, and its squared norm is
`2/(a_R(d)-2R)=4/B_R(d)`. This minimizer need not satisfy the healthy triple
or be smooth after zero extension; it is only the sharp lower relaxation.

For fixed R and d tending to zero, Taylor expansion yields

```text
B_R(d) = (8/3)*d^2*R^3 + O(d^4*R^5),
4/B_R(d) ~ 3/(2*d^2*R^3).                            (R5)
```

The exact formula R4, not an unquantified asymptotic, is the budget input.
The simple envelope from the initial discussion also follows:
`|G(d+it)-G(-d+it)| <= 2*sqrt(2R)*sinh(dR)*||g||_2`.
In particular an estimate `horizontalDefect <= (m/2)*B_R(d)*||g||^2`
cannot automatically be made small as d decreases: at the anchor its actual
left side is exactly 2m, and R4 forces the envelope to be at least 2m.
R may itself grow with rho and the orbit exponent n; no `R=O(log T)` has
been proved here. Control of `d log T` alone does not control this mechanism.

## 4. P0-R3: the signed continuous identity and its derivatives

Define for real d,t

```text
f_d(t) = Re(G(d+it) conj(G(-d+it))).
```

Elementary complex algebra gives
`f_d = |(G_+ + G_-)/2|^2 - |(G_+ - G_-)/2|^2`.
These are respectively Fourier transforms of `cosh(d*x)g(x)` and
`sinh(d*x)g(x)`. Plancherel in the positive-character/angular-frequency
convention gives the PAPER identity

```text
integral_R f_d(t) dt = 2*pi*||g||_2^2.                (R6)
```

Proof: both weighted tests are L1 and L2, since their support is bounded.
Their transforms are L2 and their product is L1 by Cauchy--Schwarz.
The cross Plancherel identity gives
`integral G_+ conj(G_-) = 2*pi*integral e^(dx)g conj(e^(-dx)g)`;
the weights cancel pointwise, giving R6. This also justifies taking real
parts through the integral. It holds for complex g without real-test symmetry.

Differentiating in t corresponds to multiplication by i*x before transform.
Using the product rule, Cauchy--Schwarz and Plancherel gives

```text
integral_R |f_d'(t)| dt
 <= 4*pi*R*||exp(d*x)g||_2*||exp(-d*x)g||_2
 <= 4*pi*R*exp(2*abs(d)*R)*||g||_2^2.                (R7)
```

All derivatives are classical: bounded support makes x*g integrable and
justifies differentiation under the transform. R6 is over the whole real
axis at ONE fixed d. It is neither a finite-window sign theorem nor a
discrete zeta-sampling theorem. No factor 4 quartet shortcut is used.

## 5. P0-R4: a deterministic sampling estimate with an honest remainder

Let `I=[a,b)`, a<b, and `mu=sum_j m_j delta_(t_j)` with t_j in I, m_j>0.
Let M be its total mass, assume M>0, and set

```text
eta = M/(b-a),
D(t) = mu([a,t)) - eta*(t-a)     (a <= t <= b),
Delta = sup_[a,b] |D(t)|.
```

Weights include analytic multiplicity. Identical ordinates are combined or
retained with their full summed weight. In particular `D(a)=D(b)=0`.
For any continuously differentiable real f on [a,b],

```text
sum_j m_j f(t_j) - eta*integral_a^b f(t)dt
  = -integral_a^b D(t) f'(t)dt,
|sum_j m_j f(t_j) - eta*integral_a^b f(t)dt|
  <= Delta*integral_a^b |f'(t)|dt.                   (R8)
```

Proof including endpoints: for the signed measure `nu=mu-eta*dt`,
`f(x)=f(b)-integral_x^b f'(t)dt`. Integrate this identity against nu.
The f(b) term vanishes since nu(I)=0. Fubini is legal because nu has finite
total variation and f' is bounded on [a,b]. The remaining inner measure is
nu([a,t]); its discrepancy from nu([a,t)) occurs only at the finitely many
atoms and has zero dt measure, proving R8. If a different reference density
is used, the uncancelled term is `f(b)*nu(I)` and must be retained.

Apply R8 to `f_0(t)=|G(it)|^2`. By R7 at d=0,

```text
sum_j m_j |G(it_j)|^2
 >= eta*integral_I |G(it)|^2 dt - 4*pi*R*Delta*||g||_2^2.
```

For nonzero g let
`theta_I(g)=integral_I |G(it)|^2 dt/(2*pi*||g||_2^2)`, so `0<=theta_I<=1`.
The quantitative, remainder-bearing sampling bound is

```text
||Sg||^2 >= 2*pi*(eta*theta_I(g)-2*R*Delta)*||g||_2^2. (R9)
```

This is valid on the full bounded-support L2 space because its coefficient
need not be positive. For the killed-prefix sampling of section 2, it forces

```text
eta*theta_I(g) <= 2*R*Delta.                         (R10)
```

Thus good discrepancy and large detector concentration cannot both be
asserted for those nodes without a new theorem forcing the B5 contradiction.
If geometry gave `Delta <= delta` and independent detector analysis gave
`theta_I >= theta0 > 0` with `eta*theta0 > 2*R*delta`, R9 would contradict
Sg=0. Neither of those quantitative inputs, nor their compatible constants,
is proved here. R10 quantifies the kernel obstruction instead of ignoring it.
An empty sample set has S=0 and is handled directly; no eta division is used.

R10 is an admission check on the quantitative inputs proposed for D2/D4,
not a supplied A2 premise. Delta is not the uninterpreted A of that schema.
Any changed analytic premise needs its explicit same-detector consumer and
dependency audit before it can replace the existing interface. The approved
plan still targets D8/D9; no alternative exit is promoted by this constraint.

## 6. P0-R5: signed sampling, horizontal bin error, and total-budget boundary

For fixed d, R7/R8 imply

```text
sum_j m_j f_d(t_j)
 >= eta*integral_I f_d(t)dt
       -4*pi*R*Delta*exp(2*abs(d)*R)*||g||_2^2.        (R11)
```

To apply this to actual zeros, their horizontal positions may not be replaced
by a common d without an error. For `0<=d_j,d_*<=Dmax` and
`|d_j-d_*|<=h`, bounded support gives

```text
|G(s)| <= sqrt(2R)*exp(Dmax*R)*||g||_2,
|dG(s)/ds| <= R*sqrt(2R)*exp(Dmax*R)*||g||_2
                                      (|Re s|<=Dmax).
```

Differentiate f_d with respect to d, retaining the minus sign in the second
factor. The two product terms give
`|partial_d f_d(t)| <= 4*R^2*exp(2*Dmax*R)*||g||_2^2`.
The mean value bound and finite weighted sum therefore give

```text
|sum_j m_j (f_(d_j)(t_j)-f_(d_*)(t_j))|
 <= 4*M*h*R^2*exp(2*Dmax*R)*||g||_2^2.              (R12)
```

R11 and R12 are an explicit cell estimate, with both discrepancy and bin
width charged. In a source-zero cell put `d_j=|Re rho_j-1/2|` and
`t_j=Im rho_j`. Since `f_-d=f_d`, each source zero contributes exactly
`m_j f_(d_j)(t_j)` to the real spectral sum. Count each source zero once;
horizontal partners at the same ordinate contribute their full weights, and
negative ordinates remain separate. No real-g assumption or quartet factor
is needed.

The local reference integral in R11 is signed; R6 does not make it positive.
Writing it as the whole-line value minus an outside-I integral is legitimate
for ONE cell, but introduces that entire signed outside integral. Summing
`2*pi*eta*||g||^2` over infinitely many cells and then subtracting the outside
integrals is NOT justified: the two separated sums need not converge.
Likewise, R12's global-norm bound cannot be summed over infinitely many
zeros with a fixed nonzero h. Height decay or sharper local norms must enter.

The lawful total variant starts with the original fixed smooth g and the
existing absolutely summable spectral family, chooses a genuine partition,
and proves summability of the NEW reference and error terms before summing.
For prospective real sequences c_k,e_k with e_k>=0, one sufficient assembly is

```text
q_k >= c_k-e_k,   Summable(c),   Summable(e),
sum_k c_k >= sum_k e_k.
```

Summability of q_k follows from the existing window split; summing the
inequalities gives `qw(g)>=0` by `qw_window_assembly`. This is PAPER assembly
of the already-formal identity, not a new Lean adapter or an input bundle
allowed to store the desired conclusion. Producing the sequences and their
last inequality remains D6/D8. The per-window option of 008 stays available;
neither option receives an automatic positivity implication from R6.

## 7. Result ledger, falsifiers, and remaining work

| Item | Result of this pass | Evidence / remaining consumer |
|---|---|---|
| Transform, triple, normalized anchor and killed-prefix values | Exact conventions read back | FORMAL SOURCE READBACK; joint D0 export remains unbuilt |
| R1-R3 | Residual sampling identity, kernel specialization, and Gram cost proved | PAPER; quantitative same-detector residual control remains OPEN |
| R4-R5 | Sharp unrestricted two-anchor norm floor derived | PAPER; forbids treating d-smallness as a free small budget |
| R6-R7 | Signed continuous identity and derivative bound derived | PAPER; discrete/variable-width comparison remains necessary |
| R8-R10 | Deterministic discrepancy estimate and kernel/concentration constraint proved | PAPER; actual-zero discrepancy and detector concentration constants remain OPEN |
| R11-R12 | Signed cell estimate and explicit horizontal-bin error derived | PAPER; reference sign and summable global error still OPEN |
| CB-HB1 | NEEDS-ANALYSIS, full P0 not passed | No hA2, hBridge, same-detector positivity, or RH theorem |

Matched paper controls: (i) E=0 and any vector in kernel(S), which make R1
purely residual and require R10; (ii) the exact L2 two-anchor minimizer, which
attains R4; (iii) constant f in R8, whose error is exactly zero by equal mass;
(iv) d=0 and h=0 in R11/R12, recovering the online identity and zero bin error.
These are symbolic checks, not numerical prototypes or CB-HB1 survival claims.

The generic ingredients are Hilbert projection/minimum-norm interpolation,
Cauchy--Schwarz, Plancherel, and integration against a finite signed measure;
no novelty claim is made for them. Prior-art context from the preceding review:
[Bass--Grochenig, Relevant Sampling of Band-limited Functions](https://arxiv.org/abs/1203.0146)
uses concentration and random sampling; it is not an actual-zeta producer.
The new project-specific output is the exact composition with the normalized
orbit's killed prefix and the explicit R,d,Delta,theta,M,h ledger. The
candidate's full prior-art/screen cards remain provisional under map 006.

Next paper target: fix a controlled-prefix interval and the retained raw owner,
derive useful compatible bounds for Delta and theta_I(g) (or for the signed
reference and errors of R11/R12), and identify the independent actual-zeta
input. Do not add another sign socket or assume that the fourth-order
DISCRETE SQUARE tail bounds the CONTINUOUS ROOT energy outside I; that
comparison requires its own theorem. No new computation or Lean campaign is
promoted by these paper results.

Documentation acceptance: exact source names, formulas and endpoint conventions
read back; relative paths and whitespace checked together after the related
map/MEMORY edits. No build or axiom-audit evidence is claimed. Route authority,
RH/C3 status, root README and frozen namespaces are unchanged.
