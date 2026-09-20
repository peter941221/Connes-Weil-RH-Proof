# 1738 - Selected-orbit joint symbol and tail sampling

Date: 2026-09-20.

Status: PAPER continuation of 1736/1737. The actual selected root is inserted
into the joint archimedean/arithmetic expression. A quantitative bound for
high harmonics of its Euler-inverse tail is derived from an existing formal
root-tail estimate. No selected sign, new Lean acceptance, or RH is claimed.

## 1. Same-owner source data

Consumer:
`C1HealthyYoshidaSpectralNegativity.healthy_sourceRH_of_right_detector_specific_qw_nonneg`.

The committed owner is, exactly,

    h = (convolutionIterate base n).convolution correction,
    g(x) = exp(x/2)*h(x),
    H(z) = L_h(z) = B(z)^(n+1)*D(z),
    B(z) = L_base(z), D(z) = L_correction(z).

The exponent is n+1, not n. Evidence:

- `Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean`:
  `selectedOwner_sourceTest`, `laplaceAt_halfDensityShift`.
- `Source/CC20YoshidaConvolution.lean`:
  `laplaceAt_convolutionIterate`, `laplaceAt_convolution`.
- `Dev/C1HealthyYoshidaUnscaledOrbit.lean`:
  `exists_fixedWindows_nearbyZero_healthyUnscaledOrbit_selectedOwner_with_raw_targets`,
  including its root-level centered-tail conjunct, not just its square tail.
- `Dev/C1G8R0OrbitGeometry.lean`: `selected_owner_test`, `raw_target_values`,
  `support_bound`, `visible_prime_cutoff`. This package does not retain the
  root-tail conjunct explicitly; the stronger construction theorem above does.

With the (-1,1) base and correction windows, supp(g) lies in (-(n+2),n+2).
Triple vanishing of g gives H(1/2)=H(1)=H(3/2)=0. No Weil sign is used below.

## 2. Put Gamma and primes in the SAME Fourier integral

Use G(t)=integral exp(i*t*x)*g(x) dx, with Plancherel measure dt/(2*pi).
Then G(t)=H(1/2+i*t). Let S be a finite set of primes containing every prime
with a nonzero prime-power correlation of this g. For p in S put

    a_p=log(p), r_p=p^(-1/2), c_j=2*j+1/2,
    K=log(8*pi)+EulerGamma+pi/2,
    A(t)=-K + 2*sum_(j>=0) t^2/(c_j*(c_j^2+t^2)),
    P_p(t)=(1-r_p^2)/(1-2*r_p*cos(a_p*t)+r_p^2)-1,
    m_S(t)=A(t)-sum_(p in S) a_p*P_p(t).

The joint formula is

    qw(g) = (1/(2*pi))*integral_R m_S(t)*|B(1/2+i*t)|^(2*(n+1))
                                      *|D(1/2+i*t)|^2 dt.             (1)

Derivation: record 1736 gives -arch = integral w(y)E_g(y)dy-K||g||^2.
Plancherel gives E_g(y)=(1/(2*pi))*integral 2*(1-cos(t*y))*|G(t)|^2dt.
The nonnegative kernel expansion w(y)=sum_(j>=0)exp(-c_j*y) permits Tonelli;
integrating each term gives t^2/(c_j*(c_j^2+t^2)). The absolutely convergent
geometric series 2*sum_(m>=1)r_p^m*cos(m*a_p*t) is P_p(t). Its integrated
readout equals the finite visible powers because all later correlations vanish.
All remaining integrals converge since g is smooth compact and G is Schwartz;
the series for A is locally uniformly convergent and bounded above by 18*t^2
after adding K, using the second-moment bound in 1736.

This is the exact combined form, not a new positivity result. Earlier record
017 already discusses archimedean Fourier multipliers; no novelty is claimed
for Fourier diagonalization. The present readout fixes the committed owner,
half-density shift, convolution exponent, and Euler-log normalization.

## 3. Test the proposed pointwise cancellation

Set C_S=2*sum_(p in S) a_p*r_p/(1-r_p). Then

    m_S(0)=-K-C_S<0,
    |sum_(p in S) a_p*P_p(t)| <= C_S.

Thus Gamma and primes do not combine into an everywhere nonnegative scalar
symbol. This refutes only that particular sufficient proof strategy, not the
selected integral inequality or B5.

A(t) is continuous and strictly increasing for t>=0, from -K to infinity.
For the last assertion, when c_j<=t its j-th positive summand is >=1/c_j;
the sum of 1/(2*j+1/2) diverges. Choose the unique T_S>0 with A(T_S)=C_S.
Then m_S(t)>=0 for |t|>=T_S. The potentially negative frequencies are in
a bounded interval, and a nonempty negative interval exists around zero.

The moment G(0)=0 does NOT remove that interval. For nonzero compact g,
G is a nonzero entire function and cannot vanish on a real open interval.
Its negative-frequency contribution is therefore strictly positive when
written as a deficit. Define

    N_S = {t:m_S(t)<0},
    deficit(g)=(1/(2*pi))*integral_(N_S) (-m_S(t))*|G(t)|^2 dt,
    credit(g) =(1/(2*pi))*integral_(R\N_S) m_S(t)*|G(t)|^2 dt.

Equation (1) is exactly credit-deficit. Proving credit>=deficit from the raw
orbit construction is OPEN. Pointwise positivity is not required. The actual
prime set and T_S can change when g or n changes; freezing S while increasing
the support would change the target.

## 4. The Euler tail samples a DIFFERENT vertical line

For a fixed p let a=log(p), r=p^(-1/2), and use the tail amplitude of 1737:

    C_p(t)=sum_(j in Z) r^(-j)*g(t+j*a), 0<=t<a,
    W_p(t)=exp(t/2)*C_p(t).

For the actual selected g this becomes

    W_p(t)=sum_(j in Z) exp(t+j*a)*h(t+j*a).

Its Fourier coefficients (with positive exponential and no normalization)
are H(1+2*pi*i*k/a). Parseval therefore gives

    integral_0^a |W_p(t)|^2 dt
      = (1/a)*sum_(k in Z)|H(1+2*pi*i*k/a)|^2.             (2)

Since C_p=exp(-t/2)W_p and exp(-a)=1/p,

    (1/(p*a))*sum |H(1+2*pi*i*k/a)|^2
      <= integral_0^a |C_p(t)|^2 dt
      <= (1/a)*sum |H(1+2*pi*i*k/a)|^2.                  (3)

Choose an integer N with N*a above supp(g). The positive magnitude of the
negative right-tail term in qw is

    cost_p = a*p^(-N)*integral_0^a |C_p(t)|^2 dt.

Hence

    p^(-N-1)*sum |H(1+2*pi*i*k/a)|^2
      <= cost_p <= p^(-N)*sum |H(1+2*pi*i*k/a)|^2.        (4)

The zero k=0 is removed exactly by H(1)=0. Notice the two different lines:

    full joint energy     H(1/2+i*t), continuous t
    inverse-tail energy   H(1+2*pi*i*k/log(p)), integer k.

Identifying them without an analytic estimate would be an owner-coordinate
error. Equations (2)-(4) do not require any hypothesized sign.

## 5. A quantitative high-harmonic bound from the actual construction

Retain T and epsilon from the stronger construction theorem in section 1.
Its centered root bound, transported back by halfDensityShift, is

    |z-rho|^2*|H(z)| < epsilon

for 0<=Re(z)<=1 and |Im(z)|>=max(T,1,2*|Im(rho)|). Put
L=max(T,1,2*|Im(rho)|). At z=1+i*t with |t|>=L,
|z-rho|>=|t|/2, so |H(1+i*t)|<=4*epsilon/|t|^2.

Choose an integer J>=1 with 2*pi*J/a>=L. Summing both signs of k and using
sum_(k>J) k^(-4) <= integral_J^infinity x^(-4)dx gives

    sum_(|k|>J)|H(1+2*pi*i*k/a)|^2
      <= (32*epsilon^2/3)*(a/(2*pi))^4/J^3.             (5)

Combining (4) and (5) supplies the actual tail estimate

    cost_p <= p^(-N) * (
      sum_(0<|k|<=J)|B(1+2*pi*i*k/a)|^(2*(n+1))
                        *|D(1+2*pi*i*k/a)|^2
      + (32*epsilon^2/3)*(a/(2*pi))^4/J^3 ).            (6)

This bounds the full tail by a finite sample block plus a proved high-mode
remainder. The weighted C_p norm itself is not an orthogonal split into those
blocks; (6) uses its upper bound by the unweighted W_p norm, where Parseval
does give an orthogonal split. This distinction avoids dropping cross terms.

The construction, not the weaker OrbitG8Geometry bundle alone, supplies the
root estimate used in (5). For the pinned epsilon=1 construction, use that
value. Changing epsilon may change correction and n; it is not a free knob
on a fixed detector.

## 6. What this attack accomplished and what it did not

The universal pointwise-cancellation ansatz fails already at t=0. The SAME
selected detector now has a precise continuous-frequency sign balance (1)
and a finite-sample-plus-remainder bound (6) for every inverse right tail.
These are paper identities/estimates, not a new endpoint supplier.

Two genuine remaining estimates are visible: the finite samples on Re(s)=1,
and enough positive weighted energy on Re(s)=1/2 to compensate the negative
part of m_S. Bounding the right tail alone does not bound the entire resolvent
energy, and upper bounds alone do not provide the needed positive credit.

Large primes have smaller first harmonic 2*pi/log(p), so a high-frequency
bound cannot simply be applied to every nonzero k. The finite block grows
with log(p), while the support bound allows primes below exp(2*(n+2)).
Increasing convolution order requires tracking correction, support, and
prime set together. No monotone improvement of the sign has been proved.

## 7. Correction-order audit and exact finite-sample annihilation

Source inspection sharpens the dependency statement above. In
`CC20YoshidaConvolution.exists_nearbyZero_unscaled_targetValues_assembly_of_fixedThreshold`,
the proof first chooses correction and its decay constant C from the finite
nodes, and only THEN chooses n. The base has value one at target nodes, so
the correction target values do not require division by B(z)^(n+1).
For fixed interpolation data the correction is independent of this later
choice of n. This differs from the rescaled full-product interpolation
theorem; those constructions must not be conflated.

For a prescribed finite prime set S0 and prescribed integers J_p, introduce

    Z0 = {1+2*pi*i*k/log(p): p in S0, 0<|k|<=J_p}.

Use Z0 as additional `routeNodes` of the SAME healthy unscaled construction.
For a right-hand off-line source zero the required healthy targets do not
collide with Z0: source-orbit points have real part strictly between zero
and one, the detector target rho+1/2 has real part strictly above one, and
the three fixed real targets have imaginary part zero. Thus every point in
Z0 is outside healthyUnscaledTargetNodes. The raw assembly's correction-zero
equation implies H(z)=0 at each z in Z0, before passing to the square.

This is a PAPER application of the existing interpolation construction, not
a new formal theorem and not a claim about an unchanged previously selected
g. It selects a new candidate g and must retain that g consistently in both
branches of the B5 exit. It cancels the finite block in (6) for the prescribed
primes, leaving only its explicit high-harmonic bound when J_p meets the
threshold there. The base and high-frequency threshold are selected before
routeNodes in the stronger construction theorem, so J_p may be chosen after
that threshold, before the correction is selected.

The dependency is nevertheless not closed for the ACTUAL visible set:

    chosen prime cutoff P and sample zeros
      -> correction and its decay constant C(P)
      -> required convolution order n(P)
      -> support bound n(P)+2
      -> safe visible-prime bound exp(2*(n(P)+2)).

To cover every prime using this particular sufficient cutoff scheme requires
P >= exp(2*(n(P)+2)). No such estimate or fixed point follows from the
existential interpolation theorem. The safe support bound may overestimate
actual visibility, so failure of this sufficient inequality would not alone
refute another visibility proof or B5. Even a successful cutoff closure would
control inverse right tails only, not the interior energy or the sign balance
in (1). This prevents promoting finite-prime annihilation to a sign producer.

## 8. Quantitative cost screen for the finite-zero construction

The source proof of
`exists_convolutionIterate_convolution_distance_bound_lt` uses the sufficient
certificate

    2^(-n) < epsilon / ((6*pi)^2*(C+1)).                 (7)

This is an actual source-level sufficient condition, not a necessary
condition for decay of the true product. Combining this SAME certificate
with the safe support cutoff P>=exp(2*(n+2)) requires an integer n satisfying

    log(((6*pi)^2*(C(P)+1))/epsilon)/log(2) < n
      <= log(P)/2 - 2.                                 (8)

In particular a necessary condition for these two sufficient certificates
to be simultaneously usable is

    C(P)+1 < epsilon*P^(log(2)/2)/(4*(6*pi)^2).          (9)

The integer condition (8), not just (9), is required. Existential finite
interpolation supplies no estimate of this strength. Failure of (9) would
reject this particular certificate combination, not the actual detector or
all possible sharper product estimates.

There is also a direct cost lower bound for the interpolation itself. Let
c be the smooth correction supported in (-1,1), D(z)=L_c(z), and D(rho)=1,
as supplied by the raw target construction. Choose m distinct prescribed
zeros z_1,...,z_m, all with real part one. Put

    R0=max_j |rho-z_j|.

Complex divided differences, or the simplex integral formula obtained by
iterating the fundamental theorem of calculus along complex segments, give

    D[rho,z_1,...,z_m] = 1/product_j(rho-z_j),
    |D[rho,z_1,...,z_m]| <= sup_convex_hull |D^(m)|/m!.

All real parts in that convex hull lie in [0,1]. Differentiating the compact
Laplace integral gives |D^(m)(z)|<=e*||c||_1, since |x|<=1. Therefore

    ||c||_1 >= m!/(e*product_j|rho-z_j|)
             >= m!/(e*R0^m).                           (10)

For example, use only z_p=1+2*pi*i/log(p), one per prescribed prime p<=P.
They are distinct, none equals rho, and all lie within the fixed radius
R0=|rho-1|+2*pi/log(2). Thus m is the number of those prescribed primes;
the lower bound is unbounded as more primes are included, without needing
any prime-number asymptotic. This disproves a uniform L1-cost assumption
for this growing-node interpolation scheme.

Equation (10) alone is not a lower bound for the strip quadratic constant
C(P) in (7). A separate bridge is essential; section 9 supplies it. Neither
the interpolation bound nor that bridge controls the interior sign balance.

## 9. Close the norm bridge and screen large-cutoff exact annihilation

Let c be the SAME correction, supported in (-1,1), and assume its committed
strip bound with constant C. On the line Re(s)=0 this says

    |D(i*t)| <= 4*pi^2*C/t^2, t!=0.

Write M=||c||_2^2. Cauchy-Schwarz on its support also gives
|D(i*t)|^2<=||c||_1^2<=2*M. Split Plancherel at b=pi/4:

    M = (1/(2*pi))*integral |D(i*t)|^2 dt
      <= (2*b/pi)*M + (16*pi^3/(3*b^3))*C^2
       = M/2 + (1024/3)*C^2.

Both tails were included: integral_(|t|>b) t^(-4)dt=2/(3*b^3).
Thus M<=2048*C^2/3 and

    ||c||_1 <= (64/sqrt(3))*C,
    C >= (sqrt(3)/64)*||c||_1.                         (11)

This proves the previously missing bridge for the exact strip normalization
used in the source theorem. Combining (10) and (11), if all first harmonics
of primes up to P are inserted as zeros, then

    C(P) >= sqrt(3)*m!/(64*e*R0^m), m=pi(P),
    R0=|rho-1|+2*pi/log(2).                            (12)

Fix rho and epsilon. Bertrand's postulate implies p_(m+1)<=2^(m+1), where
p_j denotes the j-th prime and p_1=2. Hence P<p_(m+1)<=2^(m+1).
No prime-number theorem or RH estimate is used. Source for this standard
prime-existence theorem: Mathlib/NumberTheory/Bertrand.lean.

The necessary certificate upper bound (9) is consequently at most

    epsilon*exp(((log(2))^2/2)*(m+1))/(4*(6*pi)^2).

The factorial lower bound (12) eventually exceeds this exponential upper
bound: for fixed R0, m!/R0^m dominates every fixed exponential in m.
For example m! >= (m/2)^(m/2) for m>=2 already proves the comparison.
Therefore, for every FIXED hypothetical rho and FIXED epsilon, there is a
finite cutoff beyond which (8) has no solution under this exact-zero scheme.

This is a PAPER asymptotic obstruction to the conjunction of:

1. fixed correction support (-1,1), D(rho)=1;
2. exact first-harmonic zeros for EVERY prime up to the proposed cutoff P;
3. the specific uniform 1/2-contraction certificate (7);
4. coverage using the safe bound P>=exp(2*(n+2)).

It does NOT exclude a successful smaller cutoff, sparse zero selection,
approximate suppression, a sharper product-decay argument, a sharper actual
visibility bound, or a different correction window. It is not a no-go for
B5, and does not assert the actual product cannot decay. Varying epsilon
with P is outside the fixed-epsilon conclusion and must also preserve the
detector's spectral-tail budget.

Research consequence: indiscriminately adding exact lattice zeros and then
raising the cutoff cannot be treated as a convergent repair algorithm. The
next candidate must retain weighted sampling energy or a coupled interior
estimate instead of assuming exact cancellation at all those nodes is cheap.

## 10. Tail-location audit: small exterior energy is not a sign mechanism

Fix g and p, and write v=R_p g. The arbitrary integer N in the tail
decomposition can be increased without changing g, v, or qw. Define

    I_p(N)=a*(1-1/p)*integral_(-infinity)^(N*a) |v(x)|^2 dx,
    T_p(N)=a*(1-1/p)*integral_(N*a)^infinity |v(x)|^2 dx.

Then I_p(N)+T_p(N)=a*(1-1/p)*||v||^2 for every N. Once N*a is beyond
supp(g), the exact tail identity gives

    T_p(N+1)=T_p(N)/p,
    I_p(N+1)-I_p(N)=(1-1/p)*T_p(N).

For the fixed finite visible-prime set, all exterior costs can therefore be
made arbitrarily small by increasing their N, while the total negative
resolvent energy and qw remain unchanged. Exact annihilation of C_p may be
useful if compact inverse ownership is required, but it is not necessary
merely for small exterior error. Tail location is an accounting choice.

This corrects research prioritization rather than any formula above: sections
7-9 screen a particular exact-cancellation ansatz, but do not establish that
its interpolation problem is a necessary obstacle to B5. The next sign
candidate must control the complete interior-plus-exterior expression in (1).
An exterior estimate alone cannot be counted as movement of the sign bound.

### Narrow literature cross-check (2026-09-20)

Search query: `Weil quadratic form positivity compact support lower eigenvalue
Riemann hypothesis` (arXiv search). Close-read sources:

- https://arxiv.org/html/2608.24827 : the abstract states certified positivity
  on [-0.8,0.8]; Theorem 1.4 discusses the pointwise-envelope certificate
  barrier. This is fixed-window evidence, not a certificate for the unbounded
  support of the selected orbit. Map 004 already records this source.
- https://arxiv.org/html/2606.09096 : Theorem 1.3 states continuity of the
  lowest eigenvalue as the support window varies. The following discussion
  identifies nondegeneracy for every window as RH-equivalent. Continuity does
  not prevent an eigenvalue from crossing zero. The source is already screened
  in proof record 125 and map 011; it is not a new sign supplier.

These are literature claims checked at the stated URLs, not independently
verified proofs or imported Lean results. This narrow search found no new
supplier among the two examined sources; it makes no exhaustive literature
claim and opens no universal B1 campaign.

No numerical experiments, Lean edits, or root README changes were made.
