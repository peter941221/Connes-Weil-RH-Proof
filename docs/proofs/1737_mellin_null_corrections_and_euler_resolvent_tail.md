# 1737 - Mellin-null corrections and the exact Euler resolvent tail

Date: 2026-09-20.

Status: PAPER identities and scoped candidate screening. No new Lean theorem,
numerical experiment, selected-detector positivity, or RH claim. This is a
continuation of the sign incubator in 1736, not a new route or endpoint source.

## 1. Consumer and conventions

The intended consumer remains
`C1HealthyYoshidaSpectralNegativity.healthy_sourceRH_of_right_detector_specific_qw_nonneg`.
Only positivity for the same healthy detector, with its support-dependent
visible prime set, can feed this consumer. The universal examples below screen
proposed algebraic identities; they are not a universal B1 producer campaign.

Use H = L2(R,C), U_a g(x) = g(x-a), and

    L_g(s) = integral exp(s*x)*g(x) dx,
    F_g(y) = integral conj(g(x))*g(x+y) dx.

This Laplace sign is the committed `exponentialWeight_apply` convention in
`Source/CC20YoshidaConvolution.lean`. Translation multiplies L_g(s) by exp(s*a).
The square is the genuine `CompactLogConvolution.convolutionSquare`.

The committed prime coefficient is

    log(p)*p^(-m/2)*(F_g(m*log(p)) + F_g(-m*log(p))).

Evidence: `SelectedSingleCrossing.eulerLogSingleCrossingAtom_eq_finitePrimeTerm_pow`
(under the SelectedWeilSquareOwner namespace) and
`Dev/C1SameOwnerWeil.finitePrimeTermComplex`. Record 1037 already checks the
Euler-log owner and mixed-prime cancellation; that cancellation is not a new
result here. Triple vanishing gives qw = -arch - finitePrimeSum, as in 1736.

## 2. What a Mellin-null correction can and cannot change

For this paragraph ONLY, let H be a finite-dimensional complex Hilbert space,
A a self-adjoint operator, and M:H->C^3 a surjection representing the three
moments. This restriction avoids any unbounded Weil-form domain assumption.
For any B:H->C^3 and g in ker M,

    <g, (A + M*B + B*M)g> = <g, A g>.

Here * denotes the adjoint, not multiplication. Put

    R = M*(MM*)^(-1), Q = RM, P = I-Q.

Then MR=I, Q is the orthogonal projection onto range M*, and P projects onto
ker M. In particular, P(M*B+B*M)P=0. An explicit choice is

    B = R*(-AP - (1/2)*AQ + (1/2)*Q).

Indeed M*R*=Q, so its correction is

    M*B+B*M = -QAP-PAQ-QAQ+Q,
    A+M*B+B*M = PAP+Q.

Consequently some such correction is positive semidefinite if and only if
A restricted to ker M is positive semidefinite. This proves no sign: a
completion algorithm using positivity of PAP as input would be circular.
An independently derived factorization could still be useful. For a single
selected vector the unchanged quadratic value is the relevant statement;
positivity on the entire kernel is an additional, stronger demand.

No bounded operator model of the full archimedean form is asserted here.

## 3. Exact two-prime failure of the naive product square

Let a=log 2, b=log 3, U=U_a, V=U_b and r,s>0. Commuting unitaries give

    E = (I-rU)(I-sV),
    E*E = (1+r^2)(1+s^2)I
          -r(1+s^2)(U+U*) -s(1+r^2)(V+V*)
          +rs(UV+(UV)*+U*V+V*U).

The last line introduces shifts a+b and b-a. They are not prime-power shifts.
They cannot in general be removed by a Mellin-null correction, even allowing
an additional scalar multiple of the identity.

Exact witness: put d=b-a and choose delta>0 with
2*delta < min(d,a-d). Take a nonnegative nonzero smooth bump phi supported
in (-delta,delta), and h=D(D+1/2)(D+1)phi. Integration by parts gives

    L_h(z) = (-z)*(1/2-z)*(1-z)*L_phi(z).

Thus h has the three required zeros and is nonzero: L_phi(2)>0 and the
polynomial at 2 is nonzero. Set g_plus=h+U_d h and g_minus=h-U_d h.
Translation preserves all three zeros. Disjoint supports give

    ||g_plus||^2 = ||g_minus||^2 = 2||h||^2,
    F_g_plus(d) = ||h||^2, F_g_minus(d) = -||h||^2.

Both support diameters are at most d+2*delta<a, so their correlations at
a, b and a+b vanish. The mixed operator in the last line of E*E therefore
has quadratic values +2*r*s*||h||^2 and -2*r*s*||h||^2. A Mellin-null term
vanishes on both vectors, whereas a scalar diagonal term has the same value
on both. Neither can remove this discrepancy simultaneously.

Scope: this rejects a uniform raw-product-square identity with those allowed
repairs. The witnesses are prime-free; {2,3} is an enlarged candidate set,
NOT their actual visible prime set. No assertion about the selected negative
orbit detector, all coupled factorizations, or RH follows.

## 4. The actual Euler-log owner has a different square identity

For one prime p set a=log p, r=p^(-1/2), U=U_a and R_p=(I-rU)^(-1).
The Neumann series converges in operator norm because 0<r<1. Therefore

    S_p = sum_(m>=1) r^m*(U^m+(U*)^m)
        = (1-r^2)*R_p*R_p - I.

Proof: multiply both sides by (I-rU)* and (I-rU), or sum the two geometric
series. The inverse and its adjoint commute. This is an operator identity
on L2, without a sign assumption or a moment restriction.

For compact g, correlations vanish for sufficiently large m. Thus the full
series has exactly the same quadratic readout as its visible prime powers:

    P_p(g) = log(p)*<g,S_p g>
           = log(p)*((1-1/p)*||R_p g||^2 - ||g||^2).

For any finite prime set S containing every prime with a nonzero visible
prime-power term of g, triple vanishing yields the exact identity

    qw(g) = -arch(F_g) + sum_(p in S) log(p)*||g||^2
            -sum_(p in S) log(p)*(1-1/p)*||R_p g||^2.

It retains the actual arithmetic owner and has no mixed-prime terms, but its
resolvent squares have NEGATIVE coefficients. It is not a positivity proof.
Adding an invisible prime changes nothing: its square and mass terms cancel.
For two primes the expression is simply the sum of these two contributions.

## 5. Exact tail, and why three Mellin zeros do not remove it

Fix one p and compact smooth g. For 0<=t<a define the finite sum

    C_p(t) = sum_(j in Z) r^(-j)*g(t+j*a).

Choose an integer N with N*a strictly above the support of g. The Neumann
series gives, for every n>=N,

    (R_p g)(t+n*a)
      = sum_(k>=0) r^k*g(t+(n-k)*a)
      = r^n*C_p(t).

There are uniformly finitely many nonzero j in C_p. Hence, exactly,

    integral_(N*a)^infinity |R_p g(x)|^2 dx
      = r^(2*N)/(1-r^2) * integral_0^a |C_p(t)|^2 dt.

The inverse vanishes sufficiently far to the left. It is compactly supported
if and only if C_p=0. Smoothness follows from local finiteness of the translate
series. Thus compactness is an exact tail-cancellation condition, not an
automatic consequence of invertibility on L2.

Define the smooth a-periodic weighted periodization

    W_p(t) = exp(t/2)*C_p(t).

For every integer k, direct substitution x=t+j*a gives

    integral_0^a W_p(t)*exp(2*pi*i*k*t/a) dt
      = L_g(1/2 + 2*pi*i*k/a).

Fourier completeness on the interval now proves

    R_p g compact
      <=> L_g(1/2 + 2*pi*i*k/a)=0 for EVERY integer k.

The ordinary moment at 1/2 supplies only k=0. The moments at 0 and 1 are
not the missing nonzero Fourier modes. They do not imply tail cancellation:
choose the D3 bump h from section 3 with support diameter<a. For some t
there is exactly one nonzero summand in C_p(t), so C_p is not identically
zero although all three moments vanish.

The contribution of this right tail to the NEGATIVE square in section 4 is
exactly

    -log(p)*r^(2*N)*integral_0^a |C_p(t)|^2 dt.

This is a concrete boundary cost that a denominator-clearing or reserve
argument must retain. No passage to a compact inverse owner is allowed
without the full periodization condition or an explicit tail treatment.

## 6. Research consequence and remaining obligation

Mellin-null completion alone leaves the restricted sign problem unchanged.
The naive Euler product Gram has an exact mixed-shift obstruction. The
correct Euler-log resolvent has an exact boundary energy instead of a free
positive factorization. These are PAPER calculations, not formal no-go labels.

A subsequent reserve/Bellman candidate can now name its boundary variable:
C_p, or equivalently W_p, rather than assuming a scalar reserve vanishes
because of three moments. To advance B5 it must derive from raw selected-orbit
data an upper bound for the total negative resolvent energy by the remaining
archimedean-plus-mass expression in section 4. That upper bound is OPEN;
restating it as a hypothesis or setting the reserve equal to qw is not progress.

No new route is promoted, and no universal sign claim is made. The identities
above are standard finite-dimensional completion, geometric-series, and
Fourier-periodization arguments; no literature novelty is claimed. No Lean
files or root README changes accompany this record.
