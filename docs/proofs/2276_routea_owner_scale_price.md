# 2276 - Physical owner scale audit and corrected-owner analytic prices

Date: 2026-09-30

Result: the legacy strip screen is NOT the physical owner of the 2249
transform. The exact stored coefficients agree with the 2267 replay
coefficients component by component; the mismatch is the width convention.
A Lean support witness proves the two family sums differ, and directed
MPFR arithmetic prices valid elementary bounds for the correctly scaled
functions. Those majorants miss the frozen strip and gap budgets by
approximately 2.006e6 and 1.005e34 respectively. These are failures of the
absolute-family method, not lower bounds on the true norms or ideal gap.

The generic producer theorem remains valid. Its hstrip and hgap premises
are not discharged by these artifacts; no new producer supplier, detector
readback, producer GO or RH proof is claimed.

## 1. The source-level change of variable

An owner is a particular function, not just its coefficient vector. Equal
coefficients applied to different profiles need not define the same function.
The following source fragment fixes the transform convention:

    V[j, :] = a * r59.phi_laplace(a, k, a * (s + 1j * th), XW=XW[j])

It appears in fourpoint_owner_completion_1980.py, family_values. Here
phi_laplace integrates the profile

  phi_a(x) = exp(-30/(1-(x/a)^2)) for |x| < a, and zero otherwise.

The ideal integral underlying that rule is

  a * integral phi_a(x) * exp(a*(s+i*theta)*x) dx.

Set y = a*x, with a > 0. Then dy = a*dx, so the outside factor a cancels
against the Jacobian, the factor converting an integral's coordinate scale:

  integral phi_a(y/a) * exp((s+i*theta)*y) dy
    = integral phi_(a^2)(y) * exp((s+i*theta)*y) dy.

The physical profile is therefore phi_(a^2)(y)*exp(i*theta*y), with no
remaining outside amplitude a. The legacy 2197 physical screen instead
uses u = x/a and exp(i*theta*x). The 2234 directed worker also divides
physical x by a. Both evaluate phi_a, not phi_(a^2).

For a = 2, the integral's physical support reaches 4, while the legacy
screen stops at 2. Matching coefficient hashes cannot repair this difference.
The same a-scaled phase is explicit in 2249 laplace_rows. This is an exact
change-of-variable mismatch, not a grid-rounding diagnosis.

## 2. Actual stored-data support witness and Lean verification

The 30 captured widths are encoded as exact rational literals in
C1RouteAOwnerScaleAudit.lean. Family index 4 is the unique largest width:

  a_4 = 1441151880758559/562949953421312,
  a_4^2 = 2076918743413931858457251756481/316912650057057350374175801344.

Every a_j < 6. Every a_j^2 <= 6 except j = 4, and a_4^2 > 6.
Consequently the legacy base and correction vanish at physical y = 6.
At that point the corrected sum has exactly one surviving term:

  coefficient_4 * phi_(a_4^2)(6) * exp(i*theta_4*6).

The bump is strictly positive and the phase is nonzero. The actual stored
base and correction coefficients at index 4 have nonzero real parts:

  base_4.re = -2679001875721701/262144,
  corr_4.re = -6001732121601347/32.

The Lean theorem physical_owner_ne proves that every coefficient vector
with nonzero entry 4 yields a corrected family sum unequal to the legacy
family sum. The stored_base_owner_ne and stored_corr_owner_ne specializations
use the exact stored entry-4 values, with the other 29 coefficients arbitrary.
Their hypotheses only identify that input entry; no sign or tail conclusion
is supplied as an input. The regression suite binds every width and both
entry-4 complex literals to the original capture.

This is a formal support obstruction for the displayed functions. It does
not yet build them as CompactLogTest structures, prove ideal interpolation,
or identify them with the selected detector. The coordinate substitution
above is established in this report, not formalized as a Lean integral theorem.

The directed numerical witness, enclosing magnitudes rather than floating
phase evaluations, gives:

```text
function       legacy value at 6     corrected magnitude at 6
base           exactly 0            [3.097400811079255e-71, 3.0974008110813695e-71]
correction     exactly 0            [5.8898113007932725e-67, 5.889811300797294e-67]
```

The magnitude is small but strictly separated from zero. Its size is not
used as a functional-error lower bound. Both coefficient vectors match the
2267 replay exactly: zero changed components out of 60 per vector. Thus
coefficient provenance no longer explains away the scale mismatch.

## 3. Correct-owner elementary strip bound

Let r_j = a_j^2 and set

  b(y) = sum_j base_j * phi_(r_j)(y) * exp(i*theta_j*y),
  c(y) = sum_j corr_j * phi_(r_j)(y) * exp(i*theta_j*y).

These smooth profiles are extended by zero at their support edges. For
q = 1-(y/r)^2 in (0,1], q^-m*exp(-30/q) increases with q when m <= 30,
since its logarithmic derivative is (30-m*q)/q^2. It is therefore at most
exp(-30). Differentiating the bump and applying this bound gives:

  P0 = 1,
  P1 = 60/r,
  P2 = 3900/r^2,
  P3 = 272160/r^3,
  |phi_(r)^(k)| <= exp(-30)*Pk, for k = 0,1,2,3.

The third-derivative constant here is
72*30 + 60*30^2 + 8*30^3 = 272160. It uses the full triangle bound on
log-derivative terms, not a borrowed, tighter cancellation claim.

On the centered strip |sigma| <= 1/2, let

  C_j = 2*r_j*exp(-30+r_j/2)*|coefficient_j|.

The support weight satisfies exp(sigma*y) <= exp(r_j/2). Differentiating
the modulation gives the elementary majorants

  M0 <= sum_j C_j,
  D2 <= sum_j C_j*(P2 + 2*|theta_j|*P1 + |theta_j|^2).

Hence the min-product required by hstrip has a uniform upper bound

  B_abs = min(D2_b_upper*M0_c_upper, D2_c_upper*M0_b_upper).

This is a true upper-bound construction for the corrected functions. It
loses cancellation between families before integration and is expected to
be costly; the run tests that specific method rather than guessing its price.

## 4. Ideal full-line tail for the frozen visible-prime kernel

This bound acts on the ideal transforms of the same stored coefficient
functions b and c, not on the periodic finite GL family sums. It retains
the frozen visible-prime kernel for comparison; it does NOT establish
that this visible set is the support-derived set of the selected detector.

For the transform at s = 1/2 - 2*pi*i*xi, take three integrations by parts
of exp(y/2)*b(y). The smooth compact support removes all boundary terms.
Define Db3 by replacing |theta| with |theta|+1/2 in the order-three
modulated derivative majorant:

  Db3 = sum_j C_j*(P3 + 3*t_j*P2 + 3*t_j^2*P1 + t_j^3),
  t_j = |theta_j|+1/2,
  |Lb(1/2-2*pi*i*xi)| <= Db3/(2*pi*|xi|)^3.

Define Dc3 in the same way. These bounds hold for both signs of xi.

The ideal physical integrand is

  Gi(xi) = K_visible(xi)*P(xi)^2*|Lb|^2*|Lc|^2.

P is the four-factor centered-orbit annihilator. Its factors use complex
moduli, not the real part of the polynomial. The stored orbit has
|Re node|+|Im node| < 40. For |xi| >= 40 and pi < 4,

  |P(xi)|^2 <= (40+8*|xi|)^8 <= 9^8*|xi|^8.

For the archimedean channel sigma(u) = log(pi)-Re psi(1/4-i*u/2), use the
digamma series of DLMF 5.7.6 (reference: https://dlmf.nist.gov/5.7.E6).
Here psi is the logarithmic derivative of the Gamma function. With
alpha = 1/4 and beta real, subtracting the real-axis series gives

  Re psi(alpha+i*beta) - psi(alpha)
    = sum_{n>=0} beta^2/((n+alpha)*((n+alpha)^2+beta^2))
    <= beta^2 * sum_{n>=0}(n+alpha)^-3
    <= 72*beta^2.

Also psi(alpha) = -EulerGamma-4 + sum_{n>=1} alpha/(n*(n+alpha)).
The last sum is at most alpha*(1+integral_1^infinity x^-2 dx) = 1/2;
0 <= EulerGamma <= 1 and log(pi) <= 2 imply |sigma(0)| <= 8.
Therefore, at u = 2*pi*xi,

  |sigma(2*pi*xi)| <= 8+1152*xi^2.

The frozen prime cutoff exp(2*a_max) is enclosed below 168. Every visible
prime power is therefore among integers 1..167. Bounding each positive
coefficient 2*Lambda(n)/sqrt(n) by 2*n gives the conservative sum

  prime_abs <= 167*168 = 28056.

This overbound does not add primes to the owner; it bounds the existing
finite channel. Using pi > 3, combine the factors and integrate both tails:

  integral_{|xi|>40} |Gi(xi)| dxi
    <= 2*(9^8/6^12)*Db3^2*Dc3^2*
       ((8+28056)/(3*40^3) + 1152/40).

The result is finite and analytic, unlike a ring refinement. It is far too
large to close hgap. This certificate prices a conservative elementary
method; it does not lower-bound the actual tail.

## 5. Prices, trust boundary and acceptance

All finite expressions above are evaluated by 256-bit MPFR with explicit
RNDD/RNDU rounding for each operation and directed conversion to binary64.
Stored hexadecimal inputs are first enclosed as exact dyadic rationals.
The interval engine rejects nonfinite values, zero-crossing divisors and
invalid intervals. Independent mpmath evaluations and exact rational
arithmetic provide regression anchors. MPFR interval operations, rather
than sampled grid differences, establish the expression enclosures.

```text
method expression             enclosed upper endpoint   budget             price / budget
correct-owner strip majorant  1.907160891918978e13        9.506275102584327e6  2.006212603084154e6
ideal two-sided tail bound    1.005130285058951e41        1.000000000000000e7  1.005130285058951e34
```

The lower endpoint of each COMPUTED MAJORANT expression also exceeds its
budget. That rejects this sufficient-bound method. It does not imply that
the TRUE norm or tail exceeds the budget, since an upper bound can be loose.
The status ABSOLUTE-FAMILY-METHOD-REJECTED is scoped accordingly.

The new paired Lean audit builds successfully (2943 jobs). All eight
audited declarations use exactly [propext, Classical.choice, Quot.sound].
The paired audit and root aggregate also pass together (4283 jobs); replayed
style warnings are confined to pre-existing source files.
Thirteen new regression tests, all ten 2275 controls, and all 22 Linux
strip integration controls pass (45 tests total). No old numeric artifact
is rewritten. No manifest-
bound producer module or script is changed, so the strip manifest itself
remains unchanged.

Reproduction from the repository root in Linux:

  python3 scripts/routea_owner_scale_price_2276.py
  python3 scripts/routea_owner_scale_selftest_2276.py
  lake build ConnesWeilRH.Dev.C1RouteAOwnerScaleAuditAudit

## 6. Gate decisions and next steps

1. Object binding: the physical transform convention is identified and the
   legacy equality is formally refuted. The selected-detector identity,
   CompactLog membership and ideal interpolation remain separate obligations.
   The old 2267 envelope must not be supplied as hstrip for this squared-width
   owner merely because the coefficient hashes agree.
2. Analytic budget: a correct-owner strip majorant and two-sided ideal-tail
   majorant are supplied at the expression-certificate grade. Their prices
   reject the absolute-family method. Retain signed cancellation and use a
   correctly scaled, independently checked physical evaluator before any
   panel-local improvement; do not rerun the old width-a norms.
3. Lean producer attachment: the budget gate does not pass, so hgap stays
   explicit and no supplier is attached. Complete the selected-owner and
   support-derived visible-prime readback before a new window/grid budget.
   A successful continuation must prove all same-owner analytic prices fit,
   not reinterpret the historical measurements or alter the detector silently.
