# Joint-symbol target supersedes the derivative-ratio detour (record 3056)

Date: 2026-10-19.

Status: source-backed direction audit. No new sign estimate, Lean theorem,
numerical certificate, or RH proof.

## Revalidation result

The derivative-energy threshold in record 3053 is a valid bound for the
continuous component `Q_cont`, and record 3054 validly extracts a coarse
derivative-energy estimate from the fourth-order tail. Neither is the most
direct statement of the selected-owner sign target.

Proof record 1738 already writes the full same-owner Weil value as a joint
Fourier integral:

```text
qw(g) = (1/(2*pi))*integral_R m_S(t)*|G(t)|^2 dt,
G(t) = L_h(1/2 + i*t),
m_S(t) = A(t) - sum_(p in S) log(p)*P_p(t),
A(t) = -K + 2*sum_(j>=0) t^2/(c_j*(c_j^2+t^2)),
c_j = 2*j + 1/2.
```

Here `h` is the unscaled selected orbit factor before half-density,
`g(x)=exp(x/2)*h(x)`, and `S` is the complete owner-dependent visible-prime
set. The prime profile `P_p` includes all powers of `p`; the owner and its
prime set must move together. The exact formula retains the archimedean and
arithmetic contributions in one scalar symbol.

Record 1738 also defines the exact frequency partition

```text
N_S = {t : m_S(t) < 0}
deficit = (1/(2*pi))*integral_(N_S) (-m_S(t))*|G(t)|^2 dt,
credit  = (1/(2*pi))*integral_(R \ N_S) m_S(t)*|G(t)|^2 dt,
qw(g) = credit - deficit.
```

The independently formalized record 1745 gives the same gate in prime
coordinates as `archimedeanTerm + signedProfileCredit <=
signedProfileDeficit`. These are complementary exact readbacks of the binding
same-owner inequality, not two independent proof routes.

## Correct target

The live analytic target is a lower bound on `credit - deficit` for the
selected correction and its actual support-derived prime set. The tail
certificate controls `G(t)` for sufficiently large `|t|`; record 3057 now
prices the far positive-frequency credit explicitly. It does not supply
positive credit. The remaining candidate supplier is a quantitative lower
bound for the positive part of the joint symbol on the finite/intermediate
frequency region, using the actual interpolation and tail constraints
together.

The finite-node carrier counterfamily in record 3055 explains why the
interpolation pins alone cannot supply a derivative-energy upper bound.
Record 1738's exact-zero extension screens one possible response: annihilating
more prime harmonics has a factorially growing interpolation cost and does
not control the interior signed balance. Its sections 9-10 are scoped to that
exact-zero/outer-tail strategy, not a no-go for every same-owner joint-symbol
estimate.

Therefore do not continue expanding `D/M` as a primary objective. Retain the
3053-3054 bounds only if they help estimate a term in the joint-symbol balance.
The next proof attempt must lower-bound the full positive-band credit enough
to dominate the negative-band deficit. A high-frequency upper bound can show
that the far tail is too small to carry the balance by itself; it cannot be
counted as positive credit.

```text
credit_mid + credit_tail >= deficit,
```

with all bands, weights, and the visible prime set derived from the same
`OrbitG8Geometry`.

Evidence:

- `docs/proofs/1738_selected_orbit_joint_symbol_and_tail_sampling.md` gives
  the selected-owner joint symbol, sign partition, and scoped cost analysis.
- `docs/proofs/1745_orbit_signed_credit_deficit_budget.md` records the exact
  formal prime-domain credit-deficit equivalence.
- `ConnesWeilRH/Dev/C1C3SigmaKernel.lean` defines the archimedean `c3Sigma`
  kernel and proves its monotonicity; this is the archimedean component of
  `A(t)` after sign/coordinate conversion.
- `docs/proofs/3053_exact_continuous_energy_threshold.md` and
  `docs/proofs/3054_fourth_order_tail_to_derivative_energy.md` remain valid
  auxiliary bounds, but do not close this joint balance.
- `docs/proofs/3057_joint_symbol_far_tail_credit_upper.md` bounds the far-tail
  credit and reduces the necessary lower bound to the finite frequency window.
