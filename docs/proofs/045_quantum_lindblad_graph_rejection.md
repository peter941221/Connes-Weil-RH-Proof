# Quantum Lindblad And Prime-Loop Rejection

Date: 2026-07-12

Status: both proposed quantum routes are rejected in their stated forms.  The
arithmetic Lindblad route has an unavoidable positive diagonal compensation
which is much larger than the full Weil margin on an already certified finite
direction.  The ordinary prime-loop quantum graph cannot simultaneously be a
local self-adjoint graph with discrete spectrum and carry one edge of length
`log p` for every prime.  RH remains unproved.

## 1. Result First

```text
route A, orthogonal Lindblad prime jumps: rejected
route B, ordinary local prime-loop quantum graph: rejected
supertrace or nonlocal-network variants: not covered; require a new route
Lean owner or consumer change: none
```

## 2. Route A: Forced Diagonal Compensation

Let `U_b` be translation by `b` on the log line and let

```text
w_(p,m) = log(p) p^(-m/2),
b_(p,m) = m log(p).
```

For the convolution square `F=h*tilde(h)`, the symmetric prime atom is

```text
F(b)+F(-b) = 2 Re <h,U_b h>.
```

The proposed orthogonal Lindblad channel is therefore forced, up to a phase
which does not change its norm, to use

```text
J_(p,m) = sqrt(w_(p,m)) (U_b-I).
```

Its energy is

```text
||J_(p,m)h||^2
  = w_(p,m) (2||h||^2-F(b)-F(-b)).
```

The second term is the required negative Weil prime atom.  The first term is
not optional: every such jump adds `2 w_(p,m)||h||^2`.  Orthogonal environment
channels remove cross terms but cannot remove these diagonal terms.

This is already the smallest possible diagonal cost among all positive
channels built from `I` and `U_b`.  Their coefficient Gram block has the form

```text
[ a   -w ]
[ -w   b ] >= 0.
```

Positive semidefiniteness gives `a*b>=w^2`, hence
`a+b>=2*sqrt(a*b)>=2w`.  The choice `J=sqrt(w)(U_b-I)` attains equality.
Splitting the channel, changing phases, or enlarging the environment merely
adds positive Gram blocks and cannot lower this bound.

At cutoff `c=13`, the prime powers in the exact cutoff-free dictionary give

```text
sum_(p^m<=13) w_(p,m) = 4.971884398070194,
2 sum_(p^m<=13) w_(p,m) = 9.943768796140388.
```

On the already certified `(c,N)=(13,16)` minimum direction, the component
Rayleigh values are

```text
pole  = +1.6090057222
Gamma = -1.5209954661
prime = -0.0880102560
total =  8.57e-35
```

Consequently the proposed jump energy and the residual required to complete
the Weil form are

```text
E_jump = prime + 2 sum w = 9.8557585401,
Q_res  = pole + Gamma - 2 sum w = -9.8557585400.
```

The intervals in `044_cutoff_free_weil_cancellation_verdict.md` certify the
three component values with radii below `5e-18`; the gap here is order nine.
No precision issue can change the sign.  Thus the archimedean/pole remainder
is not a positive noise channel after the forced jump compensation.

Changing the environment multiplicity, adding phases, or separating prime
powers into more orthogonal channels preserves `J*J` and cannot repair the
negative residual.  A non-orthogonal indefinite cancellation would abandon
the Lindblad-square mechanism and restore the original coupled Weil sign.

## 3. Route B: Local Prime Loops Do Not Have Compact Resolvent

The proposed ordinary metric graph assigns one propagation length

```text
ell_p = log(p)
```

to every prime.  These edge lengths tend to infinity.  On each sufficiently
long edge choose the same normalized smooth bump supported in a unit interval
away from all vertices.  The bumps have disjoint supports and the same bounded
quadratic-form energy for every local second-order graph Hamiltonian.  They
form an infinite orthonormal sequence in one bounded form-energy ball.

Therefore the form-domain embedding into `L2` is not compact.  The associated
local self-adjoint graph Hamiltonian does not have compact resolvent and cannot
have the discrete zeta-zero spectrum required by Hilbert--Polya.  Vertex
couplings do not affect these interior bump functions.

Adding external dilation channels to realize the attenuation
`p^(-m/2)` turns the loops into an open scattering system.  Its prime data then
describe resonances or a spectral shift in continuous spectrum, not the
ordinary discrete spectrum of a self-adjoint Hamiltonian.  Proving that those
resonances are real would be a new theorem, not a consequence of self-adjoint
unitary dilation.

There is also a repetition constraint for an ordinary periodic-orbit trace.
One primitive orbit with amplitude `A_p` contributes powers `A_p^m`.  The
same-sign negative Riemann coefficients cannot be obtained by setting a
negative orbit amplitude: `m=1` would require `A_p=-p^-1/2`, while `m=2`
would then give `+p^-1` rather than `-p^-1`.  An ordinary finite collection of
orbits cannot simulate a negative spectral multiplicity at all repetitions;
a fermionic supertrace can, but it no longer supplies an ordinary positive
spectral counting measure.

The general Berry--Keating quantum-graph obstruction is consistent with this
verdict: Endres--Steiner, arXiv:0912.3183, Theorem 15.6, proves a no-go theorem
for self-adjoint Berry--Keating realizations on compact quantum graphs.  The
2026 review arXiv:2606.24405 also records that the unconfined Berry--Keating
operator has Lebesgue rather than discrete spectrum.

## 4. Scope Of The Rejection

This verdict rejects exactly:

```text
A: a sum of orthogonal positive prime-power Lindblad jump energies;
B: a local ordinary self-adjoint metric graph with prime loops log(p).
```

It does not reject a genuinely new graded supertrace, nonlocal canonical
system, or indefinite Krein-space construction.  Those objects lose the
automatic Hilbert-space positivity that motivated A and B, so they must name a
new lower sign mechanism before numerical or Lean work begins.

## 5. Sources

```text
project component certificate:
  docs/proofs/044_cutoff_free_weil_cancellation_verdict.md

exact cutoff-free matrix builder:
  docs/proofs/043_cutoff_free_weil_spectrum_probe.py

Berry--Keating compact quantum graph no-go:
  https://arxiv.org/abs/0912.3183

2026 Berry--Keating operator review:
  https://arxiv.org/abs/2606.24405
```
