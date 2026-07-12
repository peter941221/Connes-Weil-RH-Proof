# 080 Canonical Xi Bad-Space Joint Separation

Date: 2026-07-12

Result: a structural joint-separation mechanism exists for the canonical
detector and finitely many M4 bad-space rows. The finite-cutoff stability
needed by the actual route remains open.

## Translation Family

Let `q` be the noncompact inverse transform of the Xi quotient and write

```text
q_c(x)=q(x-c).
```

Its centered transform is

```text
Q_c(u)=exp(c*u) Q(u).
```

Thus the four removed-orbit evaluations are exponential functions of `c`:

```text
Q(u_i) exp(c*u_i).
```

Let `e_1,...,e_m` be independent compactly supported representatives of the
M4 bad-space rows. The corresponding row functions

```text
c -> <q_c,e_j>
```

are convolutions of the superexponentially decaying `q` with compactly
supported data, and therefore decay as `c -> +/-infinity`.

## Independence Argument

Suppose a linear combination of all orbit-evaluation rows and bad-space rows
vanishes on an open interval of translation parameters. Analytic continuation
extends the relation to the real line. Taking both translation tails kills the
decaying bad-row part and, because the off-line orbit exponents are distinct,
forces every orbit coefficient to vanish. The remaining relation is

```text
q * (sum_j beta_j e_j) = 0.
```

Fourier transformation gives a product of entire functions. Since `q` is not
zero and its transform has only discrete zeros, the identity theorem forces
`sum_j beta_j e_j=0`; independence gives every `beta_j=0`.

Consequently the joint orbit/bad-row map is algebraically surjective on a
finite set of compactly supported translation witnesses, before cutoff.

## Unclosed Stability Gate

The actual detector uses a cutoff `chi_A q_c`, while the M4 space itself is
constructed from the remainder operator on the same cutoff interval `I_A`.
The proof still needs a quantitative lower bound on the joint evaluation
matrix uniformly as `A` grows. The abstract analytic independence above does
not provide that bound; a badly conditioned matrix can reintroduce the old
tail-constant cycle.

## Decision

```text
structural joint independence: survives
uniform cutoff/bad-space conditioning: open
M5C lower consumer: not yet accepted
Plan 025: remains a research candidate
```
