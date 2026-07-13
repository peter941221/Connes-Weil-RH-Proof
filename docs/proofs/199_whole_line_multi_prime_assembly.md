# Proof 199: Whole-line multi-prime crossing assembly

Status: accepted crossing-layer milestone. Finite prime-power families now
assemble from genuine whole-line forward/adjoint traces on one selected square.
RH remains unproved.

## Route obligation

```text
route obligation:
  assemble every selected finite prime-power main term on one operator owner

old weak path:
  one theorem invocation for one p^m, with no finite-family consumer

new mathematical owner:
  eulerLogWeightedGlobalPairTraceAtom on one SelectedWeilSquareOwner

consumer to rewire:
  the single-crossing main term of a future finite-S positive trace

forbidden circular inputs:
  SourceRH, detector coverage, a stored trace equality, or a remainder sign

smallest verification target:
  ConnesWeilRH.Source.CCM25Concrete.SelectedCrossingOperatorBridge

focused axiom audit:
  ConnesWeilRH.Dev.SelectedCrossingMultiPrimeAudit
```

## Result

`eulerLogWeightedGlobalPairTraceAtom` names the actual whole-line operator
scalar

```text
1/(m sqrt(p^m)) *
  (Tr(C_h C_(h*) J_(m log p)) +
   Tr((C_h C_(h*) J_(m log p))†)).
```

`GlobalPrimePowerTraceBasisData` keeps the four interval-dependent Hilbert
bases for the compact kernel, source window, reflected adjoint input, and
reflected factor on the same `(p,m)` crossing length. These are analytic
witnesses, not stored read-off conclusions.

The theorem
`eulerLogWeightedGlobalPairTraceAtom_sum_eq_finitePrimeTerm_pow_sum` proves for
every finite set of prime/exponent pairs:

```text
sum_(p,m) wholeLineCrossingAtom(owner,p,m)
  = sum_(p,m) owner.finitePrimeTerm(p^m).
```

Every summand shares the same `SelectedWeilSquareOwner` and whole-line Hilbert
basis. Only the finite-interval factorization data varies with `m log(p)`.
The `positiveInterval_...` specialization discharges the common support bound
from the canonical Yoshida source, so no second log test or square witness is
introduced at finite-family level.

```text
one selected convolution square
          |
          +--> (p1,m1) forward + adjoint trace --+
          +--> (p2,m2) forward + adjoint trace --+--> finite-prime sum
          +--> ...                               --+
```

## Source screen

A current literature search found no theorem that supplies the next positive
owner. Connes--Consani--Moscovici, *Zeta Spectral Triples*
(arXiv:2511.22755), states in its abstract that rigorous convergence of its
self-adjoint approximants would establish RH. Section 8 explicitly leaves
both the simple-even ground-state condition and the prolate approximation to
that ground state unproved:

```text
https://arxiv.org/abs/2511.22755
https://arxiv.org/pdf/2511.22755
```

The later finite Guinand--Weil dictionary (arXiv:2607.02828) supplies exact
finite matrices and archimedean tail order, but not a uniform sign theorem or
a semilocal positive trace identity:

```text
https://arxiv.org/abs/2607.02828
```

Thus the finite sum theorem is a main-term assembly result, not a positive
owner and not a remainder-sign theorem.

## Verification

The WSL source build passes `2978/2978` jobs. The dedicated import-facing audit
passes `2979/2979` jobs and prints the complete theorem types. Their premises
are only primality, nonzero exponents, one source support bound, one common
whole-line basis, and genuine interval basis data. Both the pointwise and
finite-sum theorems, including the canonical positive-interval specialization,
report only:

```text
propext
Classical.choice
Quot.sound
```

The next bottom is unchanged mathematically but narrower formally: construct a
finite-S ordinary positive trace whose single-crossing quotient is this named
finite sum, then prove that all remaining words give a same-domain compact
self-adjoint post-`Q` remainder with the required sign.
