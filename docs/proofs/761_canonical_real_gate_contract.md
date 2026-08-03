# Proof 761: Canonical-Family Real Gate Contract

## Result

Proof 761 removes two over-strong quantifiers from the route-facing Gate 3U
contract, but it does not prove the remaining analytic estimate.

For the selected family

```text
S_owner = canonicalFamily(owner),
```

the new non-vacuous contract is

```text
canonicalRealGate3UAt(owner, bound)
  := abs(Re Tr(Target_(S_owner))) <= bound.            (761.1)
```

The bound is an input.  It is not existentially chosen after inspecting the
single scalar.  For a Yoshida sequence, the intended input is a polynomial in
the support radius times the square of a fixed Sobolev energy.

Lean proves the exact order identity

```text
Tr(Target_S) = -star(Tr(SourceBand_S)),                (761.2)
```

and hence

```text
abs(Re Tr(Target_S))
  = abs(Re Tr(SourceBand_S)).                          (761.3)
```

No source-to-ambient trace cycle is used in `(761.2)--(761.3)`.

## Equivalent Readouts

Under the fixed-family trace-legality witness already supplied by Proof 758,
the same scalar bound is exactly

```text
norm Tr((Target_S + Target_S^dagger)/2) <= bound.      (761.4)
```

With the physical support and Hilbert--Schmidt witnesses from Proof 759, it is
also exactly

```text
abs(Re FullCompletedKernelTrace_S) <= bound.           (761.5)
```

The full scalar in `(761.5)` still contains the outer, reflected
second-support, and prolate branches before the real part and absolute value
are taken.

```text
canonical source family
        |
        v
Target_S = L_S^dagger [W,R] J
        |
        +---- real trace ----> Hermitian target
        |
        +---- exact readout --> completed physical kernel
        |
        +---- Gram order ----> -star(SourceBand trace)
```

## Quantifier Cut

Lean records only the valid one-way implication

```text
forall family, norm Tr(Target_family) <= bound
  -> canonicalRealGate3UAt(owner, bound).              (761.6)
```

No converse is asserted.  `canonicalRealGate3UOn` additionally permits a
specified owner class, so the contradiction sequence can be used without
claiming a theorem for unrelated selected tests.

The canonical-family cut is source-owned rather than heuristic:

```text
exists pm in canonicalFamily(owner).terms, pm.1^pm.2=n
  <-> IsPrimePow n and owner.finitePrimeTerm n != 0.
```

This is the theorem `exists_mem_ofSelectedOwner_pow_eq_iff` in
`CCM24FiniteSCanonicalFamily.lean`.

## Endpoint Boundary

The ambient endpoint

```text
rootSandwichedBandResponse = C (B_S-B_0) C^dagger
```

is self-adjoint, so its ordinary trace is real whenever its named-basis trace
is legal.  Proof 761 proves the conditional handoff

```text
Tr_source(SourceBand_S)=Tr_ambient(RootBand_S)
  -> norm Tr_ambient(RootBand_S)
       = abs(Re Tr_source(Target_S)).                  (761.7)
```

The cycle premise in `(761.7)` remains explicit.  Named-basis diagonal
summability does not manufacture it, and Proof 761 does not claim that Gate
3U alone supplies ambient trace legality.

## Verdict

```text
+---------------------------------------------+-----------------------------+
| statement                                   | status                      |
+---------------------------------------------+-----------------------------+
| arbitrary-family complex Gate is necessary | rejected as route minimum   |
| canonical-family real Gate                  | exact Lean contract         |
| target/source real trace equivalence        | proved                      |
| Hermitian/full-kernel equivalence            | proved                      |
| source-to-ambient endpoint cycle             | remains a separate premise |
| canonical completed-kernel estimate          | open                        |
| Gate 3U                                     | not yet closed              |
| RH                                          | unproved                    |
+---------------------------------------------+-----------------------------+
```

The next analytic target is `(761.5)` with a support/Sobolev majorant along
the canonical owner class.  A fixed-owner statement of the form
`exists bound` would be vacuous and must not be used.
