# Proof 423: Yoshida route-node and boundary-jet mismatch

Date: 2026-07-20

Status: exact source/consumer audit and a new axiom-clean Lean coordinate
bridge.  The current Yoshida `routeNodes` can include the source nodes `0`
and `1`, and the underlying producer then gives selected-root zeros at the
centered points `-1/2` and `1/2`.  Those zeros are produced by the final
correction, not by the repeated base.  They therefore give only a fixed-order
`Q` factorization and do not create a convolution-count-dependent boundary-jet
cancellation.

This rejects the proposed finite-jet shortcut to Proof 416 `(EN.7)`.  It does
not prove the canonical Burnol boundary estimate, Gate 3U, the finite-`S`
sign, Burnol's identity, or RH.

## 1. Result

```text
+------------------------------------------------------+----------------------+
| statement                                            | judgment             |
+------------------------------------------------------+----------------------+
| concrete RH consumer supplies `routeNodes`           | no consumer exists   |
| `routeNodes` may contain source nodes `0,1`           | yes                  |
| raw source zeros transport to centered root zeros    | Lean-owned           |
| centered root zeros imply the two pole values vanish | yes                  |
| root lies in the compactly supported `Q` range       | yes, mathematically  |
| square lies in a fixed `Q^2` range                   | yes, mathematically  |
| zero multiplicity grows with convolution count       | no                   |
| `Q^2` kills the next `exp(-3z/2)` Burnol mode        | no                   |
| finite route nodes prove `(EN.7)` / `(CF.31)`         | no                   |
| RH                                                   | unproved             |
+------------------------------------------------------+----------------------+
```

The corrected dependency is

```text
route nodes `0,1`
  -> correction zeros of the raw assembled source
  -> selected-root zeros at `-1/2,+1/2`
  -> one extra fixed `Q` factor
  -> no control of the complete inverse Gram
  -> Proof 416 `(EN.7)` remains open.                  (RJ.1)
```

## 2. There is no existing route-node consumer

The repository-wide exact call-site query is

```text
rg -n --glob '*.lean' \
  "exists_fixedWindows_nearbyZero_negativeFourPointOrbit_selectedOwner|\
exists_fixedWindows_nearbyZero_negativeOrbit_selectedOwner|\
exists_fixedWindows_nearbyZero_selectedOwner" ConnesWeilRH
```

Its complete set of files is

```text
ConnesWeilRH/Source/CCM25Concrete/UnscaledYoshidaSelectedOwner.lean
ConnesWeilRH/Dev/UnscaledYoshidaSelectedOwnerAudit.lean
```

The source file contains the three definitions.  The audit file contains only
`#check`, `#print`, and `#print axioms`.  No Source theorem instantiates any of
them, and `selectedOwner` itself occurs only in those same two files.

Consequently there is no factual answer of the form

```text
the RH consumer passes routeNodes = {...}.             (RJ.2)
```

`routeNodes` is an arbitrary finite interpolation parameter.  A new RH-facing
consumer may choose it, but it must state that choice and consume the resulting
zeros explicitly.

## 3. What the current producer actually does

Write the unscaled assembled source as

```text
h_n=base^(convolution n+1) * correction.              (RJ.3)
```

The producer

```text
exists_fixedWindows_nearbyZero_unscaled_negativeSourceOrbit_assembly
```

is in

```text
ConnesWeilRH/Source/CC20YoshidaFullProduct.lean:627
```

Its base contract is exactly

```text
forall w in sourceFunctionalEquationOrbit(rho),
  laplaceAt base w = 1.                               (RJ.4)
```

The non-target source/route zeros are returned later as

```text
forall z in sourceNontrivialZerosInClosedBallFinset(rho,R)
              union routeNodes,
  z notin sourceFunctionalEquationOrbit(rho)
  -> laplaceAt h_n z = 0.                             (RJ.5)
```

The implementation of the generic assembly identifies the zero-producing
factor before multiplying:

```lean
have hcorrectionZero : laplaceAt correction z.1 = 0 := by
  simpa [y, zNode, hz] using hvalues zNode
rw [laplaceAt_convolution, laplaceAt_convolutionIterate,
  hcorrectionZero]
simp
```

Source:

```text
ConnesWeilRH/Source/CC20YoshidaConvolution.lean:1173-1177
```

Thus the exact transform is

```text
Laplace(h_n)(s)
 =Laplace(base)(s)^(n+1) Laplace(correction)(s).       (RJ.6)
```

At a route node `s_0`, the theorem owns

```text
Laplace(correction)(s_0)=0,                           (RJ.7)
```

not

```text
Laplace(base)(s_0)=0.                                 (RJ.8)
```

Therefore increasing `n` does not increase the guaranteed zero multiplicity.
If the correction zero is simple and the base is nonzero at `s_0`, then

```text
ord_(s_0) Laplace(h_n)=1                              (RJ.9)
```

for every `n`.  Nothing in the current theorem controls the derivative of the
correction transform at `s_0`, so no stronger multiplicity may be inferred.

## 4. Exact half-density coordinate bridge

The selected root is

```text
g_n(x)=exp(x/2) h_n(x).                               (RJ.10)
```

The new Lean theorem is

```lean
theorem selectedOwner_laplaceAt_sourceTest_centered
    (base correction : CompactLogTest) (n : ℕ) (z : ℂ) :
    laplaceAt (selectedOwner base correction n).sourceTest (z - 1 / 2) =
      laplaceAt ((convolutionIterate base n).convolution correction) z := by
  rw [selectedOwner_sourceTest, laplaceAt_halfDensityShift,
    centered_add_half]
```

Source:

```text
ConnesWeilRH/Source/CCM25Concrete/
  UnscaledYoshidaSelectedOwner.lean
```

The zero specialization is separately exported and audited:

```lean
theorem selectedOwner_laplaceAt_sourceTest_centered_eq_zero
    ...
    (hz : laplaceAt rawSource z = 0) :
    laplaceAt selectedRoot (z - 1 / 2) = 0
```

For a nonreal off-line orbit, the real nodes `0` and `1` are not orbit points.
Choosing

```text
routeNodes={0,1}                                      (RJ.11)
```

in `(RJ.5)` and applying the new bridge gives

```text
Laplace(g_n)(-1/2)=0,
Laplace(g_n)( 1/2)=0.                                (RJ.12)
```

These are root-level statements.  The public selected-owner existence theorem
currently retains only the corresponding convolution-square zeros; a future
RH consumer which needs `(RJ.12)` must consume the lower producer `(RJ.5)` and
the new bridge rather than reconstructing root zeros from a zero product.

## 5. Exact compact `Q` factorization

Let

```text
L=partial_x+1/2,
L_star=-partial_x+1/2,
Q=L L_star=-partial_x^2+1/4.                         (RJ.13)
```

For the bilateral Laplace convention used by the source,

```text
Laplace(partial_x f)(s)=-s Laplace(f)(s).             (RJ.14)
```

If only the positive pole row vanishes, define

```text
xi(x)=exp(-x/2) integral_(-infinity)^x
        exp(t/2)g_n(t)dt.                            (RJ.15)
```

Then

```text
L xi=g_n.                                             (RJ.16)
```

Compactness is exact: below the support the integral in `(RJ.15)` is zero;
above the support it is the total value `Laplace(g_n)(1/2)`, also zero.

The negative pole row in `(RJ.12)` implies

```text
Laplace(xi)(-1/2)=0.                                  (RJ.17)
```

Applying the analogous compact right inverse of `L_star` gives a compact
smooth `psi` with

```text
xi=L_star psi,
g_n=Q psi.                                            (RJ.18)
```

Let

```text
F_n=g_n^star * g_n.                                   (RJ.19)
```

Because `Q` is even and commutes with reflection, conjugation, and convolution,

```text
F_n=Q^2(psi^star * psi).                              (RJ.20)
```

This is a genuine strengthening of the single-`Q` ownership from Proof 217.
It is fixed order: `(RJ.9)` gives no `Q^(n+1)` factor.

## 6. Why the extra fixed `Q` does not close the boundary estimate

Proofs 334--336 identify the actual positive-displacement Burnol moment as

```text
M(z)=exp(-z/2)M_+ + R_z,
R_z=O(exp(-3z/2))                                    (RJ.21)
```

in the required root-sandwiched boundary topology.  Proof 335 already uses

```text
Q exp(-z/2)=0                                        (RJ.22)
```

to remove `M_+` from both the static and compressed Schur terms.

For an exponential character,

```text
Q exp(-alpha z)=(1/4-alpha^2)exp(-alpha z).           (RJ.23)
```

At the next genuine boundary exponent `alpha=3/2`,

```text
Q exp(-3z/2)=-2 exp(-3z/2),
Q^2 exp(-3z/2)=4 exp(-3z/2).                         (RJ.24)
```

Therefore the extra factor in `(RJ.20)` does not improve the next displacement
exponent.  It rescales that mode instead of annihilating it.

The same conclusion follows from a simple jet guard.  For any compact smooth
`psi` with nonzero `Laplace(psi)(1/2)`, put `g=Q psi`.  Then

```text
Laplace(g)(s)=(1/4-s^2)Laplace(psi)(s),               (RJ.25)

Laplace(g)(1/2)=0,
partial_s Laplace(g)(1/2)=-Laplace(psi)(1/2) !=0.     (RJ.26)
```

Value zeros at `+/-1/2` do not imply first-jet zeros.  The current correction
producer does not prescribe derivatives, and its repeated base does not carry
the zeros.  Hence no growing finite-jet annihilator is present.

Most importantly, Proof 416's open object is not the isolated residue
`M_+`.  It is the complete normalized boundary semicommutator

```text
Lambda_(S_F)(F)
 =Tr[
   G_(S_F)^(-1) mathcalB_(h_(S_F))(w_F)
   -G_0^(-1) mathcalB_(h_0)(w_F)].                   (RJ.27)
```

The inverse Gram in `(RJ.27)` is formed only after the complete canonical
Euler family is assembled.  Equations `(RJ.12)--(RJ.20)` neither bound that
inverse nor control the mixed boundary term from Proof 415 `(CF.15)`.

## 7. Consequence for the RH-minimal target

Proof 415 reduces the contradiction route to

```text
abs Lambda_(S_(F_n))(F_n)
 <=P(B_n) norm(g_n)_(H^r)^2.                         (RJ.28)
```

Proof 249 supplies exponential contraction of the right side after a
polynomial estimate is known.  Proof 423 establishes only

```text
F_n in Range(Q^2),                                   (RJ.29)
```

with fixed multiplicity.  Since the Gate formulas in Proofs 341 and 416
already consume `F=Q phi`, and Proof 335 already removes the only
`Q`-harmonic leading residue, `(RJ.29)` does not prove `(RJ.28)`.

The finite-jet proposal is therefore rejected in its current form:

```text
arbitrary route nodes
  -X-> growing base zero multiplicity
  -X-> complete inverse-Gram control
  -X-> canonical Gate estimate.                      (RJ.30)
```

## 8. Verification

The Windows source was copied one way into an isolated WSL2 ext4 verification
directory after the cache-bearing mirror was found dirty.  The accepted build
batch is

```text
lake build ConnesWeilRH.Dev.UnscaledYoshidaSelectedOwnerAudit
  -> 3497 jobs

lake build ConnesWeilRH.Source.CCM25Concrete
  -> 3699 jobs

lake build
  -> 3780 jobs.                                       (RJ.31)
```

The two new declarations have exactly the audited axiom set

```text
[propext, Classical.choice, Quot.sound].              (RJ.32)
```

There is no `sorryAx`, new project axiom, or new linter warning.  Replayed
warnings belong to existing modules.  Windows and WSL2 SHA-256 values match:

```text
UnscaledYoshidaSelectedOwner.lean
45f5f32763858a9056493595d7bcb1eafe388d9e76f256c2de29bb1803236f2d

UnscaledYoshidaSelectedOwnerAudit.lean
767e08b9e4ab4aae91e705f2b6614c3c2f351782d7d62c733198daf01f940736
```

## 9. Evidence boundary

Primary analytic owners used here are

```text
Jean-Francois Burnol,
Sur les espaces de Sonine associes par de Branges a la transformation
de Fourier, Theorem 4:
https://arxiv.org/abs/math/0208121

Alain Connes and Caterina Consani,
Weil positivity and trace formulas, source labels spectral, sonine0,
sonineQbis, and rapid-decay:
https://arxiv.org/abs/2006.13771
```

The source/consumer and multiplicity verdicts do not rely on a literature
analogy.  They follow from the displayed Lean theorem contracts and the exact
product formula `(RJ.6)`.

## 10. Route judgment

```text
+------------------------------------------------+---------------------------+
| layer                                          | judgment                  |
+------------------------------------------------+---------------------------+
| route-node call graph                          | no RH consumer            |
| raw-to-centered source bridge                  | closed in Lean            |
| source nodes `0,1`                             | valid optional choice     |
| compact root `Q` factorization                 | exact mathematically      |
| selected square `Q^2` factorization            | exact mathematically      |
| convolution-count jet growth                   | absent                    |
| next Burnol boundary mode                      | survives `Q^2`            |
| Proof 416 `(EN.7)` / Proof 415 `(CF.31)`       | open                      |
| Gate 3U / finite-S sign / Burnol / RH          | open / open / open / no   |
+------------------------------------------------+---------------------------+
```

The next valid lane is the complete canonical-family signed boundary estimate
or its common-cutoff detector-localized Fisher equivalent.  It must retain the
outer, reflected-second-support, and prolate branches under one inverse Gram
and one normal ordering.  Adding more value-only route nodes is not a
substitute for that theorem.
