# Proof 244: Natural Mellin Completeness

Date: 2026-07-14

Status: accepted as an axiom-clean completeness producer for the ordinary
finite-window regular operator. The fixed-window/growing-support coupling to
the negative Yoshida owner, the actual finite-S post-Q identification, and RH
remain open.

## 1. Result

The result is good: the explicit row-span containment premise left by Proof
243 is no longer needed for the ordinary finite-window operator.

It is enough to use Mellin nodes on the natural-number lattice:

```text
s = 0, 1, 2, ...
```

On the logarithmic window, the corresponding rows are

```text
r_n(t) = conjugate(exp(n t)) = exp(n t).
```

Their algebraic span is dense in the complete `L2` window. Therefore the
compactness selector from Proof 242 can choose finitely many actual natural
Mellin rows. A source test supported in the same window and vanishing at those
finitely many nodes satisfies

```text
Re <x_g, (H_lambda - 2 Id) x_g> <= 0,
```

where `H_lambda` is the named ordinary Haar-window regular operator.

The final theorem is:

```text
exists_finite_cc20WindowHaarNaturalMellinZeros_remainder_nonpositive
```

Its printed type has no control-space containment parameter.

## 2. Why Natural Nodes Work

The first candidate was the pure-imaginary Fourier lattice. That route needs
a circle-to-interval measure equivalence, an endpoint null-set transport, and
a normalized-Haar scaling correction.

Natural Mellin nodes avoid all three layers. Put

```text
u = exp(t).
```

Then the row family becomes

```text
1, u, u^2, u^3, ...
```

on a compact positive interval. In Lean this is expressed directly as a star
subalgebra:

```text
r_0 = 1
r_m * r_n = r_(m+n)
star(r_n) = r_n
r_1(t) = exp(t) separates points
```

The first three identities make the generated star algebra exactly the
linear span of the original rows. The fourth supplies the point-separation
hypothesis. Mathlib's complex Stone-Weierstrass theorem then gives density in
the continuous functions, and `ContinuousMap.toLp_denseRange` gives density
in `L2`.

This is stronger than finite-node linear independence. Independence says a
finite relation has no redundancy; completeness says every `L2` direction
can be approximated by finite linear combinations of the infinite row
family.

## 3. Exact Carrier Flow

The proof never identifies unrelated copies of `L2`:

```text
+---------------------------------------------+
| continuous rows on [-log lambda, log lambda]|
+----------------------+----------------------+
                       |
                       | Stone-Weierstrass
                       v
+---------------------------------------------+
| dense span in compact-subtype L2            |
+----------------------+----------------------+
                       |
                       | exact restriction isometry inverse
                       v
+---------------------------------------------+
| dense span in restricted-log L2             |
+----------------------+----------------------+
                       |
                       | exact log/Haar isometry inverse
                       v
+---------------------------------------------+
| dense span in finite-window Haar L2          |
+----------------------+----------------------+
                       |
                       | compact finite selector
                       v
+---------------------------------------------+
| finitely many natural Mellin zero equations |
+---------------------------------------------+
```

The named density theorems are:

```text
dense_span_cc20NaturalMellinRow
dense_span_cc20RestrictedLogNaturalMellinRow
dense_span_cc20WindowHaarNaturalMellinRow
```

The finite operator consumer is:

```text
exists_finite_cc20WindowHaarNaturalMellinControlRows
```

Proof 243's same-carrier read-off then turns row orthogonality into the actual
source equations

```text
mellinAt(g,n) = 0.
```

The support premise remains explicit:

```text
support(g) subset (1/lambda,lambda).
```

## 4. The New Exact Bottom

Proof 238 accepts an arbitrary finite `routeNodes` set, so the selected
negative Yoshida square can algebraically be made zero at shifted natural
nodes by inserting `n + 1/2` for every selected `n`. That fact alone does not
close the route.

The remaining quantifier order is circular:

```text
fix lambda
    -> compactness selects finitely many rows depending on lambda
    -> the unscaled Yoshida convolution count can grow its support past lambda

build the Yoshida owner first
    -> choose a larger lambda containing its support
    -> the compactness selector at that new lambda may choose new rows
```

Thus a wrapper that merely inserts the selected nodes into Proof 238 would
hide the same-window premise. A valid successor needs one of these genuinely
new producers:

```text
uniform control rows stable under enlarging lambda
support-preserving detector assembly with a coupled far-tail theorem
post-assembly finite correction that preserves the negative orbit and tail
```

Even after that loop is broken, the ordinary regular kernel still must be
identified with the actual finite-S post-Q semilocal remainder on the same
owner.

## 5. Verification

The Windows source was copied one way into the isolated WSL2 ext4 mirror. The
following targets passed together:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock lake build \
  ConnesWeilRH.Source.CC20Concrete \
  ConnesWeilRH.Dev.DenseSourceControlFrameAudit \
  ConnesWeilRH.Dev.GlobalLogControlFrameAudit \
  ConnesWeilRH.Dev.GlobalLogMellinRowsAudit \
  ConnesWeilRH.Dev.GlobalLogMellinCompletenessAudit
```

The aggregate run completed 3535 jobs. The focused audit checks the complete
types and reports only:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx`, project axiom, stored containment conclusion, route rewire, or
new RH-level root appears.

## Route Judgment

```text
+------------------------------------------------+-----------+
| layer                                          | judgment  |
+------------------------------------------------+-----------+
| natural Mellin rows complete on subtype L2     | accepted  |
| restricted-log/Haar exact density transport    | accepted  |
| finite natural-row compactness selector        | accepted  |
| ordinary regular-kernel containment premise    | removed   |
| fixed-window/growing-support Yoshida coupling  | open      |
| actual finite-S post-Q same-object identity    | open      |
| RH                                             | unproved  |
+------------------------------------------------+-----------+
```
