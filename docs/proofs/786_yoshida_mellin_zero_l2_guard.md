# Proof 786: Yoshida Mellin-zero `L2` root guard

## Result

The proposed use of a Yoshida Mellin zero to cancel the linear Gate 3U
response has a strict carrier boundary.

For the actual selected root

```text
g = selectedOwner(base, correction, n).sourceTest,
C_g = cc20GlobalLogConvolution(g*) ,
```

Lean proves the following implications:

```text
laplaceAt(g, s) != 0
    -> g != 0,

laplaceAt(g, z - 1/2) = 1
    -> g != 0,

Fourier(g) != 0 almost everywhere
and C_g u = 0
    -> u = 0.
```

The unscaled Yoshida normalization transports exactly:

```text
laplaceAt((base^n) * correction, z) = 1
    -> C_g u = 0 -> u = 0,
```

under the existing Fourier-analyticity premise used by the fixed-boundary
injectivity bridge.

## What This Rules Out

The root used by Gate 3U is a whole-line `L2` Fourier multiplier.  A Yoshida
zero is a value of its bilateral Laplace transform at a prescribed complex
Mellin point.  These are different carriers:

```text
Mellin constraint at s = delta + i gamma
        |
        | acts on a generalized exponential, not an L2 vector
        v
isolated complex transform value

whole-line Gate root C_g
        |
        | Fourier multiplier on real frequencies
        v
injective L2 convolution when Fourier(g) is nonzero a.e.
```

Therefore an argument of the form

```text
selected Mellin zero -> C_g(v) = 0 for a nonzero Sonin vector v
```

is invalid.  The formal theorem gives the opposite conclusion whenever the
usual analytic multiplier premise is present: `C_g(v) = 0` forces `v = 0`.

## Consequence For Gate 3U

Proof 785 already shows that a generic weighted Toeplitz kernel can have a
linear response.  Proof 786 narrows the remaining possibility further:
isolated Yoshida Mellin zeros do not remove that response by a literal root
kernel.  Any valid source-specific cancellation must occur only after the
outer, reflected Hardy support, and prolate terms have been recombined in
the completed physical trace:

```text
K_complete = outer + reflected second support + prolate,

Tr Re(-A_S* Q_S K_complete J).
```

No branchwise estimate, Mellin-zero substitution, or assertion that the
root kills a nonzero `L2` vector proves Gate 3U.

## Lean Owners

```text
ConnesWeilRH/Source/CCM25Concrete/
  CCM24FiniteSGatePhysicalYoshidaMellinZeroL2Guard.lean

ConnesWeilRH/Dev/
  CCM24FiniteSGatePhysicalYoshidaMellinZeroL2GuardAudit.lean
```

## Scope

The theorem does not prove that the selected compact root has an analytic
Fourier multiplier; that Paley--Wiener input remains an explicit premise in
the existing fixed-boundary bridge.  It also does not bound the completed
trace, prove Gate 3U, the finite-S sign, Burnol's identity, or RH.
