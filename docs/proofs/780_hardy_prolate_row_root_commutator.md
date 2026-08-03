# Proof 780: Root-local completed Hardy--Prolate row

## Result

Proof 779 expressed the raw Gate target as one `WithLp 2` completed row with
the compact root on its right:

```text
Target_S = (X_S D_S)* Y_S W J,
W = C_root* C_root.
```

Proof 780 moves that same root into the two actual source boundary
commutators while preserving the one Hilbert row:

```text
Y_S W J
 = ( T_S (I-E) [W,E] J,
     L [W,R] J ).
```

Here

```text
E = radial support projection,
R = source Sonin projection,
L* L = E-R,
[W,E] = W E-E W,
[W,R] = W R-R W.
```

Consequently Lean proves the exact root-local form

```text
Target_S
 = (X_S D_S)*
   ( T_S (I-E)[W,E]J,
     L[W,R]J ).
```

Every matrix coefficient and every ordinary named-basis trace diagonal is the
same single signed `WithLp 2` row pairing.

## Why This Matters

The two commutators have the real source geometry required by Gate 3U:

```text
compact root W
      |
      +-- [W,E] : outer half-line crossing
      |
      +-- [W,R] : full Sonin crossing
                       |
                       +-- outer / reflected / second support / prolate
```

The first has the existing translated half-line identity
`detectorRadialCommutator_eq_translation_conjugation`.  The second is the
existing `sourceBoundaryCommutator`, whose physical expansion retains the
same outer, reflected-second-support, and prolate completion.

The important point is that these are coordinates of one `WithLp 2` vector.
Proof 780 does not permit a triangle inequality, separate trace norm, or
separate Hilbert--Schmidt estimate of the two coordinates.  Those operations
would discard the exact signed cancellation that Gate 3U needs.

## Proof Logic

The Hardy/prolate analysis has Gram

```text
L* L = E-R.
```

Since `(E-R)R=0`, the Hilbert-space kernel identity gives `L R=0`.  Therefore

```text
L W J = L (W R-R W) J = L[W,R]J,
```

because `R J=J`.  Likewise `EJ=J` and `(I-E)E=0` give

```text
(I-E) W J = (I-E)(W E-E W)J = (I-E)[W,E]J.
```

Both equalities are assembled before the `WithLp 2` pairing is evaluated.

## Scope

This is an exact source-object normal form, not the missing uniform estimate.
The remaining theorem is still a support-polynomial, finite-visible-set
uniform bound for the one signed root-local row pairing.  It must use the
compact support of the root before expanding the finite Euler transport or
using any absolute value.

Proof 780 does not prove Gate 3U, the finite-S sign, Burnol's identity, or
`_root_.RiemannHypothesis`.
