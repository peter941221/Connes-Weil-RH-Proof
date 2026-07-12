# Same-Square `p=2` Defect Verdict

Date: 2026-07-12

Status: the endpoint/Sonin same-range implementation of proof 126 is rejected
at `S={infinity,2}`. The abstract defect-dominance proposal is not rejected for
a genuinely different noncompact range. RH remains unproved.

## Result

```text
owner tested: endpoint metric Sonin projection
prime channel: p=2, m=2
excess coefficient: one full p^2 Weil atom
compact smooth witness: strictly positive
cutoff-decay claim for this owner: rejected
Lean owner: forbidden
```

## Exact obstruction

Proof 042 gives the endpoint metric projection coefficient at the second prime
power. Put

```text
p=2,
a=p^(-1/2),
b=2 log(p).
```

The projection produces twice the required `p^2` atom. After subtracting the
Weil main term, one excess copy remains:

```text
E_2(h)
  = a^2 log(p) * (F_h(b) + F_h(-b)),
```

where `F_h` is the autocorrelation of the same test,

```text
F_h(t) = integral_x h(x) h(x+t) dx.
```

Choose the real compactly supported smooth bump

```text
h_0(x) = exp(-1/(1-(x/2)^2))  when |x|<2,
         0                    otherwise,
h = h_0 / ||h_0||_2.
```

Because `b=2 log(2)<4`, the interiors of the supports of `h(x)` and `h(x+b)`
overlap on a nonempty open interval. Both functions are strictly positive on
that interval. Therefore

```text
F_h(b)>0.
```

The bump is real, so `F_h(-b)=F_h(b)`. Since `a^2=1/2`,

```text
E_2(h) = log(2) F_h(2 log(2)) > 0.                    (D.1)
```

This is an exact positivity argument. It does not depend on the numerical
probe.

## WSL2 numerical check

Run:

```text
python3 docs/proofs/127_same_square_p2_defect_probe.py
```

The normalized bump gives the stable values

```text
+--------+-------------------+-------------------+
| points | F_h(2 log 2)      | excess E_2(h)     |
+--------+-------------------+-------------------+
|   4096 | 0.5281191525638   | 0.3660643015993   |
|   8192 | 0.5281191525638   | 0.3660643015993   |
|  16384 | 0.5281191525638   | 0.3660643015993   |
|  32768 | 0.5281191525638   | 0.3660643015993   |
|  65536 | 0.5281191525638   | 0.3660643015993   |
| 131072 | 0.5281191525638   | 0.3660643015993   |
+--------+-------------------+-------------------+
```

The computation confirms the scale of the exact nonzero witness. It is not
used to prove positivity.

## Consequence for defect dominance

For the endpoint/Sonin same-range owner, assigning the excess channel to the
defect square does not make it a cutoff tail. Equation (D.1) gives a fixed
positive same-square value already at `S={infinity,2}`. Compactness or a larger
Galerkin section cannot turn this fixed partial-translation coefficient into
an `epsilon(S)` error.

This does not rule out interference after adding other primes for a completely
different owner. It does rule out the proposed first implementation:

```text
same Sonin range
  + endpoint metric positivity
  + p=2 defect treated as a vanishing boundary tail.
```

Any surviving implementation of proof 126 must use a genuinely different
noncompact range and derive a new same-object identity in which the
`p^(-m/2)/m` coefficient is correct before crossing length supplies the factor
`m log(p)`.

## Evidence boundary

```text
proved analytically here:
  the selected compact smooth witness has E_2(h)>0

proved in proof 042:
  the endpoint metric projection leaves exactly this excess p^2 channel

checked numerically:
  the witness value and grid convergence

not proved:
  impossibility for every different noncompact-range owner
```
