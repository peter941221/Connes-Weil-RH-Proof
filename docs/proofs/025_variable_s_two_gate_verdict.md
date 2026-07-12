# Variable-S Two-Gate Verdict

Date: 2026-07-11

Result: Gate A is rejected for the direct `S={infinity,2}` remainder. Cocycle
renormalization makes the mixed term trace-legal but leaves a pure finite-place
Dirac-comb term whose post-Q form is second order and unbounded. Gate B, the
factor-level finite-conditioning problem, remains conditionally viable.

## 1. Gate A: The First Finite Euler Factor

CCM24 gives the fixed-S scattering phase

```text
u_S(s) = product_(v in S) L_v(1/2+is) / L_v(1/2-is).
```

For one finite prime `p`, put `a=p^(-1/2)` and `x=s log p`. Then

```text
u_p(x) = (1-a exp(ix)) / (1-a exp(-ix))
       = -a exp(ix)
         + (1-a^2) sum_(k>=0) a^k exp(-ikx).                 (A.1)
```

In the additive log coordinate, `exp(ix)` is translation by `log p` (up to
the fixed Fourier convention). Let `P_+` and `P_-` be the two half-line
projections. In one cross direction, the only Fourier coefficient crossing
the boundary is the nonzero coefficient `-a`; hence the corresponding Hankel
block contains exactly

```text
-a P_- T_(log p) P_+.
```

Restricted to `L2(0,log p)`, this is a scalar multiple of a unitary translation
onto `L2(-log p,0)`. It has infinite-dimensional range and is not compact.
It is also not a scalar modulo compact operators. Relative to the two
half-lines it is off-diagonal. If it were `lambda Id + compact`, its diagonal
compressions would force `lambda=0`, after which the infinite-rank partial
translation would have to be compact.

For the product `u_infinity u_p`, the commutator identity is

```text
[P,M_(u_infinity u_p)]
  = [P,M_u_infinity] M_u_p + M_u_infinity [P,M_u_p].        (A.2)
```

CC20's archimedean quantized differential supplies the compact first term.
The second term is a unitary multiple of the noncompact finite-prime block.
A compact perturbation cannot make its Calkin class scalar.

Therefore the natural semilocal quantized differential already has a
noncompact finite-prime component for `S={infinity,2}`. Applying the post-`Q`
polynomial weight does not smooth a nonzero translation block. The proposed
normal form

```text
D_(S,1) o Q = -c_(S,I) Id + K_(S,I),  K_(S,I) compact
```

cannot follow from this natural direct realization unless a separately proved
semilocal identity subtracts every finite-prime translation before defining
`D_S`. No checked source supplies such a cancellation theorem.

This is consistent with CC20's scope statement: it proposes the semilocal
finite-prime implementation as future work and treats only support in `(1/2,2)`,
where no rational prime occurs (`weil-compo.tex:110-116`). CCM24 supplies the
local Euler factors and unitary canonical coordinate, but defers general-S
Jacobi coefficients (`mainc2m24fine.tex:232-259`).

Primary sources:

```text
Connes--Consani, arXiv:2006.13771
https://arxiv.org/abs/2006.13771

Connes--Consani--Moscovici, arXiv:2310.18423v2
https://arxiv.org/abs/2310.18423
```

Gate A raw verdict:

```text
naive raw finite-prime compactness claim: rejected.
cocycle mixed term: trace-class after smoothing and Euler decay.
pure finite-place D_p o Q: not scalar plus compact; its central Dirac
coefficient p^(-1) log(p) produces a nonzero second-order principal part.
direct cocycle-renormalized D_S: rejected.
full derivation: docs/proofs/026_semilocal_cocycle_renormalization.md.
```

## 2. Gate B: Factor-Level Joint Conditioning

Let `B` be the fixed Yoshida base power and write the final factor as

```text
H = B * correction,
F = H* * H.
```

Positivity of `F` is automatic. For each Mellin node `z`,

```text
Phi_H(z) = Phi_B(z) Phi_correction(z).
```

Thus finite Mellin interpolation remains linear in the correction whenever
`Phi_B(z) != 0`. A bad-space condition is also linear in the correction:

```text
<xi(H),e_j> = (ell_j o convolutionBy(B))(correction).
```

The complete finite interpolation problem is therefore surjective exactly
when the following pullback functionals are linearly independent on the chosen
residual correction window:

```text
Phi_B(z_i) * LaplaceAt(z_i),
ell_j o convolutionBy(B).
```

Distinct Mellin nodes give independent exponential functionals, and the base
normalization removes their zero-factor obstruction. There is no universal
dependence forcing failure of the additional bad-space rows. Conversely,
infinite-dimensionality alone does not prove surjectivity: a bad-space row can
lie in the span of the Mellin rows or vanish on every allowed translate of
`B`.

### Global-window independence argument

Assume the bad-space rows are represented by linearly independent compactly
supported `L2` vectors `e_j`, and the source factor map is the stated
convolution by a fixed nonzero compact base `B`. The pullback of a bad-space
row is represented by a compactly supported convolution of `B*` with `e_j`.

Suppose a linear combination of all Mellin and bad-space pullbacks vanished on
every compact correction window. It would vanish as a distribution on the
whole real line. Outside the common compact support of the bad-space
representers, only a finite exponential polynomial remains. Distinct Mellin
nodes force every coefficient of that exponential polynomial to vanish.

The remaining relation has the form

```text
B* * (sum_j beta_j e_j) = 0.
```

After Fourier transform, the product of two entire functions is zero. Since
`B` is nonzero, the entire-function identity theorem gives
`sum_j beta_j e_j=0`; independence of the bad vectors gives every `beta_j=0`.

Thus the full family of pullback functionals is globally independent. A finite
independent family of linear functionals on `C_c^infinity(R)` has a finite set
of compactly supported witnesses with invertible evaluation matrix. The union
of their supports lies in one finite residual window. Hence the joint map is
surjective on some finite window.

Gate B verdict:

```text
structural status: passes under the same-object linear convolution map,
nonzero base transform at the Mellin nodes, and compactly supported independent
bad vectors.
remaining route check: prove those hypotheses for the actual fixed-S owner.
```

## 3. Route Decision

```text
Gate A raw substitution: fails.
Gate A direct cocycle-renormalized remainder: fails on the pure finite-place
post-Q principal part.
Gate B: abstract joint-surjectivity mechanism passes; owner hypotheses pending.
overall variable-S direct-u_S route: rejected.
RH status: unchanged.
```

Do not implement the general finite-S owner from the desired conclusion. The
only admissible reopening is an exact pre-read-off cancellation theorem for
the pure finite-place Dirac comb, or a different pre-cutoff trace/supertrace
whose remainder never contains it. Gate B alone cannot repair Gate A.
