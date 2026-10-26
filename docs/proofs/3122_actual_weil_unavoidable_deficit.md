# Unavoidable deficit in the actual Weil density (3122)

Status: FORMAL-PASS for unavoidable integrated deficit in the exact density.
No global credit bound, Weil sign or RH claim.

Owner: the exact complete physical cosine-prime density of 3121, evaluated
on the selected healthy detector and on the actual powered spans of 3117.
The old 3081 Poisson symbol is not substituted for this density.

Named question: can the actual Fourier energy, including its zero at the
origin under triple vanishing, eliminate the whole positive-gate band?
If it could, a pointwise sign argument would avoid the global signed
budget. Completion is a same-owner strict positive integral of that
unfavourable part, with all continuity, analyticity and nonzero premises
proved for the actual function. This is a scoped mechanism test, not an
independent estimate proving the desired global sign.

The exact readback of 3121 now licenses defining credit and deficit for
the actual Weil density. Their integrability and signed identity must be
proved, without importing the failed Poisson-symbol readback contract.

Budget: one source/audit entry, at most 20 minutes of implementation,
8 GiB peak resident memory and 2 GiB derived output; at least 8 GiB free
disk. No numerical experiment, prime enumeration or additional family
scan. Stop if the owner-specific nonzero or analytic instance cannot be
closed. Source proofs and the focused Linux ext4 audit must have exactly
the standard axiom trio and no sorryAx before publication.

Primary inputs: the actual complete readback and integrability of 3121,
the compact-log Laplace analyticity and Fourier injectivity used in 3092,
the analytic isolated-zero adapter of 3085, and the scalar sigma margin
of 3090. The argument uses classical analytic uniqueness and continuity;
no novelty claim is made for those methods.

## Exact signed object

For a compact-log source g, E(g,xi) is the squared complex norm of its
cycle-frequency Fourier transform. Let S(g) be the actual complete
visible-prime set of g.square. Let K(S,xi) be the signed cosine kernel
of 3120, and sigma the Gamma multiplier of 3121. Define

```text
J(g,xi)       = sigma(2*pi*xi) + K(S(g),xi)
density(g,xi) = -J(g,xi)*E(g,xi)
credit(g,xi)  = max(density(g,xi),0)
deficit(g,xi) = max(-density(g,xi),0).
```

Credit is the favourable contribution to the Weil scalar, while deficit
is the contribution that must be compensated elsewhere. These are parts
of the exact physical density, not absolute-value bounds on individual
prime summands. In particular, all prime cancellation remains inside J.

The source proves full-line integrability of the density and both parts
from 3121. For a triple-vanishing source it then proves

```text
qw(g) = integral credit(g,xi) dxi - integral deficit(g,xi) dxi.
```

Here qw is the same scalar Weil functional whose nonnegativity the
selected-detector route must supply. Triple vanishing remains an explicit
linear condition on g; a sign conclusion is not stored as input.
No credit-versus-deficit domination is assumed or proved.

## Why the deficit cannot vanish

At zero frequency every cosine equals one. The prime weights are
nonnegative, and 3090 proves sigma(0)>0. Therefore J(g,0)>0 for every g.
Continuity gives an open interval around zero on which J stays positive.

A zero of the Fourier transform at xi=0 does not imply it vanishes on
that interval. Compact log support makes the transform real analytic.
The proof obtains this analyticity from the entire complex Laplace
transform, using the exact cycle map -2*pi*i*xi. Fourier injectivity
proves that a nonzero g has a genuinely nonzero transform. Analytic
uniqueness then supplies a nonzero frequency inside the positive-J
interval where E(g,xi)>0.

At that frequency density(g,xi)<0 and deficit(g,xi)>0. Continuity makes
the deficit positive on a smaller interval of positive Lebesgue measure;
its integral is therefore strictly positive. The formal results are
`exists_deficit_frequency3122`, `deficit_integral_pos3122`, and
`not_weilDensity_pointwise_nonneg3122`.

```text
exact full-prime kernel + sigma(0)>0
                 |
                 v
        positive J on an interval
                 |
nonzero analytic transform cannot vanish on that interval
                 |
                 v
      negative actual Weil density somewhere
                 |
                 v
       integral deficit > 0.
```

This supplies a strict integrated obstruction to a pointwise-nonnegative
density argument for the exact 3121 formula. It does not determine the
sign of its complete integral. The scope differs from 3093's earlier
Poisson-symbol screen: 3121 establishes the complete physical readback,
and this record uses its actual cosine-prime kernel. The older scoped
no-go remains unchanged; its uncertified readback is not imported.

## Actual owner instances and boundary checks

For `poweredFamilySpan3117 rho N nodes n lambda` with lambda nonzero,
the source proves the actual Laplace value at rho-1/2 is -lambda. The
base target value is one there and the full orbit annihilator vanishes.
Thus the actual span test is nonzero. This argument quantifies over all
complex rho and uses no source-zero or numerical-cap premise.
`poweredFamily_deficit_integral_pos3122` supplies its strict integrated
deficit. The binding selected detector gets the same result through
`selectedOwner_deficit_integral_pos3122`, using its existing proved
nonzero interpolation value.

The audit also proves the actual boundary under a hypothetical right
off-line source zero: the powered span's Fourier value at zero vanishes,
and hence its density at zero is zero, while its integrated deficit is
still strictly positive for nonzero lambda. It uses the actual triple
vanishing of 3117 rather than assuming the boundary value.

The zero-test guard separately proves that an identically zero source
has zero deficit integral. Thus the nonzero-test premise is essential;
analyticity and a positive symbol alone do not manufacture energy.
The remaining checks verify that a zero transform at the origin gives
zero density and deficit at that point, and that the actual span's
origin-zero and strict integral statements coexist.

## What remains

The result closes the suggestion that the triple vanishing removes the
entire unfavourable band. It gives no numerical lower bound for its mass
and no independent lower bound for credit. The missing inequality is
still integral credit >= integral deficit for the same actual source,
with its full prime cancellation retained. A local negative contribution
does not imply qw<0, and the strict positive deficit does not imply RH.

No additional scalar exit, owner replacement, prime enumeration or
numerical experiment is part of this record. A complete signed estimate,
compatible gate/tail parameters and universal hypothetical-zero coverage
remain unresolved. Route A remains the binding producer.

Reproduction in a Linux ext4 verification environment:

```text
python3 scripts/actual_weil_unavoidable_deficit_audit_3122.py
```

The retained artifact is
`results/3122_actual_weil_unavoidable_deficit_audit.json`:

```text
Build completed successfully (3919 jobs).
audited declarations: 21 / 21
axioms on every leaf: [propext, Classical.choice, Quot.sound]
error / sorryAx: absent
parser controls: 10 / 10 pass
elapsed: 39.24 seconds
peak resident memory: 4165025792 bytes
derived build-tree growth: 4520161 bytes
normalized source hashes: 22
```

Most dependencies were cached. Seventeen source theorems and four boundary
theorems are audited. The toolchain is Lean v4.30.0 and Mathlib revision
`c5ea00351c28e24afc9f0f84379aa41082b1188f`. No indexed 2664 certificate
directory is added; shared Dev outputs are retained.

The initial source checks exposed a coordinate mismatch: the existing
`hasDerivAt_digamma_criticalQuarterLine` uses 1/4-i*pi*xi, whereas c3Sigma
uses 1/4-i*xi/2. The proof supplies xi/(2*pi) explicitly, with exact field
algebra. Other elaboration fixes supplied the scalar for an analytic
constant and opened the existing vanishing consumer's namespace. These
were corrected before the successful source/audit build; no mathematical
assumption was added. The implementation and audit stayed within the
registered budgets, without a numerical run or additional analytic target.
