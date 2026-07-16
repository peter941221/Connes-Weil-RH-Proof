# Proof 304: CC20 residue-augmented same-carrier owner

Date: 2026-07-16

Status: the ordinary CC20 residue owner is now an axiom-clean Lean object on
the restricted logarithmic carrier and on the global logarithmic carrier.  The
finite natural-Mellin control theorem consumes that exact owner.  This closes
the diagonal-residue and carrier bookkeeping left by Proof 303; it does not
identify the owner with the finite-`S` post-`Q` semilocal remainder.

## 1. What changed

CC20's quantized differential has two distinct pieces:

```text
ordinary finite-window regular kernel       K_I
diagonal distributional residue             -2 Id
complete restricted owner                   K_I - 2 Id
```

On the whole logarithmic line, zero extension changes the finite-window
identity into the orthogonal window projection:

```text
E : restricted L2 -> global L2
P_window = E E*
global owner = K_window - 2 P_window.
```

The new source module is
`ConnesWeilRH/Source/CC20Concrete/QuantizedRemainder.lean`.  It defines:

```text
cc20GlobalLogWindowRestrictedQuantizedRemainder
cc20GlobalLogWindowQuantizedRemainder
```

and proves the exact zero-extension identity
`cc20GlobalLogWindowQuantizedRemainder_eq_zeroExtension_conjugation`.

## 2. Lean results

The restricted owner has the expected pointwise and quadratic forms:

```text
R_I u = K_I u - 2 u
Re <u, R_I u> = Re <u, K_I u> - 2 ||u||^2.
```

It is self-adjoint because the regular endomorphism is self-adjoint and the
residue is a real scalar multiple of the identity.  The global owner satisfies:

```text
R_global = E R_I E*
R_global u = K_window u - 2 P_window u.
```

For window-supported `u`, `P_window u = u`, so the same shifted quadratic form
is recovered on the global carrier.  The stronger bridge
`cc20GlobalLogWindowQuantizedRemainder_inner_zeroExtension` states, without a
support abbreviation,

```text
<E u, R_global (E u)> = <u, R_I u>.
```

This is the crucial ownership invariant: the `-2` term is transported with the
regular kernel instead of being silently inserted into an unrelated continuous
kernel.

## 3. Mellin control now consumes the named object

`GlobalLogMellinCompleteness.lean` now imports the owner and adds three
data-bearing theorems:

```text
exists_finite_cc20RestrictedLogNaturalMellinControlRows_quantizedRemainder_nonpositive
exists_finite_cc20RestrictedLogNaturalMellinZeros_quantizedRemainder_nonpositive
exists_finite_cc20GlobalLogNaturalMellinZeros_quantizedRemainder_nonpositive
```

The first uses compactness of the ordinary `K_I` regular endomorphism and
density of the actual rows `1, exp(t), exp(2t), ...`.  The second converts the
selected row constraints into actual source Mellin zeros.  The third applies
the zero-extension quadratic identity, so its conclusion is genuinely on the
global `K_window - 2 P_window` carrier.

The dependency shape is:

```text
natural Mellin rows are dense
          |
          v
compact ordinary K_I selects finitely many rows
          |
          v
same restricted owner K_I - 2 Id is nonpositive
          |
          v
E-conjugate global owner K_window - 2 P_window is nonpositive
```

No theorem here assumes that the finite-S post-Q semilocal remainder equals
the ordinary CC20 owner.

## 4. Verification evidence

Commands were run in an isolated WSL2 ext4 verification mirror with the Lake
lock:

```text
flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.QuantizedRemainder

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete.GlobalLogMellinCompleteness

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Dev.QuantizedRemainderAudit \
             ConnesWeilRH.Dev.GlobalLogMellinCompletenessAudit

flock -w 1800 /tmp/connes-weil-rh-lake.lock \
  lake build ConnesWeilRH.Source.CC20Concrete
```

The import-facing audits print only the Mathlib foundation axioms:

```text
[propext, Classical.choice, Quot.sound]
```

There is no `sorryAx`, no new project axiom, and no hidden no-argument
conclusion.  All new consumer theorems retain their explicit `lambda`,
`hlambda`, support, and Mellin-zero hypotheses.

The existing numerical regression was also rerun: all 97 probe files parse as
Python AST, and Proofs 278--303 (26 probes) exit successfully.  Every probe
reports `RH=UNPROVED`; the regression is a guard against accidental claims,
not evidence for RH.

## 5. Route judgment

```text
CC20 regular K_I owner                         closed
explicit -2 Id residue                         closed
global K_window - 2 P_window owner             closed
restricted/global quadratic-form compatibility closed
finite natural-Mellin control for this owner  closed
finite-S post-Q semilocal identification       open
continuous root-sandwiched moving bridge       open
Gate 3U                                        open
finite-S sign, Burnol identity, RH             open / unproved
```

The source reference for the residue and quantized calculus remains
Connes--Consani, *Weil positivity and Trace formula, the archimedean place*,
arXiv:2006.13771:

```text
https://arxiv.org/abs/2006.13771
```

## 6. Next hard bone

The next task is not another definition of `K_I - 2 Id`.  It is the continuous
same-object bridge that Proof 303 isolated:

```text
root-sandwiched [H,f] divided-difference response
    = moving outer E/R response
      + complete second-support branch
      + K_prol branch
      - 2 root inner product.
```

The proof must establish trace-class legality after root smoothing, keep all
three physical branches inside one signed scalar, and only then seek an
`S`-uniform estimate.  A finite matrix, a raw translated projection trace, a
branchwise norm bound, or a post-Q contour strip is not a substitute.

Proof 304 therefore lowers the next problem to one precise continuous theorem;
it does not claim Gate 3U or RH.

Proof 305 now closes the first analytic sub-leg of that theorem: the
root-sandwiched continuous-kernel `A†B` owner and its explicit `-2` root
pairing are implemented in
`docs/proofs/305_root_sandwiched_trace_class_bridge.md`.  The supplied kernel
is still a generic continuous regularized kernel; identifying it with the
actual CC20 `[H,f]` divided difference and matching the moving
outer/second-support/prolate branches remain open.
