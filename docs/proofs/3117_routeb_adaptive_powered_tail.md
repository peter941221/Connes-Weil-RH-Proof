# Adaptive powered-seed tail on the actual rho-dependent family (3117)

Status: FORMAL-PASS. The actual-family tail/prefix assembly is proved.
The same-owner signed gate and RH remain open.

## Campaign and owner

The owner is the existing explicit powered-seed base and correction,
with the same hypothetical right off-line source zero rho and complete
closed-ball zero prefix. The convolution count n may vary after fixing
that base and correction. The named duties are the selected span's
scalar tail smallness and prefix bound, including the actual C2 cost
identified in 3116. A lower bound for C2 is never used as an upper bound.

The result is an existence theorem on the actual family. It chooses the
base contraction threshold, then the complete zero prefix, then its correction
and finite decay constants, and finally a convolution threshold. For every
later convolution count and every positive span coefficient at least a
specified ell>0, it proves strict negativity of the same span's Weil value.
The gap-dependent C2 is chosen for the actual correction, not copied from
the stored 56-node capture. No wired height, norm or node-count cap enters.

The generic fixed-owner tail convergence already exists in 1933/1934;
1957 states the paper lower-coefficient criterion. This record attaches
that criterion to the explicit powered family and its actual prefix.

Acceptance requires a Linux ext4 Lake build and exact axiom audit of the
actual-family theorem, retaining its off-line-zero premise and positive
coefficient floor. The signed gate remains a separate condition on the same
n-dependent function. Boundary checks reject treating convolution decay alone
as uniform control when the span coefficient tends to zero too quickly.

Budget: one focused analytic entry, at most 20 minutes build wall time,
8 GiB resident memory and 2 GiB additional derived output; at least 8 GiB
free Linux disk before building. This scope excludes numerical sweeps,
generated cell batches and cold seed-certificate rebuilds. Failure to preserve
the prefix/correction identity or an applicable existing no-go is a stop
condition. An assumed gate sign or a replacement owner does not qualify
as completion.

## Actual-family theorem

`C1RouteBAdaptivePoweredTail3117.lean` defines the existing construction
without a stored capture or a replacement source:

```text
g_n = (selectedOwner (explicitPoweredHealthyBase rho)
         (explicitPoweredHealthyCorrection rho N routeNodes) n).sourceTest
u_n = fullFunctionalEquationOrbitAnnihilator g_n rho
v_n(lambda) = annihilatorDetectorSpanVector u_n g_n lambda
```

Here rho is a hypothetical nontrivial source zero with Re(rho)>1/2;
routeNodes is any finite extra node set; N selects a complete spectral
prefix; n counts convolution iterations; lambda is the coefficient in
the linear combination `u_n-lambda*g_n`. The function called the owner
is the exact test function used for both signs of the proposed Weil
contradiction. Replacing it between the two signs would invalidate that
contradiction.

The theorem `exists_eventual_powered_span_qw_neg3117` proves:

```text
for every such rho, every finite routeNodes, every ell>0,
  there exist N, C2>=0, n0 such that
    the actual correction at N satisfies its all-strip quadratic pin C2;
    C2 satisfies the necessary inverse-gap cost of 3116;
    for every n>=n0:
      g_n has the required CC20 triple vanishing;
      for every lambda>=ell, qw(v_n(lambda))<0.
```

Triple vanishing means that the transform is zero at the three prescribed
parameters 0, 1/2 and 1. These are the admissibility conditions required by
the existing nonnegative-gate consumer. The four-point annihilator and its
span preserve them. The audit connects that consumer to this same span.

There is no wired height, norm, node-count or numerical C2 cap. The
constants, complete prefix and threshold may depend on rho and the extra
nodes; n0 may also depend on ell. This is an existence theorem, not an
algorithm that computes the required prefix or an explicit bound for n0.

## Why the parameter order is sound

The contraction threshold T depends only on the base. Choose N so the
dyadic prefix covers T and rho, and its multiplicity-weighted shell budget
is below the positive multiplicity of rho. This choice uses epsilon=1.
The correction is then built for this fixed prefix. Its genuine finite C2
upper bound is obtained from compact-log transform decay, along with a
quartic base constant C4. Only after these choices is n0 selected.

```text
rho -> base -> contraction threshold T
                              |
                              v
                     complete prefix N
                              |
                              v
             actual correction and finite C2
                              |
                ell>0 --------+
                              v
                  convolution threshold n0
                              |
                              v
        all n>=n0, all lambda>=ell: qw(v_n(lambda))<0
```

The actual base has the required unit transform values at the target
nodes. Thus every convolution count preserves the correction's raw
targets and kills. `poweredFamily_prefix_square_zero3117` transports the
closed-ball zero control to every non-orbit zero of the chosen complete
prefix. `poweredFamily_span_prefix3117` then proves that the prefix
contribution is at most `-xiMultiplicity(rho)*lambda^2` for this same span.

Put `H=(3+norm(rho))^4`. The sufficient scalar high-shell budget is

```text
H*(H+abs(lambda))^2*(2*pi)^12*((1/2)^n*C4*C2)^2 < lambda^2.
```

For lambda>=ell>0, divide by lambda^2 and use
`(1+H/lambda)^2 <= (1+H/ell)^2`. Everything except `(1/2)^(2*n)` is now
bounded independently of lambda and n. Geometric decay supplies one n0
for all later n and all lambda>=ell, with no upper bound on lambda.
The existing scaled prefix/tail assembly then gives strict negative qw.

The C2 upper bound comes from the actual correction. The necessary
inverse-gap lower cost of 3116 is retained as a separate conclusion.
Substituting that lower cost into an upper-bound argument is invalid and
is not done here.

## Boundary and consumer checks

`C1RouteBAdaptivePoweredTail3117Audit.lean` checks four boundaries:

1. A negative span with this hypothetical rho cannot also satisfy the
   signed gate on that same span. This follows from preserved triple
   vanishing and the existing `qw>=0` gate consumer. It is conditional on
   the hypothetical zero and negative qw, not an unconditional rejection
   of all gate suppliers or of RH.
2. Set `q_n=(1/2)^n` and `lambda_n=q_n^2`. The scalar expression
   `q_n^2*(1+1/lambda_n)^2` is at least 4 for every n. Absolute geometric
   decay alone does not imply relative tail acceptance. This toy scalar
   sequence is not asserted to be an actual gate coefficient.
3. A nonpositive floor permits lambda=0, which cannot satisfy a strict
   positive-tail budget against lambda^2=0.
4. A factor equal to 1 does not contract. The strict base contraction in
   the actual-family proof cannot be discarded.

The first check is an actual-owner consumer test. The other checks guard
the scope of the scalar convergence argument; they do not prove that a
positive coefficient floor is necessary for every possible sequence.

## Verification and provenance

Reproduce in a Linux ext4 verification environment:

```text
python3 scripts/routeb_adaptive_powered_tail_audit_3117.py
```

The script sets `LEAN_NUM_THREADS=1` and runs Lake on the source and audit
modules. It requires the successful build footer and all twelve exact
declaration names, rejects errors or unsupported axioms, and checks that
the hashed sources remain unchanged during the build. Its ten rejection
controls cover direct/Lake formats, identifier suffix substitution, missing
footer, nonzero exit, sorry/new axioms, weakened analytic footprints and
source errors. Text hashes normalize CRLF to LF for portability.

The result is `results/3117_routeb_adaptive_powered_tail_audit.json`:

```text
Build completed successfully (3900 jobs).
status: PASS
elapsed: 24.99 seconds
peak resident memory: 4163014656 bytes
missing declarations: none
all twelve axiom footprints: [propext, Classical.choice, Quot.sound]
sorryAx: absent
```

Most dependencies were cached; this is a focused entry build. No numerical
sweep or cold certificate campaign was run. The entry pruner from 2664 is
specific to its indexed certificate directories; this record has no such
entry, so shared Dev outputs are retained.

## Remaining RH obligation

The tail/prefix side now accepts the actual rho-dependent finite price,
under its positive coefficient floor. It does not prove that the same
family has a gate-compatible coefficient above that floor at any accepted
n. Increasing n changes g_n and its support, hence the finite prime-power
owner of the gate. An old gate or the fixed coefficient 24 cannot be
transferred to those changed functions.

The remaining joint task is to prove a signed gate on at least one exact
span in the accepted range, with all prime-power contributions retained.
For the chosen fixed prefix and correction, an unbounded set of gate indices
with coefficients bounded below would suffice; a single direct joint
certificate would also suffice. Neither is
established here. Failure of this sufficient coefficient-floor method is
not a no-go for every joint tail/gate argument.

```text
hypothetical right off-line source zero
             |
             +--> actual prefix + adaptive tail      FORMAL (3117)
             |                |
             |                v
             |        qw of accepted span < 0
             |
             +--> signed gate on that same span      OPEN
                              |
                              v
                        qw of that span >= 0
                              |
                              v
                  contradiction -> SourceRH -> RH    NOT CLOSED
```

Route A remains the binding selected-detector producer. This scoped Route-B
reduction does not reopen any frozen registered-pattern row or the closed
Route-A pointwise joint-symbol mechanism.

## Method and primary sources

This is a composition of existing project mathematics: generic fixed-owner
geometric tail convergence (1933/1934), the paper positive-lower-coefficient
criterion and parameter order (1957), actual-owner interpolation and prefix
transport (3114), and the necessary C2 cost (3116). The joint interpolation
budget was also discussed in 2713. No novelty claim is made for those ideas
or for the classical geometric convergence argument.

The new formal scope is their composition on the actual powered family,
with the complete prefix fixed before the correction's decay constants
and all later convolution counts. Lean/Mathlib sources are pinned by
`lean-toolchain`, `lake-manifest.json` and the audit artifact; Mathlib
revision is `c5ea00351c28e24afc9f0f84379aa41082b1188f`.
