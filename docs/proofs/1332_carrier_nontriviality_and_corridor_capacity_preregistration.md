# Record 1332 — Carrier nontriviality and corridor capacity: preregistration of the C0 attack

Date: 2026-09-11.
Status: PREREGISTRATION + paper reduction. This record commits the attack
program, the corrigendum, and the numerical protocol BEFORE any probe cell is
executed. At commit time of this file, zero probe cells have been run.
No vanishing statement, no `qw` sign, no `SourceRH`, no RH conclusion is
proved or claimed here. RH is not claimed.

## 0. Target

The committed facts (records 1328-1331) leave exactly one life-or-death
question for the G8 P1 radial leg:

```text
hcolumn(p)  :=  Summable_j ||(I + U_log p) f_j||^2  over an ONB {f_j} of ran P_S
```

and its ξ-plane reformulation (lemma L1 below). The attack (the "C0" strike)
is decided in two sub-questions:

```text
C0a  Is the carrier W := { w in H^2(C+) : phi*w in H^2(C-) } trivial?
     (W = {0} kills the radial leg by emptiness; W != {0} is the precondition
      for EVERYTHING else, including any falsification.)
C0b  If W != {0}: can the kernel diagonal of W hide its infinite mass inside
     the zero corridors of 2+2cos(2*pi*(log p)*xi) for every visible prime?
```

Non-circularity statement: the committed HT is ARCHIMEDEAN-ONLY — the phase
in `CCM24HardyTitchmarsh.lean:104-112` is a quotient of `Gamma_R` values and
contains no zero data of any kind — so C0a/C0b are decidable without assuming
or implying RH. This is why the attack is legitimate at all.

## 1. Lemma L1 — the corridor formulation (paper)

Record 1329 section 1 gives the committed equivalence
`hcolumn(p) <=> ||(I + U_tau) o P_S||^2_HS < infinity`, tau = log p.
Conjugating by the unitary Fourier transform (translation -> modulation) and
using `parameterizedSoninPolarFrame_range` (the frame is an isometry whose
range is the finite-Euler transport of the Sonin subspace; the transport
multiplier on the xi side is a finite product `prod_{q in S}(1 - q^{-1} chi_q)`
type, bounded above and below by `prod(1 - q^{-1}) > 0` uniformly in xi), the
HS square equals

```text
E_col(p) = integral over R of (2 + 2 cos(2*pi*tau*xi)) dmu(xi),
mu = kernel-diagonal measure of the transported W in the xi picture:
dmu(xi) = Khat(xi,xi) dxi,  Khat(xi,xi) = sup { |w(xi)|^2 : ||w||_W <= 1 }
```

(up to the bounded positive transport weight, which is invisible to
convergence/divergence). Because `2 + 2 cos(2*pi*tau*xi) = 4 cos^2(pi*tau*xi)`
has its zero set exactly at the lattice `{ (k + 1/2)/tau : k in Z }` and
average value 2, convergence of `E_col(p)` is possible only if the mass of
`Khat` concentrates in narrow corridors around every prime-log lattice
simultaneously. The lattices for distinct primes are mutually incommensurable
(the numbers `1, log p_1, log p_2, ...` are Q-linearly independent by unique
factorization).

## 2. Corrigendum to record 1331 sections 2.1-2.2 (statement bug; conclusion survives)

1331 section 2.1 asserted `phi` is "analytic and nonvanishing in the interior
of each half-plane", and 2.2 derived entire-ness of `w` from "a quotient of
two functions analytic in CC- with phi nonvanishing there". Both sentences are
false as written. Exact structure, re-derived:

```text
E(z)  := Gamma_R(1/2 + 2*pi*i*z)   poles at  z^+_m = +i(m+1/2)/(2*pi)  (CC+),
                                         zero-free;  1/E entire.
E#(z) := conj(E(conj z)) = Gamma_R(1/2 - 2*pi*i*z)   poles at
                                 z^-_m = -i(m+1/2)/(2*pi)  (CC-);  1/E# entire.
phi = E#/E:  ANALYTIC in CC+ with simple ZEROS at {z^+_m};
             meromorphic with simple POLES at {z^-_m} in CC-.
```

Corrected proof of entire-ness: for `w in W`, the lower half-plane copy is
`w = h * E * (1/E#)` with `h = phi*w in H^2(C-)`; `h` analytic in CC-, `E`
analytic and nonzero in CC-, and `1/E#` ENTIRE with zeros at `{z^-_m}`, so the
copy is analytic in CC- — glueing along the real line (a.e. match of two
H^2-class functions, Privalov) makes `w` entire. The copy computation also
forces, for every `w in W`:

```text
w(z^-_m) = 0 for all m >= 0     (lower lattice), and dually the upper copy
of h = phi*w has h(z^+_m) = 0   (upper lattice).
```

This forced-lattice-zero structure is NEW and is the mechanism of C0a.
Records checked: the Blaschke condition does NOT kill W (the forced zeros of
`w` live in the opposite half-plane from `w`'s domain), the Cartwright-class
obstruction does NOT fire (the two line estimates allow `|w| <= exp(O(x log x))`
on tilted rays — exactly the critical growth), and the Fredholm/Widom index
theory does NOT apply (`arg phi(x)` winds like `-2*pi*x*log x`, unbounded
variation). The space sits on the border of every elementary theory; the
correct literature frame is the Beurling-Malliavin theory of Toeplitz kernels:

- Hedenmalm-Nikolaev, *Beurling-Malliavin theory for Toeplitz kernels*,
  Invent. Math. 165 (2006) — injectivity criteria for kernels with
  meromorphic-inner symbols.
- Hartmann-Juschenyak-Seip, *Kernels of Toeplitz operators*,
  arXiv:1511.08326 (survey of exactly this question).
- Baranov-Borichev-Fedorovskii, *Cauchy-de Branges spaces, geometry of their
  reproducing kernels*, arXiv:2206.02175 — their standing assumption
  `sum Im(z_n)/|z_n|^2 < infinity` FAILS for our lattice
  (`sum (m)/(m^2) = infinity`), i.e. our case is outside their theorem class:
  the borderline is open literature, hence the probe.

1331 section 2.3-2.5, section 3 (head-window Hilbert-Schmidt, branch (i)
unreachable) and the record-1330 brick are UNAFFECTED: the horizontal-line
Stirling bound `|phi(x - i*eta)| ~ (1+|x|)^{-2*pi*eta}` holds for every
`eta > 0` off the pole lattice, giving all polynomial moments and hence the
same RKHS conclusion. The 1331 verdict stands with the corrected mechanism.

Consequence registered: kernel-diagonal upper bound. Two-sided Cauchy
contours (upper line `Im = sigma` unweighted from `w in H^2(C+)`; lower line
`Im = -eta` weighted `(1+|x|)^{-4*pi*eta}` from `h in H^2(C-)`, `eta` any
non-lattice value) give, for every `beta > 0`,

```text
Khat(xi,xi) <= C_beta * (1 + |xi|)^beta        (xi real)
```

and continuity of the diagonal (1331 2.4). C0b therefore asks whether a
nonnegative continuous function with sub-polynomial-epsilon growth and
infinite total mass can satisfy the corridor integrability of section 1 for
EVERY prime-log lattice at once.

## 3. Outcome table (decides where the program goes)

```text
+----------------------------+-------------------------------------------+
| C0 verdict                 | consequence                               |
+----------------------------+-------------------------------------------+
| W = {0}                    | radial leg vacuous on the committed model;|
|                            | G8 dies CLEAN; 1269-1330 all true but on  |
|                            | an empty pipe. Register the emptiness     |
|                            | theorem and close the leg.                |
+----------------------------+-------------------------------------------+
| W != {0}, Khat cannot hide | classic ¬hcolumn: the premise is          |
| in all prime corridors     | inconsistent with the committed model.    |
|                            | Route A formally dead; negative theorem.  |
+----------------------------+-------------------------------------------+
| Khat can hide (needs       | hcolumn consistent: G2/G3 formalization   |
| zero-free corridor spikes) | marathon (C3) becomes justified. NOT      |
|                            | authorized by this record.                |
+----------------------------+-------------------------------------------+
```

A fourth strategic note (no action authorized): if C0a lands on `W = {0}`,
the model upgrade C4 (moving the completed phase from `Gamma_R`-only to a
zero-carrying quotient) is the only way the carrier becomes nonempty — that
is a Source-layer architecture decision and is memo-only under decision
policy section 6.

## 4. C2 probe protocol (preregistered; executed only after this commit)

Statistic: bounded-below-ness of the Toeplitz-type operator

```text
T_phi : H^2_+(trig^+) -> H^2_+(trig^+),   w |-> P_+ (phi * w)
```

whose KERNEL is exactly W (condition `phi*w in H^2(C-)` <=> `P_+(phi*w) = 0`;
note this is P_+ on the product, NOT P_-, a convention trap that must be
asserted by the controls). Discrete model: periodic grid
`x_j = (j - N/2) * 2L/N` over `[-L, L)`, unitary DFT, trial space the
positive integer modes `m = 1..N/2` (DC dropped), target space the positive
modes with matrix elements `T[i,m] = sqrt(2L) * (DFT(phi * e_m))_{i+1}`
(normalization makes the controls read exactly). `phi` evaluated via
`scipy.special.loggamma`: `phi(x) = exp(-2i*Im logGamma_R(1/2+2*pi*i*x))`,
`logGamma_R(s) = -(s/2)*log(pi) + loggamma(s/2) + loggamma((s+1)/2)`.

Cells: `L in {32, 64} x N in {512, 1024, 2048, 4096}` (8 cells), plus four
control cells: C1 `phi = 1` (must give ALL sigma < 1e-10 — kernel = whole
space), C2 `phi = e^{2*pi*i*x/(2L)}` unit mode shift (must give sigma in
[1-1e-10, 1+1e-10] on the interior... pre-registered expectation: every
singular value equals 1 up to 1e-10, EXCEPT the first row may drop to 0 from
the mode-1 push-out: registered: sigma_min(C2) <= 1e-10 allowed,
sigma_2(C2..N/2) >= 1 - 1e-10 required), C3 `phi = exp(i*0.1*sin(2*pi*x))`
(Helson-Szegő regime: require sigma_min >= 0.5), C4 `phi = conj(C3 symbol)`
(outer-side: require sigma_min >= 0.5). Control breach => ABORTED-UNINFORMATIVE,
exit 1, no verdict, no re-run interpretation.

Readouts per cell: sorted singular values; report sigma_min and the counts
below thresholds 1e-6, 1e-4, 1e-2. Completion judged ONLY by the printed
`DONE 1332` sentinel plus JSON (law: timeout-exit-0 lesson of 1329); dense
SVD only (no QR); per-cell wall-clock budget 580 s.

Verdict rule (only if all controls pass):
- NONTRIVIAL-LIKELY: sigma_min < 1e-4 at (L=64, N=4096) AND sigma_min
  strictly decreases with N at L=64 AND at least one more cell has
  sigma_min < 1e-4.
- TRIVIAL-LIKELY: sigma_min >= 1e-2 in EVERY main cell with N >= 2048.
- else INCONCLUSIVE (no follow-up authorized; report and stop).

Follow-up IF NONTRIVIAL-LIKELY (separate record required before running):
extract the minimal right-singular vector as candidate boundary value `w`,
verify the forced lower-lattice zeros numerically, and evaluate the corridor
integral `sum_tau integral (2+2cos(2*pi*tau*xi)) |what(xi)|^2 dxi` for
tau = log p, p in {2,3,5,7,11} as a capacity test of L1.

## 5. Authorization

```text
paper sections 1-3            committed by this record (done at commit)
C2 probe per section 4        AUTHORIZED now (after this commit only)
follow-up of section 4        NOT authorized (needs its own record)
C3 (G2/G3 formalization)      NOT authorized
C4 (model upgrade)            memo only; requires explicit owner decision
numerics outside protocol     NOT authorized (law 42)
```

RH is not claimed.
