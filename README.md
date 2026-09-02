# Connes-Weil RH Formalization

<p align="center">
  <a href="#status"><img alt="Research status: RH unproved" src="https://img.shields.io/badge/status-RH%20unproved-b42318?style=flat-square"></a>
  <a href="lean-toolchain"><img alt="Lean 4.30.0" src="https://img.shields.io/badge/Lean-4.30.0-5c7cfa?style=flat-square"></a>
  <a href="lakefile.toml"><img alt="Mathlib 4.30.0" src="https://img.shields.io/badge/Mathlib%204.30.0-0f766e?style=flat-square"></a>
</p>

This repository formalizes analytic and operator-theoretic pieces of the
Connes--Weil approach to the Riemann hypothesis in Lean 4. It keeps four
different things separate:

1. propositions proved by Lean;
2. explicit assumptions still required by the output theorem;
3. results quoted from the literature;
4. numerical experiments used only as diagnostics.

## Status

> [!IMPORTANT]
> The Riemann hypothesis is **not proved** here. The output skeleton still
> contains five explicit project axioms, listed in
> RhOutputAxiomLedger.lean (ConnesWeilRH/Dev/RhOutputAxiomLedger.lean).
> The Lean results below are checked implications with visible premises; they
> do not silently discharge those premises.

## 1. The mathematical spine

The target statement is the critical-line condition for every nontrivial zero:

$$
\boxed{
\zeta(s)=0,\quad 0<\mathrm{Re}(s)<1
\quad\Longrightarrow\quad
\mathrm{Re}(s)=\frac12
}
$$

For a compactly supported test g, the Weil construction uses a Hermitian
convolution square. In multiplicative coordinates:

$$
\begin{aligned}
g^{\sharp}(x)&=x^{-1}\overline{g(x^{-1})},\\
F_g&=g\ast g^{\sharp},\\
\widetilde F_g(s)&=\widetilde g(s)\widetilde g(1-s),\\
\widetilde F_g\left(\frac12+it\right)
  &=\left|\widetilde g\left(\frac12+it\right)\right|^2.
\end{aligned}
$$

The last line is the square mechanism: on the critical line, the zero-side
contribution is termwise nonnegative. The product convention is derived in
[proof 1070](docs/proofs/1070_weil_q_hunting_level1.md), rather than assumed.

The Lean owner uses the additive logarithmic coordinate. Its involution and
square are:

$$
\boxed{
\begin{aligned}
g^{\star}(x)&=\overline{g(-x)},\\
F_g&=g^{\star}\ast g,\\
F_g&=\texttt{g.involution.convolution g}.
\end{aligned}
}
$$

The implementation is
[CompactLogTest.convolutionSquare](ConnesWeilRH/Source/CCM25Concrete/CompactLogConvolution.lean#L114).
This owner is retained through the coordinate, convolution, arithmetic, trace,
and detector layers.

## 2. One quadratic form, two signs

The same-owner Weil value has both an arithmetic and a spectral description:

$$
\boxed{
\begin{aligned}
q_w(g)
  &=\mathrm{poleTerm}(F_g)
    -\mathrm{archimedeanTerm}(F_g)
    -\mathrm{finitePrimeSum}(F_g),\\[2mm]
q_w(g)
  &=\mathrm{spectralWeilValue}(F_g).
\end{aligned}
}
$$

The first line is the component decomposition. The second is the completed
center-2 contour readback, proved by
[centerTwo_arithmetic_eq_spectral](ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L232)
and used by
[qw_eq_spectralWeilValue_centerTwo](ConnesWeilRH/Dev/C1CenterTwoCriterionBridge.lean#L28).

After assuming a zero off the critical line, the live proof has one owner and
two obligations:

~~~text
                         hypothetical off-line zero rho
                                      |
                 +--------------------+--------------------+
                 |                                         |
                 v                                         v
      construct one healthy CompactLogTest g       prove positivity for the
      with detector data from rho                   same g and its visible
                 |                                  prime-power set
                 v                                         |
              q_w(g) < 0                                  q_w(g) >= 0
                 |                                         |
                 +--------------------+--------------------+
                                      |
                                      v
                               contradiction
                                      |
                                      v
                         SourceRH  ->  Mathlib RH
~~~

The negative sign is formal. The positive sign is the open C3 theorem. The
minimal contradiction is therefore:

$$
\boxed{
\begin{aligned}
q_w(g)&<0,\\
0&\le q_w(g),\\
\therefore\quad&\bot.
\end{aligned}
}
$$

This is a same-test contradiction, not an all-test positivity claim.

## 3. ROOT support versus orbit support

The ROOT window is the compact local base inherited from the CC20 theorem:

$$
\mathrm{supp}(g)\subseteq
\left[-\frac{\log 2}{2},\frac{\log 2}{2}\right].
$$

For that support class, Lean proves the square enters the open prime-free
window and the finite-prime term disappears:

$$
\boxed{
\begin{aligned}
\mathrm{supp}(g)
  &\subseteq\left[-\frac{\log 2}{2},\frac{\log 2}{2}\right]\\
\Longrightarrow\quad
\mathrm{supp}(F_g)
  &\subseteq(-\log 2,\log 2)\\
\Longrightarrow\quad
\mathrm{finitePrimeSum}(F_g)&=0\\
\Longrightarrow\quad
q_w(g)&=-\mathrm{archimedeanTerm}(F_g).
\end{aligned}
}
$$

The endpoint consumer is
[qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf](ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L133).
It still needs an actual CC20EndpointTraceCertificate; the certificate is
not currently produced by the repository.

The formal detector is different. Its fixed-window D1 export is packaged with
an explicit orbit window and a finite visible-prime bound:

$$
\boxed{
\begin{aligned}
\mathrm{supp}(g)&\subseteq
  \mathrm{Ioo}(-(n+2),n+2),\\
q\in\mathrm{globalPrimeIndexSet}(F_g)
  &\Longrightarrow (q:\mathbb{R})<\exp\bigl(2(n+2)\bigr).
\end{aligned}
}
$$

The formal gate on this same object is

$$
\boxed{
\begin{aligned}
0\le q_w(g)
  &\Longleftrightarrow
\mathrm{archimedeanTerm}(F_g)
  +\mathrm{finitePrimeSum}(F_g)\le 0.
\end{aligned}
}
$$

There is still no automatic arrow from ROOT positivity to this orbit-supported
detector. The fixed-window D1 bound is too wide for the external
[-0.8,0.8] candidate interface; map 004 marks that bridge impossible for this
family. The surviving task is the orbit-window semi-local sign, not support
discovery. See [record 1089](docs/proofs/1089_orbit_certificate_extension_design.md)
and the numerical-only [record 1087](docs/proofs/1087_c3_root_window_spectral_verdict.md).

## 4. The route choice: B1 or B5

The output audit contains two singleton logical cuts:

$$
\boxed{
\begin{aligned}
\mathrm{B1}:&\quad
\left(\forall g,\quad
  \mathrm{tripleVanishing}(g)\Longrightarrow q_w(g)\ge0\right)
  \Longrightarrow \mathrm{RH},\\[1mm]
\mathrm{B5}:&\quad
\left(\forall\rho,\quad
  \mathrm{Re}(\rho)>\frac12\Longrightarrow
  \exists g\,
  \bigl(\mathrm{Healthy}(\rho,g)\land q_w(g)\ge0\bigr)\right)
  \Longrightarrow \mathrm{RH}.
\end{aligned}
}
$$

Both cuts are RH-equivalent at the logical level. They are not equally sized
proof campaigns:

| Route | Meaning | Project decision |
| :-- | :-- | :-- |
| B1 | Positivity for every compactly supported triple-vanishing test | Frozen universal campaign |
| B5 | Positivity for the detector selected against each hypothetical zero | Active healthy-owner mainline |
| ROOT | A local CC20 support class with no visible prime powers | Shared base; not an RH exit |
| Orbit | The selected detector's actual support and visible prime powers | C3 consumer; positivity open |

The binding decision is record 1076:
[003_b1_b5_minimal_exit_route_selection.md](docs/map/003_b1_b5_minimal_exit_route_selection.md).
The endpoint scope is maintained by
[004_endpoint_literature_interface_audit.md](docs/map/004_endpoint_literature_interface_audit.md).

## 5. Representative Lean interfaces

The following declarations are the small set that best exposes the formal
architecture. They are not a claim that the surrounding modules are complete.

| Lean interface | What it fixes | Status and evidence |
| :-- | :-- | :-- |
| centerTwo_arithmetic_eq_spectral | One CompactLogTest owner has matching arithmetic and spectral values | [C1XiCenterTwoArithmeticAssembly.lean#L232](ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L232) |
| exists_healthyDetectorData_of_sourceNontrivialZero_right | A right-oriented off-line zero produces one healthy detector | [C1HealthyYoshidaSpectralNegativity.lean#L511](ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean#L511) |
| qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf | A ROOT certificate implies the same-owner nonnegative sign | [C1CC20ArchimedeanReadback.lean#L133](ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L133) |
| orbitWindowSemiLocalGate and qw_nonneg_of_orbitWindowSemiLocalGate | The orbit-window C3 sign is one Prop with a one-line bridge to q_w(g) >= 0 | [C1OrbitWindowSemiLocalGate.lean#L57](ConnesWeilRH/Dev/C1OrbitWindowSemiLocalGate.lean#L57) |
| healthy_sourceRH_of_right_detector_specific_qw_nonneg | The exact B5-shaped contradiction interface to SourceRH | [C1HealthyYoshidaSpectralNegativity.lean#L554](ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean#L554) |
| eulerLog_weighted_pair_traces_eq_finitePrimeTerm_pow | A crossing trace reads back to the exact finite prime-power coefficient | [SelectedCrossingKernel.lean#L390](ConnesWeilRH/Source/CCM25Concrete/SelectedCrossingKernel.lean#L390) |
| not_normalizedCC20MellinConvolutionLaw | The old additive socket cannot implement the Mellin square law | [CC20YoshidaConstruction.lean#L2727](ConnesWeilRH/Source/CC20YoshidaConstruction.lean#L2727) |

### 5.1 The arithmetic-to-spectral bridge

This is the center-2 equality that lets the same test be read in both
languages:

~~~lean
theorem centerTwo_arithmetic_eq_spectral
    (F : CompactLogTest) :
    C1SameOwnerWeil.psi F = spectralWeilValue F := by
  exact centerTwo_arithmetic_eq_spectral_of_gamma_contract F
    (centerTwoGammaReadbackContract_of_halfAnchorGauss F)
~~~

Evidence:
[C1XiCenterTwoArithmeticAssembly.lean#L232](ConnesWeilRH/Dev/C1XiCenterTwoArithmeticAssembly.lean#L232).
The declaration is an equality under its explicit owner and analytic
contracts; it is not a premise-free RH theorem.

### 5.2 The ROOT endpoint consumer

The endpoint interface is deliberately separated from the certificate
producer:

~~~lean
theorem qw_nonneg_of_cc20EndpointTraceCertificate_of_rootSupport_logTwoHalf
    (g : CompactLogTest)
    (hvanishes :
      CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hsupport :
      Function.support g.test ⊆
        Set.Icc (-(Real.log 2 / 2)) (Real.log 2 / 2))
    (hcertificate : CC20EndpointTraceCertificate g) :
    0 ≤ C1SameOwnerWeil.qw g
~~~

Evidence:
[C1CC20ArchimedeanReadback.lean#L133](ConnesWeilRH/Dev/C1CC20ArchimedeanReadback.lean#L133).
The missing mathematics is the construction of hcertificate, not the
logical use of a certificate once supplied.

### 5.3 The minimal B5 exit

The active exit asks for one nonnegative value for the same detector that Lean
already proves to be negative:

~~~lean
theorem healthy_sourceRH_of_right_detector_specific_qw_nonneg
    (hsemiLocal : ∀ rho : sourceNontrivialZeroSet,
      (1 / 2 : Real) < rho.1.re →
        ∃ g : CompactLogTest,
          HealthyYoshidaDetectorData rho.1 g ∧
            0 ≤ C1SameOwnerWeil.qw g) :
    RHDefinitionBridge.standard.SourceRH
~~~

Evidence:
[C1HealthyYoshidaSpectralNegativity.lean#L554](ConnesWeilRH/Dev/C1HealthyYoshidaSpectralNegativity.lean#L554).
The theorem is a conditional implication. The open producer is exactly
hsemiLocal.

### 5.4 The orbit-window C3 gate

Record 1089 makes the remaining sign obligation a single proposition on the
same explicit detector:

~~~lean
def orbitWindowSemiLocalGate (g : CompactLogTest) : Prop :=
  C1SameOwnerWeil.archimedeanTerm g.convolutionSquare +
      C1SameOwnerWeil.finitePrimeSum g.convolutionSquare <= 0

theorem qw_nonneg_of_orbitWindowSemiLocalGate
    (g : CompactLogTest)
    (hvanishes : CC20VanishesOn C1.healthyCC20TestSpace
        cc20TripleFiniteVanishingSet g)
    (hgate : orbitWindowSemiLocalGate g) :
    0 <= C1SameOwnerWeil.qw g
~~~

The same module exports one pinned detector carrying the support and visible
prime-power data:

~~~lean
theorem exists_pinnedOrbitDetector_with_window_and_visiblePrimes
    (rho : sourceNontrivialZeroSet)
    (hoff : rho.1.re ≠ 1 / 2)
    (hright : (1 / 2 : Real) < rho.1.re) :
    ∃ g : CompactLogTest, ∃ n : Nat,
      HealthyYoshidaDetectorData rho.1 g ∧
      Function.support g.test ⊆
        Set.Ioo (-((n + 2 : ℕ) : Real)) (((n + 2 : ℕ) : Real)) ∧
      ∀ q ∈ C1SameOwnerWeil.globalPrimeIndexSet g.convolutionSquare,
        (q : Real) < Real.exp (2 * ((n + 2 : ℕ) : Real))
~~~

Evidence:
[C1OrbitWindowSemiLocalGate.lean#L57](ConnesWeilRH/Dev/C1OrbitWindowSemiLocalGate.lean#L57)
and [record 1089](docs/proofs/1089_orbit_certificate_extension_design.md).
This closes the data and support interface; it does not prove the gate.

## 6. Frozen and deferred routes

The project keeps failed or superseded routes visible so that a local lemma is
not mistaken for the current RH strategy.

| Route | Status | Failure mechanism or boundary | Evidence |
| :-- | :-- | :-- | :-- |
| Universal B1 globalization | Frozen | ROOT positivity does not control mixed terms or newly visible prime powers for arbitrary long-support tests | [route ruling 1076](docs/map/003_b1_b5_minimal_exit_route_selection.md) |
| Normalized additive B5 socket | Audit-only; no new producer work | Its old additive convolution violates the Mellin product law | [not_normalizedCC20MellinConvolutionLaw](ConnesWeilRH/Source/CC20YoshidaConstruction.lean#L2727) |
| Gate 3U and Lane R | Archived | Physical finite-band and prefix/tail sign experiments do not supply global spectral nonnegativity | [RH_MAINLINE_FREEZE.md](RH_MAINLINE_FREEZE.md) |
| Nyman--Beurling / Mobius blocks | Historical obstruction | The projected energy retains the inverse Gram matrix G_N^{-1} | [proof 020](docs/proofs/020_nyman_mobius_m4_first_verdict.md) |
| Titchmarsh square-form bridge | Deliberately deferred | A formal reverse support theorem needs Paley--Wiener / Cartwright machinery not present in Mathlib | [architecture record 1043](docs/map/001_first_cut_window_architecture.md) |
| External [-0.8,0.8] compact-window candidate for the D1 orbit | Blocked for this detector family | The formal orbit window is Ioo(-(n+2), n+2), so the M6 support bridge cannot hold | [map 004](docs/map/004_endpoint_literature_interface_audit.md), [record 1089](docs/proofs/1089_orbit_certificate_extension_design.md) |

### 6.1 The normalized-socket guard

The obstruction is a concrete Lean counterexample, not a naming preference. A
finite-window interpolant is chosen with Mellin value one:

$$
\boxed{
\begin{aligned}
\widetilde g(z)&=1,\\
\widetilde{g\star_{\mathrm{add}}g}(z)&=2,\\
2&\ne 1
  =\widetilde g(z)\widetilde g(1-z).
\end{aligned}
}
$$

The exact witness and contradiction are implemented by
[not_normalizedCC20MellinConvolutionLaw](ConnesWeilRH/Source/CC20YoshidaConstruction.lean#L2727).
The healthy owner uses the genuine convolution square shown in Section 1.

### 6.2 The inverse-Gram boundary

The Nyman--Beurling/Mobius line was not rejected because its finite matrices
are uninteresting. Its projection step keeps the hard inverse:

$$
\boxed{
\|w_N\|^2
  =a_N^{\mathsf T}
    \left(B_N-C_N^{\mathsf T}G_N^{-1}C_N\right)a_N
}
$$

Any proposed cancellation must control the projected Schur complement, not only
an unprojected Mobius sum. This is the structural conclusion of
[proof 020](docs/proofs/020_nyman_mobius_m4_first_verdict.md).

### 6.3 The prolate parameter boundary

The landed Bessel estimate has a precise scope:

$$
\boxed{
q_T(\xi)\ge(1-\lambda)\|\xi\|^2
\quad(\lambda<1),
\qquad
\lambda_{\mathrm{paper}}\simeq1.05158>1.
}
$$

It is a valid lambda < 1 side branch, not a paper-scale endpoint proof.
The required exceptional direction, complement bound, and rank-one repair are
recorded in
[route record 1050](docs/map/002_one_shot_rh_route_verdict.md).

## 7. The remaining mathematics

Record 1089 closes the detector-data side of C3: the support window and the
finite visible-prime bound are formal for one pinned object. The remaining
mathematics is the sign producer:

1. prove orbitWindowSemiLocalGate for the pinned detector;
2. discharge its archimedean and finite-prime terms by a legal endpoint or
   semi-local trace certificate;
3. feed that same-object result into hsemiLocal in Section 5.3.

The endpoint literature may help with the ROOT local base, but it becomes a
valid C3 input only after the convention, support, sign, and interval
certificate bridges in
[endpoint audit 004](docs/map/004_endpoint_literature_interface_audit.md)
are discharged. A ROOT result alone is not the orbit result.

The current dependency is therefore:

$$
\boxed{
\begin{aligned}
\text{orbit support + visible primes}
&\longrightarrow
\text{same-owner semi-local trace identity}\\
&\longrightarrow
0\le q_w(g)\\
&\longrightarrow
\text{contradiction with }q_w(g)<0\\
&\longrightarrow
\mathrm{SourceRH}
\longrightarrow
\mathrm{RiemannHypothesis}.
\end{aligned}
}
$$

No arrow in this display is being reported as complete unless a linked Lean
declaration or proof record says so.

## 8. Verification

Formal claims follow this chain:

~~~text
source formula or theorem
          |
          v
exact project definition and convention bridge
          |
          v
Lean declaration
          |
          v
focused #print axioms audit
          |
          v
build log with a success footer and no error lines
~~~

The imported source tree can be built with:

~~~bash
lake build ConnesWeilRH
~~~

Research-frontier modules under ConnesWeilRH/Dev/ are not all imported by the
root aggregate. Build a leaf together with its paired audit module and inspect
the log; the repository's WSL resource-admission procedure is documented in
[RESOURCE_SCHEDULING.md](RESOURCE_SCHEDULING.md).

Numerical files under docs/proofs/ generate candidates and diagnostics.
Floating-point eigenvalues are not treated as proofs of an
infinite-dimensional sign.

## 9. Sources and repository map

Primary mathematical sources:

1. Alain Connes and Caterina Consani, *Weil positivity and Trace formula: the
   archimedean place*,
   [arXiv:2006.13771](https://arxiv.org/abs/2006.13771).
2. Alain Connes, Caterina Consani, and Henri Moscovici, *Zeta Zeros and Prolate
   Wave Operators: Semilocal Adelic Operators*,
   [arXiv:2310.18423](https://arxiv.org/abs/2310.18423).
3. Marcus Chuk, *Weil positivity in compact windows: certified two-sided
   bounds and a Landau--Widom decay law*,
   [arXiv:2608.24827](https://arxiv.org/abs/2608.24827).

The third item is an unreviewed external candidate. Its conventions and
certificate interface are not yet landed in Lean. The project's Mellin-square
dictionary is derived in
[proof 1070](docs/proofs/1070_weil_q_hunting_level1.md).

Repository layout:

~~~text
ConnesWeilRH/
  Source/       imported definitions and reusable analytic/operator facts
  Route/        conditional route compositions and equivalence audits
  Dev/          research-frontier leaves with focused audit modules

docs/map/       route authority and endpoint-interface decisions
docs/proofs/    derivations, proof records, and numerical diagnostics
scripts/        certificate generation and resource-aware build helpers
~~~

The final Mathlib target is
[_root_.RiemannHypothesis](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/LSeries/RiemannZeta.lean).
The root import is [ConnesWeilRH.lean](ConnesWeilRH.lean).

## License

Apache License 2.0. See [LICENSE](LICENSE).
