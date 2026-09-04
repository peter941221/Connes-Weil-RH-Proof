# Record 1127 - exact parity reduction of the class Gram owner

Date: 2026-09-04.  Status: PRE-REGISTRATION committed before code.

Consumer: the healthy-`CompactLog`, B5-shaped single-window Stage-B chain,
through the concrete class-window input to `C1HboxRationalData.Hbox`.
This is a true-data analytic reduction for the Hbox-G obligation; it is not a
ROOT-window or universal B1 campaign.

## 1. Motivation

The class-window core is

    phi_i^a(x) = P_i(x/a) * bump(x/a),

where the bump is even and the first eight Legendre polynomials have parity
`P_i(-x) = (-1)^i P_i(x)`.  Therefore the product for indices of opposite
parity is odd, and its whole-line Gram integral is exactly zero.  The
committed q28/q38/q48 G boxes place zero inside every such cross-parity
interval, so those Hbox-G entries can be discharged without any quadrature or
transcendental estimate.

## 2. Registered targets

1. Prove the exact finite-index parity identity for `classWindowFun` for
   `i : Fin 8`, using the defining Legendre recurrence and the even bump.
2. Prove that `classGramEntry a ha i j = 0` whenever `i + j` is odd.
3. Prove, by exact rational arithmetic, that zero lies between the lower and
   upper G endpoints for every opposite-parity entry in each committed class
   q28, q38, and q48.
4. Expose a combined partial Hbox-G helper stating the lower/upper bounds on
   all opposite-parity entries of the real class Gram matrix.

The even-even and odd-odd Gram entries remain the independent validated
integral-enclosure obligation.  No table value is promoted to an integral
fact by this record.

## 3. Non-goals and integrity boundary

No floating-point calculation, quadrature output, M-side bound, full Hbox,
matrix sign, Stage-B defect estimate, detector-specific semi-local
positivity, `SourceRH`, or RH theorem is claimed.  The exact zero comes from
the analytic parity identity, not from a rounded numerical observation.

## 4. Acceptance gates

G1. The owning module and paired audit build through the resource runner with
the success footer, zero `^error:` lines, and zero `sorryAx`.

G2. Every declaration printed by the audit has exactly
`[propext, Classical.choice, Quot.sound]`.

G3. The parity proof is tied to the actual 1124 class-window owner and the
partial bound helper names the actual q28/q38/q48 box endpoints.

G4. Staged-diff hygiene finds no private paths, generated build artifacts,
hidden proof terms, or stored integral conclusions.

RH NOT claimed.
