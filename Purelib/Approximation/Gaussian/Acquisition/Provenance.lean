module
import Purelib.Approximation.Gaussian.Division.Prepared.Decision
public import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
public import Purelib.Approximation.Gaussian.Division.Prepared.Rational
import Purelib.Approximation.Gaussian.Division.Prepared.Equivalence
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Equivalence.Zero
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Provenance.Rational.Basic

public import Purelib.Riemann.RootContinuation.SquareRootSidecar
import Init.Core
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Division.Prepared

open Purelib.Approximation.Gaussian.Equivalence

open Purelib.Approximation.Gaussian.Name

open Purelib.Approximation.Gaussian.Provenance

open Purelib.Riemann.RootContinuation

section
@[expose] public section

/-!
# Finite certificate acquisition: public theorem interface

Three distinct contracts are exposed here, without a universal partiality
framework:

* `boundedDivision` makes one prescribed request and returns an ordinary
  cached quotient or whole-ball smallness with persistent candidate bounds.
* `gapDivision` turns smallness into exact branch exclusion under a proved
  zero-or-gap law. `signedGap` computes a sufficient canonical inspection
  budget from an unsigned imaginary gap.
* `exact` decides between an equivalent prepared presentation and operational
  zero for the two supported finite provenance classes. Its semantic iff
  and presentation-invariance laws do not apply to opaque inputs lacking
  this provenance, nor to the overlapping numerical small/apart verdicts.

`separatedWord` prepares an entire word in either half-plane and exposes
single/fold agreement, braid invariance, reversal, and the dual period law
through its retained report. Negative imaginary evidence is not global
non-certifiability. Precision and inspection counts below are not CPU-time,
allocation, certificate-size, or general-polynomial separation bounds.
-/

namespace Purelib.Approximation.Gaussian.Acquisition

/-- A closed list of the supported finite provenance classes, not a caller-supplied zero/prepared answer. Unsupported
symbolic operations may forget their sidecar but cannot construct one of these inputs without proof. -/
def Provenance (channel : Coherent.CoherentNamed) :=
  Sum (Rational.Basic.RationalSidecar channel)
    (SquareRootSidecar.Sidecar channel)

namespace Provenance

/-- Retain rational provenance for the exact original coherent channel. -/
def rational {channel : Coherent.CoherentNamed}
    (sidecar : Rational.Basic.RationalSidecar channel) : Provenance
      channel := .inl sidecar

/-- Retain square-root provenance for the exact original coherent channel. -/
def squareRoot {channel :
  Coherent.CoherentNamed}
    (sidecar : SquareRootSidecar.Sidecar channel) : Provenance channel :=
      .inr sidecar

/-- Executable exact success-or-exclusion. A prepared result retains its denominator, apartness, operational comparison,
and productive quotient API. -/
def exact {channel : Coherent.CoherentNamed} (provenance :
  Provenance channel) :
    Division.Prepared.Decision channel :=
  match provenance with
  | .inl rational => rational.decide
  | .inr algebraic => algebraic.decide

/-- Exact obstruction completeness for supported provenance: zero means there is no equivalent prepared presentation,
not merely no certificate found by one search. Both directions remain constructive. -/
theorem exact_complete {channel : Coherent.CoherentNamed}
  (provenance : Provenance channel) :
    (Zero.IsZero channel ↔ ¬ Equivalence.IsPrepared channel) ∧
    (Equivalence.IsPrepared channel ↔ ¬ Zero.IsZero channel) :=
  ⟨(Approximation.Gaussian.Acquisition.Provenance.exact provenance).zero_iff_unpreparable,
    (Approximation.Gaussian.Acquisition.Provenance.exact provenance).prepared_iff_nonzero⟩

/-- The supported provenance decision flag classifies exactly preparation and operational zero. -/
theorem exact_classifies {channel : Coherent.CoherentNamed}
  (provenance : Provenance channel) :
    ((Approximation.Gaussian.Acquisition.Provenance.exact provenance).isPrepared = true ↔ Equivalence.IsPrepared
      channel) ∧
    ((Approximation.Gaussian.Acquisition.Provenance.exact provenance).isPrepared = false ↔ Zero.IsZero channel) :=
  ⟨(Approximation.Gaussian.Acquisition.Provenance.exact provenance).isPrepared_eq_true_iff,
    (Approximation.Gaussian.Acquisition.Provenance.exact provenance).isPrepared_eq_false_iff⟩

/-- Operationally equivalent channels with supported provenance have the same exact preparation decision. -/
theorem exact_respects {first second :
  Coherent.CoherentNamed}
    (left : Provenance first) (right :
      Provenance second)
    (equivalent : Gaussian.Equivalence.NamedEquivalent first.name second.name) :
    (Approximation.Gaussian.Acquisition.Provenance.exact left).isPrepared =
      (Approximation.Gaussian.Acquisition.Provenance.exact right).isPrepared :=
      (Approximation.Gaussian.Acquisition.Provenance.exact left).respects
      (Approximation.Gaussian.Acquisition.Provenance.exact right) equivalent

end Provenance

end Purelib.Approximation.Gaussian.Acquisition

end

section
@[expose] public section

/-!
# Numerical channels with automatically propagated finite provenance

Arithmetic constructors keep the actual numerical program. Their sidecars
are derived by operational laws, never by treating approximate samples as
exact values. Unsupported combinations lose only the sidecar. This is a
small supported rule set, not general algebraic-number normalization.
-/

namespace Purelib.Approximation.Gaussian.Acquisition.Provenance

open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Approximation.Gaussian.Acquisition (Provenance)
open Purelib.Approximation.Gaussian.Provenance.Rational.Basic (RationalSidecar)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)

/-- Transport the retained finite rational or square-root provenance along the supplied operational equivalence. -/
def transportProvenance {first second :
  Coherent.CoherentNamed} (provenance : Provenance first)
    (equivalent : Gaussian.Equivalence.NamedEquivalent second.name first.name) :
      Provenance second :=
  match provenance with
  | .inl rational => .inl ⟨rational.value,
      NamedEquivalent.trans equivalent rational.equivalent⟩
  | .inr root => .inr (root.transport equivalent)
end Purelib.Approximation.Gaussian.Acquisition.Provenance

end
