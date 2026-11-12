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
public import Purelib.Approximation.Gaussian.Provenance.Quadratic
public import Purelib.Approximation.Gaussian.Provenance.PolynomialRoot
public import Purelib.Approximation.Gaussian.Provenance.Algebraic
meta import Purelib.Elab.ConstructiveInjectivity
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
  zero for the supported finite provenance classes. Its semantic iff
  and presentation-invariance laws do not apply to opaque inputs lacking
  this provenance, nor to the overlapping numerical small/apart verdicts.

`separatedWord` prepares an entire word in either half-plane and exposes
single/fold agreement, braid invariance, reversal, and the dual period law
through its retained report. Negative imaginary evidence is not global
non-certifiability. Precision and inspection counts below are not CPU-time,
allocation, certificate-size, or general-polynomial separation bounds.
-/

namespace Purelib.Approximation.Gaussian.Acquisition

set_option genInjectivity false in
/-- Retained exact evidence at the original coherent numerical channel.

Each constructor keeps its own mathematical owner and operational comparison.
The polynomial-root class admits arbitrary positive degrees and retains the
original isolation or coefficient-computed multiplicity data.
-/
inductive Provenance (channel : Coherent.CoherentNamed) : Type 1 where
  /-- The original channel has a retained exact Gaussian-rational reading. -/
  | rational (sidecar : Rational.Basic.RationalSidecar channel)
  /-- The original channel has a retained square equation and branch owner. -/
  | squareRoot (sidecar : SquareRootSidecar.Sidecar channel)
  /-- The original channel has admitted quadratic coordinates at their original generator. -/
  | quadratic (sidecar : Quadratic.Sidecar channel)
  /-- The original channel has a retained arbitrary-degree polynomial-root owner. -/
  | polynomialRoot (sidecar : PolynomialRoot.Sidecar channel)
  /-- The original channel has a retained finite algebraic construction and its actual numerical caches. -/
  | algebraic (sidecar : Algebraic.Sidecar channel)

constructive_injectivity Provenance

namespace Provenance

/-- Read exact rational evidence retained by the original provenance.

An algebraic construction reads its own scalar cache. A missing reading
remains absent without invoking general root classification.
-/
def rationalReading {channel : Coherent.CoherentNamed} (provenance : Provenance channel) :
    Option (Rational.Basic.RationalSidecar channel) :=
  match provenance with
  | .rational reading => some reading
  | .squareRoot root => if zero : root.parameter = 0 then
      some ⟨0, SquareRootProvenance.zero_of_square (zero ▸ root.square)⟩ else none
  | .quadratic coordinates => if zero : coordinates.evidence.value.im = 0
      then some (coordinates.scalarReading zero) else none
  | .polynomialRoot root => root.scalar?
  | .algebraic sidecar => sidecar.scalar?

/-- Algebraic scalar inspection uses the original construction's retained scalar reader. -/
theorem rationalReading_algebraic {channel : Coherent.CoherentNamed} (sidecar : Algebraic.Sidecar channel) :
    (algebraic sidecar).rationalReading = sidecar.scalar? := rfl

/-- A retained zero-parameter root supplies exact zero provenance at the same original channel. -/
theorem rationalReading_zero_root {channel : Coherent.CoherentNamed}
    (root : SquareRootSidecar.Sidecar channel) (zero : root.parameter = 0) :
    ∃ reading, (squareRoot root).rationalReading = some reading ∧ reading.value = 0 := by
  unfold rationalReading
  dsimp only
  rewrite [dif_pos zero]
  exact ⟨_, rfl, rfl⟩

/-- Executable exact success-or-exclusion. A prepared result retains its denominator, apartness, operational comparison,
and productive quotient API. -/
def exact {channel : Coherent.CoherentNamed} (provenance :
  Provenance channel) :
    Decision channel :=
  match provenance with
  | .rational reading => reading.decide
  | .squareRoot root => root.decide
  | .quadratic coordinates => coordinates.decide
  | .polynomialRoot root => root.decide
  | .algebraic sidecar => sidecar.decide

/-- Exact obstruction completeness for supported provenance: zero means there is no equivalent prepared presentation,
not merely no certificate found by one search. Both directions remain constructive. -/
theorem exact_complete {channel : Coherent.CoherentNamed}
  (provenance : Provenance channel) :
    (Zero.IsZero channel ↔ ¬ Equivalence.IsPrepared channel) ∧
    (Equivalence.IsPrepared channel ↔ ¬ Zero.IsZero channel) :=
  ⟨(exact provenance).zero_iff_unpreparable,
    (exact provenance).prepared_iff_nonzero⟩

/-- The supported provenance decision flag classifies exactly preparation and operational zero. -/
theorem exact_classifies {channel : Coherent.CoherentNamed}
  (provenance : Provenance channel) :
    ((exact provenance).isPrepared = true ↔ Equivalence.IsPrepared
      channel) ∧
    ((exact provenance).isPrepared = false ↔ Zero.IsZero channel) :=
  ⟨(exact provenance).isPrepared_eq_true_iff,
    (exact provenance).isPrepared_eq_false_iff⟩

/-- Operationally equivalent channels with supported provenance have the same exact preparation decision. -/
theorem exact_respects {first second :
  Coherent.CoherentNamed}
    (left : Provenance first) (right :
      Provenance second)
    (equivalent : NamedEquivalent first.name second.name) :
    (exact left).isPrepared =
      (exact right).isPrepared :=
      (exact left).respects
      (exact right) equivalent

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

/-- Transport retained finite provenance along the supplied operational equivalence. -/
def transportProvenance {first second :
  CoherentNamed} (provenance : Provenance first)
    (equivalent : NamedEquivalent second.name first.name) :
      Provenance second :=
  match provenance with
  | .rational reading => .rational ⟨reading.value,
      NamedEquivalent.trans equivalent reading.equivalent⟩
  | .squareRoot root => .squareRoot (root.transport equivalent)
  | .quadratic coordinates => .quadratic (coordinates.transport equivalent)
  | .polynomialRoot root => .polynomialRoot (root.transport equivalent)
  | .algebraic sidecar => .algebraic (sidecar.transport equivalent)
end Purelib.Approximation.Gaussian.Acquisition.Provenance

end
