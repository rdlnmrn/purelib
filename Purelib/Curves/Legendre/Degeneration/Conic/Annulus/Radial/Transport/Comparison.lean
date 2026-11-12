module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Coordinates.Injective
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Arithmetic.Product.Congruence
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.RootIsolation.SquareRoot.Owner.Transport

/-! # Original parallel readings at an identical physical point

Both original retained time queries keep their own cofactor Owners, full
cubic certificates and product programs. The same actual quarter budget
compares both cofactor names. Injectivity of the regular parallel ellipse
preserves the exact original normalized ordinate, so product congruence
compares the full channels without acquiring another source or target.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Reading

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent.CoherentNamed
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Geometry.Rational

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Quarter site parameter 2 quarter positive}
variable {first last : Fraction.Rational}
variable {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}

/-- The actual original cofactor query refines the identical retained quarter reference Owner's source box. -/
theorem unit_refines (reading : Reading actual first firstInside) :
    reading.unit.track.initial.box.Refines actual.data.source.track.initial.box := by
  rewrite [reading.unit_eq, RootIsolation.SquareRoot.Owner.Transport.castOwnerParameter_initial_box]
  exact reading.trace.refines

/-- Distinct original cofactor Owners agree at the same base under the retained original quarter budget. -/
def unit_owners_of_base_eq (left : Reading actual first firstInside) (right : Reading actual last lastInside)
    (point_eq : (point site parameter 2 (Waist.direction quarter first) positive).base =
      (point site parameter 2 (Waist.direction quarter last) positive).base) :
    NamedEquivalent (ownerRootName left.unit.parameterNonzero left.unit)
      (ownerRootName right.unit.parameterNonzero right.unit) := by
  have movement := actual.data.path.firstMovement first firstInside
  rewrite [actual.data.point_eq first] at movement
  exact actual.data.budget.retainedOwnersEquivalentOfEq
    (congrArg (fun value : Canonical => (unitPolynomial site).eval value) point_eq)
    left.unit.parameterNonzero movement left.unit right.unit left.unit_refines right.unit_refines

/-- The complete original cofactor certificates agree without re-isolation, re-sampling or a replacement certificate. -/
def unit_values_of_base_eq (left : Reading actual first firstInside) (right : Reading actual last lastInside)
    (point_eq : (point site parameter 2 (Waist.direction quarter first) positive).base =
      (point site parameter 2 (Waist.direction quarter last) positive).base) :
    NamedEquivalent left.lift.unitRoot.value.name right.lift.unitRoot.value.name :=
  NamedEquivalent.transport left.lift.unitRoot_name.symm right.lift.unitRoot_name.symm
    (unit_owners_of_base_eq left right point_eq)

/-- Equal regular physical bases compare the two complete original parallel cubic product channels.

The cofactor comparison consumes both retained query Owners and their same
reference budget. Exact parallel-coordinate injectivity pays the original
normalized-ordinate factor. Both original full-value caches remain inputs;
no independently acquired common full-cubic Owner replaces either one.
-/
def agrees_of_base_eq (left : Reading actual first firstInside) (right : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site)
    (point_eq : (point site parameter 2 (Waist.direction quarter first) positive).base =
      (point site parameter 2 (Waist.direction quarter last) positive).base) :
    NamedEquivalent left.lift.value.name right.lift.value.name := by
  have ordinate := point_two_ordinate_eq site parameter (Waist.direction quarter first)
    (Waist.direction quarter last) positive regular point_eq
  have normalized : NamedEquivalent
      (Coherence.exact (point site parameter 2 (Waist.direction quarter first) positive).ordinate).name
      (Coherence.exact (point site parameter 2 (Waist.direction quarter last) positive).ordinate).name := by
    rewrite [ordinate]
    exact NamedEquivalent.refl _
  rewrite [left.lift.value_eq, right.lift.value_eq]
  exact Name.Coherent.Arithmetic.Product.Congruence.coherentMul_respects
    left.lift.unitRoot.value right.lift.unitRoot.value
    (Coherence.exact (point site parameter 2 (Waist.direction quarter first) positive).ordinate)
    (Coherence.exact (point site parameter 2 (Waist.direction quarter last) positive).ordinate)
    (unit_values_of_base_eq left right point_eq) normalized

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Reading
