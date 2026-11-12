module

public import Purelib.Curves.Legendre.Paths
public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Geometry.Path.Gaussian.Lifted.Refinement
public import Purelib.Geometry.Rational.Box.Gaussian.Corners
public import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Data.Rat.Fraction.Order.Basic

/-!
# A nonempty Legendre cycle on one continued sheet

The cubic at parameter two is nonzero at coordinate three. Its independently
selected root owner supplies an aligned seed and a computed positive regular
box. Four retained corner owners are continued from this same seed owner.
The displayed lifted path traverses the four sides of that actual box.
-/

public section

namespace Purelib.Examples.Curves.Legendre.RegularCycle

open Purelib.Curves.Legendre
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (ObservationNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic
open Purelib.Geometry.Path.Gaussian.Lifted.Closed (ClosedLiftedPath)
open Purelib.Geometry.Path.Gaussian.Lifted.Refinement (LiftedCycleRefinement)
open Purelib.Geometry.Rational.Box.Gaussian
open Purelib.Data.Rat

/-- The original nonzero cubic value at coordinate three. -/
theorem center_nonzero : (Paths.polynomial (2 : Canonical)).eval (3 : Canonical) ≠ 0 := by
  decide

/-- The retained observation site computes all bounds from the original cubic and coordinate. -/
@[expose] def site : ObservationNeighborhood (Paths.polynomial (2 : Canonical)) 2 :=
  ObservationNeighborhood.ofPoint _ 2 (3 : Canonical) center_nonzero

/-- Independently isolate the requested original square-root sheet at the displayed center. -/
@[expose] def origin (sheet : Fin 2) : Owner ((Paths.polynomial (2 : Canonical)).eval site.center) :=
  Owner.independent center_nonzero sheet

/-- Compute a positive continuation box from the same original center owner. -/
@[expose] def patch (sheet : Fin 2) : ContinuedNeighborhood (Paths.polynomial (2 : Canonical)) 2 :=
  ContinuedNeighborhood.ofOwner site (origin sheet)

/-- The original lower-left corner with its retained sheet label. -/
@[expose] def lowerLeft (sheet : Fin 2) : LiftedPoint 2 :=
  ⟨Corners.lowerLeft (patch sheet).box, sheet⟩

/-- The original lower-right corner with its retained sheet label. -/
@[expose] def lowerRight (sheet : Fin 2) : LiftedPoint 2 :=
  ⟨Corners.lowerRight (patch sheet).box, sheet⟩

/-- The original upper-right corner with its retained sheet label. -/
@[expose] def upperRight (sheet : Fin 2) : LiftedPoint 2 :=
  ⟨Corners.upperRight (patch sheet).box, sheet⟩

/-- The original upper-left corner with its retained sheet label. -/
@[expose] def upperLeft (sheet : Fin 2) : LiftedPoint 2 :=
  ⟨Corners.upperLeft (patch sheet).box, sheet⟩

/-- The lower-left corner lies in the actual computed continuation box. -/
theorem lowerLeft_inside (sheet : Fin 2) : (patch sheet).box.Contains (lowerLeft sheet).coordinate :=
  ⟨Fraction.Order.Basic.le_refl _, (patch sheet).box.x_valid, Fraction.Order.Basic.le_refl _, (patch sheet).box.y_valid⟩

/-- The lower-right corner lies in the actual computed continuation box. -/
theorem lowerRight_inside (sheet : Fin 2) : (patch sheet).box.Contains (lowerRight sheet).coordinate :=
  ⟨(patch sheet).box.x_valid, Fraction.Order.Basic.le_refl _, Fraction.Order.Basic.le_refl _, (patch sheet).box.y_valid⟩

/-- The upper-right corner lies in the actual computed continuation box. -/
theorem upperRight_inside (sheet : Fin 2) : (patch sheet).box.Contains (upperRight sheet).coordinate :=
  ⟨(patch sheet).box.x_valid, Fraction.Order.Basic.le_refl _, (patch sheet).box.y_valid, Fraction.Order.Basic.le_refl _⟩

/-- The upper-left corner lies in the actual computed continuation box. -/
theorem upperLeft_inside (sheet : Fin 2) : (patch sheet).box.Contains (upperLeft sheet).coordinate :=
  ⟨Fraction.Order.Basic.le_refl _, (patch sheet).box.x_valid, (patch sheet).box.y_valid, Fraction.Order.Basic.le_refl _⟩

/-- Cache the lower-left endpoint owner continued from the original seed. -/
@[expose] def lowerLeftRoot (sheet : Fin 2) :
    ContinuedNeighborhood.Point (patch sheet) (lowerLeft sheet).coordinate :=
  ContinuedNeighborhood.Point.acquire (patch sheet) _ (lowerLeft_inside sheet)

/-- Cache the lower-right endpoint owner continued from the original seed. -/
@[expose] def lowerRightRoot (sheet : Fin 2) :
    ContinuedNeighborhood.Point (patch sheet) (lowerRight sheet).coordinate :=
  ContinuedNeighborhood.Point.acquire (patch sheet) _ (lowerRight_inside sheet)

/-- Cache the upper-right endpoint owner continued from the original seed. -/
@[expose] def upperRightRoot (sheet : Fin 2) :
    ContinuedNeighborhood.Point (patch sheet) (upperRight sheet).coordinate :=
  ContinuedNeighborhood.Point.acquire (patch sheet) _ (upperRight_inside sheet)

/-- Cache the upper-left endpoint owner continued from the original seed. -/
@[expose] def upperLeftRoot (sheet : Fin 2) :
    ContinuedNeighborhood.Point (patch sheet) (upperLeft sheet).coordinate :=
  ContinuedNeighborhood.Point.acquire (patch sheet) _ (upperLeft_inside sheet)

/-- Preserve the same sheet along a retained edge in the continued box. -/
@[expose] def side {start finish : LiftedPoint 2} (sameSheet : start.sheet = finish.sheet) :
    LiftedCell start finish :=
  ⟨Purelib.Data.Fin.Bijection.identity 2, sameSheet⟩

/-- The original lower side of the retained continuation box on the selected sheet. -/
@[expose] def lowerSide (sheet : Fin 2) : LiftedCell (lowerLeft sheet) (lowerRight sheet) := side rfl

/-- The original right side of the retained continuation box on the selected sheet. -/
@[expose] def rightSide (sheet : Fin 2) : LiftedCell (lowerRight sheet) (upperRight sheet) := side rfl

/-- The original upper side of the retained continuation box on the selected sheet. -/
@[expose] def upperSide (sheet : Fin 2) : LiftedCell (upperRight sheet) (upperLeft sheet) := side rfl

/-- The original left side of the retained continuation box on the selected sheet. -/
@[expose] def leftSide (sheet : Fin 2) : LiftedCell (upperLeft sheet) (lowerLeft sheet) := side rfl

/-- The four original box sides form a closed path on the selected continued sheet. -/
@[expose] def loop (sheet : Fin 2) : ClosedLiftedPath 2 :=
  { basepoint := lowerLeft sheet
    path := .cons (lowerSide sheet)
      (.cons (rightSide sheet)
        (.cons (upperSide sheet)
          (.cons (leftSide sheet) (.nil _)))) }

/-- Every finite representative retains the same nonempty four-sided lifted loop. -/
@[expose] def cycle (sheet : Fin 2) : LiftedCycleRefinement 2 :=
  ⟨fun _ => loop sheet⟩

/-- Every displayed representative has four actual cells. -/
theorem cycle_cellCount (sheet : Fin 2) (index : Nat) : ((cycle sheet).liftedPath index).cellCount = 4 := rfl

/-- The first side has distinct coordinates because the computed box has positive width. -/
theorem first_side_nontrivial (sheet : Fin 2) :
    (lowerLeft sheet).coordinate ≠ (lowerRight sheet).coordinate := by
  intro equal
  have realEqual := congrArg Canonical.re equal
  change (patch sheet).box.xLower = (patch sheet).box.xUpper at realEqual
  have strict := (patch sheet).box_proper.1
  rewrite [realEqual] at strict
  exact lt_irrefl _ strict

end Purelib.Examples.Curves.Legendre.RegularCycle

end
