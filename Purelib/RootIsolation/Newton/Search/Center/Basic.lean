module
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Restriction
public import Purelib.Geometry.Rational.Box.Band.Bounds
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Boundary.Lines
public import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Gaussian.Basic
public import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.RootIsolation.State.WindingOne.Basic

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Checked shortcuts for winding-one refinement

Newton iteration supplies candidates, not a convergence assumption.  A
candidate is accepted only after exact finite checks of strict containment,
the requested diagonal bound and winding four.  Eliminant-safe sides supply
the same ambient and boundary clearances as the total extractor.  A bounded
unsuccessful search delegates to the original total track.
-/

namespace Purelib.RootIsolation.Newton.Search.Center.Basic

/-- Check one proposed centre.  No assertion about Newton convergence enters
the return type: all accepted geometry and winding are checked directly. -/
def checkCenter {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {ambient : Box} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (center : Gaussian.Basic.Canonical)
    (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination := .canonical elimination) :
    Option (Refinement current epsilon) :=
  let margin := min (center.re - current.box.xLower)
    (min (current.box.xUpper - center.re)
      (min (center.im - current.box.yLower) (current.box.yUpper - center.im)))
  let radius := min (epsilon / 8) (margin / 4)
  if positive : 0 < radius then
    let band := Elimination.Axis.Band.selectedBand elimination center radius positive
    if strict : band.box.StrictInterior current.box then
      if accurate : band.box.diagonalSq ≤ epsilon ^ 2 then
        if winding : Winding.Box.Basic.quadrupledBoxWinding p band.box = 4 then
          let nested := (Geometry.Rational.Box.Refinement.StrictInterior.refines strict).trans current.refinesAmbient
          let left := clearances.vertical ambient band.box.xLower
            (Elimination.Axis.Band.selectedBand_left_nonzero elimination center positive)
          let right := clearances.vertical ambient band.box.xUpper
            (Elimination.Axis.Band.selectedBand_right_nonzero elimination center positive)
          let bottom := clearances.horizontal ambient band.box.yLower
            (Elimination.Axis.Band.selectedBand_bottom_nonzero elimination center positive)
          let top := clearances.horizontal ambient band.box.yUpper
            (Elimination.Axis.Band.selectedBand_top_nonzero elimination center positive)
          some
            { state :=
                { box := band.box
                  refinesAmbient := nested
                  proper := band.proper positive
                  clearance := Clearance.Box.Boundary.Lines.boundaryOfLines (left.restrict nested)
                    (right.restrict nested) (bottom.restrict nested) (top.restrict nested)
                  rawWindingFour := winding
                  ambientLeftClearance := left
                  ambientRightClearance := right
                  ambientBottomClearance := bottom
                  ambientTopClearance := top }
              strict := strict
              accurate := accurate }
        else none
      else none
    else none
  else none

/-- Clearance construction cannot change acceptance or the selected box.
The complete states need not be equal: their certified lower bounds can
differ, and those bounds are executable data. -/
theorem checkCenter_box_eq {p :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) (epsilon : Fraction.Rational)
    (center : Gaussian.Basic.Canonical) (left right : Clearance.Box.Line.Elimination.Provider.AxisClearances
      elimination) :
    (checkCenter elimination current epsilon center left).map (fun result =>
      result.state.box) =
      (checkCenter elimination current epsilon center right).map (fun result =>
        result.state.box) := by
  unfold checkCenter
  dsimp only
  split
  · split
    · split
      · split <;> rfl
      · rfl
    · rfl
  · rfl
end Purelib.RootIsolation.Newton.Search.Center.Basic

end
