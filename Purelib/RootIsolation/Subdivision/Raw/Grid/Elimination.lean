module
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Winding.Box.Grid.Four
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Clearance
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Bounds.Contraction
public import Purelib.Polynomial.Clearance.Box.Grid.Four.Elimination
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Elimination.Axis.Cuts
import Purelib.RootIsolation.State.Raw
public import Purelib.RootIsolation.Subdivision.Raw.Grid

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
import Purelib.Polynomial.Clearance.Box.Refinement.Contracting
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Winding.Box.Basic

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.Raw (RawWindingState)

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
/-!
# Choice-free raw-winding safe subdivision

Central-third eliminant-certified cuts split a clear box into four clear
children.  A finite first-nonzero scan retains raw winding while every round
contracts squared diagonal by `4/9`.
-/

@[expose] public section

namespace Purelib.RootIsolation.Subdivision.Raw.Grid.Elimination

/-- One executable central safe-cut grid. -/
def safeRawFourGrid
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) : Subdivision.Raw.Grid.RawFourGrid state := by
  let grid := Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination state.box state.proper
  let clearances := grid.childClearances state.clearance
  have xSpec := Elimination.Axis.Cuts.verticalSafeCoordinate_spec elimination state.box state.proper
  have ySpec := Elimination.Axis.Cuts.horizontalSafeCoordinate_spec elimination state.box state.proper
  have xContract :=
    Elimination.Axis.Cuts.verticalSafeCoordinate_contraction elimination state.box state.proper
  have yContract :=
    Elimination.Axis.Cuts.horizontalSafeCoordinate_contraction elimination state.box state.proper
  have lowerLeftContract : grid.lowerLeft.diagonalSq ≤
      (4 / 9 : Fraction.Rational) * state.box.diagonalSq := by
    apply Box.Bounds.Contraction.diagonalSq_le_four_ninths
    · change grid.xCut - state.box.xLower ≤
        (2 / 3 : Fraction.Rational) * state.box.widthX
      exact xContract.1.le
    · change grid.yCut - state.box.yLower ≤
        (2 / 3 : Fraction.Rational) * state.box.widthY
      exact yContract.1.le
  have upperLeftContract : grid.upperLeft.diagonalSq ≤
      (4 / 9 : Fraction.Rational) * state.box.diagonalSq := by
    apply Box.Bounds.Contraction.diagonalSq_le_four_ninths
    · change grid.xCut - state.box.xLower ≤
        (2 / 3 : Fraction.Rational) * state.box.widthX
      exact xContract.1.le
    · change state.box.yUpper - grid.yCut ≤
        (2 / 3 : Fraction.Rational) * state.box.widthY
      exact yContract.2.le
  have lowerRightContract : grid.lowerRight.diagonalSq ≤
      (4 / 9 : Fraction.Rational) * state.box.diagonalSq := by
    apply Box.Bounds.Contraction.diagonalSq_le_four_ninths
    · change state.box.xUpper - grid.xCut ≤
        (2 / 3 : Fraction.Rational) * state.box.widthX
      exact xContract.2.le
    · change grid.yCut - state.box.yLower ≤
        (2 / 3 : Fraction.Rational) * state.box.widthY
      exact yContract.1.le
  have upperRightContract : grid.upperRight.diagonalSq ≤
      (4 / 9 : Fraction.Rational) * state.box.diagonalSq := by
    apply Box.Bounds.Contraction.diagonalSq_le_four_ninths
    · change state.box.xUpper - grid.xCut ≤
        (2 / 3 : Fraction.Rational) * state.box.widthX
      exact xContract.2.le
    · change state.box.yUpper - grid.yCut ≤
        (2 / 3 : Fraction.Rational) * state.box.widthY
      exact yContract.2.le
  exact
    { lowerLeft :=
        { box := grid.lowerLeft
          refinesParent := grid.lowerLeft_refines
          refinesAmbient := grid.lowerLeft_refines.trans state.refinesAmbient
          proper := ⟨xSpec.2.1, ySpec.2.1⟩
          clearance := clearances.1
          contracts := lowerLeftContract }
      upperLeft :=
        { box := grid.upperLeft
          refinesParent := grid.upperLeft_refines
          refinesAmbient := grid.upperLeft_refines.trans state.refinesAmbient
          proper := ⟨xSpec.2.1, ySpec.2.2⟩
          clearance := clearances.2.1
          contracts := upperLeftContract }
      lowerRight :=
        { box := grid.lowerRight
          refinesParent := grid.lowerRight_refines
          refinesAmbient := grid.lowerRight_refines.trans state.refinesAmbient
          proper := ⟨xSpec.2.2, ySpec.2.1⟩
          clearance := clearances.2.2.1
          contracts := lowerRightContract }
      upperRight :=
        { box := grid.upperRight
          refinesParent := grid.upperRight_refines
          refinesAmbient := grid.upperRight_refines.trans state.refinesAmbient
          proper := ⟨xSpec.2.2, ySpec.2.2⟩
          clearance := clearances.2.2.2
          contracts := upperRightContract }
      additive := grid.winding_additive }

/-- The retained lower-left child is exactly the corresponding box of the original eliminant-safe four-grid. -/
@[simp] theorem safeRawFourGrid_lowerLeft_box
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (safeRawFourGrid elimination state).lowerLeft.box =
      (Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination state.box state.proper).lowerLeft := rfl

/-- The retained upper-left child is exactly the corresponding box of the original eliminant-safe four-grid. -/
@[simp] theorem safeRawFourGrid_upperLeft_box
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (safeRawFourGrid elimination state).upperLeft.box =
      (Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination state.box state.proper).upperLeft := rfl

/-- The retained lower-right child is exactly the corresponding box of the original eliminant-safe four-grid. -/
@[simp] theorem safeRawFourGrid_lowerRight_box
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (safeRawFourGrid elimination state).lowerRight.box =
      (Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination state.box state.proper).lowerRight := rfl

/-- The retained upper-right child is exactly the corresponding box of the original eliminant-safe four-grid. -/
@[simp] theorem safeRawFourGrid_upperRight_box
    {p : CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
    (state : RawWindingState p ambient) :
    (safeRawFourGrid elimination state).upperRight.box =
      (Clearance.Box.Grid.Four.Elimination.buildClearFourGrid elimination state.box state.proper).upperRight := rfl
end Purelib.RootIsolation.Subdivision.Raw.Grid.Elimination

end
