module

public import Purelib.RootIsolation.Owner.Local.Basic
public import Purelib.Geometry.Rational.Box.Square.Centered
public import Purelib.Geometry.Rational.Box.Outside
public import Purelib.Polynomial.Dense.Gaussian.Linear.Translated
public import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Clearance.Box.Boundary.Translated
import Purelib.Polynomial.Clearance.Box.Boundary.Operations
import Purelib.Polynomial.Winding.Box.Affine
import Purelib.Polynomial.Winding.Box.Affine.Outside
import Purelib.Polynomial.Winding.Box.Product

/-!
# Local owners of an original split quadratic

A positive square centered at the first root and a strict outside side for
the second root give a winding-one owner of the original two-factor product.
The boundary bound is the product of the retained two separations.
-/

public section

namespace Purelib.RootIsolation.Owner.Local.Basic.LocalOwner

open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational
open Purelib.Polynomial

/-- Construct a local owner for the original first root of a split quadratic.

The supplied positive radius centers the retained square at that original
root. The second root's original outside side supplies its clearance and
zero winding; product winding supplies winding one without root isolation.
-/
def ofSplitPair (first last : Canonical) {radius : Rat.Fraction.Rational} (positive : 0 < radius)
    (outside : (Box.Square.Centered.Affine.centeredSquare first radius positive.le).OutsideSide last) :
    Owner.Local.Basic.LocalOwner
      (Dense.Gaussian.Linear.Translated.translatedCoordinate first *
        Dense.Gaussian.Linear.Translated.translatedCoordinate last) := by
  let box := Box.Square.Centered.Affine.centeredSquare first radius positive.le
  let firstClearance := Clearance.Box.Boundary.Translated.translatedCoordinate_boundaryClearance first positive
  let lastClearance := Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_outside
    last outside
  have proper := Box.Square.Centered.centeredSquare_proper first positive
  exact
    { box := box
      proper := proper
      clearance := firstClearance.mul lastClearance
      rawWindingFour := by
        rewrite [Winding.Box.Product.quadrupledBoxWinding_mul_of_boundaryClearances
          _ _ box proper firstClearance lastClearance,
          Winding.Box.Affine.quadrupledBoxWinding_translatedCoordinate_centeredSquare first positive,
          Winding.Box.Affine.Outside.quadrupledBoxWinding_translatedCoordinate_of_outside proper outside]
        rfl }

/-- The split-pair constructor retains exactly the original first-root square. -/
theorem ofSplitPair_box (first last : Canonical) {radius : Rat.Fraction.Rational} (positive : 0 < radius)
    (outside : (Box.Square.Centered.Affine.centeredSquare first radius positive.le).OutsideSide last) :
    (ofSplitPair first last positive outside).box =
      Box.Square.Centered.Affine.centeredSquare first radius positive.le := by
  unfold ofSplitPair
  rfl

/-- The split-pair owner retains the product of the original radius square and second-root side margin. -/
theorem ofSplitPair_clearance_bound (first last : Canonical) {radius : Rat.Fraction.Rational} (positive : 0 < radius)
    (outside : (Box.Square.Centered.Affine.centeredSquare first radius positive.le).OutsideSide last) :
    (ofSplitPair first last positive outside).clearance.bound = radius ^ 2 * outside.margin := by
  change radius ^ 2 *
    (Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_outside last outside).bound = _
  rewrite [Clearance.Box.Boundary.Translated.Affine.translatedCoordinate_boundaryClearance_of_outside_bound]
  rfl

end Purelib.RootIsolation.Owner.Local.Basic.LocalOwner
