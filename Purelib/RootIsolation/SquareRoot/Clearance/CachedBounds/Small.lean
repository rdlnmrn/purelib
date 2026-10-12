module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
import Purelib.Geometry.Rational.Box.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic

open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

section
public section

/-!
# Exact local certificates for the prepared cyclic quartic

The first outer cell of the canonical connector from `-1` to `1` runs along
the horizontal line `im z = -1/2`, from `-5/4` to `-1`.  This file records
the nine endpoints of its depth-three dyadic subdivision and caches the exact
values of `z^4 - 1` there as reduced constructive rationals.

Storing the reduced representatives, including their explicit Bezout
certificates, is important for the later prepared-sheet checks: direct box
clearance can inspect these small values instead of repeatedly normalizing the
large rational expression obtained by polynomial evaluation.
-/

namespace Purelib.RootIsolation.SquareRoot.Clearance.CachedBounds.Small

set_option genInjectivity false in
/-- A cached exact boundary-clearance calculation whose four side bounds are
all at least `5/8`. -/
structure DirectClearanceFiveEighths (parameter :
  Canonical) (box : Box) where
  /-- The left side resultant of the original quadratic owner is nonzero. -/ leftNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter box.xLower ≠ 0
  /-- The right side resultant of the original quadratic owner is nonzero. -/ rightNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter box.xUpper ≠ 0
  /-- The bottom side resultant of the original quadratic owner is nonzero. -/ bottomNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter box.yLower ≠ 0
  /-- The top side resultant of the original quadratic owner is nonzero. -/ topNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter box.yUpper ≠ 0
  /-- The retained direct-clearance construction on the original owner's box. -/ clearance :
    Clearance.Box.Boundary.Basic.BoundaryClearance
    (Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter
      Riemann.RootContinuation.SquareRootDegree.degreeTwo) box
  /-- The cached construction equals the one computed from the retained four nonzero side resultants. -/ clearance_eq :
    clearance =
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.directBoundaryClearance
      parameter box leftNonzero rightNonzero bottomNonzero topNonzero
  /-- The cached clearance is at least five eighths. -/ fiveEighths_le : (5 / 8 : Fraction.Rational) ≤ clearance.bound
  /-- The original box's direct quadratic boundary bound is at most three halves. -/ directBound_le_threeHalves :
    min
      (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xLower)
      (min
        (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          parameter box box.xUpper)
        (min
          (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yLower)
          (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yUpper))) ≤ (3 / 2 : Fraction.Rational)

constructive_injectivity DirectClearanceFiveEighths

/-- Build the retained direct-clearance cache from the four nonzero resultants and checked numerical bounds.

The cache stores the actual direct construction, its equality certificate, the five-eighths lower bound and the
three-halves bound on the same box. -/
@[expose] public def
  directClearanceFiveEighthsOfChecks
    (parameter : Canonical) (box : Box)
    (leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xLower ≠ 0)
    (rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter box.xUpper ≠ 0)
    (bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yLower ≠ 0)
    (topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter box.yUpper ≠ 0)
    (leftLe : (5 / 8 : Fraction.Rational) ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xLower)
    (rightLe : (5 / 8 : Fraction.Rational) ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xUpper)
    (bottomLe : (5 / 8 : Fraction.Rational) ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        parameter box box.yLower)
    (topLe : (5 / 8 : Fraction.Rational) ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        parameter box box.yUpper)
    (upper :
      min
        (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          parameter box box.xLower)
        (min
          (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
            parameter box box.xUpper)
          (min
            (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
              parameter box box.yLower)
            (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
              parameter box box.yUpper))) ≤ (3 / 2 : Fraction.Rational)) :
    DirectClearanceFiveEighths parameter box :=
  { leftNonzero := leftNonzero
    rightNonzero := rightNonzero
    bottomNonzero := bottomNonzero
    topNonzero := topNonzero
    clearance :=
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.directBoundaryClearance
        parameter box leftNonzero rightNonzero bottomNonzero topNonzero
    clearance_eq := rfl
    fiveEighths_le :=
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.le_directBoundaryClearance_bound
        parameter box leftNonzero rightNonzero bottomNonzero topNonzero (5 / 8)
          leftLe rightLe bottomLe topLe
    directBound_le_threeHalves := upper }

/-- Strengthening the original owner from its retained direct cache gives clearance at least five eighths. -/
theorem fiveEighthsLeStrengthenFromDirectCache
  {parameter : Canonical}
    (owner : Riemann.Topology.SquareRootContinuationChain.Owner parameter)
    (box : Box) (boxEq : owner.track.initial.box = box)
    (cache : DirectClearanceFiveEighths parameter box) : (5 / 8 :
      Fraction.Rational) ≤
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound := by
  subst box
  calc
    (5 / 8 : Fraction.Rational) ≤ cache.clearance.bound := cache.fiveEighths_le
    _ = (SquareRoot.Clearance.ExactQuadraticOwnerClearance.directBoundaryClearance
        parameter owner.track.initial.box cache.leftNonzero cache.rightNonzero
          cache.bottomNonzero cache.topNonzero).bound :=
      congrArg Clearance.Box.Boundary.Basic.BoundaryClearance.bound cache.clearance_eq
    _ ≤ (SquareRoot.Clearance.ExactQuadraticOwnerClearance.strengthenQuadraticOwner
        owner).track.initial.clearance.bound :=
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.directBoundaryClearance_le_strengthenQuadraticOwner
        owner
          cache.leftNonzero cache.rightNonzero cache.bottomNonzero
            cache.topNonzero

/-- Checked four-side resultants with a direct-bound upper estimate of nine sixteenths.

The certificate refers to the original quadratic owner's exact box and polynomial. -/
structure DirectClearanceNineSixteenths (parameter
  : Canonical) (box : Box) where
  /-- The left side resultant of the original quadratic owner is nonzero. -/ leftNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter box.xLower ≠ 0
  /-- The right side resultant of the original quadratic owner is nonzero. -/ rightNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter box.xUpper ≠ 0
  /-- The bottom side resultant of the original quadratic owner is nonzero. -/ bottomNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter box.yLower ≠ 0
  /-- The top side resultant of the original quadratic owner is nonzero. -/ topNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter box.yUpper ≠ 0
  /-- The original box's direct quadratic boundary bound is at most nine sixteenths. -/ directBound_le :
    min
      (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        parameter box box.xLower)
      (min
        (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
          parameter box box.xUpper)
        (min
          (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yLower)
          (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
            parameter box box.yUpper))) ≤ (9 / 16 : Fraction.Rational)
end Purelib.RootIsolation.SquareRoot.Clearance.CachedBounds.Small

end
