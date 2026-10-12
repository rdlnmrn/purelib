module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Bounds.Radius
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Square.Centered.Interior
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Boundary.Lines
import Purelib.Polynomial.Clearance.Box.Line.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Elimination.Band
import Purelib.Polynomial.Clearance.Box.ProtectedRadius
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Anchor
import Purelib.Polynomial.Dense.Gaussian.Newton.Box.Budget.Squarefree
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Newton.Band
public import Purelib.RootIsolation.Newton.Band.Basic
public import Purelib.RootIsolation.Newton.Extraction.Build
import Purelib.RootIsolation.State.Raw
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Clearance.Box.Line.Restriction
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
public import Purelib.Geometry.Rational.Box.Band.Bounds
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.RootIsolation.Newton.Extraction.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Choice-free eliminant-safe Newton bands

Four bounded eliminant searches choose axis-parallel sides at distances
between `r` and `2r` from an extracted Newton center.  The sides carry
full-line Bézout clearances, while finite Taylor estimates transfer affine
winding four to the original polynomial on the selected rectangle.
-/

namespace Purelib.RootIsolation.Newton.Band.Build

/-- Run source refinement, Newton computation, and four bounded eliminant
searches to obtain a globally partition-safe winding-four box. -/
def extract
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box} {degreeBound :
      Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (squarefree : Dense.Gaussian.Squarefree.Basic.SquarefreeCertificate p)
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (current : State.Raw.RawWindingState p ambient) {epsilon : Fraction.Rational}
    (epsilonPositive : 0 < epsilon) : Newton.Band.Basic.Output squarefree current epsilon := open Purelib in by
  let core := Newton.Extraction.Build.extract degreeAtLeastTwo
    squarefree elimination current epsilonPositive
  let source := core.source
  let r := Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius squarefree current.box current.clearance epsilon
  have radius_eq : core.radius = r := rfl
  let center := Dense.Gaussian.Newton.Box.Anchor.anchorNewtonCenter p source.box
  have radiusPositive : 0 < r :=
    Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius_pos squarefree current.clearance current.proper
      epsilonPositive
  let band := Elimination.Axis.Band.selectedBand elimination center r radiusPositive
  have twoPositive : (0 : Fraction.Rational) < 2 :=
    Fraction.Cast.Order.natCast_pos_direct (n := 2) (by decide)
  have twiceRadiusPositive : 0 < 2 * r :=
    Fraction.Order.Arithmetic.mul_pos_direct twoPositive radiusPositive
  have twiceRadiusNonnegative : 0 ≤ 2 * r := twiceRadiusPositive.le
  have twiceRadiusLeProtected :
      2 * r ≤ Clearance.Box.ProtectedRadius.protectedBoundaryRadius p current.box current.clearance :=
    Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius_twice_le_protected squarefree current.box
      current.clearance epsilon
  have radiusLeTwice : r ≤ 2 * r := (Data.Rat.Bounds.Radius.radius_lt_twice radiusPositive).le
  have radiusSquareLeTwice : r ^ 2 ≤ (2 * r) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radiusLeTwice 2
  have displacementForOuter :
      Data.Gaussian.Norm.Basic.normSq (center - source.box.anchor) ≤ (2 * r) ^ 2 :=
    core.displacementSmall.trans radiusSquareLeTwice
  let outerSquare := Box.Square.Centered.Affine.centeredSquare center (2 * r) twiceRadiusNonnegative
  have outerStrict : outerSquare.StrictInterior current.box :=
    Box.Square.Centered.Interior.centeredSquare_strictInterior twiceRadiusPositive
      twiceRadiusLeProtected core.stripBounds displacementForOuter
  have bandRefinesOuter : band.box.Refines outerSquare := by
    exact band.refines_outerSquare radiusPositive.le
  have bandStrict : band.box.StrictInterior current.box :=
    Geometry.Rational.Box.Refinement.StrictInterior.of_refines outerStrict bandRefinesOuter
  have bandRefinesCurrent : band.box.Refines current.box := Geometry.Rational.Box.Refinement.StrictInterior.refines
      bandStrict
  have bandRefinesAmbient : band.box.Refines ambient :=
    bandRefinesCurrent.trans current.refinesAmbient
  have bandProper : band.box.Proper := band.proper radiusPositive
  let leftLine := Clearance.Box.Line.Elimination.Band.selectedBandLeftClearance elimination current.box center
    radiusPositive
  let rightLine := Clearance.Box.Line.Elimination.Band.selectedBandRightClearance elimination current.box center
    radiusPositive
  let bottomLine := Clearance.Box.Line.Elimination.Band.selectedBandBottomClearance elimination current.box center
    radiusPositive
  let topLine := Clearance.Box.Line.Elimination.Band.selectedBandTopClearance elimination current.box center
    radiusPositive
  let ambientLeftLine := Clearance.Box.Line.Elimination.Band.selectedBandLeftClearance elimination ambient center
    radiusPositive
  let ambientRightLine := Clearance.Box.Line.Elimination.Band.selectedBandRightClearance elimination ambient center
    radiusPositive
  let ambientBottomLine := Clearance.Box.Line.Elimination.Band.selectedBandBottomClearance elimination ambient center
    radiusPositive
  let ambientTopLine := Clearance.Box.Line.Elimination.Band.selectedBandTopClearance elimination ambient center
    radiusPositive
  let bandClearance : Clearance.Box.Boundary.Basic.BoundaryClearance p band.box :=
    Clearance.Box.Boundary.Lines.boundaryOfLines
    (Clearance.Box.Line.Basic.VerticalLineClearance.restrict leftLine bandRefinesCurrent)
    (Clearance.Box.Line.Basic.VerticalLineClearance.restrict rightLine bandRefinesCurrent)
    (Clearance.Box.Line.Basic.HorizontalLineClearance.restrict bottomLine bandRefinesCurrent)
    (Clearance.Box.Line.Basic.HorizontalLineClearance.restrict topLine bandRefinesCurrent)
  have windingFour : Winding.Box.Basic.quadrupledBoxWinding p band.box = 4 :=
    Winding.Box.Newton.Band.quadrupledBoxWinding_eq_four_of_newtonBand degreeAtLeastTwo core.newton
      source.refinesAmbient radiusPositive band bandRefinesCurrent
      core.displacementSmall core.bandTaylorSmall
  have radiusEighth : r ≤ (1 / 8 : Fraction.Rational) * epsilon :=
    Dense.Gaussian.Newton.Box.Budget.Squarefree.extractionRadius_le_eighth squarefree current.box current.clearance
      epsilon
  have radiusSquare : r ^ 2 ≤ ((1 / 8 : Fraction.Rational) * epsilon) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct radiusPositive.le
      radiusEighth 2
  have thirtyTwoNonnegative : (0 : Fraction.Rational) ≤ 32 :=
    (Fraction.Cast.Order.natCast_pos_direct
      (n := 32) (by decide)).le
  have epsilonSquareNonnegative :=
    Fraction.Order.Arithmetic.sq_nonneg_direct epsilon
  have halfSquare : (1 / 2 : Fraction.Rational) * epsilon ^ 2 ≤ epsilon ^ 2 := by
    calc
      (1 / 2 : Fraction.Rational) * epsilon ^ 2 ≤ 1 * epsilon ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          (show (1 / 2 : Fraction.Rational) ≤ 1 by decide)
          epsilonSquareNonnegative
      _ = epsilon ^ 2 := by ring1
  have diagonalHalf :
      band.box.diagonalSq ≤ (1 / 2 : Fraction.Rational) * epsilon ^ 2 := by
    have coefficientIdentity :
        (32 : Fraction.Rational) * (1 / 8) ^ 2 = 1 / 2 := by
      have eightNonzero : (8 : Fraction.Rational) ≠ 0 :=
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide)).ne'
      have twoNonzero : (2 : Fraction.Rational) ≠ 0 :=
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 2) (by decide)).ne'
      have eighthCancel : (1 / 8 : Fraction.Rational) * 8 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne 1 8 eightNonzero
      have halfCancel : (1 / 2 : Fraction.Rational) * 2 = 1 :=
        Fraction.Field.div_mul_cancel_of_ne 1 2 twoNonzero
      apply Fraction.Field.mul_right_cancel_of_ne twoNonzero
      calc
        ((32 : Fraction.Rational) * (1 / 8) ^ 2) * 2 =
            ((1 / 8 : Fraction.Rational) * 8) * ((1 / 8) * 8) := by ring1
        _ = 1 := by rw [eighthCancel]; ring1
        _ = (1 / 2 : Fraction.Rational) * 2 := halfCancel.symm
    calc
      band.box.diagonalSq ≤ 32 * r ^ 2 := band.diagonalSq_le radiusPositive
      _ ≤ 32 * ((1 / 8 : Fraction.Rational) * epsilon) ^ 2 :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          radiusSquare thirtyTwoNonnegative
      _ = (32 * (1 / 8 : Fraction.Rational) ^ 2) * epsilon ^ 2 := by ring1
      _ = (1 / 2 : Fraction.Rational) * epsilon ^ 2 := by
        rw [coefficientIdentity]
  have diagonal : band.box.diagonalSq ≤ epsilon ^ 2 :=
    diagonalHalf.trans halfSquare
  exact
    { source := source
      radius := r
      radiusPositive := radiusPositive
      band := band
      newton := core.newton
      displacementSmall := by
        rw [← radius_eq]
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using core.displacementSmall
      strictCurrent := bandStrict
      refinesAmbient := bandRefinesAmbient
      proper := bandProper
      leftLineClearance := leftLine
      rightLineClearance := rightLine
      bottomLineClearance := bottomLine
      topLineClearance := topLine
      ambientLeftClearance := ambientLeftLine
      ambientRightClearance := ambientRightLine
      ambientBottomClearance := ambientBottomLine
      ambientTopClearance := ambientTopLine
      clearance := bandClearance
      rawWindingFour := windingFour
      diagonalSq_le_half := diagonalHalf
      diagonalSq_le := diagonal }

end Purelib.RootIsolation.Newton.Band.Build

end
