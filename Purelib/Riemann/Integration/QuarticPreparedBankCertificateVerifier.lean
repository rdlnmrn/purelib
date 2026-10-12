module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Order
import Purelib.Algebra.Ring.IntCast
import Purelib.Polynomial.Power.Gaussian
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Cast.Imaginary
import Purelib.Data.Gaussian.Certificate.Raw
import Purelib.Data.Gaussian.Constants
public import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Certificate.Raw
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
public import Purelib.Geometry.Rational.Box.Certificate
import Purelib.Geometry.Rational.Box.Intervals
import Purelib.Polynomial.Dense.Gaussian.Bounds.Path.Majorant
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Winding.Box.Basic

import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticAxisElimination
import Purelib.RootIsolation.SquareRoot.Clearance.QuadraticLineClearance
public import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Mathlib.Algebra.Group.Int.Defs
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Nat.Coprime.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Clearance.Box.Grid.Four.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

section

open Purelib.Data

open Purelib

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Verifier for generated quartic prepared-bank replay data

The external generator records only small rational observations made by the
executable prepared-bank checker.  This module gives that output a narrow,
proof-carrying format.  It does not trust the trace as a proof of continuation:
later bridge modules must still use the kernel-checked `prepared_eq_*` and
transport constructors to replay each recorded branch.
-/

namespace Purelib.Riemann.Integration.QuarticPreparedBankCertificateVerifier

/-- The interpreted Gaussian real coordinate is exactly its retained displayed rational value. -/
@[simp] private theorem gaussianDataToGaussian_re (value : Gaussian.Certificate.Raw.GaussianData) :
    value.toGaussian.re = value.re.toRational := rfl

/-- The interpreted Gaussian imaginary coordinate is exactly its retained displayed rational value. -/
@[simp] private theorem gaussianDataToGaussian_im (value : Gaussian.Certificate.Raw.GaussianData) :
    value.toGaussian.im = value.im.toRational := rfl

/-- The interpreted box's left coordinate is exactly the retained displayed fraction's rational value. -/
@[simp] private theorem rationalBoxDataToBox_xLower (value : Rational.Box.Certificate.RationalBoxData) :
    value.toBox.xLower = value.xLower.toRational := rfl

/-- The interpreted box's right coordinate is exactly the retained displayed fraction's rational value. -/
@[simp] private theorem rationalBoxDataToBox_xUpper (value : Rational.Box.Certificate.RationalBoxData) :
    value.toBox.xUpper = value.xUpper.toRational := rfl

/-- The interpreted box's bottom coordinate is exactly the retained displayed fraction's rational value. -/
@[simp] private theorem rationalBoxDataToBox_yLower (value : Rational.Box.Certificate.RationalBoxData) :
    value.toBox.yLower = value.yLower.toRational := rfl

/-- The interpreted box's top coordinate is exactly the retained displayed fraction's rational value. -/
@[simp] private theorem rationalBoxDataToBox_yUpper (value : Rational.Box.Certificate.RationalBoxData) :
    value.toBox.yUpper = value.yUpper.toRational := rfl

/-! ## Reduced representatives for executable replay

The ordinary generated certificate format deliberately stores displayed
fractions.  Finite winding searches are substantially cheaper when their
rational inputs also carry an already checked coprime representative.  These
small structures cache that calculation without caching any inequality or
geometric proposition. -/

set_option genInjectivity false in
/-- A generated reduced representative, including an explicit Bézout
witness for coprimality.

The positive denominator and retained integer Bézout coefficients certify coprimality of the exact numerator and
denominator. -/
structure ReducedRationalData where
  /-- The exact retained signed numerator. -/ numerator : Int
  /-- The exact retained natural denominator. -/ denominator : Nat
  /-- The retained denominator is strictly positive. -/ denominatorPositive : 0 < denominator
  /-- The retained integer Bézout coefficient for the numerator's absolute value. -/ bezoutLeft : Int
  /-- The retained integer Bézout coefficient for the denominator. -/ bezoutRight : Int
  /-- The retained coefficients express one as a combination of the absolute numerator and denominator. -/ bezout :
    bezoutLeft * (numerator.natAbs : Int) +
    bezoutRight * (denominator : Int) = 1

constructive_injectivity ReducedRationalData

namespace ReducedRationalData

/-- Construct the exact reduced rational from its retained numerator, denominator and Bézout witness. -/
@[expose] def toRational (value : ReducedRationalData) :
    Rat.Fraction.Rational where
  num := value.numerator
  den := value.denominator
  den_pos := value.denominatorPositive
  reduced := ⟨⟨value.bezoutLeft, value.bezoutRight, value.bezout⟩⟩

/-- Expose the same retained numerator and positive denominator as ordinary displayed rational data. -/
@[expose] def toRationalData (value : ReducedRationalData) : Data.Rat.Certificate.Raw.RationalData where
  numerator := value.numerator
  denominator := value.denominator
  denominatorPositive := value.denominatorPositive

/-- The reduced rational and its original displayed fraction denote exactly the same rational. -/
theorem toRational_eq_data (value : ReducedRationalData) :
    value.toRational = value.toRationalData.toRational := by
  apply Rat.Fraction.Field.mul_right_cancel_of_ne
    (Rat.Fraction.Cast.Order.natCast_pos_direct
      value.denominatorPositive).ne'
  calc
    value.toRational * (value.denominator : Rat.Fraction.Rational) =
        (value.numerator : Rat.Fraction.Rational) :=
      Rat.Fraction.Cast.representative_mul_den value.toRational
    _ = value.toRationalData.toRational *
          (value.denominator : Rat.Fraction.Rational) := by
      unfold Data.Rat.Certificate.Raw.RationalData.toRational toRationalData
      exact (Rat.Fraction.Field.div_mul_cancel_of_ne _ _
        (Rat.Fraction.Cast.Order.natCast_pos_direct
          value.denominatorPositive).ne').symm

end ReducedRationalData

set_option genInjectivity false in
/-- A Gaussian rational whose two coordinates retain checked reduced representatives.

Each coordinate retains its complete reduced rational record, including its denominator and explicit coprimality
witness. -/
structure ReducedGaussianData where
  /-- The retained reduced real coordinate. -/ re : ReducedRationalData
  /-- The retained reduced imaginary coordinate. -/ im : ReducedRationalData

constructive_injectivity ReducedGaussianData

namespace ReducedGaussianData

/-- Construct the Gaussian rational from its two retained reduced coordinates. -/
@[expose] def toGaussian (value : ReducedGaussianData) : Gaussian.Basic.Canonical :=
  ⟨value.re.toRational, value.im.toRational⟩

/-- Expose both retained reduced coordinates as displayed Gaussian fraction data. -/
@[expose] def toGaussianData (value : ReducedGaussianData) : Gaussian.Certificate.Raw.GaussianData :=
  ⟨value.re.toRationalData, value.im.toRationalData⟩

/-- The reduced Gaussian and its displayed coordinate data denote exactly the same value. -/
theorem toGaussian_eq_data (value : ReducedGaussianData) :
    value.toGaussian = value.toGaussianData.toGaussian := by
  apply Gaussian.Basic.ext
  · exact value.re.toRational_eq_data
  · exact value.im.toRational_eq_data

end ReducedGaussianData

set_option genInjectivity false in
/-- A rational box with checked reduced coordinates and retained coordinate-order witnesses.

The four reduced coordinates keep their positive denominators and the strict order of the original horizontal and
vertical endpoints. -/
structure ReducedRationalBoxData where
  /-- The original retained reduced left box coordinate. -/ xLower : ReducedRationalData
  /-- The original retained reduced right box coordinate. -/ xUpper : ReducedRationalData
  /-- The original retained reduced bottom box coordinate. -/ yLower : ReducedRationalData
  /-- The original retained reduced top box coordinate. -/ yUpper : ReducedRationalData
  /-- The checked cross-product order of the retained horizontal endpoints. -/ xValid :
    Data.Rat.Certificate.Raw.RationalData.Le xLower.toRationalData xUpper.toRationalData
  /-- The checked cross-product order of the retained vertical endpoints. -/ yValid :
    Data.Rat.Certificate.Raw.RationalData.Le yLower.toRationalData yUpper.toRationalData

constructive_injectivity ReducedRationalBoxData

namespace ReducedRationalBoxData

/-- Construct the exact rational box from the retained reduced coordinates and checked order witnesses. -/
@[expose] def toBox (box : ReducedRationalBoxData) : Rational.Box where
  xLower := box.xLower.toRational
  xUpper := box.xUpper.toRational
  yLower := box.yLower.toRational
  yUpper := box.yUpper.toRational
  x_valid := by
    rw [box.xLower.toRational_eq_data, box.xUpper.toRational_eq_data]
    exact Data.Rat.Certificate.Raw.RationalData.le_sound box.xValid
  y_valid := by
    rw [box.yLower.toRational_eq_data, box.yUpper.toRational_eq_data]
    exact Data.Rat.Certificate.Raw.RationalData.le_sound box.yValid

end ReducedRationalBoxData

set_option genInjectivity false in
/-- A reduced Gaussian linked by checked cross-products to displayed source
data.

Checked coordinate cross-products identify the reduced Gaussian with the retained displayed source, without selecting
another representative. -/
structure GaussianReductionData where
  /-- The original displayed input whose exact value is retained by the reduction. -/ original :
    Gaussian.Certificate.Raw.GaussianData
  /-- The checked reduced representative of the original displayed input. -/ reduced : ReducedGaussianData
  /-- Checked coordinate cross-products identify the reduced and original Gaussian data. -/ equal :
    Gaussian.Certificate.Raw.GaussianData.Eq (ReducedGaussianData.toGaussianData reduced) original

constructive_injectivity GaussianReductionData

namespace GaussianReductionData

/-- The checked reduced Gaussian represents exactly the original displayed value. -/
theorem sound (data : GaussianReductionData) :
    data.reduced.toGaussian = data.original.toGaussian := by
  rw [data.reduced.toGaussian_eq_data]
  exact Gaussian.Certificate.Raw.GaussianData.eq_sound data.equal

end GaussianReductionData

set_option genInjectivity false in
/-- A reduced box linked coordinatewise to an existing displayed box.

Four retained cross-product equalities identify the exact reduced endpoints with the original displayed box. -/
structure RationalBoxReductionData where
  /-- The original displayed input whose exact value is retained by the reduction. -/ original :
    Rational.Box.Certificate.RationalBoxData
  /-- The checked reduced representative of the original displayed input. -/ reduced : ReducedRationalBoxData
  /-- Checked cross-products identify the reduced left coordinate with the original displayed coordinate. -/
    xLowerMatches : Data.Rat.Certificate.Raw.RationalData.Eq
    (ReducedRationalData.toRationalData reduced.xLower) original.xLower
  /-- Checked cross-products identify the reduced right coordinate with the original displayed coordinate. -/
    xUpperMatches : Data.Rat.Certificate.Raw.RationalData.Eq
    (ReducedRationalData.toRationalData reduced.xUpper) original.xUpper
  /-- Checked cross-products identify the reduced bottom coordinate with the original displayed coordinate. -/
    yLowerMatches : Data.Rat.Certificate.Raw.RationalData.Eq
    (ReducedRationalData.toRationalData reduced.yLower) original.yLower
  /-- Checked cross-products identify the reduced top coordinate with the original displayed coordinate. -/
    yUpperMatches : Data.Rat.Certificate.Raw.RationalData.Eq
    (ReducedRationalData.toRationalData reduced.yUpper) original.yUpper

constructive_injectivity RationalBoxReductionData

namespace RationalBoxReductionData

/-- The checked reduced box is exactly the original displayed rational box. -/
theorem sound (data : RationalBoxReductionData) :
    data.reduced.toBox = data.original.toBox := by
  apply Rational.Box.ext
  · exact data.reduced.xLower.toRational_eq_data.trans
      (Data.Rat.Certificate.Raw.RationalData.eq_sound data.xLowerMatches)
  · exact data.reduced.xUpper.toRational_eq_data.trans
      (Data.Rat.Certificate.Raw.RationalData.eq_sound data.xUpperMatches)
  · exact data.reduced.yLower.toRational_eq_data.trans
      (Data.Rat.Certificate.Raw.RationalData.eq_sound data.yLowerMatches)
  · exact data.reduced.yUpper.toRational_eq_data.trans
      (Data.Rat.Certificate.Raw.RationalData.eq_sound data.yUpperMatches)

end RationalBoxReductionData

set_option genInjectivity false in
/-- Reduced executable inputs and finite branch checks for one moving-window
recenter.

The reduced inputs retain the checked midpoint child and exact moving-box computation for the selected root and source
box. -/
structure MovingResetReductionData where
  /-- The original Gaussian parameter and its checked reduced representative. -/ parameter : GaussianReductionData
  /-- The original source box and its checked reduced representative. -/ sourceBox : RationalBoxReductionData
  /-- The original selected final box and its checked reduced representative. -/ finalBox : RationalBoxReductionData
  /-- The retained reduced Gaussian parameter is nonzero. -/ reducedParameterNonzero : parameter.reduced.toGaussian ≠ 0
  /-- The retained reduced source box is proper. -/ reducedSourceProper : sourceBox.reduced.toBox.Proper
  /-- The original vertical elimination determinant is nonzero on the retained source x-midline. -/ midpointXNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      parameter.reduced.toGaussian
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint
          sourceBox.reduced.toBox.xLower sourceBox.reduced.toBox.xUpper) ≠ 0
  /-- The original horizontal elimination determinant is nonzero on the retained source y-midline. -/ midpointYNonzero :
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      parameter.reduced.toGaussian
        (SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpoint
          sourceBox.reduced.toBox.yLower sourceBox.reduced.toBox.yUpper) ≠ 0
  /-- The retained lower-left midpoint child has exact quadrupled winding four. -/ lowerLeftWinding :
    Winding.Box.Basic.quadrupledBoxWinding
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial
        parameter.reduced.toGaussian)
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpointGrid
        parameter.reduced.toGaussian sourceBox.reduced.toBox
          reducedSourceProper midpointXNonzero midpointYNonzero).lowerLeft = 4
  /-- The original reduced moving-candidate computation returns the exact retained reduced final box. -/ movingCandidate
    :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingCandidateBox?
      parameter.reduced.toGaussian reducedParameterNonzero
        sourceBox.reduced.toBox reducedSourceProper
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.midpointGrid
        parameter.reduced.toGaussian sourceBox.reduced.toBox
          reducedSourceProper midpointXNonzero midpointYNonzero).lowerLeft =
      some finalBox.reduced.toBox

constructive_injectivity MovingResetReductionData

namespace MovingResetReductionData

/-- The original moving-recenter computation returns the retained final box using the checked lower-left child and
reduced candidate. -/
theorem sound (data : MovingResetReductionData)
    (parameterNonzero : data.parameter.original.toGaussian ≠ 0)
    (sourceProper : data.sourceBox.original.toBox.Proper) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
        data.parameter.original.toGaussian parameterNonzero
          data.sourceBox.original.toBox sourceProper =
      some data.finalBox.original.toBox := by
  have computed :
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
          data.parameter.reduced.toGaussian data.reducedParameterNonzero
            data.sourceBox.reduced.toBox data.reducedSourceProper =
        some data.finalBox.reduced.toBox := by
    apply SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?_eq_some_of_lowerLeft
      data.parameter.reduced.toGaussian data.reducedParameterNonzero
        data.sourceBox.reduced.toBox data.reducedSourceProper
          data.finalBox.reduced.toBox data.midpointXNonzero
            data.midpointYNonzero data.lowerLeftWinding
    exact data.movingCandidate
  simpa only [data.parameter.sound, data.sourceBox.sound,
    data.finalBox.sound] using computed

end MovingResetReductionData

set_option genInjectivity false in
/-- Reduced executable inputs and the complete box projection for a moving
recenter.

The original reduced inputs retain the complete moving-box projection independently of the selected midpoint child. -/
structure MovingResetProjectionData where
  /-- The original Gaussian parameter and its checked reduced representative. -/ parameter : GaussianReductionData
  /-- The original source box and its checked reduced representative. -/ sourceBox : RationalBoxReductionData
  /-- The original selected final box and its checked reduced representative. -/ finalBox : RationalBoxReductionData
  /-- The retained reduced Gaussian parameter is nonzero. -/ reducedParameterNonzero : parameter.reduced.toGaussian ≠ 0
  /-- The retained reduced source box is proper. -/ reducedSourceProper : sourceBox.reduced.toBox.Proper
  /-- The complete original reduced moving-recenter computation returns the exact retained reduced final box. -/
    reducedProjection :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
        parameter.reduced.toGaussian reducedParameterNonzero
          sourceBox.reduced.toBox reducedSourceProper =
      some finalBox.reduced.toBox

constructive_injectivity MovingResetProjectionData

namespace MovingResetProjectionData

/-- The complete checked reduced moving-recenter projection gives the exact retained result for the original inputs. -/
theorem sound (data : MovingResetProjectionData)
    (parameterNonzero : data.parameter.original.toGaussian ≠ 0)
    (sourceProper : data.sourceBox.original.toBox.Proper) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
        data.parameter.original.toGaussian parameterNonzero
          data.sourceBox.original.toBox sourceProper =
      some data.finalBox.original.toBox := by
  simpa only [data.parameter.sound, data.sourceBox.sound,
    data.finalBox.sound] using data.reducedProjection

end MovingResetProjectionData

/-- Displayed rational zero, used to check positivity without normalizing a
constructive rational expression. -/
@[expose] def zero : Data.Rat.Certificate.Raw.RationalData where
  numerator := 0
  denominator := 1
  denominatorPositive := by decide

/-- Strict cross-product comparison on displayed positive-denominator
fractions. -/
@[expose] def RationalData.Lt (left right : Data.Rat.Certificate.Raw.RationalData) : Prop :=
  left.numerator * (right.denominator : Int) <
    right.numerator * (left.denominator : Int)

/-- Decide strict displayed-fraction order by the original integer cross-product comparison. -/
instance (left right : Data.Rat.Certificate.Raw.RationalData) : Decidable (RationalData.Lt left right) :=
  inferInstanceAs (Decidable
    (left.numerator * (right.denominator : Int) <
      right.numerator * (left.denominator : Int)))

/-- The retained positive displayed denominator remains strictly positive after rational casting. -/
private theorem denominatorCastPositive (value : Data.Rat.Certificate.Raw.RationalData) :
    (0 : Rat.Fraction.Rational) < value.denominator :=
  Rat.Fraction.Cast.Order.natCast_pos_direct value.denominatorPositive

/-- Promote a checked strict integer cross-product to the constructive
rational carrier. -/
theorem RationalData.lt_sound {left right : Data.Rat.Certificate.Raw.RationalData}
    (checked : RationalData.Lt left right) :
    left.toRational < right.toRational := by
  have denominatorPositive : (0 : Rat.Fraction.Rational) <
      (left.denominator : Rat.Fraction.Rational) *
        right.denominator :=
    Rat.Fraction.Order.Arithmetic.mul_pos_direct
      (denominatorCastPositive left) (denominatorCastPositive right)
  apply Rat.Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
    (c := (left.denominator : Rat.Fraction.Rational) *
      right.denominator) _ denominatorPositive
  calc
    left.toRational *
        ((left.denominator : Rat.Fraction.Rational) *
          right.denominator) =
      ((left.numerator : Rat.Fraction.Rational) /
          left.denominator * left.denominator) * right.denominator := by
        unfold Data.Rat.Certificate.Raw.RationalData.toRational
        ring1
    _ = (left.numerator : Rat.Fraction.Rational) *
        right.denominator := by
      rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _
        (denominatorCastPositive left).ne']
    _ < (right.numerator : Rat.Fraction.Rational) *
        left.denominator := by
      simpa only [Rat.Fraction.Cast.intCast_mul_direct,
        Int.cast_natCast] using
          Rat.Fraction.Cast.Order.intCast_lt_direct checked
    _ = ((right.numerator : Rat.Fraction.Rational) /
          right.denominator * right.denominator) * left.denominator := by
      rw [Rat.Fraction.Field.div_mul_cancel_of_ne _ _
        (denominatorCastPositive right).ne']
    _ = right.toRational *
        ((left.denominator : Rat.Fraction.Rational) *
          right.denominator) := by
      unfold Data.Rat.Certificate.Raw.RationalData.toRational
      ring1

/-- A generated strict coordinate comparison witnessing that two displayed
Gaussian rationals differ. -/
@[expose] def GaussianData.Different (left right : Gaussian.Certificate.Raw.GaussianData) : Prop :=
  RationalData.Lt left.re right.re ∨ RationalData.Lt right.re left.re ∨
    RationalData.Lt left.im right.im ∨ RationalData.Lt right.im left.im

/-- Decide displayed Gaussian separation using the original four strict coordinate comparisons. -/
instance (left right : Gaussian.Certificate.Raw.GaussianData) : Decidable (GaussianData.Different left right) :=
  inferInstanceAs (Decidable
    (RationalData.Lt left.re right.re ∨ RationalData.Lt right.re left.re ∨
      RationalData.Lt left.im right.im ∨ RationalData.Lt right.im left.im))

/-- A checked strict coordinate comparison proves that the original Gaussian values differ. -/
theorem GaussianData.different_sound {left right : Gaussian.Certificate.Raw.GaussianData}
    (checked : GaussianData.Different left right) :
    left.toGaussian ≠ right.toGaussian := by
  intro equal
  have realEqual : left.re.toRational = right.re.toRational :=
    congrArg Gaussian.Basic.re equal
  have imaginaryEqual : left.im.toRational = right.im.toRational :=
    congrArg Gaussian.Basic.im equal
  rcases checked with realLt | realGt | imaginaryLt | imaginaryGt
  · exact (RationalData.lt_sound realLt).ne realEqual
  · exact (RationalData.lt_sound realGt).ne realEqual.symm
  · exact (RationalData.lt_sound imaginaryLt).ne imaginaryEqual
  · exact (RationalData.lt_sound imaginaryGt).ne imaginaryEqual.symm

/-- Displayed `value² / 4`, without reducing either integer fraction. -/
@[expose] def quarterSquare (value : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData
  where
  numerator := value.numerator * value.numerator
  denominator := value.denominator * value.denominator * 4
  denominatorPositive := Nat.mul_pos
    (Nat.mul_pos value.denominatorPositive value.denominatorPositive) (by decide)

/-- Displayed quadratic transport floor `margin² / (4 * 65536)`. -/
@[expose] def transportFloor (margin : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData
  where
  numerator := margin.numerator * margin.numerator
  denominator := margin.denominator * margin.denominator * (4 * 65536)
  denominatorPositive := Nat.mul_pos
    (Nat.mul_pos margin.denominatorPositive margin.denominatorPositive)
      (by decide)

/-- Casting the product of two natural numbers preserves their exact rational product. -/
private theorem naturalCastMul (left right : Nat) :
    ((left * right : Nat) : Rat.Fraction.Rational) =
      (left : Rat.Fraction.Rational) * right := by
  calc
    ((left * right : Nat) : Rat.Fraction.Rational) =
        (((left * right : Nat) : Int) :
          Rat.Fraction.Rational) := by rw [Int.cast_natCast]
    _ = (((left : Int) * (right : Int) : Int) :
          Rat.Fraction.Rational) := by rw [Int.natCast_mul]
    _ = ((left : Int) : Rat.Fraction.Rational) *
        ((right : Int) : Rat.Fraction.Rational) :=
      Rat.Fraction.Cast.intCast_mul_direct _ _
    _ = (left : Rat.Fraction.Rational) * right := by
      rw [Int.cast_natCast, Int.cast_natCast]

/-- The displayed quarter-square represents exactly the original rational square divided by four. -/
theorem quarterSquare_toRational (value : Data.Rat.Certificate.Raw.RationalData) :
    (quarterSquare value).toRational = value.toRational ^ 2 / 4 := by
  unfold quarterSquare Data.Rat.Certificate.Raw.RationalData.toRational
  rw [pow_two, Rat.Fraction.Field.div_mul_div_direct,
    Rat.Fraction.Cast.intCast_mul_direct,
    naturalCastMul (value.denominator * value.denominator) 4,
    naturalCastMul value.denominator value.denominator]
  simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
  rw [Rat.Fraction.Field.inv_mul_direct]
  rw [show ((4 : Nat) : Rat.Fraction.Rational) =
      (4 : Rat.Fraction.Rational) by decide]
  ring1

/-- The displayed transport floor represents the original squared margin divided by four times 65536. -/
theorem transportFloor_toRational (margin : Data.Rat.Certificate.Raw.RationalData) :
    (transportFloor margin).toRational =
      margin.toRational ^ 2 / (4 * 65536) := by
  unfold transportFloor Data.Rat.Certificate.Raw.RationalData.toRational
  rw [pow_two, Rat.Fraction.Field.div_mul_div_direct,
    Rat.Fraction.Cast.intCast_mul_direct,
    naturalCastMul, naturalCastMul]
  rw [show ((4 * 65536 : Nat) : Rat.Fraction.Rational) =
      (4 : Rat.Fraction.Rational) * 65536 by
    exact naturalCastMul 4 65536]
  simp only [Rat.Fraction.Field.div_eq_mul_inv_direct]
  rw [Rat.Fraction.Field.inv_mul_direct]
  ring1

/-- Displayed rational data for the fixed squared-norm ceiling 256. -/
@[expose] def twoHundredFiftySix : Data.Rat.Certificate.Raw.RationalData where
  numerator := 256
  denominator := 1
  denominatorPositive := by decide

/-- Exact upper-bound readback from an original integer cross-product check.
The bound equality changes its representation, not the checked proposition. -/
theorem checkedUpperBound_sound {value upper : Data.Rat.Certificate.Raw.RationalData}
    {bound : Rat.Fraction.Rational}
    (checked : Data.Rat.Certificate.Raw.RationalData.Le value upper) (upper_eq : upper.toRational = bound) :
    value.toRational ≤ bound :=
  (Data.Rat.Certificate.Raw.RationalData.le_sound checked).trans_eq upper_eq

/-- The retained displayed ceiling denotes the exact rational 256. -/
theorem twoHundredFiftySix_toRational : twoHundredFiftySix.toRational =
    (256 : Rat.Fraction.Rational) := by
  unfold twoHundredFiftySix Data.Rat.Certificate.Raw.RationalData.toRational
  change (256 : Rat.Fraction.Rational) *
    (1 : Rat.Fraction.Rational)⁻¹ = 256
  rw [show (1 : Rat.Fraction.Rational)⁻¹ = 1 by decide,
    Rat.Fraction.Field.mul_one_direct]

/-- Equality of two displayed rational boxes, checked coordinatewise by
integer cross-products. -/
@[expose] def BoxEq (left right : Rational.Box.Certificate.RationalBoxData) : Prop :=
  Data.Rat.Certificate.Raw.RationalData.Eq left.xLower right.xLower ∧
    Data.Rat.Certificate.Raw.RationalData.Eq left.xUpper right.xUpper ∧
      Data.Rat.Certificate.Raw.RationalData.Eq left.yLower right.yLower ∧
        Data.Rat.Certificate.Raw.RationalData.Eq left.yUpper right.yUpper

/-- Decide displayed box equality using the original four coordinate cross-product equalities. -/
instance (left right : Rational.Box.Certificate.RationalBoxData) : Decidable (BoxEq left right) :=
  inferInstanceAs (Decidable
    (Data.Rat.Certificate.Raw.RationalData.Eq left.xLower right.xLower ∧
      Data.Rat.Certificate.Raw.RationalData.Eq left.xUpper right.xUpper ∧
        Data.Rat.Certificate.Raw.RationalData.Eq left.yLower right.yLower ∧
          Data.Rat.Certificate.Raw.RationalData.Eq left.yUpper right.yUpper))

/-- Coordinatewise checked cross-products prove equality of the original rational boxes. -/
theorem boxEq_sound {left right : Rational.Box.Certificate.RationalBoxData}
    (checked : BoxEq left right) : left.toBox = right.toBox := by
  apply Rational.Box.ext
  · exact Data.Rat.Certificate.Raw.RationalData.eq_sound checked.1
  · exact Data.Rat.Certificate.Raw.RationalData.eq_sound checked.2.1
  · exact Data.Rat.Certificate.Raw.RationalData.eq_sound checked.2.2.1
  · exact Data.Rat.Certificate.Raw.RationalData.eq_sound checked.2.2.2

set_option genInjectivity false in
/-- The five bounds retained from one executable owner.

The displayed owner clearance and four ambient-side bounds retain their checked nonnegativity at the exact original box.
-/
structure PreparedOwnerBoundsData where
  /-- The exact displayed rational box retained by this certificate. -/ box : Rational.Box.Certificate.RationalBoxData
  /-- The retained displayed owner clearance bound. -/ clearance : Data.Rat.Certificate.Raw.RationalData
  /-- The original displayed ambient left-side clearance bound. -/ ambientLeft : Data.Rat.Certificate.Raw.RationalData
  /-- The original displayed ambient right-side clearance bound. -/ ambientRight : Data.Rat.Certificate.Raw.RationalData
  /-- The original displayed ambient bottom-side clearance bound. -/ ambientBottom :
    Data.Rat.Certificate.Raw.RationalData
  /-- The original displayed ambient top-side clearance bound. -/ ambientTop : Data.Rat.Certificate.Raw.RationalData
  /-- The retained displayed owner clearance is nonnegative. -/ clearancePositive :
    Data.Rat.Certificate.Raw.RationalData.Le zero clearance
  /-- The retained ambient left-side bound is nonnegative. -/ ambientLeftPositive :
    Data.Rat.Certificate.Raw.RationalData.Le zero ambientLeft
  /-- The retained ambient right-side bound is nonnegative. -/ ambientRightPositive :
    Data.Rat.Certificate.Raw.RationalData.Le zero ambientRight
  /-- The retained ambient bottom-side bound is nonnegative. -/ ambientBottomPositive :
    Data.Rat.Certificate.Raw.RationalData.Le zero ambientBottom
  /-- The retained ambient top-side bound is nonnegative. -/ ambientTopPositive :
    Data.Rat.Certificate.Raw.RationalData.Le zero ambientTop

constructive_injectivity PreparedOwnerBoundsData

set_option genInjectivity false in
/-- One initial-box observation or later preparation transition.

The original segment, edge and endpoint data retain the reset count; zero resets preserve the displayed box and positive
resets change it. -/
structure PreparedEdgeReplayData where
  /-- The original finite outer-segment index of this observation. -/ segmentIndex : Nat
  /-- The original edge index within the retained outer segment. -/ edgeIndex : Nat
  /-- The displayed left mesh parameter of the original edge. -/ left : Data.Rat.Certificate.Raw.RationalData
  /-- The displayed right mesh parameter of the original edge. -/ right : Data.Rat.Certificate.Raw.RationalData
  /-- The retained number of preparation resets at this original edge. -/ resetCount : Nat
  /-- The original pre-reset data and their retained numerical bounds. -/ source : PreparedOwnerBoundsData
  /-- The observed prepared owner data and their retained bounds. -/ prepared : PreparedOwnerBoundsData
  /-- The displayed original edge parameters are ordered by an exact cross-product check. -/ ordered :
    Data.Rat.Certificate.Raw.RationalData.Le left right
  /-- Zero resets retain the original box; a positive reset count changes its displayed box. -/ resetMatchesBoxChange :
    (resetCount = 0 ∧ BoxEq source.box prepared.box) ∨
      (0 < resetCount ∧ ¬ BoxEq source.box prepared.box)

constructive_injectivity PreparedEdgeReplayData

set_option genInjectivity false in
/-- Conservative bounds shared by one contiguous run of zero-reset edges in
a single outer segment.

A contiguous nonempty finite edge run retains its exact displayed parameters, common source box, numerical ceilings and
positive margins. -/
structure PreparedSameBoxRunData where
  /-- The original finite outer-segment index of this observation. -/ segmentIndex : Nat
  /-- The original first edge index of the retained contiguous run. -/ firstEdge : Nat
  /-- The retained number of original edges in the contiguous run. -/ edgeCount : Nat
  /-- The exact displayed rational box retained by this certificate. -/ box : Rational.Box.Certificate.RationalBoxData
  /-- The displayed common floor for the original direct boundary clearance. -/ directLower :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed reusable clearance ceiling of the prepared owner. -/ preparedUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained squared variation ceiling for the original edge parameters. -/ variationUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained source-to-target squared-displacement ceiling. -/ displacementUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The exact displayed retained transport margin. -/ transportMargin : Data.Rat.Certificate.Raw.RationalData
  /-- The displayed positive residual floor after the original parameter displacement. -/ residualMarginFloor :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed predicted-clearance ceiling. -/ predictedUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The retained target-parameter squared-norm ceiling. -/ targetNormSqUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The retained run contains at least one edge. -/ edgeCountPositive : 0 < edgeCount
  /-- The retained run ends within the original eight-edge segment. -/ edgeRange : firstEdge + edgeCount ≤ 8
  /-- The displayed variation ceiling is strictly below the original direct-clearance floor. -/ directCarries :
    RationalData.Lt variationUpper directLower
  /-- The retained displacement ceiling is at most the original variation ceiling. -/ displacementCovered :
    Data.Rat.Certificate.Raw.RationalData.Le displacementUpper variationUpper
  /-- The retained transport margin is strictly positive by cross-product comparison. -/ transportMarginPositive :
    RationalData.Lt zero transportMargin
  /-- The retained residual floor is strictly positive by cross-product comparison. -/ residualMarginPositive :
    RationalData.Lt zero residualMarginFloor
  /-- The displayed predicted-clearance ceiling fits the retained squared-margin transport floor. -/
    predictedFitsTransport : Data.Rat.Certificate.Raw.RationalData.Le predictedUpper
    (transportFloor transportMargin)
  /-- The retained prepared-owner ceiling is strictly positive. -/ preparedUpperPositive : RationalData.Lt zero
    preparedUpper
  /-- The retained prepared-owner ceiling bounds its own square divided by four. -/ preparedUpperContracts :
    Data.Rat.Certificate.Raw.RationalData.Le (quarterSquare preparedUpper)
    preparedUpper
  /-- The retained target squared-norm ceiling is at most 256. -/ targetNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le targetNormSqUpper
    twoHundredFiftySix

constructive_injectivity PreparedSameBoxRunData

namespace PreparedSameBoxRunData

/-- The checked variation ceiling lies strictly below the original direct-clearance floor. -/
theorem variationUpper_lt_directLower (data : PreparedSameBoxRunData) :
    data.variationUpper.toRational < data.directLower.toRational :=
  RationalData.lt_sound data.directCarries

/-- The retained displacement ceiling is bounded by the original variation ceiling. -/
theorem displacementUpper_le_variationUpper (data : PreparedSameBoxRunData) :
    data.displacementUpper.toRational ≤ data.variationUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.displacementCovered

/-- The retained displayed transport margin denotes a strictly positive rational. -/
theorem transportMargin_positive (data : PreparedSameBoxRunData) :
    0 < data.transportMargin.toRational := by
  have promoted := RationalData.lt_sound data.transportMarginPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The retained residual margin floor denotes a strictly positive rational. -/
theorem residualMarginFloor_positive (data : PreparedSameBoxRunData) :
    0 < data.residualMarginFloor.toRational := by
  have promoted := RationalData.lt_sound data.residualMarginPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The retained predicted clearance ceiling fits the original squared-margin transport floor. -/
theorem predictedUpper_le_transportFloor (data : PreparedSameBoxRunData) :
    data.predictedUpper.toRational ≤
      data.transportMargin.toRational ^ 2 / (4 * 65536) := by
  rw [← transportFloor_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.predictedFitsTransport

/-- The retained preparation ceiling denotes a strictly positive rational. -/
theorem preparedUpper_positive (data : PreparedSameBoxRunData) :
    0 < data.preparedUpper.toRational := by
  have promoted := RationalData.lt_sound data.preparedUpperPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The square of the retained preparation ceiling divided by four does not exceed that same ceiling. -/
theorem preparedUpper_contracts (data : PreparedSameBoxRunData) :
    data.preparedUpper.toRational ^ 2 / 4 ≤
      data.preparedUpper.toRational := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.preparedUpperContracts
  rw [quarterSquare_toRational] at promoted
  exact promoted

/-- The retained target squared-norm ceiling is at most 256. -/
theorem targetNormSqUpper_le_twoHundredFiftySix
    (data : PreparedSameBoxRunData) :
    data.targetNormSqUpper.toRational ≤ 256 :=
  checkedUpperBound_sound data.targetNormSqBounded twoHundredFiftySix_toRational

end PreparedSameBoxRunData

/-! ## Generated side-majorant inputs -/

/-- Displayed square, kept unreduced so generated integer cross-products stay
small and transparent to the kernel. -/
@[expose] def squareData (value : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData :=
  value.mul value

/-- The displayed product used for a square denotes exactly the original rational square. -/
theorem squareData_toRational (value : Data.Rat.Certificate.Raw.RationalData) :
    (squareData value).toRational = value.toRational ^ 2 := by
  unfold squareData
  rw [Data.Rat.Certificate.Raw.RationalData.mul_toRational, pow_two]

/-- The constant term appearing in the real part on a vertical box side. -/
@[expose] def verticalRealConstantSq
    (x : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData) :
      Data.Rat.Certificate.Raw.RationalData :=
  squareData ((x.mul x).sub parameter.re)

/-- The constant term appearing in the real part on a horizontal box side. -/
@[expose] def horizontalRealConstantSq
    (y : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData) :
      Data.Rat.Certificate.Raw.RationalData :=
  squareData ((y.mul y).neg.sub parameter.re)

/-- The constant term appearing in the imaginary part on every box side. -/
@[expose] def imaginaryConstantSq (parameter : Gaussian.Certificate.Raw.GaussianData) :
  Data.Rat.Certificate.Raw.RationalData :=
  squareData parameter.im.neg

/-- The displayed vertical real constant denotes the square of x² minus the parameter's real coordinate. -/
theorem verticalRealConstantSq_toRational
    (x : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData) :
    (verticalRealConstantSq x parameter).toRational =
      (x.toRational ^ 2 - parameter.re.toRational) ^ 2 := by
  unfold verticalRealConstantSq
  rw [squareData_toRational, Data.Rat.Certificate.Raw.RationalData.sub_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, pow_two]
  ring1

/-- The displayed horizontal real constant denotes the square of minus y² minus the parameter's real coordinate. -/
theorem horizontalRealConstantSq_toRational
    (y : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData) :
    (horizontalRealConstantSq y parameter).toRational =
      (-(y.toRational ^ 2) - parameter.re.toRational) ^ 2 := by
  unfold horizontalRealConstantSq
  rw [squareData_toRational, Data.Rat.Certificate.Raw.RationalData.sub_toRational,
    Data.Rat.Certificate.Raw.RationalData.neg_toRational, Data.Rat.Certificate.Raw.RationalData.mul_toRational, pow_two]
  ring1

/-- The displayed imaginary constant denotes the square of the negated parameter imaginary coordinate. -/
theorem imaginaryConstantSq_toRational (parameter : Gaussian.Certificate.Raw.GaussianData) :
    (imaginaryConstantSq parameter).toRational =
      (-parameter.im.toRational) ^ 2 := by
  unfold imaginaryConstantSq
  rw [squareData_toRational, Data.Rat.Certificate.Raw.RationalData.neg_toRational]

/-- Represent the supplied natural number by its original numerator over denominator one. -/
@[expose] def naturalData (value : Nat) : Data.Rat.Certificate.Raw.RationalData where
  numerator := value
  denominator := 1
  denominatorPositive := by decide

/-- The displayed natural-number data denotes its exact rational cast. -/
theorem naturalData_toRational (value : Nat) :
    (naturalData value).toRational = (value : Rat.Fraction.Rational) := by
  unfold naturalData Data.Rat.Certificate.Raw.RationalData.toRational
  rw [Int.cast_natCast]
  change (value : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ = value
  rw [show (1 : Rat.Fraction.Rational)⁻¹ = 1 by decide,
    Rat.Fraction.Field.mul_one_direct]

/-- Parameterized natural-number bound for finite generated certificates. -/
theorem checkedNaturalUpperBound_sound {value : Data.Rat.Certificate.Raw.RationalData} (bound : Nat)
    (checked : Data.Rat.Certificate.Raw.RationalData.Le value (naturalData bound)) :
    value.toRational ≤ (bound : Rat.Fraction.Rational) :=
  checkedUpperBound_sound checked (naturalData_toRational bound)

/-- The fixed retained margin used by the depth-three continuation cells. -/
@[expose] def oneEighthData : Data.Rat.Certificate.Raw.RationalData where
  numerator := 1
  denominator := 8
  denominatorPositive := by decide

/-- The retained fixed-margin data denotes exactly one eighth. -/
theorem oneEighthData_toRational :
    oneEighthData.toRational =
      (1 / 8 : Rat.Fraction.Rational) := by
  rfl

/-- The fixed derivative margin of the quartic A-boundary segments. -/
@[expose] def oneFourthData : Data.Rat.Certificate.Raw.RationalData where
  numerator := 1
  denominator := 4
  denominatorPositive := by decide

/-- The retained derivative-margin data denotes exactly one fourth. -/
theorem oneFourthData_toRational :
    oneFourthData.toRational =
      (1 / 4 : Rat.Fraction.Rational) := by
  rfl

/-- The squared parameter increment of one depth-three mesh edge. -/
@[expose] def oneSixtyFourthData : Data.Rat.Certificate.Raw.RationalData where
  numerator := 1
  denominator := 64
  denominatorPositive := by decide

/-- The retained squared mesh-step data denotes exactly one sixty-fourth. -/
theorem oneSixtyFourthData_toRational :
    oneSixtyFourthData.toRational =
      (1 / 64 : Rat.Fraction.Rational) := by
  rfl

/-- Scan-free lower bound for the root-sample derivative majorant, computed
from a generated lower bound for the squared norm at the segment source. -/
@[expose] def predictedDerivativeLowerData (sourceNormSqLower : Data.Rat.Certificate.Raw.RationalData) :
    Data.Rat.Certificate.Raw.RationalData :=
  Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4)
    (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 2)
      (Data.Rat.Certificate.Raw.RationalData.add oneFourthData
        (Data.Rat.Certificate.Raw.RationalData.add
          (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 2) sourceNormSqLower)
          (naturalData 1))))

/-- The displayed derivative floor denotes the exact formula `8 * (1/4 + 2 * sourceFloor + 1)`. -/
theorem predictedDerivativeLowerData_toRational
    (sourceNormSqLower : Data.Rat.Certificate.Raw.RationalData) :
    (predictedDerivativeLowerData sourceNormSqLower).toRational =
      4 * (2 * ((1 / 4 : Rat.Fraction.Rational) +
        (2 * sourceNormSqLower.toRational + 1))) := by
  unfold predictedDerivativeLowerData
  simp only [Data.Rat.Certificate.Raw.RationalData.mul_toRational, Data.Rat.Certificate.Raw.RationalData.add_toRational,
    naturalData_toRational, oneFourthData_toRational]
  rfl

/-- Exact numerator of the predicted-clearance expression in the fixed
quarter-margin, one-sixty-fourth-radius regime. -/
@[expose] def predictedClearanceNumeratorData : Data.Rat.Certificate.Raw.RationalData :=
  squareData
    (Data.Rat.Certificate.Raw.RationalData.sub
      (Data.Rat.Certificate.Raw.RationalData.mul oneFourthData (squareData oneSixtyFourthData))
      (Data.Rat.Certificate.Raw.RationalData.mul
        (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 36) (naturalData 8))
        (squareData (squareData oneSixtyFourthData))))

/-- The displayed predicted-clearance numerator denotes its original fixed-margin squared residual formula. -/
theorem predictedClearanceNumeratorData_toRational :
    predictedClearanceNumeratorData.toRational =
      ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 := by
  unfold predictedClearanceNumeratorData
  simp only [squareData_toRational, Data.Rat.Certificate.Raw.RationalData.sub_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, oneFourthData_toRational,
    oneSixtyFourthData_toRational, naturalData_toRational]
  rfl

/-- Denominator obtained from a generated lower bound for the root-sample
derivative majorant at the fixed one-sixty-fourth preparation radius. -/
@[expose] def predictedClearanceDenominatorLowerData
    (derivativeLower : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData :=
  Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4)
    (Data.Rat.Certificate.Raw.RationalData.mul
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 2) derivativeLower)
      (squareData oneSixtyFourthData))

/-- The displayed clearance denominator floor denotes four times twice the retained derivative floor times the squared
one-sixty-fourth radius. -/
theorem predictedClearanceDenominatorLowerData_toRational
    (derivativeLower : Data.Rat.Certificate.Raw.RationalData) :
    (predictedClearanceDenominatorLowerData derivativeLower).toRational =
      4 * (2 * derivativeLower.toRational *
        (1 / 64 : Rat.Fraction.Rational) ^ 2) := by
  unfold predictedClearanceDenominatorLowerData
  simp only [Data.Rat.Certificate.Raw.RationalData.mul_toRational, naturalData_toRational,
    squareData_toRational, oneSixtyFourthData_toRational]
  rfl

/-- Displayed mesh parameter `index / 8`, used by generated affine quartic
cells without normalizing a constructive rational. -/
@[expose] def eighthParameterData (index : Nat) : Data.Rat.Certificate.Raw.RationalData where
  numerator := index
  denominator := 8
  denominatorPositive := by decide

/-- The displayed eighth-grid parameter denotes the original natural index divided by eight. -/
theorem eighthParameterData_toRational (index : Nat) :
    (eighthParameterData index).toRational =
      (index : Rat.Fraction.Rational) / 8 := by
  unfold eighthParameterData Data.Rat.Certificate.Raw.RationalData.toRational
  rw [Int.cast_natCast]
  rfl

/-- Coordinatewise scalar multiplication of displayed Gaussian data. -/
@[expose] def scaleGaussianData (scale : Data.Rat.Certificate.Raw.RationalData) (value :
  Gaussian.Certificate.Raw.GaussianData) :
    Gaussian.Certificate.Raw.GaussianData where
  re := Data.Rat.Certificate.Raw.RationalData.mul scale value.re
  im := Data.Rat.Certificate.Raw.RationalData.mul scale value.im

/-- Displayed coordinate scaling denotes exact Gaussian scaling by the original rational factor.

The two retained coordinate products identify the original scaled Gaussian without altering its rational factor or
coordinate data. -/
theorem scaleGaussianData_toGaussian (scale : Data.Rat.Certificate.Raw.RationalData)
    (value : Gaussian.Certificate.Raw.GaussianData) :
    (scaleGaussianData scale value).toGaussian =
      Gaussian.Scale.scale scale.toRational value.toGaussian := by
  apply Gaussian.Basic.ext <;>
    simp only [-eq_self, -iff_self, scaleGaussianData, Gaussian.Certificate.Raw.GaussianData.toGaussian,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im,
      Data.Rat.Certificate.Raw.RationalData.mul_toRational] <;> rfl

/-- Generated affine input point at one displayed mesh parameter. -/
@[expose] def affineGaussianData (origin direction : Gaussian.Certificate.Raw.GaussianData)
    (parameter : Data.Rat.Certificate.Raw.RationalData) : Gaussian.Certificate.Raw.GaussianData :=
  Gaussian.Certificate.Raw.GaussianData.add origin (scaleGaussianData parameter direction)

/-- The displayed affine point denotes the original Gaussian origin plus the scaled direction. -/
theorem affineGaussianData_toGaussian (origin direction : Gaussian.Certificate.Raw.GaussianData)
    (parameter : Data.Rat.Certificate.Raw.RationalData) :
    (affineGaussianData origin direction parameter).toGaussian =
      origin.toGaussian +
        Gaussian.Scale.scale parameter.toRational direction.toGaussian := by
  unfold affineGaussianData
  rw [Gaussian.Certificate.Raw.GaussianData.add_toGaussian, scaleGaussianData_toGaussian]

/-- Displayed Gaussian coordinate data for the exact multiplicative identity. -/
@[expose] def gaussianOneData : Gaussian.Certificate.Raw.GaussianData where
  re := naturalData 1
  im := zero

/-- The displayed Gaussian identity denotes the exact value one. -/
theorem gaussianOneData_toGaussian : gaussianOneData.toGaussian = 1 := by
  apply Gaussian.Basic.ext <;>
    simp only [gaussianOneData, Gaussian.Certificate.Raw.GaussianData.toGaussian,
      zero, Data.Rat.Certificate.Raw.RationalData.toRational]
  · rfl
  · exact Rat.Fraction.Field.zero_mul_direct _

/-- Exact displayed value of `point⁴ - 1`. -/
@[expose] def quarticParameterData (point : Gaussian.Certificate.Raw.GaussianData) :
  Gaussian.Certificate.Raw.GaussianData :=
  Gaussian.Certificate.Raw.GaussianData.sub
    (Gaussian.Certificate.Raw.GaussianData.mul (Gaussian.Certificate.Raw.GaussianData.mul point point)
      (Gaussian.Certificate.Raw.GaussianData.mul point point))
    gaussianOneData

/-- The displayed quartic parameter denotes the original Gaussian point to the fourth power minus one. -/
theorem quarticParameterData_toGaussian (point : Gaussian.Certificate.Raw.GaussianData) :
    (quarticParameterData point).toGaussian = point.toGaussian ^ 4 - 1 := by
  unfold quarticParameterData
  rw [Gaussian.Certificate.Raw.GaussianData.sub_toGaussian, Gaussian.Certificate.Raw.GaussianData.mul_toGaussian,
    Gaussian.Certificate.Raw.GaussianData.mul_toGaussian, gaussianOneData_toGaussian]
  ring1

/-- Compute the displayed quartic parameter at the original affine Gaussian point. -/
@[expose] def affineQuarticParameterData (origin direction : Gaussian.Certificate.Raw.GaussianData)
    (parameter : Data.Rat.Certificate.Raw.RationalData) : Gaussian.Certificate.Raw.GaussianData :=
  quarticParameterData (affineGaussianData origin direction parameter)

/-- The displayed affine quartic parameter denotes the original affine point to the fourth power minus one. -/
theorem affineQuarticParameterData_toGaussian
    (origin direction : Gaussian.Certificate.Raw.GaussianData) (parameter : Data.Rat.Certificate.Raw.RationalData) :
    (affineQuarticParameterData origin direction parameter).toGaussian =
      (origin.toGaussian +
        Gaussian.Scale.scale parameter.toRational direction.toGaussian) ^ 4 -
          1 := by
  unfold affineQuarticParameterData
  rw [quarticParameterData_toGaussian, affineGaussianData_toGaussian]

/-- Select the larger original displayed fraction using its exact integer cross-product comparison. -/
@[expose] def maxData (left right : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData :=
  if Data.Rat.Certificate.Raw.RationalData.Le left right then right else left

/-- The selected displayed fraction denotes the exact rational maximum of the two inputs.

The original checked integer cross-product branch selects one of the two retained fractions and certifies that same
selection as their rational maximum. -/
theorem maxData_toRational (left right : Data.Rat.Certificate.Raw.RationalData) :
    (maxData left right).toRational =
      max left.toRational right.toRational := by
  unfold maxData
  by_cases checked : Data.Rat.Certificate.Raw.RationalData.Le left right
  · rw [if_pos checked, Rat.Fraction.Order.Basic.max_eq_right (Data.Rat.Certificate.Raw.RationalData.le_sound checked)]
  · rw [if_neg checked, Rat.Fraction.Order.Basic.max_eq_left]
    exact (RationalData.lt_sound
      (show RationalData.Lt right left from Int.Order.lt_of_not_le checked)).le

/-- Compute a finite natural power by multiplication of the original displayed rational data. -/
@[expose] def powerData (value : Data.Rat.Certificate.Raw.RationalData) : Nat → Data.Rat.Certificate.Raw.RationalData
  | 0 => naturalData 1
  | exponent + 1 => Data.Rat.Certificate.Raw.RationalData.mul (powerData value exponent) value

/-- The displayed finite-power recursion denotes the exact original rational power. -/
theorem powerData_toRational (value : Data.Rat.Certificate.Raw.RationalData) : ∀ exponent,
    (powerData value exponent).toRational = value.toRational ^ exponent
  | 0 => by
      rw [powerData, naturalData_toRational, pow_zero]
      exact (by decide :
        ((1 : Nat) : Rat.Fraction.Rational) = 1)
  | exponent + 1 => by
      rw [powerData, Data.Rat.Certificate.Raw.RationalData.mul_toRational,
        powerData_toRational value exponent, pow_succ]

/-- The four nonconstant coefficient norms in the dense-Horner Lipschitz
formula for `(origin + t * direction)^4 - 1`, evaluated only as displayed
rational data. -/
@[expose] def affineQuarticSlopeData
    (originNormSq directionNormSq : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData :=
  Data.Rat.Certificate.Raw.RationalData.add
    (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 1024) (powerData directionNormSq 4))
    (Data.Rat.Certificate.Raw.RationalData.add
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 192)
        (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 16)
          (Data.Rat.Certificate.Raw.RationalData.mul originNormSq (powerData directionNormSq 3))))
      (Data.Rat.Certificate.Raw.RationalData.add
        (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 32)
          (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 36)
            (Data.Rat.Certificate.Raw.RationalData.mul (powerData originNormSq 2)
              (powerData directionNormSq 2))))
        (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4)
          (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 16)
            (Data.Rat.Certificate.Raw.RationalData.mul (powerData originNormSq 3)
              directionNormSq)))))

/-- The displayed quartic slope denotes the original weighted sum of the four coefficient squared-norm bounds. -/
theorem affineQuarticSlopeData_toRational
    (originNormSq directionNormSq : Data.Rat.Certificate.Raw.RationalData) :
    (affineQuarticSlopeData originNormSq directionNormSq).toRational =
      1024 * directionNormSq.toRational ^ 4 +
        192 * (16 * originNormSq.toRational *
          directionNormSq.toRational ^ 3) +
        32 * (36 * originNormSq.toRational ^ 2 *
          directionNormSq.toRational ^ 2) +
        4 * (16 * originNormSq.toRational ^ 3 *
          directionNormSq.toRational) := by
  unfold affineQuarticSlopeData
  simp only [Data.Rat.Certificate.Raw.RationalData.add_toRational, Data.Rat.Certificate.Raw.RationalData.mul_toRational,
    naturalData_toRational, powerData_toRational]
  rw [show ((1024 : Nat) : Rat.Fraction.Rational) = 1024 by rfl,
    show ((192 : Nat) : Rat.Fraction.Rational) = 192 by rfl,
    show ((16 : Nat) : Rat.Fraction.Rational) = 16 by rfl,
    show ((32 : Nat) : Rat.Fraction.Rational) = 32 by rfl,
    show ((36 : Nat) : Rat.Fraction.Rational) = 36 by rfl,
    show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl]
  ring1

/-- Compute the displayed vertical elimination determinant 4x²(x²−Re w)−(Im w)². -/
@[expose] def verticalDeterminantData
    (x : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData) :
      Data.Rat.Certificate.Raw.RationalData :=
  Data.Rat.Certificate.Raw.RationalData.sub
    (Data.Rat.Certificate.Raw.RationalData.mul
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) (squareData x))
      (Data.Rat.Certificate.Raw.RationalData.sub (squareData x) parameter.re))
    (squareData parameter.im)

/-- Compute the displayed horizontal elimination determinant (Im w)²−4y²(y²+Re w). -/
@[expose] def horizontalDeterminantData
    (y : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData) :
      Data.Rat.Certificate.Raw.RationalData :=
  Data.Rat.Certificate.Raw.RationalData.sub (squareData parameter.im)
    (Data.Rat.Certificate.Raw.RationalData.mul
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) (squareData y))
      (Data.Rat.Certificate.Raw.RationalData.add (squareData y) parameter.re))

/-- Compute the displayed positive line majorant as the maximum of one and the retained quadratic coefficient bound. -/
@[expose] def directLineMajorantData
    (constant slope intercept radiusSq : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData
      :=
  maxData (naturalData 1)
    (Data.Rat.Certificate.Raw.RationalData.add (squareData constant)
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 2)
        (Data.Rat.Certificate.Raw.RationalData.add
          (Data.Rat.Certificate.Raw.RationalData.mul (squareData slope) radiusSq)
          (squareData intercept))))

/-- Specialize the displayed line majorant to the original vertical side coordinate and parameter. -/
@[expose] def verticalMajorantData
    (x : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData)
    (verticalIntervalSq : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData :=
  directLineMajorantData
    (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) (squareData x))
    (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 2) x) parameter.im verticalIntervalSq

/-- Specialize the displayed line majorant to the original horizontal side coordinate and parameter. -/
@[expose] def horizontalMajorantData
    (y : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData)
    (horizontalIntervalSq : Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData :=
  directLineMajorantData
    (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) (squareData y))
    (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 2) y).neg parameter.im.neg
      horizontalIntervalSq

/-- The displayed vertical determinant denotes the exact original quadratic elimination determinant. -/
theorem verticalDeterminantData_toRational
    (x : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData) :
    (verticalDeterminantData x parameter).toRational =
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        parameter.toGaussian x.toRational := by
  unfold verticalDeterminantData
    SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
  simp only [Data.Rat.Certificate.Raw.RationalData.sub_toRational, Data.Rat.Certificate.Raw.RationalData.mul_toRational,
    squareData_toRational, naturalData_toRational,
    gaussianDataToGaussian_re, gaussianDataToGaussian_im]
  rw [show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl]

/-- The displayed horizontal determinant denotes the exact original quadratic elimination determinant. -/
theorem horizontalDeterminantData_toRational
    (y : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData) :
    (horizontalDeterminantData y parameter).toRational =
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        parameter.toGaussian y.toRational := by
  unfold horizontalDeterminantData
    SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
  simp only [Data.Rat.Certificate.Raw.RationalData.sub_toRational, Data.Rat.Certificate.Raw.RationalData.mul_toRational,
    Data.Rat.Certificate.Raw.RationalData.add_toRational, squareData_toRational,
    naturalData_toRational, gaussianDataToGaussian_re,
    gaussianDataToGaussian_im]
  rw [show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl]

/-- The displayed line majorant denotes the exact retained rational quadratic-line majorant. -/
theorem directLineMajorantData_toRational
    (constant slope intercept radiusSq : Data.Rat.Certificate.Raw.RationalData) :
    (directLineMajorantData constant slope intercept radiusSq).toRational =
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant
        constant.toRational slope.toRational intercept.toRational
          radiusSq.toRational := by
  unfold directLineMajorantData
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant
  simp only [maxData_toRational, Data.Rat.Certificate.Raw.RationalData.add_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, squareData_toRational,
    naturalData_toRational]
  rw [show ((1 : Nat) : Rat.Fraction.Rational) = 1 by rfl,
    show ((2 : Nat) : Rat.Fraction.Rational) = 2 by rfl]

/-- The displayed vertical majorant denotes the exact original side-majorant formula. -/
theorem verticalMajorantData_toRational
    (x : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData)
    (verticalIntervalSq : Data.Rat.Certificate.Raw.RationalData) :
    (verticalMajorantData x parameter verticalIntervalSq).toRational =
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant
        (4 * x.toRational ^ 2) (2 * x.toRational)
          parameter.toGaussian.im verticalIntervalSq.toRational := by
  unfold verticalMajorantData
  rw [directLineMajorantData_toRational]
  simp only [Data.Rat.Certificate.Raw.RationalData.mul_toRational, squareData_toRational,
    naturalData_toRational, gaussianDataToGaussian_im]
  rw [show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl,
    show ((2 : Nat) : Rat.Fraction.Rational) = 2 by rfl]

/-- The displayed horizontal majorant denotes the exact original side-majorant formula. -/
theorem horizontalMajorantData_toRational
    (y : Data.Rat.Certificate.Raw.RationalData) (parameter : Gaussian.Certificate.Raw.GaussianData)
    (horizontalIntervalSq : Data.Rat.Certificate.Raw.RationalData) :
    (horizontalMajorantData y parameter horizontalIntervalSq).toRational =
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant
        (4 * y.toRational ^ 2) (-(2 * y.toRational))
          (-parameter.toGaussian.im) horizontalIntervalSq.toRational := by
  unfold horizontalMajorantData
  rw [directLineMajorantData_toRational]
  simp only [Data.Rat.Certificate.Raw.RationalData.mul_toRational, Data.Rat.Certificate.Raw.RationalData.neg_toRational,
    squareData_toRational, naturalData_toRational,
    gaussianDataToGaussian_im]
  rw [show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl,
    show ((2 : Nat) : Rat.Fraction.Rational) = 2 by rfl]

/-- Compute the exact displayed real and imaginary quartic grid parameters from the supplied integer grid index. -/
@[expose] def quarticHorizontalGridParameterData (index : Int) : Gaussian.Certificate.Raw.GaussianData where
  re :=
    { numerator := index ^ 4 - 1536 * index ^ 2 - 983040
      denominator := 1048576
      denominatorPositive := by decide }
  im :=
    { numerator := index ^ 3 - 256 * index
      denominator := 16384
      denominatorPositive := by decide }

/-- The displayed horizontal-grid parameter denotes its original rational polynomial coordinate formulas.

Integer cast laws identify the retained numerator polynomials and positive constant denominators with the exact two
rational coordinates. -/
theorem quarticHorizontalGridParameterData_toGaussian (index : Int) :
    (quarticHorizontalGridParameterData index).toGaussian =
      ⟨(((index : Rat.Fraction.Rational) ^ 4 -
          1536 * index ^ 2 - 983040) / 1048576),
        (((index : Rat.Fraction.Rational) ^ 3 -
          256 * index) / 16384)⟩ := by
  have intCastPow (power : Nat) :
      (((index ^ power : Int) : Rat.Fraction.Rational)) =
        (index : Rat.Fraction.Rational) ^ power := by
    induction power with
    | zero => simp only [-eq_self, -iff_self, pow_zero, Int.cast_one]; rfl
    | succ power inductionHypothesis =>
        rw [pow_succ, pow_succ,
          Rat.Fraction.Cast.intCast_mul_direct,
          inductionHypothesis]
  apply Gaussian.Basic.ext
  · simp only [-eq_self, -iff_self, quarticHorizontalGridParameterData,
      Gaussian.Certificate.Raw.GaussianData.toGaussian,
      Data.Rat.Certificate.Raw.RationalData.toRational, Algebra.Ring.IntCast.sub,
      Rat.Fraction.Cast.intCast_mul_direct,
      intCastPow, Int.cast_ofNat]
    rw [show ((1048576 : Nat) : Rat.Fraction.Rational) =
      1048576 by rfl]
  · simp only [-eq_self, -iff_self, quarticHorizontalGridParameterData,
      Gaussian.Certificate.Raw.GaussianData.toGaussian,
      Data.Rat.Certificate.Raw.RationalData.toRational, Algebra.Ring.IntCast.sub,
      Rat.Fraction.Cast.intCast_mul_direct,
      intCastPow, Int.cast_ofNat]
    rw [show ((16384 : Nat) : Rat.Fraction.Rational) =
      16384 by rfl]

/-- Two integer coefficients over one positive denominator.  Generated dyadic
parameter grids use this constructor so the coefficients remain explicit data
and their Lean interpretation is shared rather than re-proved cell by cell. -/
@[expose] def gaussianAtDenominatorData (real imaginary : Int) (denominator : Nat)
    (positive : 0 < denominator) : Gaussian.Certificate.Raw.GaussianData where
  re :=
    { numerator := real
      denominator := denominator
      denominatorPositive := positive }
  im :=
    { numerator := imaginary
      denominator := denominator
      denominatorPositive := positive }

/-- The retained integer coefficients over the common positive denominator denote the exact Gaussian coordinates. -/
theorem gaussianAtDenominatorData_toGaussian
    (real imaginary : Int) (denominator : Nat) (positive : 0 < denominator) :
    (gaussianAtDenominatorData real imaginary denominator positive).toGaussian =
      ⟨(real : Rat.Fraction.Rational) / denominator,
        (imaginary : Rat.Fraction.Rational) / denominator⟩ := by
  rfl

/-- The common quadratic side budget, represented entirely as finite rational
data so a generated certificate can decide its final comparison by integer
cross-products. -/
@[expose] def sideBudgetData (intervalSq coordinateSq realConstantSq imaginaryConstantSq :
    Data.Rat.Certificate.Raw.RationalData) : Data.Rat.Certificate.Raw.RationalData :=
  Data.Rat.Certificate.Raw.RationalData.add
    (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 2)
      (Data.Rat.Certificate.Raw.RationalData.add
        (Data.Rat.Certificate.Raw.RationalData.mul
          (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) intervalSq) intervalSq)
        realConstantSq))
    (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 2)
      (Data.Rat.Certificate.Raw.RationalData.add
        (Data.Rat.Certificate.Raw.RationalData.mul
          (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 8) coordinateSq) intervalSq)
        imaginaryConstantSq))

/-- The displayed side budget denotes the original sum of real and imaginary quadratic bounds with their retained
factors. -/
theorem sideBudgetData_toRational
    (intervalSq coordinateSq realConstantSq imaginaryConstantSq : Data.Rat.Certificate.Raw.RationalData) :
    (sideBudgetData intervalSq coordinateSq realConstantSq
        imaginaryConstantSq).toRational =
      2 * (4 * intervalSq.toRational * intervalSq.toRational +
          realConstantSq.toRational) +
        2 * (8 * coordinateSq.toRational * intervalSq.toRational +
          imaginaryConstantSq.toRational) := by
  unfold sideBudgetData
  simp only [Data.Rat.Certificate.Raw.RationalData.add_toRational, Data.Rat.Certificate.Raw.RationalData.mul_toRational,
    naturalData_toRational]
  rw [show ((2 : Nat) : Rat.Fraction.Rational) = 2 by rfl,
    show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl,
    show ((8 : Nat) : Rat.Fraction.Rational) = 8 by rfl]

/-- Exact squared diagonal of a displayed rational box. -/
@[expose] def boxDiagonalSqData (box : Rational.Box.Certificate.RationalBoxData) : Data.Rat.Certificate.Raw.RationalData
  :=
  Data.Rat.Certificate.Raw.RationalData.add (squareData (Data.Rat.Certificate.Raw.RationalData.sub box.xUpper
    box.xLower))
    (squareData (Data.Rat.Certificate.Raw.RationalData.sub box.yUpper box.yLower))

/-- The displayed squared-diagonal calculation equals the original rational box's squared diagonal.

The original endpoint differences and their displayed squares reconstruct the same horizontal and vertical squared
lengths. -/
theorem boxDiagonalSqData_toRational (box : Rational.Box.Certificate.RationalBoxData) :
    (boxDiagonalSqData box).toRational = box.toBox.diagonalSq := by
  unfold boxDiagonalSqData Rational.Box.diagonalSq
  simp only [-eq_self, -iff_self, Data.Rat.Certificate.Raw.RationalData.add_toRational, squareData_toRational,
    Data.Rat.Certificate.Raw.RationalData.sub_toRational, rationalBoxDataToBox_xUpper,
    rationalBoxDataToBox_xLower, rationalBoxDataToBox_yUpper,
    rationalBoxDataToBox_yLower]
  rfl

set_option genInjectivity false in
/-- Kernel-checked constant-term ceilings for eight explicitly displayed
source parameters.

All eight source parameters retain their checked reductions, determinant floors, coordinate ceilings and exact
side-majorant bounds. -/
structure PreparedExplicitSideBoundsData where
  /-- The original displayed Gaussian source parameter at each of the eight edges. -/ sourceParameter : Fin 8 →
    Gaussian.Certificate.Raw.GaussianData
  /-- The retained checked reduced source parameter at each original edge. -/ sourceParameterReduced : Fin 8 →
    ReducedGaussianData
  /-- Checked coordinate cross-products identify every reduced source parameter with its original displayed value. -/
    sourceParameterReducedMatches : ∀ edge, Gaussian.Certificate.Raw.GaussianData.Eq
    (sourceParameterReduced edge).toGaussianData (sourceParameter edge)
  /-- The original displayed Gaussian target parameter at each of the eight edges. -/ targetParameter : Fin 8 →
    Gaussian.Certificate.Raw.GaussianData
  /-- The retained checked reduced target parameter at each original edge. -/ targetParameterReduced : Fin 8 →
    ReducedGaussianData
  /-- Checked coordinate cross-products identify every reduced target parameter with its original displayed value. -/
    targetParameterReducedMatches : ∀ edge, Gaussian.Certificate.Raw.GaussianData.Eq
    (targetParameterReduced edge).toGaussianData (targetParameter edge)
  /-- The retained squared variation ceiling for the original edge parameters. -/ variationUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained source-to-target squared-displacement ceiling. -/ displacementUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed positive residual floor after the original parameter displacement. -/ residualMarginFloor :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained source-parameter squared-norm floor. -/ sourceNormSqLower : Data.Rat.Certificate.Raw.RationalData
  /-- The retained source-parameter squared-norm ceiling. -/ sourceNormSqUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The retained target-parameter squared-norm ceiling. -/ targetNormSqUpper : Data.Rat.Certificate.Raw.RationalData
  /-- Every original source-to-target squared displacement satisfies the retained ceiling. -/ displacementBounds : ∀
    edge, Data.Rat.Certificate.Raw.RationalData.Le
    ((sourceParameter edge).sub (targetParameter edge)).normSq
      displacementUpper
  /-- At every original edge, variation minus squared displacement covers the retained residual floor. -/
    residualMarginBounds : ∀ edge, Data.Rat.Certificate.Raw.RationalData.Le residualMarginFloor
    (variationUpper.sub
      ((sourceParameter edge).sub (targetParameter edge)).normSq)
  /-- Every original displayed source squared norm satisfies the retained floor. -/ sourceNormSqBounds : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le sourceNormSqLower
    (sourceParameter edge).normSq
  /-- Every original displayed source squared norm satisfies the retained ceiling. -/ sourceNormSqUpperBounds : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le
    (sourceParameter edge).normSq sourceNormSqUpper
  /-- Every original displayed target squared norm satisfies the retained ceiling. -/ targetNormSqBounds : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le
    (targetParameter edge).normSq targetNormSqUpper
  /-- The exact displayed rational box retained by this certificate. -/ box : Rational.Box.Certificate.RationalBoxData
  /-- The displayed ceiling for squared real constant terms on both original vertical sides. -/ verticalRealUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed ceiling for squared real constant terms on both original horizontal sides. -/ horizontalRealUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed ceiling for the original squared imaginary constant terms. -/ imaginaryUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained exact maximum of the original squared y-endpoints. -/ verticalIntervalSqUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained exact maximum of the original squared x-endpoints. -/ horizontalIntervalSqUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained ceiling for both original squared x-side coordinates. -/ xSqUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained ceiling for both original squared y-side coordinates. -/ ySqUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained common ceiling for the original quadratic boundary-side majorants. -/ sideMajorantUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed common floor for the original direct boundary clearance. -/ directLower :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed common ceiling for the original direct boundary clearance. -/ directUpper :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed vertical interval bound equals the maximum of the original squared y-endpoints. -/
    verticalIntervalExact : Data.Rat.Certificate.Raw.RationalData.Eq verticalIntervalSqUpper
    (maxData (squareData box.yLower) (squareData box.yUpper))
  /-- The displayed horizontal interval bound equals the maximum of the original squared x-endpoints. -/
    horizontalIntervalExact : Data.Rat.Certificate.Raw.RationalData.Eq horizontalIntervalSqUpper
    (maxData (squareData box.xLower) (squareData box.xUpper))
  /-- The original left coordinate squared satisfies its retained coordinate ceiling. -/ leftXSqBound :
    Data.Rat.Certificate.Raw.RationalData.Le (squareData box.xLower) xSqUpper
  /-- The original right coordinate squared satisfies its retained coordinate ceiling. -/ rightXSqBound :
    Data.Rat.Certificate.Raw.RationalData.Le (squareData box.xUpper) xSqUpper
  /-- The original bottom coordinate squared satisfies its retained coordinate ceiling. -/ bottomYSqBound :
    Data.Rat.Certificate.Raw.RationalData.Le (squareData box.yLower) ySqUpper
  /-- The original top coordinate squared satisfies its retained coordinate ceiling. -/ topYSqBound :
    Data.Rat.Certificate.Raw.RationalData.Le (squareData box.yUpper) ySqUpper
  /-- Every retained edge has checked positive squared elimination determinant on the original left side. -/
    leftDeterminantPositive : ∀ edge, RationalData.Lt zero
    (squareData (verticalDeterminantData box.xLower (sourceParameter edge)))
  /-- Every retained edge has checked positive squared elimination determinant on the original right side. -/
    rightDeterminantPositive : ∀ edge, RationalData.Lt zero
    (squareData (verticalDeterminantData box.xUpper (sourceParameter edge)))
  /-- Every retained edge has checked positive squared elimination determinant on the original bottom side. -/
    bottomDeterminantPositive : ∀ edge, RationalData.Lt zero
    (squareData (horizontalDeterminantData box.yLower (sourceParameter edge)))
  /-- Every retained edge has checked positive squared elimination determinant on the original top side. -/
    topDeterminantPositive : ∀ edge, RationalData.Lt zero
    (squareData (horizontalDeterminantData box.yUpper (sourceParameter edge)))
  /-- The retained direct floor times the vertical majorant is bounded by the original left squared determinant. -/
    leftDirectLower : ∀ edge, Data.Rat.Certificate.Raw.RationalData.Le
    (Data.Rat.Certificate.Raw.RationalData.mul directLower
      (verticalMajorantData box.xLower (sourceParameter edge)
        verticalIntervalSqUpper))
    (squareData (verticalDeterminantData box.xLower (sourceParameter edge)))
  /-- The retained direct floor times the vertical majorant is bounded by the original right squared determinant. -/
    rightDirectLower : ∀ edge, Data.Rat.Certificate.Raw.RationalData.Le
    (Data.Rat.Certificate.Raw.RationalData.mul directLower
      (verticalMajorantData box.xUpper (sourceParameter edge)
        verticalIntervalSqUpper))
    (squareData (verticalDeterminantData box.xUpper (sourceParameter edge)))
  /-- The retained direct floor times the horizontal majorant is bounded by the original bottom squared determinant. -/
    bottomDirectLower : ∀ edge, Data.Rat.Certificate.Raw.RationalData.Le
    (Data.Rat.Certificate.Raw.RationalData.mul directLower
      (horizontalMajorantData box.yLower (sourceParameter edge)
        horizontalIntervalSqUpper))
    (squareData (horizontalDeterminantData box.yLower (sourceParameter edge)))
  /-- The retained direct floor times the horizontal majorant is bounded by the original top squared determinant. -/
    topDirectLower : ∀ edge, Data.Rat.Certificate.Raw.RationalData.Le
    (Data.Rat.Certificate.Raw.RationalData.mul directLower
      (horizontalMajorantData box.yUpper (sourceParameter edge)
        horizontalIntervalSqUpper))
    (squareData (horizontalDeterminantData box.yUpper (sourceParameter edge)))
  /-- For each original edge, a checked side determinant supplies the retained common direct-clearance ceiling. -/
    directUpperWitness : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le
        (squareData (verticalDeterminantData box.xLower (sourceParameter edge)))
        (Data.Rat.Certificate.Raw.RationalData.mul directUpper
          (verticalMajorantData box.xLower (sourceParameter edge)
            verticalIntervalSqUpper)) ∨
    Data.Rat.Certificate.Raw.RationalData.Le
        (squareData (verticalDeterminantData box.xUpper (sourceParameter edge)))
        (Data.Rat.Certificate.Raw.RationalData.mul directUpper
          (verticalMajorantData box.xUpper (sourceParameter edge)
            verticalIntervalSqUpper)) ∨
    Data.Rat.Certificate.Raw.RationalData.Le
        (squareData (horizontalDeterminantData box.yLower (sourceParameter edge)))
        (Data.Rat.Certificate.Raw.RationalData.mul directUpper
          (horizontalMajorantData box.yLower (sourceParameter edge)
            horizontalIntervalSqUpper)) ∨
    Data.Rat.Certificate.Raw.RationalData.Le
        (squareData (horizontalDeterminantData box.yUpper (sourceParameter edge)))
        (Data.Rat.Certificate.Raw.RationalData.mul directUpper
          (horizontalMajorantData box.yUpper (sourceParameter edge)
            horizontalIntervalSqUpper))
  /-- The original left squared real constant satisfies the retained vertical ceiling at every edge. -/
    leftVerticalBounds : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le
      (verticalRealConstantSq box.xLower (sourceParameter edge))
      verticalRealUpper
  /-- The original right squared real constant satisfies the retained vertical ceiling at every edge. -/
    rightVerticalBounds : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le
      (verticalRealConstantSq box.xUpper (sourceParameter edge))
      verticalRealUpper
  /-- The original bottom squared real constant satisfies the retained horizontal ceiling at every edge. -/
    bottomHorizontalBounds : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le
      (horizontalRealConstantSq box.yLower (sourceParameter edge))
      horizontalRealUpper
  /-- The original top squared real constant satisfies the retained horizontal ceiling at every edge. -/
    topHorizontalBounds : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le
      (horizontalRealConstantSq box.yUpper (sourceParameter edge))
      horizontalRealUpper
  /-- Each original parameter's squared imaginary constant satisfies the displayed common ceiling. -/ imaginaryBounds :
    ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le (imaginaryConstantSq (sourceParameter edge))
      imaginaryUpper
  /-- The displayed vertical quadratic side budget satisfies the retained common majorant ceiling. -/
    verticalBudgetBound : Data.Rat.Certificate.Raw.RationalData.Le
    (sideBudgetData verticalIntervalSqUpper xSqUpper verticalRealUpper
      imaginaryUpper) sideMajorantUpper
  /-- The displayed horizontal quadratic side budget satisfies the retained common majorant ceiling. -/
    horizontalBudgetBound : Data.Rat.Certificate.Raw.RationalData.Le
    (sideBudgetData horizontalIntervalSqUpper ySqUpper horizontalRealUpper
      imaginaryUpper) sideMajorantUpper

constructive_injectivity PreparedExplicitSideBoundsData

set_option genInjectivity false in
/-- Extra generated comparisons required by a retained-floor same-box cell
at an explicitly selected transport margin.

The selected transport margin and exact edge run retain the checked comparisons that let the original box carry each
edge without recentering. -/
structure PreparedParametricSameBoxCellBoundsData extends
    PreparedExplicitSideBoundsData where
  /-- The original first edge index of the retained contiguous run. -/ firstEdge : Nat
  /-- The retained number of original edges in the contiguous run. -/ edgeCount : Nat
  /-- The retained first edge belongs to the original eight-edge segment. -/ firstEdgeLtEight : firstEdge < 8
  /-- The retained run contains at least one edge. -/ edgeCountPositive : 0 < edgeCount
  /-- The retained run's first index plus its length is at most eight. -/ edgeEndLeEight : firstEdge + edgeCount ≤ 8
  /-- The retained direct-clearance ceiling specific to each original edge. -/ directUpperAt : Fin 8 →
    Data.Rat.Certificate.Raw.RationalData
  /-- For each original edge, a checked side determinant supplies its retained edge-specific direct-clearance
ceiling. -/
  directUpperAtWitness : ∀ edge,
    Data.Rat.Certificate.Raw.RationalData.Le
        (squareData (verticalDeterminantData box.xLower (sourceParameter edge)))
        (Data.Rat.Certificate.Raw.RationalData.mul (directUpperAt edge)
          (verticalMajorantData box.xLower (sourceParameter edge)
            verticalIntervalSqUpper)) ∨
    Data.Rat.Certificate.Raw.RationalData.Le
        (squareData (verticalDeterminantData box.xUpper (sourceParameter edge)))
        (Data.Rat.Certificate.Raw.RationalData.mul (directUpperAt edge)
          (verticalMajorantData box.xUpper (sourceParameter edge)
            verticalIntervalSqUpper)) ∨
    Data.Rat.Certificate.Raw.RationalData.Le
        (squareData (horizontalDeterminantData box.yLower (sourceParameter edge)))
        (Data.Rat.Certificate.Raw.RationalData.mul (directUpperAt edge)
          (horizontalMajorantData box.yLower (sourceParameter edge)
            horizontalIntervalSqUpper)) ∨
    Data.Rat.Certificate.Raw.RationalData.Le
        (squareData (horizontalDeterminantData box.yUpper (sourceParameter edge)))
        (Data.Rat.Certificate.Raw.RationalData.mul (directUpperAt edge)
          (horizontalMajorantData box.yUpper (sourceParameter edge)
            horizontalIntervalSqUpper))
  /-- The original displayed Gaussian origin of the affine segment. -/ affineOrigin :
    Gaussian.Certificate.Raw.GaussianData
  /-- The original displayed Gaussian direction of the affine segment. -/ affineDirection :
    Gaussian.Certificate.Raw.GaussianData
  /-- The retained exact displayed squared norm of the affine origin. -/ affineOriginNormSq :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained exact displayed squared norm of the affine direction. -/ affineDirectionNormSq :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained dense-Horner quartic Lipschitz ceiling, bounded below by one. -/ affineDenseLipschitz :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed origin squared norm equals the original Gaussian calculation. -/ affineOriginNormSqExact :
    Data.Rat.Certificate.Raw.RationalData.Eq affineOrigin.normSq
    affineOriginNormSq
  /-- The displayed direction squared norm equals the original Gaussian calculation. -/ affineDirectionNormSqExact :
    Data.Rat.Certificate.Raw.RationalData.Eq affineDirection.normSq
    affineDirectionNormSq
  /-- The retained Lipschitz ceiling equals the maximum of one and the original quartic slope formula. -/
    affineDenseLipschitzExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (maxData (naturalData 1)
      (affineQuarticSlopeData affineOriginNormSq affineDirectionNormSq))
    affineDenseLipschitz
  /-- The retained variation ceiling equals the original affine Lipschitz ceiling times one sixty-fourth. -/
    affineVariationExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (Data.Rat.Certificate.Raw.RationalData.mul affineDenseLipschitz oneSixtyFourthData)
    variationUpper
  /-- The original affine quartic value at the selected edge's eighth-grid start equals the displayed source
parameter. -/
  affineSourceParameterExact : ∀ edge, firstEdge ≤ edge.val →
    edge.val < firstEdge + edgeCount → Gaussian.Certificate.Raw.GaussianData.Eq
    (affineQuarticParameterData affineOrigin affineDirection
      (eighthParameterData edge.val))
    (sourceParameter edge)
  /-- The original affine quartic value at the selected edge's eighth-grid endpoint equals the displayed target
    parameter. -/ affineTargetParameterExact : ∀ edge, firstEdge ≤ edge.val →
    edge.val < firstEdge + edgeCount → Gaussian.Certificate.Raw.GaussianData.Eq
    (affineQuarticParameterData affineOrigin affineDirection
    (eighthParameterData (edge.val + 1)))
    (targetParameter edge)
  /-- A checked strict coordinate comparison separates the original source and target parameters. -/
    sourceTargetDifferent : ∀ edge, GaussianData.Different
    (sourceParameter edge) (targetParameter edge)
  /-- The retained segment-source floor bounds the original quartic value's squared norm at the affine origin. -/
    affineOriginNormSqLower : Data.Rat.Certificate.Raw.RationalData.Le sourceNormSqLower
    (quarticParameterData affineOrigin).normSq
  /-- The original displayed box's squared diagonal is strictly below five. -/ boxDiagonalLtFive : RationalData.Lt
    (boxDiagonalSqData box)
    (naturalData 5)
  /-- The original box's lower x coordinate is at least negative three. -/ boxNegativeThreeLeXLower :
    Data.Rat.Certificate.Raw.RationalData.Le (naturalData 3).neg box.xLower
  /-- The original box's upper x coordinate is at most three. -/ boxXUpperLeThree :
    Data.Rat.Certificate.Raw.RationalData.Le box.xUpper (naturalData 3)
  /-- The original box's lower y coordinate is at least negative three. -/ boxNegativeThreeLeYLower :
    Data.Rat.Certificate.Raw.RationalData.Le (naturalData 3).neg box.yLower
  /-- The original box's upper y coordinate is at most three. -/ boxYUpperLeThree :
    Data.Rat.Certificate.Raw.RationalData.Le box.yUpper (naturalData 3)
  /-- The retained displayed derivative-majorant floor. -/ predictedDerivativeLower :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained derivative floor equals the original fixed-margin formula from the source squared-norm floor. -/
    predictedDerivativeLowerExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (predictedDerivativeLowerData sourceNormSqLower)
    predictedDerivativeLower
  /-- The exact displayed retained transport margin. -/ transportMargin : Data.Rat.Certificate.Raw.RationalData
  /-- The retained transport margin is strictly positive by cross-product comparison. -/ transportMarginPositive :
    RationalData.Lt zero transportMargin
  /-- The original predicted-clearance numerator fits the retained transport floor times its certified denominator
    floor. -/ predictedClearanceFitsTransport : Data.Rat.Certificate.Raw.RationalData.Le
    predictedClearanceNumeratorData
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor transportMargin)
      (predictedClearanceDenominatorLowerData predictedDerivativeLower))
  /-- The retained squared-margin transport floor does not exceed the original direct-clearance floor. -/
    retainedFloorLeDirectLower : Data.Rat.Certificate.Raw.RationalData.Le
    (transportFloor transportMargin) directLower
  /-- The displayed variation ceiling is strictly below the original direct-clearance floor. -/ directCarries :
    RationalData.Lt variationUpper directLower
  /-- The retained residual floor is strictly positive by cross-product comparison. -/ residualMarginPositive :
    RationalData.Lt zero residualMarginFloor
  /-- The retained common side-majorant ceiling is at least one. -/ oneLeSideMajorant :
    Data.Rat.Certificate.Raw.RationalData.Le (naturalData 1) sideMajorantUpper
  /-- The retained transport floor times four times the side-majorant ceiling is bounded by the squared residual
floor. -/
  retainedFloorTradeoff : Data.Rat.Certificate.Raw.RationalData.Le
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor transportMargin)
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) sideMajorantUpper))
    (squareData residualMarginFloor)
  /-- The retained source squared-norm ceiling is at most 256. -/ sourceNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le sourceNormSqUpper
    twoHundredFiftySix
  /-- The retained target squared-norm ceiling is at most 256. -/ targetNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le targetNormSqUpper
    twoHundredFiftySix

constructive_injectivity PreparedParametricSameBoxCellBoundsData

set_option genInjectivity false in
/-- A same-box cell with the retained one-eighth transport margin.

The inherited parametric same-box fields retain a transport margin equal to the exact displayed one-eighth value. -/
structure PreparedSameBoxCellBoundsData extends
    PreparedParametricSameBoxCellBoundsData where
  /-- The retained transport margin is exactly the displayed one-eighth value. -/ transportMarginIsEighth :
    Data.Rat.Certificate.Raw.RationalData.Eq transportMargin oneEighthData

constructive_injectivity PreparedSameBoxCellBoundsData

set_option genInjectivity false in
/-- Generator-selected cap transition for one same-box action.

The original same-box action retains its selected per-edge ceiling and the cap transition between the two retained owner
states. -/
structure PreparedSameBoxReplayCapData
    (cell : PreparedParametricSameBoxCellBoundsData) (edge : Fin 8) where
  /-- The original retained incoming replay cap. -/ sourceUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The retained outgoing replay cap. -/ targetUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The original edge-specific direct-clearance ceiling fits the retained target cap. -/ directUpperLe :
    Data.Rat.Certificate.Raw.RationalData.Le (cell.directUpperAt edge) targetUpper
  /-- The retained incoming cap squared and divided by four fits the outgoing cap. -/ sourceQuarterLeTarget :
    Data.Rat.Certificate.Raw.RationalData.Le
    (quarterSquare sourceUpper) targetUpper
  /-- The retained outgoing cap bounds its own square divided by four. -/ targetContracts :
    Data.Rat.Certificate.Raw.RationalData.Le
    (quarterSquare targetUpper) targetUpper

constructive_injectivity PreparedSameBoxReplayCapData

set_option genInjectivity false in
/-- Generator-selected initial cap for a prepared-bank replay.

The exact edge-zero ceiling bounds the direct owner clearance and all four retained ambient-side clearances. -/
structure PreparedInitialReplayCapData
    (cell : PreparedParametricSameBoxCellBoundsData) where
  /-- The original retained incoming replay cap. -/ sourceUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The original edge-zero direct-clearance ceiling fits the retained source cap squared and divided by four. -/
    directUpperLeQuarter : Data.Rat.Certificate.Raw.RationalData.Le (cell.directUpperAt 0)
    (quarterSquare sourceUpper)
  /-- The retained source cap bounds its own square divided by four. -/ sourceContracts :
    Data.Rat.Certificate.Raw.RationalData.Le (quarterSquare sourceUpper) sourceUpper
  /-- The retained squared x-coordinate ceiling is at most sixteen. -/ xSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le cell.xSqUpper (naturalData 16)
  /-- The retained squared y-coordinate ceiling is at most sixteen. -/ ySqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le cell.ySqUpper (naturalData 16)

constructive_injectivity PreparedInitialReplayCapData

set_option genInjectivity false in
/-- Generator-owned endpoint data for one eight-edge boundary cell.

The eight-edge boundary cell retains the ordered endpoint boxes, replay caps and margins at the exact selected indices.
-/
structure PreparedSegmentReplayScheduleData where
  /-- The original displayed owner box at each of the nine retained segment endpoints. -/ boxAt : Fin 9 →
    Rational.Box.Certificate.RationalBoxData
  /-- The original replay cap retained at each of the nine segment endpoints. -/ upperAt : Fin 9 →
    Data.Rat.Certificate.Raw.RationalData
  /-- The original transport margin retained at each of the nine segment endpoints. -/ marginAt : Fin 9 →
    Data.Rat.Certificate.Raw.RationalData
  /-- The original displayed source parameter at each of the eight segment edges. -/ sourceParameterAt : Fin 8 →
    Gaussian.Certificate.Raw.GaussianData
  /-- The original displayed Gaussian direction of the scheduled segment. -/ direction :
    Gaussian.Certificate.Raw.GaussianData

constructive_injectivity PreparedSegmentReplayScheduleData

set_option genInjectivity false in
/-- Generator-owned arithmetic for a moving-recenter edge whose incoming and
outgoing retained floors may differ.

The affine edge and incoming and outgoing floors retain the exact checked arithmetic for the selected moving recenter.
-/
structure PreparedParametricResetCellBoundsData where
  /-- The original same-box cell immediately preceding the reset. -/ beforeCell :
    PreparedParametricSameBoxCellBoundsData
  /-- The original same-box cell immediately following the reset. -/ afterCell : PreparedParametricSameBoxCellBoundsData
  /-- The original pre-reset data and their retained numerical bounds. -/ source : PreparedExplicitSideBoundsData
  /-- The selected final box's original parameter and side-bound data. -/ final : PreparedExplicitSideBoundsData
  /-- The checked reduced computation and exact box projection for the original moving reset. -/ moving :
    MovingResetProjectionData
  /-- The original edge index selected for the moving reset. -/ resetEdge : Nat
  /-- The retained reset index belongs to the original eight-edge segment. -/ resetEdgeLtEight : resetEdge < 8
  /-- The original displayed Gaussian origin of the affine segment. -/ affineOrigin :
    Gaussian.Certificate.Raw.GaussianData
  /-- The original displayed Gaussian direction of the affine segment. -/ affineDirection :
    Gaussian.Certificate.Raw.GaussianData
  /-- The retained exact displayed squared norm of the affine origin. -/ affineOriginNormSq :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained exact displayed squared norm of the affine direction. -/ affineDirectionNormSq :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained dense-Horner quartic Lipschitz ceiling, bounded below by one. -/ affineDenseLipschitz :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed origin squared norm equals the original Gaussian calculation. -/ affineOriginNormSqExact :
    Data.Rat.Certificate.Raw.RationalData.Eq affineOrigin.normSq
    affineOriginNormSq
  /-- The displayed direction squared norm equals the original Gaussian calculation. -/ affineDirectionNormSqExact :
    Data.Rat.Certificate.Raw.RationalData.Eq affineDirection.normSq
    affineDirectionNormSq
  /-- The retained Lipschitz ceiling equals the maximum of one and the original quartic slope formula. -/
    affineDenseLipschitzExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (maxData (naturalData 1)
      (affineQuarticSlopeData affineOriginNormSq affineDirectionNormSq))
    affineDenseLipschitz
  /-- The retained variation ceiling equals the original affine Lipschitz ceiling times one sixty-fourth. -/
    affineVariationExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (Data.Rat.Certificate.Raw.RationalData.mul affineDenseLipschitz oneSixtyFourthData)
    source.variationUpper
  /-- The original affine quartic value at the selected edge's eighth-grid start equals the displayed source
parameter. -/
  affineSourceParameterExact : Gaussian.Certificate.Raw.GaussianData.Eq
    (affineQuarticParameterData affineOrigin affineDirection
      (eighthParameterData resetEdge))
    (source.sourceParameter 0)
  /-- The original affine quartic value at the selected edge's eighth-grid endpoint equals the displayed target
    parameter. -/ affineTargetParameterExact : Gaussian.Certificate.Raw.GaussianData.Eq
    (affineQuarticParameterData affineOrigin affineDirection
      (eighthParameterData (resetEdge + 1)))
    (source.targetParameter 0)
  /-- A checked strict coordinate comparison separates the original source and target parameters. -/
    sourceTargetDifferent : GaussianData.Different
    (source.sourceParameter 0) (source.targetParameter 0)
  /-- The retained squared-norm floor for the original quartic parameter at the segment origin. -/
    segmentSourceNormSqLower : Data.Rat.Certificate.Raw.RationalData
  /-- The retained segment-source floor bounds the original quartic value's squared norm at the affine origin. -/
    affineOriginNormSqLower : Data.Rat.Certificate.Raw.RationalData.Le segmentSourceNormSqLower
    (quarticParameterData affineOrigin).normSq
  /-- The retained displayed derivative-majorant floor. -/ predictedDerivativeLower :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained derivative floor equals the original fixed-margin formula from the source squared-norm floor. -/
    predictedDerivativeLowerExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (predictedDerivativeLowerData segmentSourceNormSqLower)
    predictedDerivativeLower
  /-- The original predicted-clearance numerator fits the retained before transport floor times its certified
    denominator floor. -/ predictedClearanceFitsBefore : Data.Rat.Certificate.Raw.RationalData.Le
    predictedClearanceNumeratorData
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor beforeCell.transportMargin)
      (predictedClearanceDenominatorLowerData predictedDerivativeLower))
  /-- The original predicted-clearance numerator fits the retained after transport floor times its certified denominator
    floor. -/ predictedClearanceFitsAfter : Data.Rat.Certificate.Raw.RationalData.Le
    predictedClearanceNumeratorData
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor afterCell.transportMargin)
      (predictedClearanceDenominatorLowerData predictedDerivativeLower))
  /-- The retained replay cap before the original reset. -/ beforeUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The retained replay cap after the original reset. -/ afterUpper : Data.Rat.Certificate.Raw.RationalData
  /-- Checked coordinate comparisons identify the source box with the preceding cell's original box. -/
    sourceBoxMatchesBefore : BoxEq source.box beforeCell.box
  /-- Checked coordinate comparisons identify the final box with the following cell's original box. -/
    finalBoxMatchesAfter : BoxEq final.box afterCell.box
  /-- Checked coordinates identify the source and final records' original source parameters. -/
    sourceFinalParameterMatch : Gaussian.Certificate.Raw.GaussianData.Eq
    (source.sourceParameter 0) (final.sourceParameter 0)
  /-- The retained reduced moving computation uses exactly the original reset source parameter. -/
    movingParameterMatchesSource : Gaussian.Certificate.Raw.GaussianData.Eq moving.parameter.original
    (source.sourceParameter 0)
  /-- The moving computation's original input box equals the retained source box. -/ movingSourceBoxMatches : BoxEq
    moving.sourceBox.original source.box
  /-- The moving computation's original returned box equals the retained final box. -/ movingFinalBoxMatches : BoxEq
    moving.finalBox.original final.box
  /-- The retained incoming cap bounds its own square divided by four. -/ beforeUpperContracts :
    Data.Rat.Certificate.Raw.RationalData.Le (quarterSquare beforeUpper) beforeUpper
  /-- The retained outgoing cap bounds its own square divided by four. -/ afterUpperContracts :
    Data.Rat.Certificate.Raw.RationalData.Le (quarterSquare afterUpper) afterUpper
  /-- The incoming cap squared and divided by four does not exceed the original variation ceiling. -/
    beforeQuarterLeVariation : Data.Rat.Certificate.Raw.RationalData.Le
    (quarterSquare beforeUpper) source.variationUpper
  /-- The original source direct-clearance ceiling does not exceed the variation ceiling, requiring a reset. -/
    sourceUpperLeVariation : Data.Rat.Certificate.Raw.RationalData.Le
    source.directUpper source.variationUpper
  /-- The original variation ceiling is strictly below the selected final direct-clearance floor. -/
    variationLtFinalLower : RationalData.Lt
    source.variationUpper final.directLower
  /-- The retained outgoing transport floor does not exceed the selected final direct-clearance floor. -/
    transportFloorLeFinalLower : Data.Rat.Certificate.Raw.RationalData.Le
    (transportFloor afterCell.transportMargin) final.directLower
  /-- The selected final direct-clearance ceiling fits the retained outgoing cap. -/ finalUpperLeAfterUpper :
    Data.Rat.Certificate.Raw.RationalData.Le final.directUpper afterUpper
  /-- The original reset source's retained residual floor is strictly positive. -/ resetResidualPositive :
    RationalData.Lt zero source.residualMarginFloor
  /-- Final direct clearance minus original displacement covers the retained reset residual floor. -/
    resetResidualLeFinalLowerSubDisplacement : Data.Rat.Certificate.Raw.RationalData.Le
    source.residualMarginFloor
    (Data.Rat.Certificate.Raw.RationalData.sub final.directLower source.displacementUpper)
  /-- The selected final box's retained side-majorant ceiling is at least one. -/ oneLeFinalSideMajorant :
    Data.Rat.Certificate.Raw.RationalData.Le
    (naturalData 1) final.sideMajorantUpper
  /-- The retained transport floor times four times the side-majorant ceiling is bounded by the squared residual
floor. -/
  retainedFloorTradeoff : Data.Rat.Certificate.Raw.RationalData.Le
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor afterCell.transportMargin)
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) final.sideMajorantUpper))
    (squareData source.residualMarginFloor)
  /-- The retained source squared-norm ceiling is at most 256. -/ sourceNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le source.sourceNormSqUpper
    twoHundredFiftySix
  /-- The retained target squared-norm ceiling is at most 256. -/ targetNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le source.targetNormSqUpper
    twoHundredFiftySix
  /-- The selected final box's retained squared x-coordinate ceiling is at most sixteen. -/ finalXSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le final.xSqUpper (naturalData 16)
  /-- The selected final box's retained squared y-coordinate ceiling is at most sixteen. -/ finalYSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le final.ySqUpper (naturalData 16)

constructive_injectivity PreparedParametricResetCellBoundsData

set_option genInjectivity false in
/-- Generator-owned arithmetic for an edge on which the bounded preparation
loop selects its second moving recenter.

The first selected moving box retains its insufficient strengthened clearance; the second selected box retains the
checked carrying bound. -/
structure PreparedParametricDoubleResetCellBoundsData where
  /-- The original same-box cell immediately preceding the reset. -/ beforeCell :
    PreparedParametricSameBoxCellBoundsData
  /-- The original same-box cell immediately following the reset. -/ afterCell : PreparedParametricSameBoxCellBoundsData
  /-- The original pre-reset data and their retained numerical bounds. -/ source : PreparedExplicitSideBoundsData
  /-- The first reset's selected box and bounds, retained before the second reset. -/ intermediate :
    PreparedExplicitSideBoundsData
  /-- The selected final box's original parameter and side-bound data. -/ final : PreparedExplicitSideBoundsData
  /-- The checked reduced computation and exact box projection for the first moving reset. -/ firstMoving :
    MovingResetProjectionData
  /-- The checked reduced computation and exact box projection for the second moving reset. -/ secondMoving :
    MovingResetProjectionData
  /-- The original edge index selected for the moving reset. -/ resetEdge : Nat
  /-- The retained reset index belongs to the original eight-edge segment. -/ resetEdgeLtEight : resetEdge < 8
  /-- The original displayed Gaussian origin of the affine segment. -/ affineOrigin :
    Gaussian.Certificate.Raw.GaussianData
  /-- The original displayed Gaussian direction of the affine segment. -/ affineDirection :
    Gaussian.Certificate.Raw.GaussianData
  /-- The retained exact displayed squared norm of the affine origin. -/ affineOriginNormSq :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained exact displayed squared norm of the affine direction. -/ affineDirectionNormSq :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained dense-Horner quartic Lipschitz ceiling, bounded below by one. -/ affineDenseLipschitz :
    Data.Rat.Certificate.Raw.RationalData
  /-- The displayed origin squared norm equals the original Gaussian calculation. -/ affineOriginNormSqExact :
    Data.Rat.Certificate.Raw.RationalData.Eq affineOrigin.normSq
    affineOriginNormSq
  /-- The displayed direction squared norm equals the original Gaussian calculation. -/ affineDirectionNormSqExact :
    Data.Rat.Certificate.Raw.RationalData.Eq affineDirection.normSq
    affineDirectionNormSq
  /-- The retained Lipschitz ceiling equals the maximum of one and the original quartic slope formula. -/
    affineDenseLipschitzExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (maxData (naturalData 1)
      (affineQuarticSlopeData affineOriginNormSq affineDirectionNormSq))
    affineDenseLipschitz
  /-- The retained variation ceiling equals the original affine Lipschitz ceiling times one sixty-fourth. -/
    affineVariationExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (Data.Rat.Certificate.Raw.RationalData.mul affineDenseLipschitz oneSixtyFourthData)
    source.variationUpper
  /-- The original affine quartic value at the selected edge's eighth-grid start equals the displayed source
parameter. -/
  affineSourceParameterExact : Gaussian.Certificate.Raw.GaussianData.Eq
    (affineQuarticParameterData affineOrigin affineDirection
      (eighthParameterData resetEdge))
    (source.sourceParameter 0)
  /-- The original affine quartic value at the selected edge's eighth-grid endpoint equals the displayed target
    parameter. -/ affineTargetParameterExact : Gaussian.Certificate.Raw.GaussianData.Eq
    (affineQuarticParameterData affineOrigin affineDirection
      (eighthParameterData (resetEdge + 1)))
    (source.targetParameter 0)
  /-- A checked strict coordinate comparison separates the original source and target parameters. -/
    sourceTargetDifferent : GaussianData.Different
    (source.sourceParameter 0) (source.targetParameter 0)
  /-- The retained squared-norm floor for the original quartic parameter at the segment origin. -/
    segmentSourceNormSqLower : Data.Rat.Certificate.Raw.RationalData
  /-- The retained segment-source floor bounds the original quartic value's squared norm at the affine origin. -/
    affineOriginNormSqLower : Data.Rat.Certificate.Raw.RationalData.Le segmentSourceNormSqLower
    (quarticParameterData affineOrigin).normSq
  /-- The retained displayed derivative-majorant floor. -/ predictedDerivativeLower :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained derivative floor equals the original fixed-margin formula from the source squared-norm floor. -/
    predictedDerivativeLowerExact : Data.Rat.Certificate.Raw.RationalData.Eq
    (predictedDerivativeLowerData segmentSourceNormSqLower)
    predictedDerivativeLower
  /-- The original predicted-clearance numerator fits the retained before transport floor times its certified
    denominator floor. -/ predictedClearanceFitsBefore : Data.Rat.Certificate.Raw.RationalData.Le
    predictedClearanceNumeratorData
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor beforeCell.transportMargin)
      (predictedClearanceDenominatorLowerData predictedDerivativeLower))
  /-- The exact displayed transport margin retained after the first reset. -/ intermediateMargin :
    Data.Rat.Certificate.Raw.RationalData
  /-- The retained intermediate transport margin is strictly positive. -/ intermediateMarginPositive : RationalData.Lt
    zero intermediateMargin
  /-- The original predicted-clearance numerator fits the retained intermediate transport floor times its certified
    denominator floor. -/ predictedClearanceFitsIntermediate : Data.Rat.Certificate.Raw.RationalData.Le
    predictedClearanceNumeratorData
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor intermediateMargin)
      (predictedClearanceDenominatorLowerData predictedDerivativeLower))
  /-- The original predicted-clearance numerator fits the retained after transport floor times its certified denominator
    floor. -/ predictedClearanceFitsAfter : Data.Rat.Certificate.Raw.RationalData.Le
    predictedClearanceNumeratorData
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor afterCell.transportMargin)
      (predictedClearanceDenominatorLowerData predictedDerivativeLower))
  /-- The retained replay cap before the original reset. -/ beforeUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The retained replay cap after the original reset. -/ afterUpper : Data.Rat.Certificate.Raw.RationalData
  /-- Checked coordinate comparisons identify the source box with the preceding cell's original box. -/
    sourceBoxMatchesBefore : BoxEq source.box beforeCell.box
  /-- Checked coordinate comparisons identify the final box with the following cell's original box. -/
    finalBoxMatchesAfter : BoxEq final.box afterCell.box
  /-- Checked coordinates identify the source and intermediate records' original source parameters. -/
    sourceIntermediateParameterMatch : Gaussian.Certificate.Raw.GaussianData.Eq
    (source.sourceParameter 0) (intermediate.sourceParameter 0)
  /-- Checked coordinates identify the source and final records' original source parameters. -/
    sourceFinalParameterMatch : Gaussian.Certificate.Raw.GaussianData.Eq
    (source.sourceParameter 0) (final.sourceParameter 0)
  /-- The first reset's selected original box has squared diagonal strictly below five. -/ intermediateBoxDiagonalLtFive
    : RationalData.Lt
    (boxDiagonalSqData intermediate.box) (naturalData 5)
  /-- The original intermediate box's lower x coordinate is at least negative three. -/
    intermediateBoxNegativeThreeLeXLower : Data.Rat.Certificate.Raw.RationalData.Le
    (naturalData 3).neg intermediate.box.xLower
  /-- The original intermediate box's upper x coordinate is at most three. -/ intermediateBoxXUpperLeThree :
    Data.Rat.Certificate.Raw.RationalData.Le
    intermediate.box.xUpper (naturalData 3)
  /-- The original intermediate box's lower y coordinate is at least negative three. -/
    intermediateBoxNegativeThreeLeYLower : Data.Rat.Certificate.Raw.RationalData.Le
    (naturalData 3).neg intermediate.box.yLower
  /-- The original intermediate box's upper y coordinate is at most three. -/ intermediateBoxYUpperLeThree :
    Data.Rat.Certificate.Raw.RationalData.Le
    intermediate.box.yUpper (naturalData 3)
  /-- The retained reduced moving computation uses exactly the original reset source parameter. -/
    firstMovingParameterMatchesSource : Gaussian.Certificate.Raw.GaussianData.Eq
    firstMoving.parameter.original (source.sourceParameter 0)
  /-- The moving computation's original input box equals the retained source box. -/ firstMovingSourceBoxMatches : BoxEq
    firstMoving.sourceBox.original source.box
  /-- The moving computation's original returned box equals the retained intermediate box. -/ firstMovingFinalBoxMatches
    : BoxEq firstMoving.finalBox.original
    intermediate.box
  /-- The retained reduced moving computation uses exactly the original reset source parameter. -/
    secondMovingParameterMatchesSource : Gaussian.Certificate.Raw.GaussianData.Eq
    secondMoving.parameter.original (source.sourceParameter 0)
  /-- The moving computation's original input box equals the retained intermediate box. -/ secondMovingSourceBoxMatches
    : BoxEq secondMoving.sourceBox.original
    intermediate.box
  /-- The moving computation's original returned box equals the retained final box. -/ secondMovingFinalBoxMatches :
    BoxEq secondMoving.finalBox.original final.box
  /-- The retained incoming cap bounds its own square divided by four. -/ beforeUpperContracts :
    Data.Rat.Certificate.Raw.RationalData.Le (quarterSquare beforeUpper) beforeUpper
  /-- The retained outgoing cap bounds its own square divided by four. -/ afterUpperContracts :
    Data.Rat.Certificate.Raw.RationalData.Le (quarterSquare afterUpper) afterUpper
  /-- The incoming cap squared and divided by four does not exceed the original variation ceiling. -/
    beforeQuarterLeVariation : Data.Rat.Certificate.Raw.RationalData.Le
    (quarterSquare beforeUpper) source.variationUpper
  /-- The original source direct-clearance ceiling does not exceed the variation ceiling, requiring a reset. -/
    sourceUpperLeVariation : Data.Rat.Certificate.Raw.RationalData.Le
    source.directUpper source.variationUpper
  /-- The first reset's direct-clearance ceiling still does not exceed variation, requiring the second reset. -/
    intermediateUpperLeVariation : Data.Rat.Certificate.Raw.RationalData.Le
    intermediate.directUpper source.variationUpper
  /-- The retained intermediate transport floor does not exceed the first reset's direct-clearance floor. -/
    transportFloorLeIntermediateLower : Data.Rat.Certificate.Raw.RationalData.Le
    (transportFloor intermediateMargin) intermediate.directLower
  /-- The original variation ceiling is strictly below the selected final direct-clearance floor. -/
    variationLtFinalLower : RationalData.Lt
    source.variationUpper final.directLower
  /-- The retained outgoing transport floor does not exceed the selected final direct-clearance floor. -/
    transportFloorLeFinalLower : Data.Rat.Certificate.Raw.RationalData.Le
    (transportFloor afterCell.transportMargin) final.directLower
  /-- The selected final direct-clearance ceiling fits the retained outgoing cap. -/ finalUpperLeAfterUpper :
    Data.Rat.Certificate.Raw.RationalData.Le final.directUpper afterUpper
  /-- The original reset source's retained residual floor is strictly positive. -/ resetResidualPositive :
    RationalData.Lt zero source.residualMarginFloor
  /-- Final direct clearance minus original displacement covers the retained reset residual floor. -/
    resetResidualLeFinalLowerSubDisplacement : Data.Rat.Certificate.Raw.RationalData.Le
    source.residualMarginFloor
    (Data.Rat.Certificate.Raw.RationalData.sub final.directLower source.displacementUpper)
  /-- The selected final box's retained side-majorant ceiling is at least one. -/ oneLeFinalSideMajorant :
    Data.Rat.Certificate.Raw.RationalData.Le
    (naturalData 1) final.sideMajorantUpper
  /-- The retained transport floor times four times the side-majorant ceiling is bounded by the squared residual
floor. -/
  retainedFloorTradeoff : Data.Rat.Certificate.Raw.RationalData.Le
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor afterCell.transportMargin)
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) final.sideMajorantUpper))
    (squareData source.residualMarginFloor)
  /-- The retained source squared-norm ceiling is at most 256. -/ sourceNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le source.sourceNormSqUpper
    twoHundredFiftySix
  /-- The retained target squared-norm ceiling is at most 256. -/ targetNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le source.targetNormSqUpper
    twoHundredFiftySix
  /-- The selected final box's retained squared x-coordinate ceiling is at most sixteen. -/ finalXSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le final.xSqUpper (naturalData 16)
  /-- The selected final box's retained squared y-coordinate ceiling is at most sixteen. -/ finalYSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le final.ySqUpper (naturalData 16)

constructive_injectivity PreparedParametricDoubleResetCellBoundsData

set_option genInjectivity false in
/-- Generator-owned arithmetic for one moving-recenter edge and the two
same-box runs adjacent to it.

The reset edge and adjacent same-box runs retain separate state caps and exact direct-clearance ceilings that determine
the reset branch. -/
structure PreparedResetCellBoundsData where
  /-- The original same-box cell immediately preceding the reset. -/ beforeCell : PreparedSameBoxCellBoundsData
  /-- The original same-box cell immediately following the reset. -/ afterCell : PreparedSameBoxCellBoundsData
  /-- The original pre-reset data and their retained numerical bounds. -/ source : PreparedExplicitSideBoundsData
  /-- The selected final box's original parameter and side-bound data. -/ final : PreparedExplicitSideBoundsData
  /-- The checked reduced computation and exact box projection for the original moving reset. -/ moving :
    MovingResetReductionData
  /-- The retained replay cap before the original reset. -/ beforeUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The retained replay cap after the original reset. -/ afterUpper : Data.Rat.Certificate.Raw.RationalData
  /-- The retained displayed fixed reset margin. -/ marginFloor : Data.Rat.Certificate.Raw.RationalData
  /-- The retained fixed reset margin equals the original displayed one-eighth value. -/ marginFloorIsEighth :
    Data.Rat.Certificate.Raw.RationalData.Eq marginFloor oneEighthData
  /-- Checked coordinate comparisons identify the source box with the preceding cell's original box. -/
    sourceBoxMatchesBefore : BoxEq source.box beforeCell.box
  /-- Checked coordinate comparisons identify the final box with the following cell's original box. -/
    finalBoxMatchesAfter : BoxEq final.box afterCell.box
  /-- Checked coordinates identify the source and final records' original source parameters. -/
    sourceFinalParameterMatch : Gaussian.Certificate.Raw.GaussianData.Eq
    (source.sourceParameter 0) (final.sourceParameter 0)
  /-- The retained reduced moving computation uses exactly the original reset source parameter. -/
    movingParameterMatchesSource : Gaussian.Certificate.Raw.GaussianData.Eq moving.parameter.original
    (source.sourceParameter 0)
  /-- The moving computation's original input box equals the retained source box. -/ movingSourceBoxMatches : BoxEq
    moving.sourceBox.original source.box
  /-- The moving computation's original returned box equals the retained final box. -/ movingFinalBoxMatches : BoxEq
    moving.finalBox.original final.box
  /-- The preceding cell and the original reset source retain exactly the same variation ceiling. -/
    resetVariationMatchesBefore : Data.Rat.Certificate.Raw.RationalData.Eq
    beforeCell.variationUpper source.variationUpper
  /-- The preceding cell's original direct-clearance ceiling fits the retained incoming cap. -/ beforeDirectUpperLe :
    Data.Rat.Certificate.Raw.RationalData.Le beforeCell.directUpper beforeUpper
  /-- The following cell's original direct-clearance ceiling fits the retained outgoing cap. -/ afterDirectUpperLe :
    Data.Rat.Certificate.Raw.RationalData.Le afterCell.directUpper afterUpper
  /-- The retained incoming cap bounds its own square divided by four. -/ beforeUpperContracts :
    Data.Rat.Certificate.Raw.RationalData.Le (quarterSquare beforeUpper) beforeUpper
  /-- The retained outgoing cap bounds its own square divided by four. -/ afterUpperContracts :
    Data.Rat.Certificate.Raw.RationalData.Le (quarterSquare afterUpper) afterUpper
  /-- The retained fixed reset margin is strictly positive. -/ marginFloorPositive : RationalData.Lt zero marginFloor
  /-- The incoming cap squared and divided by four does not exceed the original variation ceiling. -/
    beforeQuarterLeVariation : Data.Rat.Certificate.Raw.RationalData.Le
    (quarterSquare beforeUpper) source.variationUpper
  /-- The original source direct-clearance ceiling does not exceed the variation ceiling, requiring a reset. -/
    sourceUpperLeVariation : Data.Rat.Certificate.Raw.RationalData.Le
    source.directUpper source.variationUpper
  /-- The original variation ceiling is strictly below the selected final direct-clearance floor. -/
    variationLtFinalLower : RationalData.Lt
    source.variationUpper final.directLower
  /-- The retained outgoing transport floor does not exceed the selected final direct-clearance floor. -/
    transportFloorLeFinalLower : Data.Rat.Certificate.Raw.RationalData.Le
    (transportFloor marginFloor) final.directLower
  /-- The selected final direct-clearance ceiling fits the retained outgoing cap. -/ finalUpperLeAfterUpper :
    Data.Rat.Certificate.Raw.RationalData.Le final.directUpper afterUpper
  /-- The original reset source's retained residual floor is strictly positive. -/ resetResidualPositive :
    RationalData.Lt zero source.residualMarginFloor
  /-- Final direct clearance minus original displacement covers the retained reset residual floor. -/
    resetResidualLeFinalLowerSubDisplacement : Data.Rat.Certificate.Raw.RationalData.Le
    source.residualMarginFloor
    (Data.Rat.Certificate.Raw.RationalData.sub final.directLower source.displacementUpper)
  /-- The selected final box's retained side-majorant ceiling is at least one. -/ oneLeFinalSideMajorant :
    Data.Rat.Certificate.Raw.RationalData.Le
    (naturalData 1) final.sideMajorantUpper
  /-- The retained transport floor times four times the side-majorant ceiling is bounded by the squared residual
floor. -/
  retainedFloorTradeoff : Data.Rat.Certificate.Raw.RationalData.Le
    (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor marginFloor)
      (Data.Rat.Certificate.Raw.RationalData.mul (naturalData 4) final.sideMajorantUpper))
    (squareData source.residualMarginFloor)
  /-- The retained source squared-norm ceiling is at most 256. -/ sourceNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le source.sourceNormSqUpper
    twoHundredFiftySix
  /-- The retained target squared-norm ceiling is at most 256. -/ targetNormSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le source.targetNormSqUpper
    twoHundredFiftySix
  /-- The selected final box's original left coordinate has checked strictly positive square. -/
    finalLeftCoordinateNonzero : RationalData.Lt zero
    (squareData final.box.xLower)
  /-- The selected final box's original right coordinate has checked strictly positive square. -/
    finalRightCoordinateNonzero : RationalData.Lt zero
    (squareData final.box.xUpper)
  /-- The selected final box's original bottom coordinate has checked strictly positive square. -/
    finalBottomCoordinateNonzero : RationalData.Lt zero
    (squareData final.box.yLower)
  /-- The selected final box's original top coordinate has checked strictly positive square. -/
    finalTopCoordinateNonzero : RationalData.Lt zero
    (squareData final.box.yUpper)
  /-- The selected final box's retained squared x-coordinate ceiling is at most sixteen. -/ finalXSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le final.xSqUpper (naturalData 16)
  /-- The selected final box's retained squared y-coordinate ceiling is at most sixteen. -/ finalYSqBounded :
    Data.Rat.Certificate.Raw.RationalData.Le final.ySqUpper (naturalData 16)

constructive_injectivity PreparedResetCellBoundsData

set_option genInjectivity false in
/-- Horizontal-grid specialization retained for the reverse-horizontal
quartic certificates.

The inherited same-box fields retain the exact horizontal-grid specialization and its original coordinate identities. -/
structure PreparedSameBoxSideBoundsData extends
    PreparedExplicitSideBoundsData where
  /-- The original integer horizontal-grid index assigned to each retained edge source. -/ sourceGridIndex : Fin 8 → Int
  /-- Each displayed source parameter equals the original quartic horizontal-grid value at its retained index. -/
    sourceGridFormula : ∀ edge, Gaussian.Certificate.Raw.GaussianData.Eq (sourceParameter edge)
    (quarticHorizontalGridParameterData (sourceGridIndex edge))
  /-- The original left box coordinate has checked strictly positive square. -/ leftCoordinateNonzero : RationalData.Lt
    zero (squareData box.xLower)
  /-- The original right box coordinate has checked strictly positive square. -/ rightCoordinateNonzero :
    RationalData.Lt zero (squareData box.xUpper)
  /-- The original bottom box coordinate has checked strictly positive square. -/ bottomCoordinateNonzero :
    RationalData.Lt zero (squareData box.yLower)
  /-- The original top box coordinate has checked strictly positive square. -/ topCoordinateNonzero : RationalData.Lt
    zero (squareData box.yUpper)

constructive_injectivity PreparedSameBoxSideBoundsData

namespace PreparedExplicitSideBoundsData

/-- The original displayed source parameter equals its retained checked reduced representative. -/
theorem sourceParameter_eq_reduced
    (data : PreparedExplicitSideBoundsData) (edge : Fin 8) :
    (data.sourceParameter edge).toGaussian =
      (data.sourceParameterReduced edge).toGaussian := by
  rw [(data.sourceParameterReduced edge).toGaussian_eq_data]
  exact (Gaussian.Certificate.Raw.GaussianData.eq_sound
    (data.sourceParameterReducedMatches edge)).symm

/-- The original displayed target parameter equals its retained checked reduced representative. -/
theorem targetParameter_eq_reduced
    (data : PreparedExplicitSideBoundsData) (edge : Fin 8) :
    (data.targetParameter edge).toGaussian =
      (data.targetParameterReduced edge).toGaussian := by
  rw [(data.targetParameterReduced edge).toGaussian_eq_data]
  exact (Gaussian.Certificate.Raw.GaussianData.eq_sound
    (data.targetParameterReducedMatches edge)).symm

/-- The original source-to-target squared displacement satisfies the retained displayed ceiling. -/
theorem displacement_le (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) :
    Data.Gaussian.Norm.Basic.normSq
        ((data.sourceParameter edge).toGaussian -
          (data.targetParameter edge).toGaussian) ≤
      data.displacementUpper.toRational := by
  rw [← Gaussian.Certificate.Raw.GaussianData.sub_toGaussian, ← Gaussian.Certificate.Raw.GaussianData.normSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.displacementBounds edge)

/-- The retained residual floor is bounded by variation minus the original source-to-target squared displacement. -/
theorem residualMargin_le (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) :
    data.residualMarginFloor.toRational ≤
      data.variationUpper.toRational -
        Data.Gaussian.Norm.Basic.normSq
          ((data.sourceParameter edge).toGaussian -
            (data.targetParameter edge).toGaussian) := by
  rw [← Gaussian.Certificate.Raw.GaussianData.sub_toGaussian, ← Gaussian.Certificate.Raw.GaussianData.normSq_toRational,
    ← Data.Rat.Certificate.Raw.RationalData.sub_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.residualMarginBounds edge)

/-- The original source parameter's squared norm satisfies the retained displayed floor. -/
theorem sourceNormSq_lower (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) :
    data.sourceNormSqLower.toRational ≤
      Data.Gaussian.Norm.Basic.normSq
        (data.sourceParameter edge).toGaussian := by
  rw [← Gaussian.Certificate.Raw.GaussianData.normSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.sourceNormSqBounds edge)

/-- The original source parameter's squared norm satisfies the retained displayed ceiling. -/
theorem sourceNormSq_le (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) :
    Data.Gaussian.Norm.Basic.normSq
        (data.sourceParameter edge).toGaussian ≤
      data.sourceNormSqUpper.toRational := by
  rw [← Gaussian.Certificate.Raw.GaussianData.normSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.sourceNormSqUpperBounds edge)

/-- The original target parameter's squared norm satisfies the retained displayed ceiling. -/
theorem targetNormSq_le (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) :
    Data.Gaussian.Norm.Basic.normSq
        (data.targetParameter edge).toGaussian ≤
      data.targetNormSqUpper.toRational := by
  rw [← Gaussian.Certificate.Raw.GaussianData.normSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.targetNormSqBounds edge)

/-- The retained vertical interval bound equals the maximum of the original squared y-endpoints.

The checked retained equality identifies the original endpoint-square maximum with the exact stored interval ceiling. -/
private theorem verticalIntervalSq_eq (data : PreparedExplicitSideBoundsData) :
    data.verticalIntervalSqUpper.toRational =
      max (data.box.toBox.yLower ^ 2) (data.box.toBox.yUpper ^ 2) := by
  calc
    data.verticalIntervalSqUpper.toRational =
        (maxData (squareData data.box.yLower)
          (squareData data.box.yUpper)).toRational :=
      Data.Rat.Certificate.Raw.RationalData.eq_sound data.verticalIntervalExact
    _ = max (data.box.toBox.yLower ^ 2)
        (data.box.toBox.yUpper ^ 2) := by
      rw [maxData_toRational, squareData_toRational, squareData_toRational]
      simp only [-eq_self, -iff_self, rationalBoxDataToBox_yLower, rationalBoxDataToBox_yUpper]
      rfl

/-- The retained horizontal interval bound equals the maximum of the original squared x-endpoints.

The checked retained equality identifies the original endpoint-square maximum with the exact stored interval ceiling. -/
private theorem horizontalIntervalSq_eq (data : PreparedExplicitSideBoundsData) :
    data.horizontalIntervalSqUpper.toRational =
      max (data.box.toBox.xLower ^ 2) (data.box.toBox.xUpper ^ 2) := by
  calc
    data.horizontalIntervalSqUpper.toRational =
        (maxData (squareData data.box.xLower)
          (squareData data.box.xUpper)).toRational :=
      Data.Rat.Certificate.Raw.RationalData.eq_sound data.horizontalIntervalExact
    _ = max (data.box.toBox.xLower ^ 2)
        (data.box.toBox.xUpper ^ 2) := by
      rw [maxData_toRational, squareData_toRational, squareData_toRational]
      simp only [-eq_self, -iff_self, rationalBoxDataToBox_xLower, rationalBoxDataToBox_xUpper]
      rfl

/-- A checked positive displayed square proves the original rational value is nonzero. -/
theorem ne_of_squareData_positive (value : Data.Rat.Certificate.Raw.RationalData)
    (positive : RationalData.Lt zero (squareData value)) :
    value.toRational ≠ 0 := by
  have squarePositive : (0 : Rat.Fraction.Rational) <
      value.toRational ^ 2 := by
    have promoted := RationalData.lt_sound positive
    change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
    rw [Rat.Fraction.Field.zero_mul_direct,
      squareData_toRational] at promoted
    exact promoted
  intro equal
  rw [equal, zero_pow (by omega : 2 ≠ 0)] at squarePositive
  exact (lt_irrefl 0) squarePositive

/-- The checked determinant comparison bounds the original vertical direct clearance below. -/
private theorem lower_le_vertical (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) (x : Data.Rat.Certificate.Raw.RationalData)
    (checked : Data.Rat.Certificate.Raw.RationalData.Le
      (Data.Rat.Certificate.Raw.RationalData.mul data.directLower
        (verticalMajorantData x (data.sourceParameter edge)
          data.verticalIntervalSqUpper))
      (squareData (verticalDeterminantData x
        (data.sourceParameter edge)))) :
    data.directLower.toRational ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (data.sourceParameter edge).toGaussian data.box.toBox x.toRational := by
  unfold SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
  apply (Rat.Fraction.Order.Field.le_div_iff_pos
    (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant_positive
      _ _ _ _)).2
  rw [← verticalDeterminantData_toRational,
    ← verticalIntervalSq_eq data,
    ← verticalMajorantData_toRational]
  simpa only [Data.Rat.Certificate.Raw.RationalData.mul_toRational, squareData_toRational] using
    Data.Rat.Certificate.Raw.RationalData.le_sound checked

/-- The checked determinant comparison bounds the original horizontal direct clearance below. -/
private theorem lower_le_horizontal (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) (y : Data.Rat.Certificate.Raw.RationalData)
    (checked : Data.Rat.Certificate.Raw.RationalData.Le
      (Data.Rat.Certificate.Raw.RationalData.mul data.directLower
        (horizontalMajorantData y (data.sourceParameter edge)
          data.horizontalIntervalSqUpper))
      (squareData (horizontalDeterminantData y
        (data.sourceParameter edge)))) :
    data.directLower.toRational ≤
      SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (data.sourceParameter edge).toGaussian data.box.toBox y.toRational := by
  unfold SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
  apply (Rat.Fraction.Order.Field.le_div_iff_pos
    (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant_positive
      _ _ _ _)).2
  rw [← horizontalDeterminantData_toRational,
    ← horizontalIntervalSq_eq data,
    ← horizontalMajorantData_toRational]
  simpa only [Data.Rat.Certificate.Raw.RationalData.mul_toRational, squareData_toRational] using
    Data.Rat.Certificate.Raw.RationalData.le_sound checked

/-- The checked determinant comparison bounds the original vertical direct clearance above. -/
private theorem vertical_le_upper (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) (x upper : Data.Rat.Certificate.Raw.RationalData)
    (checked : Data.Rat.Certificate.Raw.RationalData.Le
      (squareData (verticalDeterminantData x (data.sourceParameter edge)))
      (Data.Rat.Certificate.Raw.RationalData.mul upper
        (verticalMajorantData x (data.sourceParameter edge)
          data.verticalIntervalSqUpper))) :
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
        (data.sourceParameter edge).toGaussian data.box.toBox x.toRational ≤
      upper.toRational := by
  unfold SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directVerticalClearanceBound
  apply (Rat.Fraction.Order.Field.div_le_iff_pos
    (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant_positive
      _ _ _ _)).2
  rw [← verticalDeterminantData_toRational,
    ← verticalIntervalSq_eq data,
    ← verticalMajorantData_toRational]
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound checked
  simpa only [Data.Rat.Certificate.Raw.RationalData.mul_toRational, squareData_toRational,
    Rat.Fraction.Field.mul_comm] using promoted

/-- The checked determinant comparison bounds the original horizontal direct clearance above. -/
private theorem horizontal_le_upper (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) (y upper : Data.Rat.Certificate.Raw.RationalData)
    (checked : Data.Rat.Certificate.Raw.RationalData.Le
      (squareData (horizontalDeterminantData y (data.sourceParameter edge)))
      (Data.Rat.Certificate.Raw.RationalData.mul upper
        (horizontalMajorantData y (data.sourceParameter edge)
          data.horizontalIntervalSqUpper))) :
    SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
        (data.sourceParameter edge).toGaussian data.box.toBox y.toRational ≤
      upper.toRational := by
  unfold SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directHorizontalClearanceBound
  apply (Rat.Fraction.Order.Field.div_le_iff_pos
    (SquareRoot.Clearance.QuadraticLineClearance.ExactQuadraticOwnerClearance.directLineMajorant_positive
      _ _ _ _)).2
  rw [← horizontalDeterminantData_toRational,
    ← horizontalIntervalSq_eq data,
    ← horizontalMajorantData_toRational]
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound checked
  simpa only [Data.Rat.Certificate.Raw.RationalData.mul_toRational, squareData_toRational,
    Rat.Fraction.Field.mul_comm] using promoted

/-- Reconstruct all four original direct-clearance floors and a selected side's upper bound from checked displayed data.

The four nonzero determinants retain their individual floors; the supplied selected-side check bounds the original
nested minimum by the exact displayed upper value. -/
theorem directBoundaryBoundsWithUpper
    (data : PreparedExplicitSideBoundsData) (edge : Fin 8)
    (upper : Data.Rat.Certificate.Raw.RationalData)
    (upperWitness :
      Data.Rat.Certificate.Raw.RationalData.Le
          (squareData (verticalDeterminantData data.box.xLower
            (data.sourceParameter edge)))
          (Data.Rat.Certificate.Raw.RationalData.mul upper
            (verticalMajorantData data.box.xLower (data.sourceParameter edge)
              data.verticalIntervalSqUpper)) ∨
      Data.Rat.Certificate.Raw.RationalData.Le
          (squareData (verticalDeterminantData data.box.xUpper
            (data.sourceParameter edge)))
          (Data.Rat.Certificate.Raw.RationalData.mul upper
            (verticalMajorantData data.box.xUpper (data.sourceParameter edge)
              data.verticalIntervalSqUpper)) ∨
      Data.Rat.Certificate.Raw.RationalData.Le
          (squareData (horizontalDeterminantData data.box.yLower
            (data.sourceParameter edge)))
          (Data.Rat.Certificate.Raw.RationalData.mul upper
            (horizontalMajorantData data.box.yLower (data.sourceParameter edge)
              data.horizontalIntervalSqUpper)) ∨
      Data.Rat.Certificate.Raw.RationalData.Le
          (squareData (horizontalDeterminantData data.box.yUpper
            (data.sourceParameter edge)))
          (Data.Rat.Certificate.Raw.RationalData.mul upper
            (horizontalMajorantData data.box.yUpper (data.sourceParameter edge)
              data.horizontalIntervalSqUpper))) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (data.sourceParameter edge).toGaussian data.box.toBox
        data.directLower.toRational upper.toRational := by
  let leftNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        (data.sourceParameter edge).toGaussian data.box.toBox.xLower ≠ 0 := by
    change SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      (data.sourceParameter edge).toGaussian data.box.xLower.toRational ≠ 0
    rw [← verticalDeterminantData_toRational]
    exact ne_of_squareData_positive _ (data.leftDeterminantPositive edge)
  let rightNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
        (data.sourceParameter edge).toGaussian data.box.toBox.xUpper ≠ 0 := by
    change SquareRoot.Clearance.QuadraticAxisElimination.verticalDeterminant
      (data.sourceParameter edge).toGaussian data.box.xUpper.toRational ≠ 0
    rw [← verticalDeterminantData_toRational]
    exact ne_of_squareData_positive _ (data.rightDeterminantPositive edge)
  let bottomNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        (data.sourceParameter edge).toGaussian data.box.toBox.yLower ≠ 0 := by
    change SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      (data.sourceParameter edge).toGaussian data.box.yLower.toRational ≠ 0
    rw [← horizontalDeterminantData_toRational]
    exact ne_of_squareData_positive _ (data.bottomDeterminantPositive edge)
  let topNonzero :
      SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
        (data.sourceParameter edge).toGaussian data.box.toBox.yUpper ≠ 0 := by
    change SquareRoot.Clearance.QuadraticAxisElimination.horizontalDeterminant
      (data.sourceParameter edge).toGaussian data.box.yUpper.toRational ≠ 0
    rw [← horizontalDeterminantData_toRational]
    exact ne_of_squareData_positive _ (data.topDeterminantPositive edge)
  apply SquareRoot.Clearance.ExactQuadraticOwnerClearance.directBoundaryBoundsOfSideChecks
    _ _ _ _ leftNonzero rightNonzero bottomNonzero topNonzero
  · exact lower_le_vertical data edge data.box.xLower (data.leftDirectLower edge)
  · exact lower_le_vertical data edge data.box.xUpper (data.rightDirectLower edge)
  · exact lower_le_horizontal data edge data.box.yLower (data.bottomDirectLower edge)
  · exact lower_le_horizontal data edge data.box.yUpper (data.topDirectLower edge)
  · rcases upperWitness with left | right | bottom | top
    · exact (Rat.Fraction.Order.Basic.min_le_left _ _).trans (vertical_le_upper data edge _ upper left)
    · exact (Rat.Fraction.Order.Basic.min_le_right _ _).trans
        ((Rat.Fraction.Order.Basic.min_le_left _ _).trans
          (vertical_le_upper data edge _ upper right))
    · exact (Rat.Fraction.Order.Basic.min_le_right _ _).trans ((Rat.Fraction.Order.Basic.min_le_right _ _).trans
        ((Rat.Fraction.Order.Basic.min_le_left _ _).trans
          (horizontal_le_upper data edge _ upper bottom)))
    · exact (Rat.Fraction.Order.Basic.min_le_right _ _).trans ((Rat.Fraction.Order.Basic.min_le_right _ _).trans
        ((Rat.Fraction.Order.Basic.min_le_right _ _).trans
          (horizontal_le_upper data edge _ upper top)))

/-- Reconstruct the original box's direct boundary-clearance bounds from its retained checked side data. -/
theorem directBoundaryBounds (data : PreparedExplicitSideBoundsData)
    (edge : Fin 8) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (data.sourceParameter edge).toGaussian data.box.toBox
        data.directLower.toRational data.directUpper.toRational :=
  data.directBoundaryBoundsWithUpper edge data.directUpper
    (data.directUpperWitness edge)

/-- The original left side's squared real constant satisfies the retained vertical ceiling. -/
theorem leftVertical_le (data : PreparedExplicitSideBoundsData) (edge : Fin 8) :
    (data.box.toBox.xLower ^ 2 -
        (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
      data.verticalRealUpper.toRational := by
  change (data.box.xLower.toRational ^ 2 -
      (data.sourceParameter edge).re.toRational) ^ 2 ≤ _
  rw [← verticalRealConstantSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.leftVerticalBounds edge)

/-- The original right side's squared real constant satisfies the retained vertical ceiling. -/
theorem rightVertical_le (data : PreparedExplicitSideBoundsData) (edge : Fin 8) :
    (data.box.toBox.xUpper ^ 2 -
        (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
      data.verticalRealUpper.toRational := by
  change (data.box.xUpper.toRational ^ 2 -
      (data.sourceParameter edge).re.toRational) ^ 2 ≤ _
  rw [← verticalRealConstantSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.rightVerticalBounds edge)

/-- The original bottom side's squared real constant satisfies the retained horizontal ceiling. -/
theorem bottomHorizontal_le
    (data : PreparedExplicitSideBoundsData) (edge : Fin 8) :
    (-data.box.toBox.yLower ^ 2 -
        (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
      data.horizontalRealUpper.toRational := by
  change (-(data.box.yLower.toRational ^ 2) -
      (data.sourceParameter edge).re.toRational) ^ 2 ≤ _
  rw [← horizontalRealConstantSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.bottomHorizontalBounds edge)

/-- The original top side's squared real constant satisfies the retained horizontal ceiling. -/
theorem topHorizontal_le
    (data : PreparedExplicitSideBoundsData) (edge : Fin 8) :
    (-data.box.toBox.yUpper ^ 2 -
        (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
      data.horizontalRealUpper.toRational := by
  change (-(data.box.yUpper.toRational ^ 2) -
      (data.sourceParameter edge).re.toRational) ^ 2 ≤ _
  rw [← horizontalRealConstantSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.topHorizontalBounds edge)

/-- The original parameter's squared imaginary constant satisfies the retained ceiling. -/
theorem imaginary_le (data : PreparedExplicitSideBoundsData) (edge : Fin 8) :
    (-(data.sourceParameter edge).toGaussian.im) ^ 2 ≤
      data.imaginaryUpper.toRational := by
  change (-(data.sourceParameter edge).im.toRational) ^ 2 ≤ _
  rw [← imaginaryConstantSq_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound (data.imaginaryBounds edge)

/-- The original vertical quadratic side budget satisfies the retained common majorant ceiling. -/
theorem verticalBudget_le (data : PreparedExplicitSideBoundsData) :
    2 * (4 * data.verticalIntervalSqUpper.toRational *
          data.verticalIntervalSqUpper.toRational +
        data.verticalRealUpper.toRational) +
      2 * (8 * data.xSqUpper.toRational *
          data.verticalIntervalSqUpper.toRational +
        data.imaginaryUpper.toRational) ≤
      data.sideMajorantUpper.toRational := by
  rw [← sideBudgetData_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.verticalBudgetBound

/-- The original horizontal quadratic side budget satisfies the retained common majorant ceiling. -/
theorem horizontalBudget_le (data : PreparedExplicitSideBoundsData) :
    2 * (4 * data.horizontalIntervalSqUpper.toRational *
          data.horizontalIntervalSqUpper.toRational +
        data.horizontalRealUpper.toRational) +
      2 * (8 * data.ySqUpper.toRational *
          data.horizontalIntervalSqUpper.toRational +
        data.imaginaryUpper.toRational) ≤
      data.sideMajorantUpper.toRational := by
  rw [← sideBudgetData_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.horizontalBudgetBound

/-- The original left box coordinate squared satisfies its retained coordinate ceiling. -/
theorem leftXSq_le (data : PreparedExplicitSideBoundsData) :
    data.box.toBox.xLower ^ 2 ≤ data.xSqUpper.toRational := by
  change data.box.xLower.toRational ^ 2 ≤ data.xSqUpper.toRational
  rw [← squareData_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.leftXSqBound

/-- The original right box coordinate squared satisfies its retained coordinate ceiling. -/
theorem rightXSq_le (data : PreparedExplicitSideBoundsData) :
    data.box.toBox.xUpper ^ 2 ≤ data.xSqUpper.toRational := by
  change data.box.xUpper.toRational ^ 2 ≤ data.xSqUpper.toRational
  rw [← squareData_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.rightXSqBound

/-- The original bottom box coordinate squared satisfies its retained coordinate ceiling. -/
theorem bottomYSq_le (data : PreparedExplicitSideBoundsData) :
    data.box.toBox.yLower ^ 2 ≤ data.ySqUpper.toRational := by
  change data.box.yLower.toRational ^ 2 ≤ data.ySqUpper.toRational
  rw [← squareData_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.bottomYSqBound

/-- The original top box coordinate squared satisfies its retained coordinate ceiling. -/
theorem topYSq_le (data : PreparedExplicitSideBoundsData) :
    data.box.toBox.yUpper ^ 2 ≤ data.ySqUpper.toRational := by
  change data.box.yUpper.toRational ^ 2 ≤ data.ySqUpper.toRational
  rw [← squareData_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.topYSqBound

/-- The original vertical boundary polynomial majorant is bounded by the supplied cap covering one and the retained side
ceiling.

The original path-coordinate bounds and retained vertical interval ceiling bound the same maximum by a cap that already
covers one and the side ceiling. -/
private theorem verticalBoundarySideMajorant_le_cap
    (data : PreparedExplicitSideBoundsData) (edge : Fin 8)
    (x : Rat.Fraction.Rational)
    (xSqLe : x ^ 2 ≤ data.xSqUpper.toRational)
    (realConstantSqLe :
      (x ^ 2 - (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
        data.verticalRealUpper.toRational)
    (cap : Rat.Fraction.Rational) (oneLeCap : (1 : Rat.Fraction.Rational) ≤ cap)
    (sideUpperLeCap : data.sideMajorantUpper.toRational ≤ cap) :
    Purelib.Polynomial.Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial
          (data.sourceParameter edge).toGaussian
          Purelib.Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Purelib.Data.Gaussian.Cast.Winding.verticalBase x) Purelib.Data.Gaussian.Constants.imaginaryUnit
        (Purelib.Geometry.Rational.Box.Intervals.verticalInterval data.box.toBox) ≤ cap := by
  let interval := Rational.Box.Intervals.verticalInterval data.box.toBox
  let intervalUpper := data.verticalIntervalSqUpper.toRational
  let xUpper := data.xSqUpper.toRational
  let realUpper := data.verticalRealUpper.toRational
  let imaginaryUpper := data.imaginaryUpper.toRational
  have intervalEq : interval.squareBound = intervalUpper := by
    exact (verticalIntervalSq_eq data).symm
  have intervalNonnegative : (0 : Rat.Fraction.Rational) ≤ intervalUpper := by
    rw [← intervalEq]
    exact Data.Rat.Interval.Bounds.squareBound_nonneg interval
  have xUpperNonnegative : (0 : Rat.Fraction.Rational) ≤ xUpper :=
    (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct x).trans xSqLe
  have doubledXSqLe : (2 * x) ^ 2 ≤ 4 * xUpper := by
    calc
      (2 * x) ^ 2 = 4 * x ^ 2 := by ring1
      _ ≤ 4 * xUpper :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct xSqLe
          (Rat.Fraction.Cast.Order.natCast_pos_direct
            (n := 4) (by omega)).le
  have realLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial
          (data.sourceParameter edge).toGaussian
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
      interval ≤
        2 * ((2 * ((2 * (1 : Rat.Fraction.Rational)) * intervalUpper + 0)) *
          intervalUpper + realUpper) := by
    rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticVerticalPathReal_all]
    exact Dense.Rational.Bounds.Horner.evalSqBound_three_le _ (-1) 0
      (x ^ 2 - (data.sourceParameter edge).toGaussian.re) rfl interval
        intervalUpper 1 0 realUpper intervalNonnegative (by decide) le_rfl
          intervalEq.le (by rw [show (-1 : Rat.Fraction.Rational) ^ 2 = 1 by ring1])
            (by rw [zero_pow (by omega : 2 ≠ 0)]) realConstantSqLe
  have imaginaryLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial
          (data.sourceParameter edge).toGaussian
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
      interval ≤
        2 * ((2 * ((2 * (0 : Rat.Fraction.Rational)) * intervalUpper + 4 * xUpper)) *
          intervalUpper + imaginaryUpper) := by
    rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticVerticalPathImag_all]
    exact Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 0 (2 * x)
      (-(data.sourceParameter edge).toGaussian.im) rfl interval intervalUpper
        0 (4 * xUpper) imaginaryUpper intervalNonnegative le_rfl
          (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
            (Rat.Fraction.Cast.Order.natCast_pos_direct
              (n := 4) (by omega)).le xUpperNonnegative)
          intervalEq.le (by rw [zero_pow (by omega : 2 ≠ 0)]) doubledXSqLe
            (data.imaginary_le edge)
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Rat.Fraction.Order.Basic.max_le
  · exact oneLeCap
  · calc
      Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathReal
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial
                (data.sourceParameter edge).toGaussian
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
            interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathImag
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial
                (data.sourceParameter edge).toGaussian
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Winding.verticalBase x) Gaussian.Constants.imaginaryUnit)
            interval ≤
          2 * ((2 * ((2 * (1 : Rat.Fraction.Rational)) * intervalUpper + 0)) *
              intervalUpper + realUpper) +
            2 * ((2 * ((2 * (0 : Rat.Fraction.Rational)) * intervalUpper +
              4 * xUpper)) * intervalUpper + imaginaryUpper) :=
        add_le_add realLe imaginaryLe
      _ = 2 * (4 * intervalUpper * intervalUpper + realUpper) +
          2 * (8 * xUpper * intervalUpper + imaginaryUpper) := by ring1
      _ ≤ data.sideMajorantUpper.toRational := data.verticalBudget_le
      _ ≤ cap := sideUpperLeCap

/-- The original horizontal boundary polynomial majorant is bounded by the supplied cap covering one and the retained
side ceiling.

The original path-coordinate bounds and retained horizontal interval ceiling bound the same maximum by a cap that
already covers one and the side ceiling. -/
private theorem horizontalBoundarySideMajorant_le_cap
    (data : PreparedExplicitSideBoundsData) (edge : Fin 8)
    (y : Rat.Fraction.Rational)
    (ySqLe : y ^ 2 ≤ data.ySqUpper.toRational)
    (realConstantSqLe :
      (-(y ^ 2) - (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
        data.horizontalRealUpper.toRational)
    (cap : Rat.Fraction.Rational) (oneLeCap : (1 : Rat.Fraction.Rational) ≤ cap)
    (sideUpperLeCap : data.sideMajorantUpper.toRational ≤ cap) :
    Purelib.Polynomial.Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial
          (data.sourceParameter edge).toGaussian
          Purelib.Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Purelib.Data.Gaussian.Cast.Imaginary.horizontalBase y) Purelib.Data.Gaussian.Constants.horizontalDirection
        (Purelib.Geometry.Rational.Box.Intervals.horizontalInterval data.box.toBox) ≤ cap := by
  let interval := Rational.Box.Intervals.horizontalInterval data.box.toBox
  let intervalUpper := data.horizontalIntervalSqUpper.toRational
  let yUpper := data.ySqUpper.toRational
  let realUpper := data.horizontalRealUpper.toRational
  let imaginaryUpper := data.imaginaryUpper.toRational
  have intervalEq : interval.squareBound = intervalUpper := by
    exact (horizontalIntervalSq_eq data).symm
  have intervalNonnegative : (0 : Rat.Fraction.Rational) ≤ intervalUpper := by
    rw [← intervalEq]
    exact Data.Rat.Interval.Bounds.squareBound_nonneg interval
  have yUpperNonnegative : (0 : Rat.Fraction.Rational) ≤ yUpper :=
    (Rat.Fraction.Order.Arithmetic.sq_nonneg_direct y).trans ySqLe
  have doubledYSqLe : (2 * y) ^ 2 ≤ 4 * yUpper := by
    calc
      (2 * y) ^ 2 = 4 * y ^ 2 := by ring1
      _ ≤ 4 * yUpper :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ySqLe
          (Rat.Fraction.Cast.Order.natCast_pos_direct
            (n := 4) (by omega)).le
  have realLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathReal
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial
          (data.sourceParameter edge).toGaussian
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
      interval ≤
        2 * ((2 * ((2 * (1 : Rat.Fraction.Rational)) * intervalUpper + 0)) *
          intervalUpper + realUpper) := by
    rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticHorizontalPathReal_all]
    exact Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 1 0
      (-(y ^ 2) - (data.sourceParameter edge).toGaussian.re) rfl interval
        intervalUpper 1 0 realUpper intervalNonnegative (by decide) le_rfl
          intervalEq.le (by rw [one_pow])
            (by rw [zero_pow (by omega : 2 ≠ 0)]) realConstantSqLe
  have imaginaryLe : Dense.Rational.Bounds.Horner.evalSqBound
      (Dense.Gaussian.Path.Components.pathImag
        (Purelib.Polynomial.Power.Gaussian.rootPolynomial
          (data.sourceParameter edge).toGaussian
          Riemann.RootContinuation.SquareRootDegree.degreeTwo)
        (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
      interval ≤
        2 * ((2 * ((2 * (0 : Rat.Fraction.Rational)) * intervalUpper + 4 * yUpper)) *
          intervalUpper + imaginaryUpper) := by
    rw [SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticHorizontalPathImag_all]
    exact Dense.Rational.Bounds.Horner.evalSqBound_three_le _ 0 (2 * y)
      (-(data.sourceParameter edge).toGaussian.im) rfl interval intervalUpper
        0 (4 * yUpper) imaginaryUpper intervalNonnegative le_rfl
          (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
            (Rat.Fraction.Cast.Order.natCast_pos_direct
              (n := 4) (by omega)).le yUpperNonnegative)
          intervalEq.le (by rw [zero_pow (by omega : 2 ≠ 0)]) doubledYSqLe
            (data.imaginary_le edge)
  unfold Dense.Gaussian.Bounds.Path.Majorant.boundarySideMajorant
  apply Rat.Fraction.Order.Basic.max_le
  · exact oneLeCap
  · calc
      Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathReal
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial
                (data.sourceParameter edge).toGaussian
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
            interval +
          Dense.Rational.Bounds.Horner.evalSqBound
            (Dense.Gaussian.Path.Components.pathImag
              (Purelib.Polynomial.Power.Gaussian.rootPolynomial
                (data.sourceParameter edge).toGaussian
                Riemann.RootContinuation.SquareRootDegree.degreeTwo)
              (Gaussian.Cast.Imaginary.horizontalBase y) Gaussian.Constants.horizontalDirection)
            interval ≤
          2 * ((2 * ((2 * (1 : Rat.Fraction.Rational)) * intervalUpper + 0)) *
              intervalUpper + realUpper) +
            2 * ((2 * ((2 * (0 : Rat.Fraction.Rational)) * intervalUpper +
              4 * yUpper)) * intervalUpper + imaginaryUpper) :=
        add_le_add realLe imaginaryLe
      _ = 2 * (4 * intervalUpper * intervalUpper + realUpper) +
          2 * (8 * yUpper * intervalUpper + imaginaryUpper) := by ring1
      _ ≤ data.sideMajorantUpper.toRational := data.horizontalBudget_le
      _ ≤ cap := sideUpperLeCap

/-- Reconstruct all four concrete quadratic side bounds from generated
coefficient and interval calculations. -/
theorem quadraticBoxSideMajorantBounds
    (data : PreparedExplicitSideBoundsData) (edge : Fin 8)
    (cap : Rat.Fraction.Rational) (oneLeCap : (1 : Rat.Fraction.Rational) ≤ cap)
    (sideUpperLeCap : data.sideMajorantUpper.toRational ≤ cap) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.QuadraticBoxSideMajorantBounds
      (data.sourceParameter edge).toGaussian data.box.toBox cap :=
  ⟨verticalBoundarySideMajorant_le_cap data edge data.box.toBox.xLower
      data.leftXSq_le (data.leftVertical_le edge)
        cap oneLeCap sideUpperLeCap,
    verticalBoundarySideMajorant_le_cap data edge data.box.toBox.xUpper
      data.rightXSq_le (data.rightVertical_le edge)
        cap oneLeCap sideUpperLeCap,
    horizontalBoundarySideMajorant_le_cap data edge data.box.toBox.yLower
      data.bottomYSq_le (data.bottomHorizontal_le edge)
        cap oneLeCap sideUpperLeCap,
    horizontalBoundarySideMajorant_le_cap data edge data.box.toBox.yUpper
      data.topYSq_le (data.topHorizontal_le edge)
        cap oneLeCap sideUpperLeCap⟩

end PreparedExplicitSideBoundsData

namespace PreparedParametricSameBoxCellBoundsData

/-- Reconstruct the original direct-clearance floor with the retained ceiling specific to the selected edge. -/
theorem directBoundaryBoundsAt
    (data : PreparedParametricSameBoxCellBoundsData) (edge : Fin 8) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (data.sourceParameter edge).toGaussian data.box.toBox
        data.directLower.toRational (data.directUpperAt edge).toRational :=
  data.toPreparedExplicitSideBoundsData.directBoundaryBoundsWithUpper edge
    (data.directUpperAt edge) (data.directUpperAtWitness edge)

/-- The original quartic value at the retained edge's affine source equals its checked displayed source parameter. -/
theorem affineSourceParameter_eq
    (data : PreparedParametricSameBoxCellBoundsData) (edge : Fin 8)
    (firstLe : data.firstEdge ≤ edge.val)
    (lastLt : edge.val < data.firstEdge + data.edgeCount) :
    (data.affineOrigin.toGaussian +
      Gaussian.Scale.scale ((edge.val : Rat.Fraction.Rational) / 8)
        data.affineDirection.toGaussian) ^ 4 - 1 =
      (data.sourceParameter edge).toGaussian := by
  rw [← eighthParameterData_toRational]
  exact (affineQuarticParameterData_toGaussian data.affineOrigin
    data.affineDirection (eighthParameterData edge.val)).symm.trans
      (Gaussian.Certificate.Raw.GaussianData.eq_sound
        (data.affineSourceParameterExact edge firstLe lastLt))

/-- The original quartic value at the retained edge's affine endpoint equals its checked displayed target parameter. -/
theorem affineTargetParameter_eq
    (data : PreparedParametricSameBoxCellBoundsData) (edge : Fin 8)
    (firstLe : data.firstEdge ≤ edge.val)
    (lastLt : edge.val < data.firstEdge + data.edgeCount) :
    (data.affineOrigin.toGaussian +
      Gaussian.Scale.scale
        (((edge.val + 1 : Nat) : Rat.Fraction.Rational) / 8)
          data.affineDirection.toGaussian) ^ 4 - 1 =
      (data.targetParameter edge).toGaussian := by
  rw [← eighthParameterData_toRational]
  exact (affineQuarticParameterData_toGaussian data.affineOrigin
    data.affineDirection (eighthParameterData (edge.val + 1))).symm.trans
      (Gaussian.Certificate.Raw.GaussianData.eq_sound
        (data.affineTargetParameterExact edge firstLe lastLt))

/-- The retained strict coordinate comparison separates the original source and target Gaussian parameters. -/
theorem sourceTarget_ne
    (data : PreparedParametricSameBoxCellBoundsData) (edge : Fin 8) :
    (data.sourceParameter edge).toGaussian ≠
      (data.targetParameter edge).toGaussian :=
  GaussianData.different_sound (data.sourceTargetDifferent edge)

/-- The original quartic value at the affine origin satisfies the retained segment-source squared-norm floor. -/
theorem affineOriginNormSq_lower
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.sourceNormSqLower.toRational ≤
      Data.Gaussian.Norm.Basic.normSq
        (data.affineOrigin.toGaussian ^ 4 - 1) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.affineOriginNormSqLower
  rw [Gaussian.Certificate.Raw.GaussianData.normSq_toRational,
    quarticParameterData_toGaussian] at promoted
  exact promoted

/-- The retained original box has squared diagonal strictly below five. -/
theorem boxDiagonalSq_lt_five
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.box.toBox.diagonalSq < (5 : Rat.Fraction.Rational) := by
  have promoted := RationalData.lt_sound data.boxDiagonalLtFive
  rw [boxDiagonalSqData_toRational, naturalData_toRational,
    show ((5 : Nat) : Rat.Fraction.Rational) = 5 by rfl]
    at promoted
  exact promoted

/-- The original box's lower x coordinate is at least negative three. -/
theorem negativeThree_le_boxXLower
    (data : PreparedParametricSameBoxCellBoundsData) :
    (-3 : Rat.Fraction.Rational) ≤ data.box.toBox.xLower := by
  have xLower := Data.Rat.Certificate.Raw.RationalData.le_sound data.boxNegativeThreeLeXLower
  rw [Data.Rat.Certificate.Raw.RationalData.neg_toRational, naturalData_toRational,
    show ((3 : Nat) : Rat.Fraction.Rational) = 3 by rfl]
    at xLower
  exact xLower

/-- The original box's upper x coordinate is at most three. -/
theorem boxXUpper_le_three
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.box.toBox.xUpper ≤ (3 : Rat.Fraction.Rational) := by
  have xUpper := Data.Rat.Certificate.Raw.RationalData.le_sound data.boxXUpperLeThree
  rw [naturalData_toRational,
    show ((3 : Nat) : Rat.Fraction.Rational) = 3 by rfl]
    at xUpper
  exact xUpper

/-- The original box's lower y coordinate is at least negative three. -/
theorem negativeThree_le_boxYLower
    (data : PreparedParametricSameBoxCellBoundsData) :
    (-3 : Rat.Fraction.Rational) ≤ data.box.toBox.yLower := by
  have yLower := Data.Rat.Certificate.Raw.RationalData.le_sound data.boxNegativeThreeLeYLower
  rw [Data.Rat.Certificate.Raw.RationalData.neg_toRational, naturalData_toRational,
    show ((3 : Nat) : Rat.Fraction.Rational) = 3 by rfl]
    at yLower
  exact yLower

/-- The original box's upper y coordinate is at most three. -/
theorem boxYUpper_le_three
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.box.toBox.yUpper ≤ (3 : Rat.Fraction.Rational) := by
  have yUpper := Data.Rat.Certificate.Raw.RationalData.le_sound data.boxYUpperLeThree
  rw [naturalData_toRational,
    show ((3 : Nat) : Rat.Fraction.Rational) = 3 by rfl]
    at yUpper
  exact yUpper

/-- The retained derivative floor equals the original fixed-margin formula computed from its source squared-norm floor.
-/
theorem predictedDerivativeLower_eq
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.predictedDerivativeLower.toRational =
      4 * (2 * ((1 / 4 : Rat.Fraction.Rational) +
        (2 * data.sourceNormSqLower.toRational + 1))) := by
  exact (Data.Rat.Certificate.Raw.RationalData.eq_sound data.predictedDerivativeLowerExact).symm.trans
    (predictedDerivativeLowerData_toRational data.sourceNormSqLower)

/-- The original predicted-clearance numerator fits the retained transport floor times the certified denominator floor.
-/
theorem predictedClearanceFitsTransport_sound
    (data : PreparedParametricSameBoxCellBoundsData) :
    ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          data.transportMargin.toRational *
        (4 * (2 * data.predictedDerivativeLower.toRational *
          (1 / 64 : Rat.Fraction.Rational) ^ 2)) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.predictedClearanceFitsTransport
  rw [predictedClearanceNumeratorData_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, transportFloor_toRational,
    predictedClearanceDenominatorLowerData_toRational] at promoted
  exact promoted

/-- The checked variation ceiling lies strictly below the original direct-clearance floor. -/
theorem variationUpper_lt_directLower
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.variationUpper.toRational < data.directLower.toRational :=
  RationalData.lt_sound data.directCarries

/-- The retained displayed transport margin denotes a strictly positive rational. -/
theorem transportMargin_positive
    (data : PreparedParametricSameBoxCellBoundsData) :
    0 < data.transportMargin.toRational := by
  have promoted := RationalData.lt_sound data.transportMarginPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The original retained transport floor is bounded by the checked direct-clearance floor. -/
theorem retainedFloor_le_directLower
    (data : PreparedParametricSameBoxCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.transportMargin.toRational ≤
      data.directLower.toRational := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.retainedFloorLeDirectLower
  rw [transportFloor_toRational] at promoted
  exact promoted

/-- The retained residual margin floor denotes a strictly positive rational. -/
theorem residualMarginFloor_positive
    (data : PreparedParametricSameBoxCellBoundsData) :
    0 < data.residualMarginFloor.toRational := by
  have promoted := RationalData.lt_sound data.residualMarginPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The retained side-majorant ceiling is at least one. -/
theorem one_le_sideMajorantUpper
    (data : PreparedParametricSameBoxCellBoundsData) :
    (1 : Rat.Fraction.Rational) ≤
      data.sideMajorantUpper.toRational := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.oneLeSideMajorant
  rw [naturalData_toRational,
    show ((1 : Nat) : Rat.Fraction.Rational) = 1 by rfl]
    at promoted
  exact promoted

/-- The retained target squared-norm ceiling is at most 256. -/
theorem targetNormSqUpper_le_twoHundredFiftySix
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.targetNormSqUpper.toRational ≤ 256 :=
  checkedUpperBound_sound data.targetNormSqBounded twoHundredFiftySix_toRational

/-- The retained source squared-norm ceiling is at most 256. -/
theorem sourceNormSqUpper_le_twoHundredFiftySix
    (data : PreparedParametricSameBoxCellBoundsData) :
    data.sourceNormSqUpper.toRational ≤ 256 :=
  checkedUpperBound_sound data.sourceNormSqBounded twoHundredFiftySix_toRational

/-- The original retained transport floor is at most the squared residual floor divided by four times the side-majorant
ceiling. -/
theorem retainedFloorTradeoff_sound
    (data : PreparedParametricSameBoxCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.transportMargin.toRational ≤
      data.residualMarginFloor.toRational ^ 2 /
        (4 * data.sideMajorantUpper.toRational) := by
  have sidePositive : (0 : Rat.Fraction.Rational) <
      data.sideMajorantUpper.toRational :=
    (by decide : (0 : Rat.Fraction.Rational) < 1).trans_le
      data.one_le_sideMajorantUpper
  apply (Rat.Fraction.Order.Field.le_div_iff_pos
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide) sidePositive)).2
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.retainedFloorTradeoff
  rw [Data.Rat.Certificate.Raw.RationalData.mul_toRational, transportFloor_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, naturalData_toRational,
    squareData_toRational] at promoted
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  simpa only [show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl]
    using promoted

end PreparedParametricSameBoxCellBoundsData

namespace PreparedSameBoxCellBoundsData

/-- The retained transport margin equals exactly one eighth. -/
theorem transportMargin_eq_oneEighth
    (data : PreparedSameBoxCellBoundsData) :
    data.transportMargin.toRational = (1 / 8 :
      Rat.Fraction.Rational) := by
  exact (Data.Rat.Certificate.Raw.RationalData.eq_sound data.transportMarginIsEighth).trans
    oneEighthData_toRational

/-- The checked variation ceiling lies strictly below the original direct-clearance floor. -/
theorem variationUpper_lt_directLower
    (data : PreparedSameBoxCellBoundsData) :
    data.variationUpper.toRational < data.directLower.toRational :=
  data.toPreparedParametricSameBoxCellBoundsData.variationUpper_lt_directLower

/-- The original retained transport floor is bounded by the checked direct-clearance floor. -/
theorem retainedFloor_le_directLower
    (data : PreparedSameBoxCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Rat.Fraction.Rational) ≤
      data.directLower.toRational := by
  rw [← data.transportMargin_eq_oneEighth]
  exact data.toPreparedParametricSameBoxCellBoundsData.retainedFloor_le_directLower

/-- The retained residual margin floor denotes a strictly positive rational. -/
theorem residualMarginFloor_positive
    (data : PreparedSameBoxCellBoundsData) :
    0 < data.residualMarginFloor.toRational :=
  data.toPreparedParametricSameBoxCellBoundsData.residualMarginFloor_positive

/-- The retained side-majorant ceiling is at least one. -/
theorem one_le_sideMajorantUpper
    (data : PreparedSameBoxCellBoundsData) :
    (1 : Rat.Fraction.Rational) ≤
      data.sideMajorantUpper.toRational :=
  data.toPreparedParametricSameBoxCellBoundsData.one_le_sideMajorantUpper

/-- The retained target squared-norm ceiling is at most 256. -/
theorem targetNormSqUpper_le_twoHundredFiftySix
    (data : PreparedSameBoxCellBoundsData) :
    data.targetNormSqUpper.toRational ≤ 256 :=
  data.toPreparedParametricSameBoxCellBoundsData.targetNormSqUpper_le_twoHundredFiftySix

/-- The one-eighth transport floor fits the retained squared-residual over side-majorant tradeoff. -/
theorem retainedEighthTradeoff_sound
    (data : PreparedSameBoxCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        (1 / 8 : Rat.Fraction.Rational) ≤
      data.residualMarginFloor.toRational ^ 2 /
        (4 * data.sideMajorantUpper.toRational) := by
  rw [← data.transportMargin_eq_oneEighth]
  exact data.toPreparedParametricSameBoxCellBoundsData.retainedFloorTradeoff_sound

end PreparedSameBoxCellBoundsData

namespace PreparedSameBoxReplayCapData

/-- The original edge-specific direct-clearance ceiling is bounded by the retained target cap. -/
theorem directUpper_le {cell : PreparedParametricSameBoxCellBoundsData}
    {edge : Fin 8} (data : PreparedSameBoxReplayCapData cell edge) :
    (cell.directUpperAt edge).toRational ≤ data.targetUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.directUpperLe

/-- The square of the original source cap divided by four fits the retained target cap. -/
theorem sourceQuarter_le_target
    {cell : PreparedParametricSameBoxCellBoundsData} {edge : Fin 8}
    (data : PreparedSameBoxReplayCapData cell edge) :
    data.sourceUpper.toRational ^ 2 / 4 ≤ data.targetUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.sourceQuarterLeTarget

/-- The retained target cap bounds its own square divided by four. -/
theorem target_contracts
    {cell : PreparedParametricSameBoxCellBoundsData} {edge : Fin 8}
    (data : PreparedSameBoxReplayCapData cell edge) :
    data.targetUpper.toRational ^ 2 / 4 ≤ data.targetUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.targetContracts

end PreparedSameBoxReplayCapData

namespace PreparedInitialReplayCapData

/-- The original initial edge's direct-clearance ceiling fits the retained source cap's square divided by four. -/
theorem directUpper_le_quarter
    {cell : PreparedParametricSameBoxCellBoundsData}
    (data : PreparedInitialReplayCapData cell) :
    (cell.directUpperAt 0).toRational ≤ data.sourceUpper.toRational ^ 2 / 4 := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.directUpperLeQuarter

/-- The retained source cap bounds its own square divided by four. -/
theorem source_contracts
    {cell : PreparedParametricSameBoxCellBoundsData}
    (data : PreparedInitialReplayCapData cell) :
    data.sourceUpper.toRational ^ 2 / 4 ≤ data.sourceUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.sourceContracts

/-- The retained x-coordinate squared ceiling is at most sixteen. -/
theorem xSqUpper_le_sixteen
    {cell : PreparedParametricSameBoxCellBoundsData}
    (data : PreparedInitialReplayCapData cell) :
    cell.xSqUpper.toRational ≤ (16 : Rat.Fraction.Rational) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.xSqBounded
  rw [naturalData_toRational,
    show ((16 : Nat) : Rat.Fraction.Rational) = 16 by rfl]
    at promoted
  exact promoted

/-- The retained y-coordinate squared ceiling is at most sixteen. -/
theorem ySqUpper_le_sixteen
    {cell : PreparedParametricSameBoxCellBoundsData}
    (data : PreparedInitialReplayCapData cell) :
    cell.ySqUpper.toRational ≤ (16 : Rat.Fraction.Rational) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.ySqBounded
  rw [naturalData_toRational,
    show ((16 : Nat) : Rat.Fraction.Rational) = 16 by rfl]
    at promoted
  exact promoted

end PreparedInitialReplayCapData

namespace PreparedParametricResetCellBoundsData

/-- The original quartic value at the retained edge's affine source equals its checked displayed source parameter. -/
theorem affineSourceParameter_eq
    (data : PreparedParametricResetCellBoundsData) :
    (data.affineOrigin.toGaussian +
      Gaussian.Scale.scale
        ((data.resetEdge : Rat.Fraction.Rational) / 8)
          data.affineDirection.toGaussian) ^ 4 - 1 =
      (data.source.sourceParameter 0).toGaussian := by
  rw [← eighthParameterData_toRational]
  exact (affineQuarticParameterData_toGaussian data.affineOrigin
    data.affineDirection (eighthParameterData data.resetEdge)).symm.trans
      (Gaussian.Certificate.Raw.GaussianData.eq_sound data.affineSourceParameterExact)

/-- The original quartic value at the retained edge's affine endpoint equals its checked displayed target parameter. -/
theorem affineTargetParameter_eq
    (data : PreparedParametricResetCellBoundsData) :
    (data.affineOrigin.toGaussian +
      Gaussian.Scale.scale
        (((data.resetEdge + 1 : Nat) :
          Rat.Fraction.Rational) / 8)
          data.affineDirection.toGaussian) ^ 4 - 1 =
      (data.source.targetParameter 0).toGaussian := by
  rw [← eighthParameterData_toRational]
  exact (affineQuarticParameterData_toGaussian data.affineOrigin
    data.affineDirection (eighthParameterData (data.resetEdge + 1))).symm.trans
      (Gaussian.Certificate.Raw.GaussianData.eq_sound data.affineTargetParameterExact)

/-- The retained strict coordinate comparison separates the original source and target Gaussian parameters. -/
theorem sourceTarget_ne (data : PreparedParametricResetCellBoundsData) :
    (data.source.sourceParameter 0).toGaussian ≠
      (data.source.targetParameter 0).toGaussian :=
  GaussianData.different_sound data.sourceTargetDifferent

/-- The original quartic value at the affine origin satisfies the retained segment-source squared-norm floor. -/
theorem affineOriginNormSq_lower
    (data : PreparedParametricResetCellBoundsData) :
    data.segmentSourceNormSqLower.toRational ≤
      Data.Gaussian.Norm.Basic.normSq
        (data.affineOrigin.toGaussian ^ 4 - 1) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.affineOriginNormSqLower
  rw [Gaussian.Certificate.Raw.GaussianData.normSq_toRational,
    quarticParameterData_toGaussian] at promoted
  exact promoted

/-- The original affine Lipschitz ceiling times one sixty-fourth equals the retained variation ceiling. -/
theorem affineVariation_eq
    (data : PreparedParametricResetCellBoundsData) :
    data.affineDenseLipschitz.toRational * (1 / 64) =
      data.source.variationUpper.toRational := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.eq_sound data.affineVariationExact
  rw [Data.Rat.Certificate.Raw.RationalData.mul_toRational, oneSixtyFourthData_toRational] at promoted
  exact promoted

/-- The retained derivative floor equals the original fixed-margin formula computed from its source squared-norm floor.
-/
theorem predictedDerivativeLower_eq
    (data : PreparedParametricResetCellBoundsData) :
    data.predictedDerivativeLower.toRational =
      4 * (2 * ((1 / 4 : Rat.Fraction.Rational) +
        (2 * data.segmentSourceNormSqLower.toRational + 1))) := by
  exact (Data.Rat.Certificate.Raw.RationalData.eq_sound data.predictedDerivativeLowerExact).symm.trans
    (predictedDerivativeLowerData_toRational data.segmentSourceNormSqLower)

/-- Promote the checked numerator comparison to the original rational predicted-clearance bound at the supplied margin.
-/
private theorem predictedClearanceFits_sound
    (data : PreparedParametricResetCellBoundsData) (margin : Data.Rat.Certificate.Raw.RationalData)
    (checked : Data.Rat.Certificate.Raw.RationalData.Le predictedClearanceNumeratorData
      (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor margin)
        (predictedClearanceDenominatorLowerData
          data.predictedDerivativeLower))) :
    ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          margin.toRational *
        (4 * (2 * data.predictedDerivativeLower.toRational *
          (1 / 64 : Rat.Fraction.Rational) ^ 2)) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound checked
  rw [predictedClearanceNumeratorData_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, transportFloor_toRational,
    predictedClearanceDenominatorLowerData_toRational] at promoted
  exact promoted

/-- The original predicted-clearance numerator fits the retained before transport floor times its certified denominator
floor. -/
theorem predictedClearanceFitsBefore_sound
    (data : PreparedParametricResetCellBoundsData) :
    ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          data.beforeCell.transportMargin.toRational *
        (4 * (2 * data.predictedDerivativeLower.toRational *
          (1 / 64 : Rat.Fraction.Rational) ^ 2)) :=
  data.predictedClearanceFits_sound data.beforeCell.transportMargin
    data.predictedClearanceFitsBefore

/-- The original predicted-clearance numerator fits the retained after transport floor times its certified denominator
floor. -/
theorem predictedClearanceFitsAfter_sound
    (data : PreparedParametricResetCellBoundsData) :
    ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          data.afterCell.transportMargin.toRational *
        (4 * (2 * data.predictedDerivativeLower.toRational *
          (1 / 64 : Rat.Fraction.Rational) ^ 2)) :=
  data.predictedClearanceFits_sound data.afterCell.transportMargin
    data.predictedClearanceFitsAfter

/-- The source box is exactly the original box retained by the preceding same-box cell. -/
theorem sourceBox_eq_before (data : PreparedParametricResetCellBoundsData) :
    data.source.box.toBox = data.beforeCell.box.toBox :=
  boxEq_sound data.sourceBoxMatchesBefore

/-- The final box is exactly the original box retained by the following same-box cell. -/
theorem finalBox_eq_after (data : PreparedParametricResetCellBoundsData) :
    data.final.box.toBox = data.afterCell.box.toBox :=
  boxEq_sound data.finalBoxMatchesAfter

/-- The original source and final bound records retain the same source Gaussian parameter. -/
theorem sourceParameter_eq_final
    (data : PreparedParametricResetCellBoundsData) :
    (data.source.sourceParameter 0).toGaussian =
      (data.final.sourceParameter 0).toGaussian :=
  Gaussian.Certificate.Raw.GaussianData.eq_sound data.sourceFinalParameterMatch

/-- The original moving-recenter computation returns the exact box retained by the following cell. -/
theorem resetBoxProjection (data : PreparedParametricResetCellBoundsData)
    (parameterNonzero : (data.source.sourceParameter 0).toGaussian ≠ 0)
    (sourceProper : data.beforeCell.box.toBox.Proper) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
        (data.source.sourceParameter 0).toGaussian parameterNonzero
          data.beforeCell.box.toBox sourceProper =
      some data.afterCell.box.toBox := by
  have parameterEq : data.moving.parameter.original.toGaussian =
      (data.source.sourceParameter 0).toGaussian :=
    Gaussian.Certificate.Raw.GaussianData.eq_sound data.movingParameterMatchesSource
  have movingSourceEq : data.moving.sourceBox.original.toBox =
      data.beforeCell.box.toBox :=
    (boxEq_sound data.movingSourceBoxMatches).trans data.sourceBox_eq_before
  have movingFinalEq : data.moving.finalBox.original.toBox =
      data.afterCell.box.toBox :=
    (boxEq_sound data.movingFinalBoxMatches).trans data.finalBox_eq_after
  have computed := data.moving.sound
    (parameterEq.trans_ne parameterNonzero)
    (movingSourceEq ▸ sourceProper)
  simpa only [parameterEq, movingSourceEq, movingFinalEq] using computed

/-- The retained incoming cap bounds its own square divided by four. -/
theorem before_contracts (data : PreparedParametricResetCellBoundsData) :
    data.beforeUpper.toRational ^ 2 / 4 ≤ data.beforeUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.beforeUpperContracts

/-- The retained outgoing cap bounds its own square divided by four. -/
theorem after_contracts (data : PreparedParametricResetCellBoundsData) :
    data.afterUpper.toRational ^ 2 / 4 ≤ data.afterUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.afterUpperContracts

/-- The square of the original incoming cap divided by four does not exceed the retained variation ceiling. -/
theorem beforeQuarter_le_variation
    (data : PreparedParametricResetCellBoundsData) :
    data.beforeUpper.toRational ^ 2 / 4 ≤
      data.source.variationUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.beforeQuarterLeVariation

/-- The original source direct-clearance ceiling does not exceed the retained variation ceiling. -/
theorem sourceUpper_le_variation
    (data : PreparedParametricResetCellBoundsData) :
    data.source.directUpper.toRational ≤
      data.source.variationUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.sourceUpperLeVariation

/-- The retained variation ceiling is strictly below the original final direct-clearance floor. -/
theorem variation_lt_finalLower
    (data : PreparedParametricResetCellBoundsData) :
    data.source.variationUpper.toRational <
      data.final.directLower.toRational :=
  RationalData.lt_sound data.variationLtFinalLower

/-- The retained outgoing transport floor is bounded by the original final direct-clearance floor. -/
theorem transportFloor_le_finalLower
    (data : PreparedParametricResetCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.afterCell.transportMargin.toRational ≤
      data.final.directLower.toRational := by
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  rw [← transportFloor_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.transportFloorLeFinalLower

/-- The original final direct-clearance ceiling is bounded by the retained outgoing cap. -/
theorem finalUpper_le_afterUpper
    (data : PreparedParametricResetCellBoundsData) :
    data.final.directUpper.toRational ≤ data.afterUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.finalUpperLeAfterUpper

/-- The retained reset residual floor denotes a strictly positive rational. -/
theorem resetResidual_positive
    (data : PreparedParametricResetCellBoundsData) :
    0 < data.source.residualMarginFloor.toRational := by
  have promoted := RationalData.lt_sound data.resetResidualPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The retained reset residual floor is bounded by final direct clearance minus the original displacement ceiling. -/
theorem resetResidual_le_finalLower_sub_displacement
    (data : PreparedParametricResetCellBoundsData) :
    data.source.residualMarginFloor.toRational ≤
      data.final.directLower.toRational -
      data.source.displacementUpper.toRational := by
  rw [← Data.Rat.Certificate.Raw.RationalData.sub_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.resetResidualLeFinalLowerSubDisplacement

/-- The retained final side-majorant ceiling is at least one. -/
theorem one_le_finalSideMajorant
    (data : PreparedParametricResetCellBoundsData) :
    (1 : Rat.Fraction.Rational) ≤
      data.final.sideMajorantUpper.toRational := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.oneLeFinalSideMajorant
  rw [naturalData_toRational,
    show ((1 : Nat) : Rat.Fraction.Rational) = 1 by rfl]
    at promoted
  exact promoted

/-- The original retained transport floor is at most the squared residual floor divided by four times the side-majorant
ceiling. -/
theorem retainedFloorTradeoff_sound
    (data : PreparedParametricResetCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.afterCell.transportMargin.toRational ≤
      data.source.residualMarginFloor.toRational ^ 2 /
        (4 * data.final.sideMajorantUpper.toRational) := by
  have sidePositive : (0 : Rat.Fraction.Rational) <
      data.final.sideMajorantUpper.toRational :=
    (by decide : (0 : Rat.Fraction.Rational) < 1).trans_le
      data.one_le_finalSideMajorant
  apply (Rat.Fraction.Order.Field.le_div_iff_pos
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide) sidePositive)).2
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.retainedFloorTradeoff
  rw [Data.Rat.Certificate.Raw.RationalData.mul_toRational, transportFloor_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, naturalData_toRational,
    squareData_toRational] at promoted
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  simpa only [show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl]
    using promoted

/-- The retained source squared-norm ceiling is at most 256. -/
theorem sourceNormSqUpper_le_twoHundredFiftySix
    (data : PreparedParametricResetCellBoundsData) :
    data.source.sourceNormSqUpper.toRational ≤
      (256 : Rat.Fraction.Rational) :=
  checkedUpperBound_sound data.sourceNormSqBounded twoHundredFiftySix_toRational

/-- The retained target squared-norm ceiling is at most 256. -/
theorem targetNormSqUpper_le_twoHundredFiftySix
    (data : PreparedParametricResetCellBoundsData) :
    data.source.targetNormSqUpper.toRational ≤
      (256 : Rat.Fraction.Rational) :=
  checkedUpperBound_sound data.targetNormSqBounded twoHundredFiftySix_toRational

/-- The original final box's retained x-coordinate squared ceiling is at most sixteen. -/
theorem finalXSqUpper_le_sixteen
    (data : PreparedParametricResetCellBoundsData) :
    data.final.xSqUpper.toRational ≤
      (16 : Rat.Fraction.Rational) :=
  checkedNaturalUpperBound_sound 16 data.finalXSqBounded

/-- The original final box's retained y-coordinate squared ceiling is at most sixteen. -/
theorem finalYSqUpper_le_sixteen
    (data : PreparedParametricResetCellBoundsData) :
    data.final.ySqUpper.toRational ≤
      (16 : Rat.Fraction.Rational) :=
  checkedNaturalUpperBound_sound 16 data.finalYSqBounded

end PreparedParametricResetCellBoundsData

namespace PreparedParametricDoubleResetCellBoundsData

/-- The original quartic value at the retained edge's affine source equals its checked displayed source parameter. -/
theorem affineSourceParameter_eq
    (data : PreparedParametricDoubleResetCellBoundsData) :
    (data.affineOrigin.toGaussian +
      Gaussian.Scale.scale
        ((data.resetEdge : Rat.Fraction.Rational) / 8)
          data.affineDirection.toGaussian) ^ 4 - 1 =
      (data.source.sourceParameter 0).toGaussian := by
  rw [← eighthParameterData_toRational]
  exact (affineQuarticParameterData_toGaussian data.affineOrigin
    data.affineDirection (eighthParameterData data.resetEdge)).symm.trans
      (Gaussian.Certificate.Raw.GaussianData.eq_sound data.affineSourceParameterExact)

/-- The original quartic value at the retained edge's affine endpoint equals its checked displayed target parameter. -/
theorem affineTargetParameter_eq
    (data : PreparedParametricDoubleResetCellBoundsData) :
    (data.affineOrigin.toGaussian +
      Gaussian.Scale.scale
        (((data.resetEdge + 1 : Nat) :
          Rat.Fraction.Rational) / 8)
          data.affineDirection.toGaussian) ^ 4 - 1 =
      (data.source.targetParameter 0).toGaussian := by
  rw [← eighthParameterData_toRational]
  exact (affineQuarticParameterData_toGaussian data.affineOrigin
    data.affineDirection (eighthParameterData (data.resetEdge + 1))).symm.trans
      (Gaussian.Certificate.Raw.GaussianData.eq_sound data.affineTargetParameterExact)

/-- The retained strict coordinate comparison separates the original source and target Gaussian parameters. -/
theorem sourceTarget_ne (data : PreparedParametricDoubleResetCellBoundsData) :
    (data.source.sourceParameter 0).toGaussian ≠
      (data.source.targetParameter 0).toGaussian :=
  GaussianData.different_sound data.sourceTargetDifferent

/-- The original quartic value at the affine origin satisfies the retained segment-source squared-norm floor. -/
theorem affineOriginNormSq_lower
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.segmentSourceNormSqLower.toRational ≤
      Data.Gaussian.Norm.Basic.normSq
        (data.affineOrigin.toGaussian ^ 4 - 1) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.affineOriginNormSqLower
  rw [Gaussian.Certificate.Raw.GaussianData.normSq_toRational,
    quarticParameterData_toGaussian] at promoted
  exact promoted

/-- The original affine Lipschitz ceiling times one sixty-fourth equals the retained variation ceiling. -/
theorem affineVariation_eq
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.affineDenseLipschitz.toRational * (1 / 64) =
      data.source.variationUpper.toRational := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.eq_sound data.affineVariationExact
  rw [Data.Rat.Certificate.Raw.RationalData.mul_toRational, oneSixtyFourthData_toRational] at promoted
  exact promoted

/-- The retained derivative floor equals the original fixed-margin formula computed from its source squared-norm floor.
-/
theorem predictedDerivativeLower_eq
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.predictedDerivativeLower.toRational =
      4 * (2 * ((1 / 4 : Rat.Fraction.Rational) +
        (2 * data.segmentSourceNormSqLower.toRational + 1))) := by
  exact (Data.Rat.Certificate.Raw.RationalData.eq_sound data.predictedDerivativeLowerExact).symm.trans
    (predictedDerivativeLowerData_toRational data.segmentSourceNormSqLower)

/-- Promote the checked numerator comparison to the original rational predicted-clearance bound at the supplied margin.
-/
private theorem predictedClearanceFits_sound
    (data : PreparedParametricDoubleResetCellBoundsData)
    (margin : Data.Rat.Certificate.Raw.RationalData)
    (checked : Data.Rat.Certificate.Raw.RationalData.Le predictedClearanceNumeratorData
      (Data.Rat.Certificate.Raw.RationalData.mul (transportFloor margin)
        (predictedClearanceDenominatorLowerData
          data.predictedDerivativeLower))) :
    ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          margin.toRational *
        (4 * (2 * data.predictedDerivativeLower.toRational *
          (1 / 64 : Rat.Fraction.Rational) ^ 2)) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound checked
  rw [predictedClearanceNumeratorData_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, transportFloor_toRational,
    predictedClearanceDenominatorLowerData_toRational] at promoted
  exact promoted

/-- The original predicted-clearance numerator fits the retained before transport floor times its certified denominator
floor. -/
theorem predictedClearanceFitsBefore_sound
    (data : PreparedParametricDoubleResetCellBoundsData) :
    ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          data.beforeCell.transportMargin.toRational *
        (4 * (2 * data.predictedDerivativeLower.toRational *
          (1 / 64 : Rat.Fraction.Rational) ^ 2)) :=
  data.predictedClearanceFits_sound data.beforeCell.transportMargin
    data.predictedClearanceFitsBefore

/-- The original predicted-clearance numerator fits the retained intermediate transport floor times its certified
denominator floor. -/
theorem predictedClearanceFitsIntermediate_sound
    (data : PreparedParametricDoubleResetCellBoundsData) :
    ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          data.intermediateMargin.toRational *
        (4 * (2 * data.predictedDerivativeLower.toRational *
          (1 / 64 : Rat.Fraction.Rational) ^ 2)) :=
  data.predictedClearanceFits_sound data.intermediateMargin
    data.predictedClearanceFitsIntermediate

/-- The retained intermediate transport margin denotes a strictly positive rational. -/
theorem intermediateMargin_positive
    (data : PreparedParametricDoubleResetCellBoundsData) :
    0 < data.intermediateMargin.toRational := by
  have promoted := RationalData.lt_sound data.intermediateMarginPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The original predicted-clearance numerator fits the retained after transport floor times its certified denominator
floor. -/
theorem predictedClearanceFitsAfter_sound
    (data : PreparedParametricDoubleResetCellBoundsData) :
    ((1 / 4 : Rat.Fraction.Rational) * (1 / 64) ^ 2 -
        36 * 8 * ((1 / 64) ^ 2) ^ 2) ^ 2 ≤
      SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
          data.afterCell.transportMargin.toRational *
        (4 * (2 * data.predictedDerivativeLower.toRational *
          (1 / 64 : Rat.Fraction.Rational) ^ 2)) :=
  data.predictedClearanceFits_sound data.afterCell.transportMargin
    data.predictedClearanceFitsAfter

/-- The source box is exactly the original box retained by the preceding same-box cell. -/
theorem sourceBox_eq_before
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.source.box.toBox = data.beforeCell.box.toBox :=
  boxEq_sound data.sourceBoxMatchesBefore

/-- The final box is exactly the original box retained by the following same-box cell. -/
theorem finalBox_eq_after
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.final.box.toBox = data.afterCell.box.toBox :=
  boxEq_sound data.finalBoxMatchesAfter

/-- The original source and intermediate bound records retain the same source Gaussian parameter. -/
theorem sourceParameter_eq_intermediate
    (data : PreparedParametricDoubleResetCellBoundsData) :
    (data.source.sourceParameter 0).toGaussian =
      (data.intermediate.sourceParameter 0).toGaussian :=
  Gaussian.Certificate.Raw.GaussianData.eq_sound data.sourceIntermediateParameterMatch

/-- The original source and final bound records retain the same source Gaussian parameter. -/
theorem sourceParameter_eq_final
    (data : PreparedParametricDoubleResetCellBoundsData) :
    (data.source.sourceParameter 0).toGaussian =
      (data.final.sourceParameter 0).toGaussian :=
  Gaussian.Certificate.Raw.GaussianData.eq_sound data.sourceFinalParameterMatch

/-- The original intermediate box has squared diagonal strictly below five. -/
theorem intermediateBoxDiagonalSq_lt_five
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.intermediate.box.toBox.diagonalSq <
      (5 : Rat.Fraction.Rational) := by
  have promoted := RationalData.lt_sound data.intermediateBoxDiagonalLtFive
  rw [boxDiagonalSqData_toRational, naturalData_toRational,
    show ((5 : Nat) : Rat.Fraction.Rational) = 5 by rfl]
    at promoted
  exact promoted

/-- The original intermediate box's lower x coordinate is at least negative three. -/
theorem negativeThree_le_intermediateXLower
    (data : PreparedParametricDoubleResetCellBoundsData) :
    (-3 : Rat.Fraction.Rational) ≤
      data.intermediate.box.toBox.xLower := by
  have promoted :=
    Data.Rat.Certificate.Raw.RationalData.le_sound data.intermediateBoxNegativeThreeLeXLower
  rw [Data.Rat.Certificate.Raw.RationalData.neg_toRational, naturalData_toRational,
    show ((3 : Nat) : Rat.Fraction.Rational) = 3 by rfl]
    at promoted
  exact promoted

/-- The original intermediate box's upper x coordinate is at most three. -/
theorem intermediateXUpper_le_three
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.intermediate.box.toBox.xUpper ≤
      (3 : Rat.Fraction.Rational) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.intermediateBoxXUpperLeThree
  rw [naturalData_toRational,
    show ((3 : Nat) : Rat.Fraction.Rational) = 3 by rfl]
    at promoted
  exact promoted

/-- The original intermediate box's lower y coordinate is at least negative three. -/
theorem negativeThree_le_intermediateYLower
    (data : PreparedParametricDoubleResetCellBoundsData) :
    (-3 : Rat.Fraction.Rational) ≤
      data.intermediate.box.toBox.yLower := by
  have promoted :=
    Data.Rat.Certificate.Raw.RationalData.le_sound data.intermediateBoxNegativeThreeLeYLower
  rw [Data.Rat.Certificate.Raw.RationalData.neg_toRational, naturalData_toRational,
    show ((3 : Nat) : Rat.Fraction.Rational) = 3 by rfl]
    at promoted
  exact promoted

/-- The original intermediate box's upper y coordinate is at most three. -/
theorem intermediateYUpper_le_three
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.intermediate.box.toBox.yUpper ≤
      (3 : Rat.Fraction.Rational) := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.intermediateBoxYUpperLeThree
  rw [naturalData_toRational,
    show ((3 : Nat) : Rat.Fraction.Rational) = 3 by rfl]
    at promoted
  exact promoted

/-- The first original moving-recenter computation returns the exact retained intermediate box. -/
theorem firstResetBoxProjection
    (data : PreparedParametricDoubleResetCellBoundsData)
    (parameterNonzero : (data.source.sourceParameter 0).toGaussian ≠ 0)
    (sourceProper : data.beforeCell.box.toBox.Proper) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
        (data.source.sourceParameter 0).toGaussian parameterNonzero
          data.beforeCell.box.toBox sourceProper =
      some data.intermediate.box.toBox := by
  have parameterEq : data.firstMoving.parameter.original.toGaussian =
      (data.source.sourceParameter 0).toGaussian :=
    Gaussian.Certificate.Raw.GaussianData.eq_sound data.firstMovingParameterMatchesSource
  have sourceEq : data.firstMoving.sourceBox.original.toBox =
      data.beforeCell.box.toBox :=
    (boxEq_sound data.firstMovingSourceBoxMatches).trans data.sourceBox_eq_before
  have finalEq : data.firstMoving.finalBox.original.toBox =
      data.intermediate.box.toBox :=
    boxEq_sound data.firstMovingFinalBoxMatches
  have computed := data.firstMoving.sound
    (parameterEq.trans_ne parameterNonzero) (sourceEq ▸ sourceProper)
  simpa only [parameterEq, sourceEq, finalEq] using computed

/-- The second original moving-recenter computation returns the exact box retained by the following cell. -/
theorem secondResetBoxProjection
    (data : PreparedParametricDoubleResetCellBoundsData)
    (parameterNonzero : (data.source.sourceParameter 0).toGaussian ≠ 0)
    (sourceProper : data.intermediate.box.toBox.Proper) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
        (data.source.sourceParameter 0).toGaussian parameterNonzero
          data.intermediate.box.toBox sourceProper =
      some data.afterCell.box.toBox := by
  have parameterEq : data.secondMoving.parameter.original.toGaussian =
      (data.source.sourceParameter 0).toGaussian :=
    Gaussian.Certificate.Raw.GaussianData.eq_sound data.secondMovingParameterMatchesSource
  have sourceEq : data.secondMoving.sourceBox.original.toBox =
      data.intermediate.box.toBox :=
    boxEq_sound data.secondMovingSourceBoxMatches
  have finalEq : data.secondMoving.finalBox.original.toBox =
      data.afterCell.box.toBox :=
    (boxEq_sound data.secondMovingFinalBoxMatches).trans data.finalBox_eq_after
  have computed := data.secondMoving.sound
    (parameterEq.trans_ne parameterNonzero) (sourceEq ▸ sourceProper)
  simpa only [parameterEq, sourceEq, finalEq] using computed

/-- The retained incoming cap bounds its own square divided by four. -/
theorem before_contracts
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.beforeUpper.toRational ^ 2 / 4 ≤ data.beforeUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.beforeUpperContracts

/-- The retained outgoing cap bounds its own square divided by four. -/
theorem after_contracts
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.afterUpper.toRational ^ 2 / 4 ≤ data.afterUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.afterUpperContracts

/-- The square of the original incoming cap divided by four does not exceed the retained variation ceiling. -/
theorem beforeQuarter_le_variation
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.beforeUpper.toRational ^ 2 / 4 ≤
      data.source.variationUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.beforeQuarterLeVariation

/-- The original source direct-clearance ceiling does not exceed the retained variation ceiling. -/
theorem sourceUpper_le_variation
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.source.directUpper.toRational ≤
      data.source.variationUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.sourceUpperLeVariation

/-- The original intermediate direct-clearance ceiling still does not exceed the retained variation ceiling. -/
theorem intermediateUpper_le_variation
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.intermediate.directUpper.toRational ≤
      data.source.variationUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.intermediateUpperLeVariation

/-- The retained intermediate transport floor is bounded by the original intermediate direct-clearance floor. -/
theorem transportFloor_le_intermediateLower
    (data : PreparedParametricDoubleResetCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.intermediateMargin.toRational ≤
      data.intermediate.directLower.toRational := by
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  rw [← transportFloor_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.transportFloorLeIntermediateLower

/-- The retained variation ceiling is strictly below the original final direct-clearance floor. -/
theorem variation_lt_finalLower
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.source.variationUpper.toRational < data.final.directLower.toRational :=
  RationalData.lt_sound data.variationLtFinalLower

/-- The retained outgoing transport floor is bounded by the original final direct-clearance floor. -/
theorem transportFloor_le_finalLower
    (data : PreparedParametricDoubleResetCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.afterCell.transportMargin.toRational ≤
      data.final.directLower.toRational := by
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  rw [← transportFloor_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.transportFloorLeFinalLower

/-- The original final direct-clearance ceiling is bounded by the retained outgoing cap. -/
theorem finalUpper_le_afterUpper
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.final.directUpper.toRational ≤ data.afterUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.finalUpperLeAfterUpper

/-- The retained reset residual floor denotes a strictly positive rational. -/
theorem resetResidual_positive
    (data : PreparedParametricDoubleResetCellBoundsData) :
    0 < data.source.residualMarginFloor.toRational := by
  have promoted := RationalData.lt_sound data.resetResidualPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The retained reset residual floor is bounded by final direct clearance minus the original displacement ceiling. -/
theorem resetResidual_le_finalLower_sub_displacement
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.source.residualMarginFloor.toRational ≤
      data.final.directLower.toRational -
      data.source.displacementUpper.toRational := by
  rw [← Data.Rat.Certificate.Raw.RationalData.sub_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.resetResidualLeFinalLowerSubDisplacement

/-- The retained final side-majorant ceiling is at least one. -/
theorem one_le_finalSideMajorant
    (data : PreparedParametricDoubleResetCellBoundsData) :
    (1 : Rat.Fraction.Rational) ≤
      data.final.sideMajorantUpper.toRational := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.oneLeFinalSideMajorant
  rw [naturalData_toRational,
    show ((1 : Nat) : Rat.Fraction.Rational) = 1 by rfl]
    at promoted
  exact promoted

/-- The original retained transport floor is at most the squared residual floor divided by four times the side-majorant
ceiling. -/
theorem retainedFloorTradeoff_sound
    (data : PreparedParametricDoubleResetCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.afterCell.transportMargin.toRational ≤
      data.source.residualMarginFloor.toRational ^ 2 /
        (4 * data.final.sideMajorantUpper.toRational) := by
  have sidePositive : (0 : Rat.Fraction.Rational) <
      data.final.sideMajorantUpper.toRational :=
    (by decide : (0 : Rat.Fraction.Rational) < 1).trans_le
      data.one_le_finalSideMajorant
  apply (Rat.Fraction.Order.Field.le_div_iff_pos
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide) sidePositive)).2
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.retainedFloorTradeoff
  rw [Data.Rat.Certificate.Raw.RationalData.mul_toRational, transportFloor_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, naturalData_toRational,
    squareData_toRational] at promoted
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  simpa only [show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl]
    using promoted

/-- The retained source squared-norm ceiling is at most 256. -/
theorem sourceNormSqUpper_le_twoHundredFiftySix
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.source.sourceNormSqUpper.toRational ≤
      (256 : Rat.Fraction.Rational) :=
  checkedUpperBound_sound data.sourceNormSqBounded twoHundredFiftySix_toRational

/-- The retained target squared-norm ceiling is at most 256. -/
theorem targetNormSqUpper_le_twoHundredFiftySix
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.source.targetNormSqUpper.toRational ≤
      (256 : Rat.Fraction.Rational) :=
  checkedUpperBound_sound data.targetNormSqBounded twoHundredFiftySix_toRational

/-- The original final box's retained x-coordinate squared ceiling is at most sixteen. -/
theorem finalXSqUpper_le_sixteen
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.final.xSqUpper.toRational ≤
      (16 : Rat.Fraction.Rational) :=
  checkedNaturalUpperBound_sound 16 data.finalXSqBounded

/-- The original final box's retained y-coordinate squared ceiling is at most sixteen. -/
theorem finalYSqUpper_le_sixteen
    (data : PreparedParametricDoubleResetCellBoundsData) :
    data.final.ySqUpper.toRational ≤
      (16 : Rat.Fraction.Rational) :=
  checkedNaturalUpperBound_sound 16 data.finalYSqBounded

end PreparedParametricDoubleResetCellBoundsData

namespace PreparedResetCellBoundsData

/-- The original final box's left side coordinate is nonzero by its checked positive square. -/
theorem finalLeftCoordinate_ne (data : PreparedResetCellBoundsData) :
    data.final.box.toBox.xLower ≠ 0 := by
  change data.final.box.xLower.toRational ≠ 0
  exact PreparedExplicitSideBoundsData.ne_of_squareData_positive _
    data.finalLeftCoordinateNonzero

/-- The original final box's right side coordinate is nonzero by its checked positive square. -/
theorem finalRightCoordinate_ne (data : PreparedResetCellBoundsData) :
    data.final.box.toBox.xUpper ≠ 0 := by
  change data.final.box.xUpper.toRational ≠ 0
  exact PreparedExplicitSideBoundsData.ne_of_squareData_positive _
    data.finalRightCoordinateNonzero

/-- The original final box's bottom side coordinate is nonzero by its checked positive square. -/
theorem finalBottomCoordinate_ne (data : PreparedResetCellBoundsData) :
    data.final.box.toBox.yLower ≠ 0 := by
  change data.final.box.yLower.toRational ≠ 0
  exact PreparedExplicitSideBoundsData.ne_of_squareData_positive _
    data.finalBottomCoordinateNonzero

/-- The original final box's top side coordinate is nonzero by its checked positive square. -/
theorem finalTopCoordinate_ne (data : PreparedResetCellBoundsData) :
    data.final.box.toBox.yUpper ≠ 0 := by
  change data.final.box.yUpper.toRational ≠ 0
  exact PreparedExplicitSideBoundsData.ne_of_squareData_positive _
    data.finalTopCoordinateNonzero

/-- The source box is exactly the original box retained by the preceding same-box cell. -/
theorem sourceBox_eq_before (data : PreparedResetCellBoundsData) :
    data.source.box.toBox = data.beforeCell.box.toBox :=
  boxEq_sound data.sourceBoxMatchesBefore

/-- The final box is exactly the original box retained by the following same-box cell. -/
theorem finalBox_eq_after (data : PreparedResetCellBoundsData) :
    data.final.box.toBox = data.afterCell.box.toBox :=
  boxEq_sound data.finalBoxMatchesAfter

/-- The original source and final bound records retain the same source Gaussian parameter. -/
theorem sourceParameter_eq_final (data : PreparedResetCellBoundsData) :
    (data.source.sourceParameter 0).toGaussian =
      (data.final.sourceParameter 0).toGaussian :=
  Gaussian.Certificate.Raw.GaussianData.eq_sound data.sourceFinalParameterMatch

/-- The original moving-recenter computation returns the exact box retained by the following cell. -/
theorem resetBoxProjection (data : PreparedResetCellBoundsData)
    (parameterNonzero : (data.source.sourceParameter 0).toGaussian ≠ 0)
    (sourceProper : data.beforeCell.box.toBox.Proper) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.movingRecenterBox?
        (data.source.sourceParameter 0).toGaussian parameterNonzero
          data.beforeCell.box.toBox sourceProper =
      some data.afterCell.box.toBox := by
  have parameterEq : data.moving.parameter.original.toGaussian =
      (data.source.sourceParameter 0).toGaussian :=
    Gaussian.Certificate.Raw.GaussianData.eq_sound data.movingParameterMatchesSource
  have movingSourceEq : data.moving.sourceBox.original.toBox =
      data.beforeCell.box.toBox :=
    (boxEq_sound data.movingSourceBoxMatches).trans data.sourceBox_eq_before
  have movingFinalEq : data.moving.finalBox.original.toBox =
      data.afterCell.box.toBox :=
    (boxEq_sound data.movingFinalBoxMatches).trans data.finalBox_eq_after
  have computed := data.moving.sound
    (parameterEq.trans_ne parameterNonzero)
    (movingSourceEq ▸ sourceProper)
  simpa only [parameterEq, movingSourceEq, movingFinalEq] using computed

/-- The preceding same-box cell and original reset source retain the same variation ceiling. -/
theorem variation_eq_source (data : PreparedResetCellBoundsData) :
    data.beforeCell.variationUpper.toRational =
      data.source.variationUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.eq_sound data.resetVariationMatchesBefore

/-- The preceding cell's original direct-clearance ceiling fits the retained incoming cap. -/
theorem beforeDirectUpper_le (data : PreparedResetCellBoundsData) :
    data.beforeCell.directUpper.toRational ≤ data.beforeUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.beforeDirectUpperLe

/-- The following cell's original direct-clearance ceiling fits the retained outgoing cap. -/
theorem afterDirectUpper_le (data : PreparedResetCellBoundsData) :
    data.afterCell.directUpper.toRational ≤ data.afterUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.afterDirectUpperLe

/-- The retained incoming cap bounds its own square divided by four. -/
theorem before_contracts (data : PreparedResetCellBoundsData) :
    data.beforeUpper.toRational ^ 2 / 4 ≤ data.beforeUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.beforeUpperContracts

/-- The retained outgoing cap bounds its own square divided by four. -/
theorem after_contracts (data : PreparedResetCellBoundsData) :
    data.afterUpper.toRational ^ 2 / 4 ≤ data.afterUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.afterUpperContracts

/-- The retained fixed reset margin denotes a strictly positive rational. -/
theorem margin_positive (data : PreparedResetCellBoundsData) :
    0 < data.marginFloor.toRational := by
  have promoted := RationalData.lt_sound data.marginFloorPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The retained fixed reset margin equals exactly one eighth. -/
theorem marginFloor_eq_eighth (data : PreparedResetCellBoundsData) :
    data.marginFloor.toRational =
      (1 / 8 : Rat.Fraction.Rational) :=
  (Data.Rat.Certificate.Raw.RationalData.eq_sound data.marginFloorIsEighth).trans
    oneEighthData_toRational

/-- The square of the original incoming cap divided by four does not exceed the retained variation ceiling. -/
theorem beforeQuarter_le_variation (data : PreparedResetCellBoundsData) :
    data.beforeUpper.toRational ^ 2 / 4 ≤
      data.source.variationUpper.toRational := by
  rw [← quarterSquare_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.beforeQuarterLeVariation

/-- The original source direct-clearance ceiling does not exceed the retained variation ceiling. -/
theorem sourceUpper_le_variation (data : PreparedResetCellBoundsData) :
    data.source.directUpper.toRational ≤
      data.source.variationUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.sourceUpperLeVariation

/-- The retained variation ceiling is strictly below the original final direct-clearance floor. -/
theorem variation_lt_finalLower (data : PreparedResetCellBoundsData) :
    data.source.variationUpper.toRational <
      data.final.directLower.toRational :=
  RationalData.lt_sound data.variationLtFinalLower

/-- The retained outgoing transport floor is bounded by the original final direct-clearance floor. -/
theorem transportFloor_le_finalLower (data : PreparedResetCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.marginFloor.toRational ≤ data.final.directLower.toRational := by
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  rw [← transportFloor_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.transportFloorLeFinalLower

/-- The original final direct-clearance ceiling is bounded by the retained outgoing cap. -/
theorem finalUpper_le_afterUpper (data : PreparedResetCellBoundsData) :
    data.final.directUpper.toRational ≤ data.afterUpper.toRational :=
  Data.Rat.Certificate.Raw.RationalData.le_sound data.finalUpperLeAfterUpper

/-- The retained reset residual floor denotes a strictly positive rational. -/
theorem resetResidual_positive
    (data : PreparedResetCellBoundsData) :
    0 < data.source.residualMarginFloor.toRational := by
  have promoted := RationalData.lt_sound data.resetResidualPositive
  change (0 : Rat.Fraction.Rational) *
      (1 : Rat.Fraction.Rational)⁻¹ < _ at promoted
  simpa only [Rat.Fraction.Field.zero_mul_direct] using promoted

/-- The retained reset residual floor is bounded by final direct clearance minus the original displacement ceiling. -/
theorem resetResidual_le_finalLower_sub_displacement
    (data : PreparedResetCellBoundsData) :
    data.source.residualMarginFloor.toRational ≤
      data.final.directLower.toRational -
      data.source.displacementUpper.toRational := by
  rw [← Data.Rat.Certificate.Raw.RationalData.sub_toRational]
  exact Data.Rat.Certificate.Raw.RationalData.le_sound data.resetResidualLeFinalLowerSubDisplacement

/-- The retained final side-majorant ceiling is at least one. -/
theorem one_le_finalSideMajorant (data : PreparedResetCellBoundsData) :
    (1 : Rat.Fraction.Rational) ≤
      data.final.sideMajorantUpper.toRational := by
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.oneLeFinalSideMajorant
  rw [naturalData_toRational,
    show ((1 : Nat) : Rat.Fraction.Rational) = 1 by rfl]
    at promoted
  exact promoted

/-- The original retained transport floor is at most the squared residual floor divided by four times the side-majorant
ceiling. -/
theorem retainedFloorTradeoff_sound (data : PreparedResetCellBoundsData) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
        data.marginFloor.toRational ≤
      data.source.residualMarginFloor.toRational ^ 2 /
        (4 * data.final.sideMajorantUpper.toRational) := by
  have sidePositive : (0 : Rat.Fraction.Rational) <
      data.final.sideMajorantUpper.toRational :=
    (by decide : (0 : Rat.Fraction.Rational) < 1).trans_le
      data.one_le_finalSideMajorant
  apply (Rat.Fraction.Order.Field.le_div_iff_pos
    (Rat.Fraction.Order.Arithmetic.mul_pos_direct (by decide) sidePositive)).2
  have promoted := Data.Rat.Certificate.Raw.RationalData.le_sound data.retainedFloorTradeoff
  rw [Data.Rat.Certificate.Raw.RationalData.mul_toRational, transportFloor_toRational,
    Data.Rat.Certificate.Raw.RationalData.mul_toRational, naturalData_toRational,
    squareData_toRational] at promoted
  unfold SquareRoot.Clearance.ExactQuadraticOwnerClearance.quadraticAmbientTransportFloorAt
  simpa only [show ((4 : Nat) : Rat.Fraction.Rational) = 4 by rfl]
    using promoted

/-- The retained source squared-norm ceiling is at most 256. -/
theorem sourceNormSqUpper_le_twoHundredFiftySix
    (data : PreparedResetCellBoundsData) :
    data.source.sourceNormSqUpper.toRational ≤
      (256 : Rat.Fraction.Rational) :=
  checkedUpperBound_sound data.sourceNormSqBounded twoHundredFiftySix_toRational

/-- The retained target squared-norm ceiling is at most 256. -/
theorem targetNormSqUpper_le_twoHundredFiftySix
    (data : PreparedResetCellBoundsData) :
    data.source.targetNormSqUpper.toRational ≤
      (256 : Rat.Fraction.Rational) :=
  checkedUpperBound_sound data.targetNormSqBounded twoHundredFiftySix_toRational

/-- The original final box's retained x-coordinate squared ceiling is at most sixteen. -/
theorem finalXSqUpper_le_sixteen (data : PreparedResetCellBoundsData) :
    data.final.xSqUpper.toRational ≤
      (16 : Rat.Fraction.Rational) :=
  checkedNaturalUpperBound_sound 16 data.finalXSqBounded

/-- The original final box's retained y-coordinate squared ceiling is at most sixteen. -/
theorem finalYSqUpper_le_sixteen (data : PreparedResetCellBoundsData) :
    data.final.ySqUpper.toRational ≤
      (16 : Rat.Fraction.Rational) :=
  checkedNaturalUpperBound_sound 16 data.finalYSqBounded

end PreparedResetCellBoundsData

namespace PreparedSameBoxSideBoundsData

/-- The original box's left side coordinate is nonzero by its checked positive square. -/
theorem leftCoordinate_ne (data : PreparedSameBoxSideBoundsData) :
    data.box.toBox.xLower ≠ 0 := by
  change data.box.xLower.toRational ≠ 0
  exact PreparedExplicitSideBoundsData.ne_of_squareData_positive _
    data.leftCoordinateNonzero

/-- The original box's right side coordinate is nonzero by its checked positive square. -/
theorem rightCoordinate_ne (data : PreparedSameBoxSideBoundsData) :
    data.box.toBox.xUpper ≠ 0 := by
  change data.box.xUpper.toRational ≠ 0
  exact PreparedExplicitSideBoundsData.ne_of_squareData_positive _
    data.rightCoordinateNonzero

/-- The original box's bottom side coordinate is nonzero by its checked positive square. -/
theorem bottomCoordinate_ne (data : PreparedSameBoxSideBoundsData) :
    data.box.toBox.yLower ≠ 0 := by
  change data.box.yLower.toRational ≠ 0
  exact PreparedExplicitSideBoundsData.ne_of_squareData_positive _
    data.bottomCoordinateNonzero

/-- The original box's top side coordinate is nonzero by its checked positive square. -/
theorem topCoordinate_ne (data : PreparedSameBoxSideBoundsData) :
    data.box.toBox.yUpper ≠ 0 := by
  change data.box.yUpper.toRational ≠ 0
  exact PreparedExplicitSideBoundsData.ne_of_squareData_positive _
    data.topCoordinateNonzero

/-- The original displayed source parameter equals the quartic value at its retained horizontal grid index. -/
theorem sourceParameter_eq_quarticGrid
    (data : PreparedSameBoxSideBoundsData) (edge : Fin 8) :
    (data.sourceParameter edge).toGaussian =
      (quarticHorizontalGridParameterData
        (data.sourceGridIndex edge)).toGaussian :=
  Gaussian.Certificate.Raw.GaussianData.eq_sound (data.sourceGridFormula edge)

/-- Reconstruct the original box's direct boundary-clearance bounds from its retained checked side data. -/
theorem directBoundaryBounds (data : PreparedSameBoxSideBoundsData)
    (edge : Fin 8) :
    SquareRoot.Clearance.ExactQuadraticOwnerClearance.DirectBoundaryBounds
      (data.sourceParameter edge).toGaussian data.box.toBox
        data.directLower.toRational data.directUpper.toRational :=
  data.toPreparedExplicitSideBoundsData.directBoundaryBounds edge

/-- The original left side's squared real constant satisfies the retained vertical ceiling. -/
theorem leftVertical_le (data : PreparedSameBoxSideBoundsData)
    (edge : Fin 8) :
    (data.box.toBox.xLower ^ 2 -
        (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
      data.verticalRealUpper.toRational :=
  data.toPreparedExplicitSideBoundsData.leftVertical_le edge

/-- The original right side's squared real constant satisfies the retained vertical ceiling. -/
theorem rightVertical_le (data : PreparedSameBoxSideBoundsData)
    (edge : Fin 8) :
    (data.box.toBox.xUpper ^ 2 -
        (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
      data.verticalRealUpper.toRational :=
  data.toPreparedExplicitSideBoundsData.rightVertical_le edge

/-- The original bottom side's squared real constant satisfies the retained horizontal ceiling. -/
theorem bottomHorizontal_le (data : PreparedSameBoxSideBoundsData)
    (edge : Fin 8) :
    (-data.box.toBox.yLower ^ 2 -
        (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
      data.horizontalRealUpper.toRational :=
  data.toPreparedExplicitSideBoundsData.bottomHorizontal_le edge

/-- The original top side's squared real constant satisfies the retained horizontal ceiling. -/
theorem topHorizontal_le (data : PreparedSameBoxSideBoundsData)
    (edge : Fin 8) :
    (-data.box.toBox.yUpper ^ 2 -
        (data.sourceParameter edge).toGaussian.re) ^ 2 ≤
      data.horizontalRealUpper.toRational :=
  data.toPreparedExplicitSideBoundsData.topHorizontal_le edge

/-- The original parameter's squared imaginary constant satisfies the retained ceiling. -/
theorem imaginary_le (data : PreparedSameBoxSideBoundsData)
    (edge : Fin 8) :
    (-(data.sourceParameter edge).toGaussian.im) ^ 2 ≤
      data.imaginaryUpper.toRational :=
  data.toPreparedExplicitSideBoundsData.imaginary_le edge

/-- The original vertical quadratic side budget satisfies the retained common majorant ceiling. -/
theorem verticalBudget_le (data : PreparedSameBoxSideBoundsData) :
    2 * (4 * data.verticalIntervalSqUpper.toRational *
          data.verticalIntervalSqUpper.toRational +
        data.verticalRealUpper.toRational) +
      2 * (8 * data.xSqUpper.toRational *
          data.verticalIntervalSqUpper.toRational +
        data.imaginaryUpper.toRational) ≤
      data.sideMajorantUpper.toRational :=
  data.toPreparedExplicitSideBoundsData.verticalBudget_le

/-- The original horizontal quadratic side budget satisfies the retained common majorant ceiling. -/
theorem horizontalBudget_le (data : PreparedSameBoxSideBoundsData) :
    2 * (4 * data.horizontalIntervalSqUpper.toRational *
          data.horizontalIntervalSqUpper.toRational +
        data.horizontalRealUpper.toRational) +
      2 * (8 * data.ySqUpper.toRational *
          data.horizontalIntervalSqUpper.toRational +
        data.imaginaryUpper.toRational) ≤
      data.sideMajorantUpper.toRational :=
  data.toPreparedExplicitSideBoundsData.horizontalBudget_le

end PreparedSameBoxSideBoundsData

namespace PreparedEdgeReplayData

/-- Flatten the original segment and edge indices using the supplied number of edges per segment. -/
@[expose] def flatIndex (event : PreparedEdgeReplayData) (edgesPerSegment : Nat) : Nat :=
  event.segmentIndex * edgesPerSegment + event.edgeIndex

end PreparedEdgeReplayData

set_option genInjectivity false in
/-- A compact run map for one prepared bank.

The retained events start at the first edge, increase strictly, and remain within the exact finite bank dimensions. -/
structure PreparedBankReplayCertificate where
  /-- The original finite number of outer segments in the bank. -/ segmentCount : Nat
  /-- The original finite number of mesh edges in each segment. -/ edgesPerSegment : Nat
  /-- The retained ordered list of original preparation observations. -/ events : List PreparedEdgeReplayData
  /-- The retained bank contains at least one outer segment. -/ segmentCountPositive : 0 < segmentCount
  /-- Every retained segment has at least one edge. -/ edgesPerSegmentPositive : 0 < edgesPerSegment
  /-- The original observation list is nonempty. -/ eventsNonempty : events ≠ []
  /-- The first retained observation is exactly at segment zero and edge zero. -/ startsAtZero : match events with
    | [] => False
    | first :: _ => first.segmentIndex = 0 ∧ first.edgeIndex = 0
  /-- Every retained observation has original indices within the bank's finite dimensions. -/ eventsInRange : ∀ event ∈
    events,
    event.segmentIndex < segmentCount ∧ event.edgeIndex < edgesPerSegment
  /-- The original observation list has strictly increasing flattened segment-edge indices. -/ eventsIncreasing :
    events.Pairwise fun left right =>
    left.flatIndex edgesPerSegment < right.flatIndex edgesPerSegment

constructive_injectivity PreparedBankReplayCertificate

end Purelib.Riemann.Integration.QuarticPreparedBankCertificateVerifier

end
