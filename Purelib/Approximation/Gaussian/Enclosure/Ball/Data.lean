module

public import Purelib.Data.Gaussian.Norm.Comparison
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Add
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Ball.Apart
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Division
public import Purelib.Approximation.Gaussian.Enclosure.Ball.Mul
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.Gaussian.Basic (Canonical)

/-!
# Numerical ball data and certified readback

Ball data retain exactly a Gaussian rational centre and rational squared-radius
datum, without a process or hidden callback. Point, translation, scaling and
division compute the original numerical formulas. Their readback laws compare
those exact fields with the original certified ball constructions.

A raw squared radius carries no nonnegativity or apartness certificate.
Division readback additionally retains the original denominator apartness owner.
-/

namespace Purelib.Approximation.Gaussian.Enclosure.Ball.Data

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Data.Gaussian.Basic.Canonical.Norm
open Purelib.Approximation.Gaussian.Enclosure

@[expose] public section

set_option genInjectivity false in
/-- Exactly the executable numerical fields of a ball.

The Gaussian centre and rational squared-radius datum retain no hidden
process, callback or nonnegativity witness. -/
@[ext] structure BallData where
  /-- The retained Gaussian rational numerical centre. -/ center : Canonical
  /-- The retained rational squared-radius datum, without a nonnegativity certificate. -/ radiusSq : Fraction.Rational
deriving DecidableEq

constructive_injectivity BallData

end

namespace BallData

/-- Read the centre and squared-radius data of a certified rational ball.

The retained centre and squared radius are copied exactly. The original
certified ball remains the separate owner of its nonnegativity proof. -/
@[expose] public def ofBall (ball : Ball) : BallData := ⟨ball.center, ball.radiusSq⟩

/-- Build numerical zero-radius ball data at the displayed Gaussian rational point.

The centre is the supplied point and the stored squared radius is zero.
No additional candidate or process reading is selected. -/
@[expose] public def point (value : Canonical) : BallData := ⟨value, 0⟩

/-- Subtract a displayed shift from the numerical centre and double the stored radius datum.

The original Gaussian subtraction and exact radius expression are retained.
The operation stores numerical data without claiming a semantic enclosure. -/
@[expose] public def translate (ball : BallData) (shift : Canonical) : BallData :=
  ⟨ball.center - shift, 2 * (ball.radiusSq + 0)⟩

/-- Scale the numerical centre and radius datum by the displayed Gaussian factor and its reduced quadrance.

The original Gaussian product and reduced quadrance calculation determine
the centre and radius, including the original rational factor four. -/
@[expose] public def scale (factor : Canonical) (ball : BallData) : BallData :=
  ⟨factor * ball.center,
    4 * (Comparison.normSqFromReduced factor * ball.radiusSq)⟩

/-- Compute numerical quotient ball data from a scalar numerator and supplied lower-quadrance datum.

The operation performs finite arithmetic; apartness and accuracy require separate certificates for the supplied
denominator data. -/
@[expose] public def divide (numerator : Canonical) (lowerSq : Fraction.Rational) (ball : BallData) :
  BallData :=
  ⟨numerator / ball.center,
    (2 * (Comparison.normSqFromReduced numerator * ball.radiusSq)) / (lowerSq * Comparison.normSqFromReduced
      ball.center)⟩

/-- Numerical translation agrees with reading back certified subtraction of the exact shift ball.

The certified subtraction uses the exact zero-radius shift ball. Its
original numerical fields agree with the displayed data translation. -/
public theorem translate_ofBall (ball : Ball) (shift : Canonical) :
    (BallData.ofBall ball).translate shift = BallData.ofBall (ball.sub (Ball.point shift)) := by
  apply BallData.ext
  · exact Gaussian.Basic.sub_eq_add_neg _ _
  · rfl

/-- Numerical scaling agrees with reading back certified multiplication by the exact scalar ball.

The certified scalar ball has zero radius. Scalar zero identities and the
reduced quadrance readback identify both retained numerical fields. -/
public theorem scale_ofBall (factor : Canonical) (ball : Ball) :
    (BallData.ofBall ball).scale factor = BallData.ofBall ((Ball.point factor).mul ball) := by
  apply BallData.ext
  · rfl
  · change 4 * (Comparison.normSqFromReduced factor * ball.radiusSq) =
      4 * (0 * Data.Gaussian.Norm.Basic.normSq ball.center +
        Data.Gaussian.Norm.Basic.normSq factor * ball.radiusSq) +
        2 * (0 * ball.radiusSq)
    rewrite [Comparison.normSqFromReduced_eq,
      Fraction.Field.zero_mul_direct, Fraction.Field.zero_mul_direct,
      Fraction.zero_add, Fraction.Field.mul_zero_direct, add_zero]
    exact Eq.refl _

/-- With the original ball's apartness certificate, numerical division agrees with certified division of the exact
numerator ball.

The denominator uses the same retained apartness lower quadrance. The
zero-radius numerator leaves exactly the original quotient-radius expression. -/
public theorem divide_ofBall (numerator : Canonical) (ball : Ball)
    (apart : Apart ball) :
    (BallData.ofBall ball).divide numerator apart.lowerSq =
      BallData.ofBall ((Ball.point numerator).div ball apart) := by
  apply BallData.ext
  · rfl
  · change
      (2 * (Comparison.normSqFromReduced numerator * ball.radiusSq)) /
          (apart.lowerSq * Comparison.normSqFromReduced ball.center) =
        (2 * (0 * Data.Gaussian.Norm.Basic.normSq ball.center +
          Data.Gaussian.Norm.Basic.normSq numerator * ball.radiusSq)) /
          (apart.lowerSq * Data.Gaussian.Norm.Basic.normSq ball.center)
    rewrite [Comparison.normSqFromReduced_eq, Comparison.normSqFromReduced_eq,
      Fraction.Field.zero_mul_direct, Fraction.zero_add]
    exact Eq.refl _

end BallData

end Purelib.Approximation.Gaussian.Enclosure.Ball.Data
