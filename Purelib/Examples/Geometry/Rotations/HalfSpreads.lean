module

import Purelib.Algebra.Field.Inverse
import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Geometry.Rotations.Reflection
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Examples.Geometry.Rotations.Reflections
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Cast
public import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

@[expose] public section

/-!
# Rational rotations, section 6: half spreads

Half spread and spread are stored as executable field expressions.  For the
paper's auxiliary perpendicular direction, this module computes one of three
fixed coordinate candidates and caches both its perpendicularity and
non-nullness certificates.  No basis choice or representation theorem is
used.
-/

namespace Purelib.Examples.Geometry.Rotations.HalfSpreads

open Purelib.Examples

open Purelib.Examples.Geometry.Rotations.Reflections
open Purelib.Data.Rat.Fraction (Rational)

variable {K : Type*} [ExplicitField K]
namespace ExampleThirtyThree

/-- The two retained reflection vectors have dot product one. -/
theorem dot_value :
    Vector3.dot ExampleTwenty.first ExampleTwenty.second =
      (1 : Fraction.Rational) := by
  unfold ExampleTwenty.first ExampleTwenty.second
    Vector3.dot
  ring1

/-- The two retained reflection vectors have spread `83/84`. -/
theorem spread_value :
    Vector3.spread ExampleTwenty.first
      ExampleTwenty.second
        ExampleTwenty.first_nonNull
          ExampleTwenty.second_nonNull =
      (83 : Fraction.Rational) / 84 := by
  unfold Vector3.spread
  rw [dot_value,
    ExampleTwenty.first_quadrance,
    ExampleTwenty.second_quadrance]
  exact Purelib.Algebra.Field.Inverse.one_sub_div_fourteen_six
    (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 84) (by decide) : (84 :
      Rational) ≠ 0)

/-- Their reflection-product rotation has half spread `83/84`. -/
theorem product_halfSpread :
    Rotations.Spread.halfSpread
        (Rotations.Reflection.reflectionProductRotation ExampleTwenty.first
          ExampleTwenty.second
          ExampleTwenty.first_nonNull
            ExampleTwenty.second_nonNull) =
      (83 : Fraction.Rational) / 84 := by
  rw [Rotations.Spread.halfSpread_reflectionProduct _ _ _ _
    (Purelib.Data.Rat.Fraction.Order.Cast.rational_natCast_nonzero (value := 2) (by decide) : (2 :
      Rational) ≠ 0)]
  exact spread_value

/-- The displayed reflection-product matrix has trace `-20/21`. -/
theorem product_trace :
    Coordinates3.Matrix3.trace
        (Coordinates3.Matrix3.mul
          (Rotations.Reflection.reflection ExampleTwenty.first
            ExampleTwenty.first_nonNull)
          (Rotations.Reflection.reflection ExampleTwenty.second
            ExampleTwenty.second_nonNull)) =
      (-20 : Fraction.Rational) / 21 := by
  rw [ExampleTwenty.product_displayed]
  decide

end ExampleThirtyThree

end Purelib.Examples.Geometry.Rotations.HalfSpreads

end
