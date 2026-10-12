module
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Coordinates3.Vector

public import Purelib.Geometry.Rotations.Reflection
import Purelib.Data.Rat.Fraction.Compatibility
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Field

open Purelib.Algebra.Field

open Purelib.Data.Rat

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

@[expose] public section

namespace Purelib.Examples.Geometry.Rotations.Reflections

open Purelib.LinearAlgebra.Coordinates3
open Purelib.Geometry.Rotations.Reflection

variable {K : Type*} [ExplicitField K]

namespace ExampleTwenty

/-- The first rational reflection normal (1,2,3). -/
def first : Vector Fraction.Rational := ⟨1, 2, 3⟩

/-- The second rational reflection normal (2,1,-1). -/
def second : Vector Fraction.Rational := ⟨2, 1, -1⟩

/-- The first reflection normal has quadrance 14. -/
theorem first_quadrance : first.quadrance = 14 := by decide

/-- The second reflection normal has quadrance six. -/
theorem second_quadrance : second.quadrance = 6 := by decide

/-- The first rational reflection normal has nonzero quadrance. -/
theorem first_nonNull : first.quadrance ≠ 0 := by decide

/-- The second rational reflection normal has nonzero quadrance. -/
theorem second_nonNull : second.quadrance ≠ 0 := by decide

/-- The explicit first reflection matrix with denominator seven. -/
def firstDisplayed : Matrix3 Fraction.Rational :=
  Matrix3.scale (1 / 7) ⟨6, -2, -3, -2, 3, -6, -3, -6, -2⟩

/-- The explicit second reflection matrix with denominator three. -/
def secondDisplayed : Matrix3 Fraction.Rational :=
  Matrix3.scale (1 / 3) ⟨-1, -2, 2, -2, 2, 1, 2, 1, 2⟩

/-- The displayed product of the two rational reflection matrices, with denominator 21. -/
def productDisplayed : Matrix3 Fraction.Rational :=
  Matrix3.scale (1 / 21) ⟨-8, -19, 4, -16, 4, -13, 11, -8, -16⟩

/-- The cross-product axis (-5,7,-3) of the two reflection normals. -/
def axis : Vector Fraction.Rational := ⟨-5, 7, -3⟩

/-- The first reflection equals its displayed rational matrix. -/
theorem first_reflection_displayed :
    reflection first first_nonNull = firstDisplayed := by decide

/-- The second reflection equals its displayed rational matrix. -/
theorem second_reflection_displayed :
    reflection second second_nonNull = secondDisplayed := by decide

/-- The product of the two reflections equals the displayed denominator-21 matrix. -/
theorem product_displayed :
    Matrix3.mul (reflection first first_nonNull)
        (reflection second second_nonNull) = productDisplayed := by decide

/-- The cross product of the two retained reflection normals is the displayed axis. -/
theorem cross_displayed : Vector3.cross first second = axis := by decide

/-- The displayed product of reflections fixes their retained cross-product axis. -/
theorem axis_fixed : Matrix3.rowMul axis productDisplayed = axis := by decide

end ExampleTwenty

end Purelib.Examples.Geometry.Rotations.Reflections
