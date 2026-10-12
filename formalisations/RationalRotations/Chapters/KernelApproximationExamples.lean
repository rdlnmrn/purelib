module
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Examples.Geometry.Rotations.QuaternionObstruction
public import Purelib.Geometry.Rotations.Rational.Kernel.Approximation

import Purelib.Algebra.Quaternion.Projective.Basic
public import formalisations.RationalRotations.Chapters.IntroductoryExample
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib

open Purelib.Data.Rat

@[expose] public section

/-!
# Finite kernel-approximation regression requests

These named values exercise the arbitrary-precision constructor on the five
chart shapes called for by the finite density plan.  Each target is requested
at squared radii `1/10` and `1/100`; the returned records themselves retain
the exact error proofs.
-/

namespace formalisations.RationalRotations.Chapters

namespace KernelApproximationExamples

/-- The canonical constructive rational coefficient type for the approximation requests. -/
abbrev Scalar := Fraction.Rational

/-- The identity target, displayed through the projective identity
representative. -/
def identitySource : Algebra.Quaternion.Projective.Basic.NonNullProportion Scalar :=
  Algebra.Quaternion.Projective.Basic.NonNullProportion.identity
    Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.quarterTurn

/-- A coordinate half-turn target. -/
def halfTurnSource : Algebra.Quaternion.Projective.Basic.NonNullProportion Scalar where
  scalar := 0
  vector := Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.axis
  normNonzero := by
    change (1 : Scalar) ≠ 0
    decide

/-- The generic all-nonzero target `(2:1:2:3)` from the introduction. -/
def genericSource : Algebra.Quaternion.Projective.Basic.NonNullProportion Scalar := IntroductoryExample.proportion

/-- A certified unit-kernel approximation of the identity with squared error radius 1/10. -/
def identityTenth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation identitySource)
    ((1 : Scalar) / 10) (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the identity with squared error radius 1/100. -/
def identityHundredth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation identitySource)
    ((1 : Scalar) / 100) (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the coordinate half-turn with squared error radius 1/10. -/
def halfTurnTenth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation halfTurnSource)
    ((1 : Scalar) / 10) (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the coordinate half-turn with squared error radius 1/100. -/
def halfTurnHundredth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation halfTurnSource)
    ((1 : Scalar) / 100) (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the quarter-turn with squared error radius 1/10. -/
def quarterTurnTenth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation
      Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.quarterTurn) ((1 : Scalar) / 10)
      (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the quarter-turn with squared error radius 1/100. -/
def quarterTurnHundredth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation
      Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.quarterTurn) ((1 : Scalar) / 100)
      (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the three-four-five rotation with squared error radius 1/10. -/
def threeFourFiveTenth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation
      Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.threeFourFive) ((1 : Scalar) / 10)
      (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the three-four-five rotation with squared error radius 1/100. -/
def threeFourFiveHundredth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation
      Examples.Geometry.Rotations.QuaternionObstruction.ExampleSixtyFour.threeFourFive) ((1 : Scalar) / 100)
      (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the rotation (2:1:2:3) with squared error radius 1/10. -/
def genericTenth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation genericSource)
    ((1 : Scalar) / 10) (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A certified unit-kernel approximation of the rotation (2:1:2:3) with squared error radius 1/100. -/
def genericHundredth :=
  Geometry.Rotations.Rational.Kernel.Approximation.KernelApproximation.kernelApproximation
    (Geometry.Rotations.Projective.Action.NonNullProportion.rotation genericSource)
    ((1 : Scalar) / 100) (Fraction.Order.Field.div_pos_direct (by decide)
      (Fraction.Cast.Order.natCast_pos_direct (by decide)))

/-- A small concrete computation guard for the finite refinement and the
base-four square-root bracket. -/
theorem quarterTurnTenth_scale : quarterTurnTenth.scale = 980 := by decide

end KernelApproximationExamples

end formalisations.RationalRotations.Chapters
