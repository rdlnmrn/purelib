module

import Purelib.Data.Rat.Fraction.Order.Cast
import Purelib.Algebra.Quaternion.Projective.SquareClass
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Algebra.Quaternion.Projective.Basic
public import Purelib.Algebra.Quaternion.Projective.UnitObstruction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Geometry.Rotations.Projective.Action
import Purelib.Geometry.Rotations.Spread
import Purelib.LinearAlgebra.Coordinates3.Vector
import Purelib.NumberTheory.SquareClass.Rational.Nonsquare
import Purelib.LinearAlgebra.Coordinates3.Matrix
import Mathlib.Algebra.Ring.Defs
import Purelib.Algebra.Field.SquareClass.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

open Purelib.Algebra.Field

open Purelib

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.Coordinates3 renaming Vector -> Vector3

section
@[expose] public section

/-!
# Rational rotations, Corollary 63 and Example 64

The finite obstruction is the existence of a norm-one representative in a
projective class.  The claims that the rational image or its index is
infinite are not used here; the two displayed nonsquare obstructions are
proved from canonical reduced fractions.
-/

namespace Purelib.Examples.Geometry.Rotations.QuaternionObstruction

open Purelib.Examples

open Purelib.Data.Rat.Fraction.Order.Cast (rational_natCast_nonzero)

open Purelib.Algebra.Quaternion.Projective
open Purelib.Data.Rat.Fraction (Rational)

open Purelib.Rotations

variable {K : Type*} [ExplicitField K]

namespace ExampleSixtyFour

/-- The rational coordinate axis (1,0,0). -/
def axis : Vector3 Fraction.Rational
  := ⟨1, 0, 0⟩

/-- The nonnull projective quaternion representative (1:1:0:0). -/
def quarterTurn :
  Basic.NonNullProportion Fraction.Rational where
  scalar := 1
  vector := axis
  normNonzero := by
    change (2 : Fraction.Rational) ≠ 0
    exact (fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero
      (value := value) nonzero : (value : Rational) ≠ 0)) (by decide)

/-- The displayed rational quarter-turn matrix with rows (1,0,0), (0,0,1), (0,-1,0). -/
def quarterTurnDisplayed :
  Coordinates3.Matrix3 Fraction.Rational :=
  ⟨1, 0, 0, 0, 0, 1, 0, -1, 0⟩

section
/-- The retained quarterTurn representative has norm 2. -/
theorem quarterTurn_norm :
  quarterTurn.toProportion.norm = 2 := by
  unfold quarterTurn
    axis Basic.Proportion.norm
    Vector3.quadrance Vector3.dot
  ring1

/-- The rotation of the retained quarterTurn representative equals its displayed matrix. -/
theorem quarterTurn_matrix :
  (Rotations.Projective.Action.NonNullProportion.rotationMatrix
  quarterTurn) =
    quarterTurnDisplayed := by
  decide

/-- The displayed quarter-turn matrix sends coordinates (t,r,s) to (t,-s,r). -/
theorem quarterTurn_action (vector :
  Vector3 Fraction.Rational) :
    Coordinates3.Matrix3.rowMul vector quarterTurnDisplayed =
      ⟨vector.t, -vector.s, vector.r⟩ := by
  apply Vector3.ext <;> unfold quarterTurnDisplayed
    Coordinates3.Matrix3.rowMul <;> ring1

/-- The retained quarterTurn rotation has half-spread one half. -/
theorem quarterTurn_halfSpread :
    Rotations.Spread.halfSpread (Rotations.Projective.Action.NonNullProportion.rotation
      quarterTurn) = (1 : Fraction.Rational) / 2 := by
  rw [Rotations.Projective.Action.NonNullProportion.halfSpread_rotation
    quarterTurn
      ((fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero (value
        := value) nonzero : (value : Rational) ≠ 0)) (by decide))]
  change axis.quadrance /
    quarterTurn.toProportion.norm = (1 : Fraction.Rational) /
    2
  rw [quarterTurn_norm]
  rw [show axis.quadrance = (1 : Fraction.Rational) by
    unfold axis Vector3.quadrance Vector3.dot
    ring1]

/-- The retained quadrance square class is represented by 2. -/
theorem quarterTurn_class :
  (SquareClass.NonNullProportion.quadranceClass
  quarterTurn).value = 2 :=
  quarterTurn_norm

/-- The quadrance class represented by 2 is not the unit rational square class. -/
theorem quarterTurn_class_nontrivial :
    ¬ (SquareClass.NonNullProportion.quadranceClass
      quarterTurn).Equivalent
      (UnitObstruction.NonNullProportion.unitSquareClass
      quarterTurn) := open Purelib.NumberTheory in by
  rintro ⟨factor, _, unitValue⟩
  change (1 : Fraction.Rational) = factor ^ 2 * 2 at unitValue
  apply SquareClass.Rational.Nonsquare.square_ne_two (2 * factor)
  calc
    (2 * factor) ^ 2 = 2 * (factor ^ 2 * 2) := by ring1
    _ = 2 := by rw [← unitValue]; ring1

/-- The retained quarterTurn projective class has no rational norm-one quaternion representative. -/
theorem quarterTurn_no_unit_quaternion
  :
    ¬ (UnitObstruction.NonNullProportion.QuaternionObstruction.HasUnitRepresentative
      quarterTurn) := by
  intro unitRepresentative
  apply quarterTurn_class_nontrivial
  exact
    (UnitObstruction.NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial
    quarterTurn).mp unitRepresentative

/-- The paper's `3-4-5` rotation representative `(2:1:0:0)`. -/
def threeFourFive :
  Basic.NonNullProportion Fraction.Rational where
  scalar := 2
  vector := axis
  normNonzero := by
    change (5 : Fraction.Rational) ≠ 0
    exact (fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero
      (value := value) nonzero : (value : Rational) ≠ 0)) (by decide)

end

/-- The displayed rotation matrix fixing the first axis, with transverse cosine 3/5 and sine 4/5. -/
def threeFourFiveDisplayed :
  Coordinates3.Matrix3 Fraction.Rational :=
  ⟨1, 0, 0,
    0, (3 : Fraction.Rational) / 5, 4 / 5,
    0, -4 / 5, 3 / 5⟩

/-- The retained threeFourFive representative has norm 5. -/
theorem threeFourFive_norm :
  threeFourFive.toProportion.norm = 5 := by
  unfold threeFourFive
    axis Basic.Proportion.norm
    Vector3.quadrance Vector3.dot
  ring1

/-- The rotation of the retained threeFourFive representative equals its displayed matrix. -/
theorem threeFourFive_matrix :
  (Rotations.Projective.Action.NonNullProportion.rotationMatrix
  threeFourFive) =
    threeFourFiveDisplayed := by
  decide

/-- The retained threeFourFive rotation has half-spread one fifth. -/
theorem threeFourFive_halfSpread :
    Rotations.Spread.halfSpread (Rotations.Projective.Action.NonNullProportion.rotation
      threeFourFive) = (1 : Fraction.Rational) / 5 := by
  rw [Rotations.Projective.Action.NonNullProportion.halfSpread_rotation
    threeFourFive
      ((fun {value : Nat} (nonzero : value ≠ 0) => (rational_natCast_nonzero (value
        := value) nonzero : (value : Rational) ≠ 0)) (by decide))]
  change axis.quadrance /
    threeFourFive.toProportion.norm = (1 : Fraction.Rational)
    / 5
  rw [threeFourFive_norm]
  rw [show axis.quadrance = (1 : Fraction.Rational) by
    unfold axis Vector3.quadrance Vector3.dot
    ring1]

/-- The retained quadrance square class is represented by 5. -/
theorem threeFourFive_class :
  (SquareClass.NonNullProportion.quadranceClass
  threeFourFive).value = 5 :=
  threeFourFive_norm

/-- The quadrance class represented by 5 is not the unit rational square class. -/
theorem threeFourFive_class_nontrivial
  :
    ¬ (SquareClass.NonNullProportion.quadranceClass
      threeFourFive).Equivalent
      (UnitObstruction.NonNullProportion.unitSquareClass
        threeFourFive) := open Purelib.NumberTheory in by
  rintro ⟨factor, _, unitValue⟩
  change (1 : Fraction.Rational) = factor ^ 2 * 5 at unitValue
  apply SquareClass.Rational.Nonsquare.square_ne_five (5 * factor)
  calc
    (5 * factor) ^ 2 = 5 * (factor ^ 2 * 5) := by ring1
    _ = 5 := by rw [← unitValue]; ring1

/-- The retained threeFourFive projective class has no rational norm-one quaternion representative. -/
theorem
  threeFourFive_no_unit_quaternion :
    ¬ (UnitObstruction.NonNullProportion.QuaternionObstruction.HasUnitRepresentative
      threeFourFive) := by
  intro unitRepresentative
  apply threeFourFive_class_nontrivial
  exact
    (UnitObstruction.NonNullProportion.hasUnitRepresentative_iff_quadranceClass_trivial
    threeFourFive).mp unitRepresentative

end ExampleSixtyFour

end Purelib.Examples.Geometry.Rotations.QuaternionObstruction

end
