module
import Purelib.Algebra.NatCast
public import Purelib.Geometry.Conics.Parabola.Basic
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Finite.Eleven
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Addition
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Physics.Mechanics.Discrete.Planar
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Divine Proportions, Chapter 23: physics applications

The calculus passages in the source are retained through their finite
polynomial stationarity equations.  Extremum conclusions are separated from
those equations, so no completed real line, limit, or general derivative
operator enters the formalization.
-/

namespace formalisations.DivineProportions.Chapters.Applications

namespace PhysicsApplications

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The quadratic vertical-position expression five times time squared minus twice time. -/
def trajectoryPositionY (time : K) : K :=
  5 * time ^ 2 - 2 * time

/-- The affine vertical-velocity expression three minus time. -/
def trajectoryVelocityY (time : K) : K := 3 - time

/-- The position increment agrees with the velocity up to eleven times the current time. -/
private theorem trajectory_step_y_identity (time : K) :
    trajectoryPositionY time + trajectoryVelocityY time =
      trajectoryPositionY (time + 1) - 11 * time := by
  unfold trajectoryPositionY trajectoryVelocityY
  ring1

/-- Substitution of the quadratic trajectory leaves eleven times the squared horizontal coordinate. -/
private theorem trajectory_curve_identity (x : K) :
    x ^ 2 + 4 * x + 2 * trajectoryPositionY x = 11 * x ^ 2 := by
  unfold trajectoryPositionY
  ring1

/-- Isolate twice the vertical coordinate in the trajectory polynomial. -/
private theorem isolate_linear_coordinate (x y : K) :
    2 * y = (x ^ 2 + 4 * x + 2 * y) - (x ^ 2 + 4 * x) := by
  ring1

/-- Express the trajectory's linear-coordinate solution up to the eleven-times-square term. -/
private theorem trajectory_y_identity (x : K) :
    -(x ^ 2 + 4 * x) =
      trajectoryPositionY x * 2 - 11 * x ^ 2 := by
  unfold trajectoryPositionY
  ring1

open Purelib.Geometry.Plane.Point in
open Purelib.Physics.Mechanics.Discrete in
/-- Iterate the discrete planar particle step from the fixed initial position and velocity.

The supplied acceleration is retained unchanged at each finite natural time. -/
def particleStateAt (acceleration : Purelib.Geometry.Plane.Point K) : Nat → Planar.ParticleState K
  | 0 => ⟨⟨0, 0⟩, ⟨1, 3⟩⟩
  | time + 1 => Planar.particleStep acceleration (particleStateAt acceleration time)

open Purelib.Geometry.Plane.Point in
/-- The planar acceleration with zero horizontal and minus-one vertical component. -/
def constantGravityAcceleration : Purelib.Geometry.Plane.Point K := ⟨0, -1⟩

open Purelib.Physics.Mechanics.Discrete in
/-- The polynomial position and affine velocity at the supplied field-valued time. -/
def algebraicDynamicsClosedForm (time : K) : Planar.ParticleState K :=
  ⟨⟨time, trajectoryPositionY time⟩,
    ⟨1, trajectoryVelocityY time⟩⟩

open Purelib.Geometry.Plane.Point in
open Purelib.Geometry.Plane.Point.Basic in
open Purelib.Physics.Mechanics.Discrete in
open Purelib.Physics.Mechanics.Discrete.Planar in
/-- The displayed closed form obeys one constant-gravity step when eleven vanishes.

The characteristic condition cancels the exact discrepancy in the vertical position recurrence. -/
theorem algebraicDynamicsClosedForm_step
    (time : K) (elevenZero : (11 : K) = 0) :
    Planar.particleStep (constantGravityAcceleration (K := K))
        (algebraicDynamicsClosedForm time) =
      algebraicDynamicsClosedForm (time + 1) := by
  apply ParticleState.ext
  · apply Purelib.Geometry.Plane.Point.ext
    · unfold Planar.particleStep algebraicDynamicsClosedForm Addition.pointAdd
      ring1
    · unfold Planar.particleStep algebraicDynamicsClosedForm Addition.pointAdd
      calc
        trajectoryPositionY time + trajectoryVelocityY time =
            trajectoryPositionY (time + 1) - 11 * time :=
          trajectory_step_y_identity time
        _ = trajectoryPositionY (time + 1) := by rw [elevenZero]; ring1
  · apply Purelib.Geometry.Plane.Point.ext
    · unfold Planar.particleStep algebraicDynamicsClosedForm
        constantGravityAcceleration Addition.pointAdd
      ring1
    · unfold Planar.particleStep algebraicDynamicsClosedForm
        constantGravityAcceleration Addition.pointAdd trajectoryVelocityY
      ring1

open Purelib.Geometry.Plane.Point in
/-- The conic equation x squared plus four x plus twice y. -/
def trajectoryEquation (point : Purelib.Geometry.Plane.Point K) : K :=
  point.x ^ 2 + 4 * point.x + 2 * point.y

open Purelib.Algebra.Field in
open Purelib.Geometry.Plane.Point in
/-- The trajectory equation determines its displayed vertical coordinate when eleven vanishes and two is nonzero. -/
theorem trajectory_y_unique
    (x y : K) (elevenZero : (11 : K) = 0)
    (twoNonzero : (2 : K) ≠ 0)
    (onCurve : trajectoryEquation (⟨x, y⟩ : Purelib.Geometry.Plane.Point K) = 0) :
    y = trajectoryPositionY x := by
  apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
  calc
    y * 2 = 2 * y := by ring1
    _ = (x ^ 2 + 4 * x + 2 * y) - (x ^ 2 + 4 * x) :=
      isolate_linear_coordinate x y
    _ = -(x ^ 2 + 4 * x) := by
      unfold trajectoryEquation at onCurve
      rw [onCurve]
      ring1
    _ = trajectoryPositionY x * 2 - 11 * x ^ 2 :=
      trajectory_y_identity x
    _ = trajectoryPositionY x * 2 := by rw [elevenZero]; ring1

open Purelib.Curves.Plane in
/-- The nondegenerate-coefficient conic representation of the trajectory equation. -/
def trajectoryConic [Nontrivial K] : Conic K where
  d := 1
  e := 0
  f := 0
  a := 4
  b := 2
  c := 0
  quadratic_nonzero := Or.inl one_ne_zero

open Purelib.Curves.Plane in
open Purelib.Geometry.Plane.Point in
/-- The trajectory conic evaluates to the displayed trajectory polynomial. -/
theorem trajectoryConic_evaluate [Nontrivial K] (point : Purelib.Geometry.Plane.Point K) :
    (trajectoryConic (K := K)).evaluate point = trajectoryEquation point := by
  unfold Conic.evaluate trajectoryConic trajectoryEquation
  ring1

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
/-- The fixed constant-gravity acceleration over the executable field of eleven elements. -/
def fieldElevenAcceleration : Purelib.Geometry.Plane.Point Eleven.Element :=
  constantGravityAcceleration (K := Eleven.Element)

section
open Purelib.Algebra.Field.Finite
open Purelib.Physics.Mechanics.Discrete
/-- The actual finite particle recurrence over the field of eleven elements. -/
def fieldElevenStateAt (time : Nat) : Planar.ParticleState Eleven.Element :=
  particleStateAt fieldElevenAcceleration time

/-- The displayed closed form at a natural time cast into the field of eleven elements. -/
def fieldElevenClosedForm (time : Nat) : Planar.ParticleState Eleven.Element :=
  algebraicDynamicsClosedForm (time : Eleven.Element)

/-- The field-eleven closed form obeys the exact discrete particle step. -/
theorem fieldElevenClosedForm_step (time : Nat) :
    Planar.particleStep fieldElevenAcceleration (fieldElevenClosedForm time) =
      fieldElevenClosedForm (time + 1) := by
  have castSuccessor :
      ((time + 1 : Nat) : Eleven.Element) = (time : Eleven.Element) + 1 := by
    exact Nat.cast_succ time
  unfold fieldElevenAcceleration fieldElevenClosedForm
  rw [castSuccessor]
  exact algebraicDynamicsClosedForm_step
    (time : Eleven.Element) Eleven.eleven_eq_zero

end

open Purelib.Physics.Mechanics.Discrete in
/-- Every finite particle state equals the displayed field-eleven closed form.

Induction follows the actual recurrence from its fixed initial state. -/
theorem fieldElevenStateAt_formula (time : Nat) :
    fieldElevenStateAt time = fieldElevenClosedForm time := by
  induction time with
  | zero => decide
  | succ time inductionHypothesis =>
      change Planar.particleStep fieldElevenAcceleration (fieldElevenStateAt time) =
        fieldElevenClosedForm (time + 1)
      rw [inductionHypothesis]
      exact fieldElevenClosedForm_step time

open Purelib.Algebra.Field.Finite in
open Purelib.Algebra in
/-- The actual field-eleven particle recurrence repeats after eleven steps. -/
theorem fieldElevenStateAt_period (time : Nat) :
    fieldElevenStateAt (time + 11) = fieldElevenStateAt time := by
  rw [fieldElevenStateAt_formula, fieldElevenStateAt_formula]
  have castPeriod :
      ((time + 11 : Nat) : Eleven.Element) = (time : Eleven.Element) := by
    calc
      ((time + 11 : Nat) : Eleven.Element) =
          (time : Eleven.Element) + (11 : Eleven.Element) := by
            rw [NatCast.add]
            congr 1
      _ = (time : Eleven.Element) + 0 := by rw [Eleven.eleven_eq_zero]
      _ = (time : Eleven.Element) := add_zero _
  unfold fieldElevenClosedForm
  rw [castPeriod]

open Purelib.Algebra.Field.Finite in
open Purelib.Physics.Mechanics.Discrete in
/-- The twelve displayed particle states, including the repeated initial state. -/
def fieldElevenDisplayedStates : List (Planar.ParticleState Eleven.Element) :=
  [ ⟨⟨0, 0⟩, ⟨1, 3⟩⟩, ⟨⟨1, 3⟩, ⟨1, 2⟩⟩,
    ⟨⟨2, 5⟩, ⟨1, 1⟩⟩, ⟨⟨3, 6⟩, ⟨1, 0⟩⟩,
    ⟨⟨4, 6⟩, ⟨1, 10⟩⟩, ⟨⟨5, 5⟩, ⟨1, 9⟩⟩,
    ⟨⟨6, 3⟩, ⟨1, 8⟩⟩, ⟨⟨7, 0⟩, ⟨1, 7⟩⟩,
    ⟨⟨8, 7⟩, ⟨1, 6⟩⟩, ⟨⟨9, 2⟩, ⟨1, 5⟩⟩,
    ⟨⟨10, 7⟩, ⟨1, 4⟩⟩, ⟨⟨0, 0⟩, ⟨1, 3⟩⟩ ]

/-- The first twelve actual particle states equal the complete displayed table. -/
theorem example_23_1_table :
    (List.range 12).map fieldElevenStateAt = fieldElevenDisplayedStates := by
  decide

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Plane.Point
/-- The trajectory point at a natural time viewed as a field-eleven residue. -/
def fieldElevenTrajectoryPoint (time : Nat) : Purelib.Geometry.Plane.Point Eleven.Element :=
  ⟨time, trajectoryPositionY (time : Eleven.Element)⟩

/-- The exact trajectory conic equation over the field of eleven elements. -/
def fieldElevenTrajectoryEquation (point : Purelib.Geometry.Plane.Point Eleven.Element) : Eleven.Element :=
  trajectoryEquation point

/-- Every displayed field-eleven trajectory point satisfies the trajectory equation. -/
theorem fieldElevenTrajectoryPoint_on_curve (time : Nat) :
    fieldElevenTrajectoryEquation (fieldElevenTrajectoryPoint time) = 0 := by
  have elevenZero : (11 : Eleven.Element) = 0 := Eleven.eleven_eq_zero
  change trajectoryEquation
    (⟨(time : Eleven.Element), trajectoryPositionY (time : Eleven.Element)⟩ :
      Purelib.Geometry.Plane.Point Eleven.Element) = 0
  unfold trajectoryEquation
  calc
    (time : Eleven.Element) ^ 2 + 4 * (time : Eleven.Element) +
        2 * trajectoryPositionY (time : Eleven.Element) =
      11 * (time : Eleven.Element) ^ 2 :=
        trajectory_curve_identity (time : Eleven.Element)
    _ = 0 := by rw [elevenZero]; exact zero_mul _

/-- For each field-eleven horizontal coordinate, the trajectory has the displayed unique vertical coordinate. -/
theorem fieldElevenTrajectory_y_unique (x y : Eleven.Element)
    (onCurve : trajectoryEquation (⟨x, y⟩ : Purelib.Geometry.Plane.Point Eleven.Element) = 0) :
    y = trajectoryPositionY x :=
  trajectory_y_unique x y Eleven.eleven_eq_zero (by decide) onCurve

/-- At each supplied natural residue label, the curve equation is equivalent to the displayed vertical coordinate. -/
theorem fieldElevenTrajectory_chart (time : Nat) (y : Eleven.Element) :
    trajectoryEquation (⟨(time : Eleven.Element), y⟩ : Purelib.Geometry.Plane.Point Eleven.Element) = 0 ↔
      y = trajectoryPositionY (time : Eleven.Element) := by
  constructor
  · exact fieldElevenTrajectory_y_unique (time : Eleven.Element) y
  · intro yValue
    rw [yValue]
    have onCurve := fieldElevenTrajectoryPoint_on_curve time
    exact onCurve

end

open Purelib.Algebra.Field.Finite in
open Purelib.Curves.Plane in
/-- The trajectory conic over the field of eleven elements. -/
def fieldElevenTrajectoryConic : Conic Eleven.Element :=
  trajectoryConic (K := Eleven.Element)

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
/-- The field-eleven focus with coordinates nine and seven. -/
def fieldElevenTrajectoryFocus : Purelib.Geometry.Plane.Point Eleven.Element := ⟨9, 7⟩

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Line in
/-- The field-eleven directrix with homogeneous coefficients zero, one and three. -/
def fieldElevenTrajectoryDirectrix : Purelib.Geometry.Plane.Line Eleven.Element :=
  ⟨0, 1, 3, Or.inr (by decide)⟩

open Purelib.Geometry.Plane.Line.Basic in
/-- The retained focus and directrix present the exact field-eleven trajectory conic.

The certificate supplies a nonnull directrix, a focus off that line and all six conic coefficient equations. -/
theorem example_23_1_parabola :
    fieldElevenTrajectoryConic.IsParabolaPresentation
      fieldElevenTrajectoryFocus fieldElevenTrajectoryDirectrix := by
  refine ⟨
    { directrixNonNull := by
        unfold fieldElevenTrajectoryDirectrix Purelib.Geometry.Plane.Line.IsNull
        decide
      focusNotOnDirectrix := by
        unfold fieldElevenTrajectoryDirectrix fieldElevenTrajectoryFocus
          Purelib.Geometry.Plane.Line.Contains
        decide
      scale := 1
      scaleNonzero := by decide
      dEquation := by decide
      eEquation := by decide
      fEquation := by decide
      aEquation := by decide
      bEquation := by decide
      cEquation := by decide }⟩

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Plane.Point in
/-- Evaluating the field-eleven conic gives the exact trajectory equation. -/
theorem fieldElevenTrajectoryConic_evaluate (point : Purelib.Geometry.Plane.Point Eleven.Element) :
    fieldElevenTrajectoryConic.evaluate point =
      fieldElevenTrajectoryEquation point := by
  exact trajectoryConic_evaluate point

/-- The point with coordinates nine and two lies on the field-eleven trajectory conic. -/
theorem example_23_1_vertex :
    fieldElevenTrajectoryConic.evaluate ⟨9, 2⟩ = 0 := by
  decide
end PhysicsApplications
end formalisations.DivineProportions.Chapters.Applications

end
