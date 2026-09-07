import DivineProportions.Conics.Parabola
import DivineProportions.Trigonometry.Quadrea
import mathlib.RFAP.ConstructiveFraction

/-!
# Divine Proportions, Chapter 23: physics applications

The calculus passages in the source are retained through their finite
polynomial stationarity equations.  Extremum conclusions are separated from
those equations, so no completed real line, limit, or general derivative
operator enters the formalization.
-/

namespace DivineProportions
namespace PhysicsApplications

variable {K : Type*} [RFAP.ExplicitField K]

private theorem eq_of_mul_eq_mul_right
    {left right factor : K} (factorNonzero : factor ≠ 0)
    (productsEqual : left * factor = right * factor) : left = right := by
  have factorCancel : factor * factor⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    left = left * 1 := by rw [mul_one]
    _ = left * (factor * factor⁻¹) := by rw [factorCancel]
    _ = (left * factor) * factor⁻¹ := by ring1
    _ = (right * factor) * factor⁻¹ := by rw [productsEqual]
    _ = right * (factor * factor⁻¹) := by ring1
    _ = right := by rw [factorCancel, mul_one]

private theorem div_eq_div_of_cross_mul
    {leftNumerator rightNumerator leftDenominator rightDenominator : K}
    (leftNonzero : leftDenominator ≠ 0)
    (rightNonzero : rightDenominator ≠ 0)
    (crossProduct :
      leftNumerator * rightDenominator =
        rightNumerator * leftDenominator) :
    leftNumerator / leftDenominator =
      rightNumerator / rightDenominator := by
  have leftCancel : leftDenominator * leftDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel leftDenominator leftNonzero
  have rightCancel : rightDenominator * rightDenominator⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel rightDenominator rightNonzero
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  calc
    leftNumerator * leftDenominator⁻¹ =
        leftNumerator * leftDenominator⁻¹ *
          (rightDenominator * rightDenominator⁻¹) := by
            rw [rightCancel, mul_one]
    _ = (leftNumerator * rightDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by ring1
    _ = (rightNumerator * leftDenominator) *
        (leftDenominator⁻¹ * rightDenominator⁻¹) := by
          rw [crossProduct]
    _ = rightNumerator *
        (leftDenominator * leftDenominator⁻¹) *
          rightDenominator⁻¹ := by ring1
    _ = rightNumerator * rightDenominator⁻¹ := by
      rw [leftCancel, mul_one]

def trajectoryPositionY (time : K) : K :=
  5 * time ^ 2 - 2 * time

def trajectoryVelocityY (time : K) : K := 3 - time

private theorem trajectory_step_y_identity (time : K) :
    trajectoryPositionY time + trajectoryVelocityY time =
      trajectoryPositionY (time + 1) - 11 * time := by
  unfold trajectoryPositionY trajectoryVelocityY
  ring1

private theorem trajectory_curve_identity (x : K) :
    x ^ 2 + 4 * x + 2 * trajectoryPositionY x = 11 * x ^ 2 := by
  unfold trajectoryPositionY
  ring1

private theorem isolate_linear_coordinate (x y : K) :
    2 * y = (x ^ 2 + 4 * x + 2 * y) - (x ^ 2 + 4 * x) := by
  ring1

private theorem trajectory_y_identity (x : K) :
    -(x ^ 2 + 4 * x) =
      trajectoryPositionY x * 2 - 11 * x ^ 2 := by
  unfold trajectoryPositionY
  ring1

/-! ## Problem 14: projectile motion -/

/-- The vertical landing equation with its two finite factors exposed. -/
theorem projectile_landing_factorization (heightVelocity gravity time : K) :
    heightVelocity * time - gravity * time ^ 2 / 2 =
      time * (heightVelocity - gravity * time / 2) := by
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  ring1

/-- Away from the initial instant, a displayed landing-time equation reduces
to `g·t=2b`. -/
theorem projectile_landing_time [DecidableEq K]
    (heightVelocity gravity time : K)
    (timeNonzero : time ≠ 0) (twoNonzero : (2 : K) ≠ 0)
    (landing : heightVelocity * time - gravity * time ^ 2 / 2 = 0) :
    gravity * time = 2 * heightVelocity := by
  have factored :
      time * (heightVelocity - gravity * time / 2) = 0 := by
    rw [← projectile_landing_factorization]
    exact landing
  have secondFactor : heightVelocity - gravity * time / 2 = 0 := by
    by_cases factorZero : heightVelocity - gravity * time / 2 = 0
    · exact factorZero
    · exact False.elim
        ((RFAP.ExplicitField.mul_ne_zero timeNonzero factorZero) factored)
  have halfRelation : gravity * time / 2 = heightVelocity := by
    calc
      gravity * time / 2 =
          heightVelocity - (heightVelocity - gravity * time / 2) := by ring1
      _ = heightVelocity := by rw [secondFactor]; ring1
  calc
    gravity * time = (gravity * time / 2) * 2 :=
      (RFAP.ExplicitField.div_mul_cancel (gravity * time) twoNonzero).symm
    _ = 2 * heightVelocity := by rw [halfRelation]; ring1

/-- The exact horizontal-quadrance equation at the nonzero landing time. -/
theorem projectile_horizontal_quadrance_cleared
    (horizontalVelocity heightVelocity gravity time : K)
    (landingTime : gravity * time = 2 * heightVelocity) :
    gravity ^ 2 * (horizontalVelocity * time) ^ 2 =
      4 * horizontalVelocity ^ 2 * heightVelocity ^ 2 := by
  calc
    gravity ^ 2 * (horizontalVelocity * time) ^ 2 =
        horizontalVelocity ^ 2 * (gravity * time) ^ 2 := by ring1
    _ = 4 * horizontalVelocity ^ 2 * heightVelocity ^ 2 := by
      rw [landingTime]
      ring1

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- The finite maximum-product inequality used in Problem 14. -/
theorem fixed_sum_product_bound (A B V : Rational) (sum : A + B = V) :
    4 * A * B ≤ V ^ 2 := by
  have squareNonnegative : (0 : Rational) ≤ (A - B) ^ 2 :=
    RFAP.ConstructiveFraction.sq_nonneg_direct (A - B)
  have differenceNonnegative :
      (0 : Rational) ≤ V ^ 2 - 4 * A * B := by
    calc
      0 ≤ (A - B) ^ 2 := squareNonnegative
      _ = V ^ 2 - 4 * A * B := by rw [← sum]; ring1
  exact RFAP.ConstructiveFraction.le_of_sub_nonneg_direct
    differenceNonnegative

/-- Equality in the product bound is attained by the equal split. -/
theorem fixed_sum_equal_split (V : K) (twoNonzero : (2 : K) ≠ 0) :
    V / 2 + V / 2 = V ∧
      4 * (V / 2) * (V / 2) = V ^ 2 := by
  have cancel := RFAP.ExplicitField.div_mul_cancel V twoNonzero
  constructor
  · calc
      V / 2 + V / 2 = (V / 2) * 2 := by ring1
      _ = V := cancel
  · have twoInverse : (2 : K) * (2 : K)⁻¹ = 1 :=
      RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
    simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      4 * (V * (2 : K)⁻¹) * (V * (2 : K)⁻¹) =
          V ^ 2 * (2 * (2 : K)⁻¹) ^ 2 := by ring1
      _ = V ^ 2 := by rw [twoInverse]; ring1

/-- Problem 14: the maximizing equal split has spread `A/V=1/2` from the
vertical and cleared maximum horizontal quadrance `g²x²=V²`. -/
theorem problem_14
    (V gravity : K) (VNonzero : V ≠ 0) (gravityNonzero : gravity ≠ 0)
    : (V / 2) / V = 1 / 2 ∧
      gravity ^ 2 * (V ^ 2 / gravity ^ 2) = V ^ 2 := by
  have VCancel : V * V⁻¹ = (1 : K) :=
    RFAP.ExplicitField.mul_inv_cancel V VNonzero
  constructor
  · simp only [RFAP.ExplicitField.div_eq_mul_inv]
    calc
      V * (2 : K)⁻¹ * V⁻¹ =
          (V * V⁻¹) * (2 : K)⁻¹ := by ring1
      _ = 1 * (2 : K)⁻¹ := by rw [VCancel]
      _ = 1 * (2 : K)⁻¹ := rfl
  · have gravitySquareNonzero : gravity ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        RFAP.ExplicitField.mul_ne_zero gravityNonzero gravityNonzero
    calc
      gravity ^ 2 * (V ^ 2 / gravity ^ 2) =
          (V ^ 2 / gravity ^ 2) * gravity ^ 2 := by ring1
      _ = V ^ 2 :=
        RFAP.ExplicitField.div_mul_cancel (V ^ 2) gravitySquareNonzero

/-! ## Problem 15: projectile motion on a hill -/

/-- Eliminate the auxiliary square `c²=(1-r)/r` from the source's Lagrange
equation.  The cancellation is polynomial: no assumption `r≠0` is needed once
the defining relation has been supplied in cleared form. -/
theorem problem_15_lagrange_elimination
    (horizontalSquare totalSquare hillSpread cSquare : K)
    (cSquareRelation : hillSpread * cSquare = 1 - hillSpread)
    (lagrangeEquation :
      4 * horizontalSquare * (totalSquare - horizontalSquare) * cSquare =
        (2 * horizontalSquare - totalSquare) ^ 2) :
    (2 * horizontalSquare - totalSquare) ^ 2 =
      totalSquare ^ 2 * (1 - hillSpread) := by
  have multipliedLagrange :
      hillSpread * (2 * horizontalSquare - totalSquare) ^ 2 =
        4 * horizontalSquare * (totalSquare - horizontalSquare) *
          (1 - hillSpread) := by
    calc
      hillSpread * (2 * horizontalSquare - totalSquare) ^ 2 =
          hillSpread *
            (4 * horizontalSquare *
              (totalSquare - horizontalSquare) * cSquare) := by
                rw [lagrangeEquation]
      _ = 4 * horizontalSquare * (totalSquare - horizontalSquare) *
          (hillSpread * cSquare) := by ring1
      _ = 4 * horizontalSquare * (totalSquare - horizontalSquare) *
          (1 - hillSpread) := by rw [cSquareRelation]
  calc
    (2 * horizontalSquare - totalSquare) ^ 2 =
        hillSpread * (2 * horizontalSquare - totalSquare) ^ 2 +
          (1 - hillSpread) *
            (2 * horizontalSquare - totalSquare) ^ 2 := by ring1
    _ = 4 * horizontalSquare * (totalSquare - horizontalSquare) *
          (1 - hillSpread) +
        (1 - hillSpread) *
          (2 * horizontalSquare - totalSquare) ^ 2 := by
            rw [multipliedLagrange]
    _ = totalSquare ^ 2 * (1 - hillSpread) := by ring1

/-- The Lagrange calculation in Problem 15 after every square-root and
fraction has been cleared. -/
theorem problem_15_stationary_reduction
    (horizontalSquare totalSquare hillSpread : K)
    (twoNonzero : (2 : K) ≠ 0)
    (stationary :
      (2 * horizontalSquare - totalSquare) ^ 2 =
        totalSquare ^ 2 * (1 - hillSpread)) :
    (horizontalSquare - totalSquare / 2) ^ 2 * 4 =
      totalSquare ^ 2 * (1 - hillSpread) := by
  simp only [RFAP.ExplicitField.div_eq_mul_inv]
  have cancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    RFAP.ExplicitField.mul_inv_cancel 2 twoNonzero
  have identity :
      (horizontalSquare - totalSquare * (2 : K)⁻¹) ^ 2 * 4 =
        (2 * horizontalSquare - totalSquare) ^ 2 := by
    calc
      (horizontalSquare - totalSquare * (2 : K)⁻¹) ^ 2 * 4 =
          (2 * (horizontalSquare -
            totalSquare * (2 : K)⁻¹)) ^ 2 := by ring1
      _ = (2 * horizontalSquare -
          totalSquare * (2 * (2 : K)⁻¹)) ^ 2 := by
        ring1
      _ = (2 * horizontalSquare - totalSquare) ^ 2 := by
        rw [cancel]
        ring1
  rw [identity, stationary]

/-- Dividing the horizontal velocity quadrance by the fixed total quadrance
turns the stationary equation into the second spread equation
`r=S₂(s)=4s(1-s)`. -/
theorem problem_15
    (horizontalSquare totalSquare hillSpread launchSpread : K)
    (totalNonzero : totalSquare ≠ 0)
    (horizontalRatio : launchSpread * totalSquare = horizontalSquare)
    (stationary :
      (2 * horizontalSquare - totalSquare) ^ 2 =
        totalSquare ^ 2 * (1 - hillSpread)) :
    hillSpread = 4 * launchSpread * (1 - launchSpread) := by
  have totalSquareNonzero : totalSquare ^ 2 ≠ 0 := by
    simpa only [pow_two] using
      RFAP.ExplicitField.mul_ne_zero totalNonzero totalNonzero
  have scaledEquation :
      totalSquare ^ 2 * (2 * launchSpread - 1) ^ 2 =
        totalSquare ^ 2 * (1 - hillSpread) := by
    calc
      totalSquare ^ 2 * (2 * launchSpread - 1) ^ 2 =
          (2 * horizontalSquare - totalSquare) ^ 2 := by
            rw [← horizontalRatio]
            ring1
      _ = totalSquare ^ 2 * (1 - hillSpread) := stationary
  have rootEquation :
      (2 * launchSpread - 1) ^ 2 = 1 - hillSpread := by
    apply eq_of_mul_eq_mul_right totalSquareNonzero
    calc
      (2 * launchSpread - 1) ^ 2 * totalSquare ^ 2 =
          totalSquare ^ 2 * (2 * launchSpread - 1) ^ 2 := by ring1
      _ = totalSquare ^ 2 * (1 - hillSpread) := scaledEquation
      _ = (1 - hillSpread) * totalSquare ^ 2 := by ring1
  calc
    hillSpread = 1 - (2 * launchSpread - 1) ^ 2 := by
      rw [rootEquation]
      ring1
    _ = 4 * launchSpread * (1 - launchSpread) := by ring1

def downhillLaunchSpread (root : K) : K := (1 - root) / 2
def uphillLaunchSpread (root : K) : K := (1 + root) / 2

/-- The two launch directions in Problem 15, supplied by one finite witness
`root²=1-r`. -/
theorem problem_15_two_launches [DecidableEq K]
    (hillSpread root launchSpread : K)
    (twoNonzero : (2 : K) ≠ 0)
    (rootSquare : root ^ 2 = 1 - hillSpread)
    (launchEquation :
      hillSpread = 4 * launchSpread * (1 - launchSpread)) :
    launchSpread = downhillLaunchSpread root ∨
      launchSpread = uphillLaunchSpread root := by
  have launchRoot : (2 * launchSpread - 1) ^ 2 = root ^ 2 := by
    rw [rootSquare]
    calc
      (2 * launchSpread - 1) ^ 2 =
          1 - 4 * launchSpread * (1 - launchSpread) := by ring1
      _ = 1 - hillSpread := by rw [launchEquation]
  have productZero :
      ((2 * launchSpread - 1) - root) *
        ((2 * launchSpread - 1) + root) = 0 := by
    calc
      ((2 * launchSpread - 1) - root) *
          ((2 * launchSpread - 1) + root) =
        (2 * launchSpread - 1) ^ 2 - root ^ 2 := by ring1
      _ = 0 := by rw [launchRoot]; ring1
  have solvePositive (equation : 2 * launchSpread - 1 = root) :
      launchSpread = uphillLaunchSpread root := by
    unfold uphillLaunchSpread
    apply eq_of_mul_eq_mul_right twoNonzero
    calc
      launchSpread * 2 = (2 * launchSpread - 1) + 1 := by ring1
      _ = root + 1 := by rw [equation]
      _ = 1 + root := by ring1
      _ = ((1 + root) / 2) * 2 :=
        (RFAP.ExplicitField.div_mul_cancel (1 + root) twoNonzero).symm
  have solveNegative (equation : 2 * launchSpread - 1 = -root) :
      launchSpread = downhillLaunchSpread root := by
    unfold downhillLaunchSpread
    apply eq_of_mul_eq_mul_right twoNonzero
    calc
      launchSpread * 2 = (2 * launchSpread - 1) + 1 := by ring1
      _ = -root + 1 := by rw [equation]
      _ = 1 - root := by ring1
      _ = ((1 - root) / 2) * 2 :=
        (RFAP.ExplicitField.div_mul_cancel (1 - root) twoNonzero).symm
  by_cases firstFactor : (2 * launchSpread - 1) - root = 0
  · right
    apply solvePositive
    calc
      2 * launchSpread - 1 =
          ((2 * launchSpread - 1) - root) + root := by ring1
      _ = root := by rw [firstFactor]; ring1
  · left
    have secondFactor : (2 * launchSpread - 1) + root = 0 := by
      by_cases zero : (2 * launchSpread - 1) + root = 0
      · exact zero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstFactor zero) productZero)
    apply solveNegative
    calc
      2 * launchSpread - 1 =
          ((2 * launchSpread - 1) + root) - root := by ring1
      _ = -root := by rw [secondFactor]; ring1

/-! ## Example 23.1: algebraic dynamics in `F₁₁` -/

@[ext] structure ParticleState (K : Type*) where
  position : Point K
  velocity : Point K
deriving DecidableEq

def pointAdd (left right : Point K) : Point K :=
  ⟨left.x + right.x, left.y + right.y⟩

def particleStep (acceleration : Point K)
    (state : ParticleState K) : ParticleState K :=
  ⟨pointAdd state.position state.velocity,
    pointAdd state.velocity acceleration⟩

def particleStateAt (acceleration : Point K) : Nat → ParticleState K
  | 0 => ⟨⟨0, 0⟩, ⟨1, 3⟩⟩
  | time + 1 => particleStep acceleration (particleStateAt acceleration time)

def constantGravityAcceleration : Point K := ⟨0, -1⟩

def algebraicDynamicsClosedForm (time : K) : ParticleState K :=
  ⟨⟨time, trajectoryPositionY time⟩,
    ⟨1, trajectoryVelocityY time⟩⟩

theorem algebraicDynamicsClosedForm_step
    (time : K) (elevenZero : (11 : K) = 0) :
    particleStep (constantGravityAcceleration (K := K))
        (algebraicDynamicsClosedForm time) =
      algebraicDynamicsClosedForm (time + 1) := by
  apply ParticleState.ext
  · apply Point.ext
    · unfold particleStep algebraicDynamicsClosedForm pointAdd
      ring1
    · unfold particleStep algebraicDynamicsClosedForm pointAdd
      calc
        trajectoryPositionY time + trajectoryVelocityY time =
            trajectoryPositionY (time + 1) - 11 * time :=
          trajectory_step_y_identity time
        _ = trajectoryPositionY (time + 1) := by rw [elevenZero]; ring1
  · apply Point.ext
    · unfold particleStep algebraicDynamicsClosedForm
        constantGravityAcceleration pointAdd
      ring1
    · unfold particleStep algebraicDynamicsClosedForm
        constantGravityAcceleration pointAdd trajectoryVelocityY
      ring1

def trajectoryEquation (point : Point K) : K :=
  point.x ^ 2 + 4 * point.x + 2 * point.y

theorem trajectory_y_unique
    (x y : K) (elevenZero : (11 : K) = 0)
    (twoNonzero : (2 : K) ≠ 0)
    (onCurve : trajectoryEquation (⟨x, y⟩ : Point K) = 0) :
    y = trajectoryPositionY x := by
  apply eq_of_mul_eq_mul_right twoNonzero
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

def trajectoryConic [Nontrivial K] : Conic K where
  d := 1
  e := 0
  f := 0
  a := 4
  b := 2
  c := 0
  quadratic_nonzero := Or.inl one_ne_zero

theorem trajectoryConic_evaluate [Nontrivial K] (point : Point K) :
    (trajectoryConic (K := K)).evaluate point = trajectoryEquation point := by
  unfold Conic.evaluate trajectoryConic trajectoryEquation
  ring1

abbrev F₁₁ := FieldEleven.Element

def fieldElevenAcceleration : Point F₁₁ :=
  constantGravityAcceleration (K := F₁₁)

def fieldElevenStateAt (time : Nat) : ParticleState F₁₁ :=
  particleStateAt fieldElevenAcceleration time

def fieldElevenClosedForm (time : Nat) : ParticleState F₁₁ :=
  algebraicDynamicsClosedForm (time : F₁₁)

theorem fieldElevenClosedForm_step (time : Nat) :
    particleStep fieldElevenAcceleration (fieldElevenClosedForm time) =
      fieldElevenClosedForm (time + 1) := by
  have castSuccessor :
      ((time + 1 : Nat) : F₁₁) = (time : F₁₁) + 1 := by
    exact Nat.cast_succ time
  unfold fieldElevenAcceleration fieldElevenClosedForm
  rw [castSuccessor]
  exact algebraicDynamicsClosedForm_step
    (time : F₁₁) FieldEleven.eleven_eq_zero

/-- The printed position and velocity formulas hold for every requested
finite time, by primitive recursion. -/
theorem fieldElevenStateAt_formula (time : Nat) :
    fieldElevenStateAt time = fieldElevenClosedForm time := by
  induction time with
  | zero => decide
  | succ time inductionHypothesis =>
      change particleStep fieldElevenAcceleration (fieldElevenStateAt time) =
        fieldElevenClosedForm (time + 1)
      rw [inductionHypothesis]
      exact fieldElevenClosedForm_step time

/-- The recurrence repeats after eleven steps, for every requested time. -/
theorem fieldElevenStateAt_period (time : Nat) :
    fieldElevenStateAt (time + 11) = fieldElevenStateAt time := by
  rw [fieldElevenStateAt_formula, fieldElevenStateAt_formula]
  have castPeriod :
      ((time + 11 : Nat) : F₁₁) = (time : F₁₁) := by
    calc
      ((time + 11 : Nat) : F₁₁) =
          (time : F₁₁) + (11 : F₁₁) := by
            rw [Nat.cast_add]
            congr 1
      _ = (time : F₁₁) + 0 := by rw [FieldEleven.eleven_eq_zero]
      _ = (time : F₁₁) := add_zero _
  unfold fieldElevenClosedForm
  rw [castPeriod]

def fieldElevenDisplayedStates : List (ParticleState F₁₁) :=
  [ ⟨⟨0, 0⟩, ⟨1, 3⟩⟩, ⟨⟨1, 3⟩, ⟨1, 2⟩⟩,
    ⟨⟨2, 5⟩, ⟨1, 1⟩⟩, ⟨⟨3, 6⟩, ⟨1, 0⟩⟩,
    ⟨⟨4, 6⟩, ⟨1, 10⟩⟩, ⟨⟨5, 5⟩, ⟨1, 9⟩⟩,
    ⟨⟨6, 3⟩, ⟨1, 8⟩⟩, ⟨⟨7, 0⟩, ⟨1, 7⟩⟩,
    ⟨⟨8, 7⟩, ⟨1, 6⟩⟩, ⟨⟨9, 2⟩, ⟨1, 5⟩⟩,
    ⟨⟨10, 7⟩, ⟨1, 4⟩⟩, ⟨⟨0, 0⟩, ⟨1, 3⟩⟩ ]

/-- Example 23.1's complete displayed twelve-column table. -/
theorem example_23_1_table :
    (List.range 12).map fieldElevenStateAt = fieldElevenDisplayedStates := by
  decide

def fieldElevenTrajectoryPoint (time : Nat) : Point F₁₁ :=
  ⟨time, trajectoryPositionY (time : F₁₁)⟩

def fieldElevenTrajectoryEquation (point : Point F₁₁) : F₁₁ :=
  trajectoryEquation point

theorem fieldElevenTrajectoryPoint_on_curve (time : Nat) :
    fieldElevenTrajectoryEquation (fieldElevenTrajectoryPoint time) = 0 := by
  have elevenZero : (11 : F₁₁) = 0 := FieldEleven.eleven_eq_zero
  change trajectoryEquation
    (⟨(time : F₁₁), trajectoryPositionY (time : F₁₁)⟩ :
      Point F₁₁) = 0
  unfold trajectoryEquation
  calc
    (time : F₁₁) ^ 2 + 4 * (time : F₁₁) +
        2 * trajectoryPositionY (time : F₁₁) =
      11 * (time : F₁₁) ^ 2 :=
        trajectory_curve_identity (time : F₁₁)
    _ = 0 := by rw [elevenZero]; exact zero_mul _

/-- For every supplied horizontal residue label there is exactly one vertical
coordinate on the trajectory curve.  This is the constructive replacement
for globally enumerating the ambient field carrier. -/
theorem fieldElevenTrajectory_y_unique (x y : F₁₁)
    (onCurve : trajectoryEquation (⟨x, y⟩ : Point F₁₁) = 0) :
    y = trajectoryPositionY x :=
  trajectory_y_unique x y FieldEleven.eleven_eq_zero (by decide) onCurve

/-- Pointwise chart for the source's phrase "exactly those points": for each
supplied natural residue label, the curve equation has precisely the displayed
vertical coordinate. -/
theorem fieldElevenTrajectory_chart (time : Nat) (y : F₁₁) :
    trajectoryEquation (⟨(time : F₁₁), y⟩ : Point F₁₁) = 0 ↔
      y = trajectoryPositionY (time : F₁₁) := by
  constructor
  · exact fieldElevenTrajectory_y_unique (time : F₁₁) y
  · intro yValue
    rw [yValue]
    have onCurve := fieldElevenTrajectoryPoint_on_curve time
    exact onCurve

def fieldElevenTrajectoryConic : Conic F₁₁ :=
  trajectoryConic (K := F₁₁)

def fieldElevenTrajectoryFocus : Point F₁₁ := ⟨9, 7⟩

def fieldElevenTrajectoryDirectrix : Line F₁₁ :=
  ⟨0, 1, 3, Or.inr (by decide)⟩

/-- The focus `[9,7]` and directrix `⟨0:1:3⟩` give the displayed
trajectory conic exactly. -/
theorem example_23_1_parabola :
    fieldElevenTrajectoryConic.IsParabolaPresentation
      fieldElevenTrajectoryFocus fieldElevenTrajectoryDirectrix := by
  refine ⟨
    { directrixNonNull := by
        unfold fieldElevenTrajectoryDirectrix Line.IsNull
        decide
      focusNotOnDirectrix := by
        unfold fieldElevenTrajectoryDirectrix fieldElevenTrajectoryFocus
          Line.Contains
        decide
      scale := 1
      scaleNonzero := by decide
      dEquation := by decide
      eEquation := by decide
      fEquation := by decide
      aEquation := by decide
      bEquation := by decide
      cEquation := by decide }⟩

theorem fieldElevenTrajectoryConic_evaluate (point : Point F₁₁) :
    fieldElevenTrajectoryConic.evaluate point =
      fieldElevenTrajectoryEquation point := by
  exact trajectoryConic_evaluate point

/-- The source's surprising vertex `[9,2]` is on the trajectory. -/
theorem example_23_1_vertex :
    fieldElevenTrajectoryConic.evaluate ⟨9, 2⟩ = 0 := by
  decide

/-! ## Problem 16: Snell's law -/

private theorem eq_zero_of_mul_eq_zero_left
    {factor value : K} (factorNonzero : factor ≠ 0)
    (productZero : factor * value = 0) : value = 0 := by
  have inverseCancel : factor⁻¹ * factor = (1 : K) := by
    calc
      factor⁻¹ * factor = factor * factor⁻¹ := by ring1
      _ = 1 := RFAP.ExplicitField.mul_inv_cancel factor factorNonzero
  calc
    value = 1 * value := by rw [one_mul]
    _ = (factor⁻¹ * factor) * value := by rw [inverseCancel]
    _ = factor⁻¹ * (factor * value) := by ring1
    _ = 0 := by rw [productZero]; ring1

/-- Equations (23.5)--(23.7), with the source's cancelled factor made
explicit.  When `T₁=T₂`, the squared differentiated quad-triple equation
does not by itself imply (23.7), so the printed cancellation requires the
visible `firstTime ≠ secondTime` premise. -/
theorem stationary_quadTriple_derivative [DecidableEq K]
    (firstTime secondTime totalTime firstRate secondRate : K)
    (twoNonzero : (2 : K) ≠ 0)
    (timesDifferent : firstTime ≠ secondTime)
    (quadTriple :
      (firstTime + secondTime - totalTime) ^ 2 =
        4 * firstTime * secondTime)
    (stationaryDerivative :
      2 * (firstTime + secondTime - totalTime) *
          (firstRate + secondRate) =
        4 * (firstRate * secondTime + firstTime * secondRate)) :
    secondTime * firstRate ^ 2 = firstTime * secondRate ^ 2 := by
  have fourNonzero : (4 : K) ≠ 0 := by
    rw [show (4 : K) = 2 * 2 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero twoNonzero twoNonzero
  have sixteenNonzero : (16 : K) ≠ 0 := by
    rw [show (16 : K) = 4 * 4 by ring1]
    exact RFAP.ExplicitField.mul_ne_zero fourNonzero fourNonzero
  have squaredDerivative := congrArg (fun value : K => value ^ 2)
    stationaryDerivative
  have scaledFactorization :
      16 * ((firstTime - secondTime) *
        (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2)) = 0 := by
    calc
      16 * ((firstTime - secondTime) *
          (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2)) =
        4 * (firstTime + secondTime - totalTime) ^ 2 *
            (firstRate + secondRate) ^ 2 -
          16 * (firstRate * secondTime +
            firstTime * secondRate) ^ 2 := by
              rw [quadTriple]
              ring1
      _ =
        (2 * (firstTime + secondTime - totalTime) *
            (firstRate + secondRate)) ^ 2 -
          (4 * (firstRate * secondTime +
            firstTime * secondRate)) ^ 2 := by
              ring1
      _ = 0 := by rw [squaredDerivative]; ring1
  have factorization :
      (firstTime - secondTime) *
        (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2) = 0 :=
    eq_zero_of_mul_eq_zero_left sixteenNonzero (by
      calc
        16 * ((firstTime - secondTime) *
            (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2)) = 0 :=
          scaledFactorization)
  have differenceNonzero : firstTime - secondTime ≠ 0 := by
    intro differenceZero
    apply timesDifferent
    calc
      firstTime = (firstTime - secondTime) + secondTime := by ring1
      _ = secondTime := by rw [differenceZero]; ring1
  have resultDifference :
      secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2 = 0 :=
    eq_zero_of_mul_eq_zero_left differenceNonzero factorization
  calc
    secondTime * firstRate ^ 2 =
        (secondTime * firstRate ^ 2 - firstTime * secondRate ^ 2) +
          firstTime * secondRate ^ 2 := by ring1
    _ = firstTime * secondRate ^ 2 := by rw [resultDifference]; ring1

def snellUpperPathQuadrance (a x : K) : K := a ^ 2 + x ^ 2

def snellLowerPathQuadrance (b c x : K) : K :=
  (c - x) ^ 2 + b ^ 2

def snellUpperSpread (a x : K) : K :=
  x ^ 2 / snellUpperPathQuadrance a x

def snellLowerSpread (b c x : K) : K :=
  (c - x) ^ 2 / snellLowerPathQuadrance b c x

/-- Problem 16, Snell's law.  `stationaryCleared` is equation (23.7) after
substituting (23.3)--(23.4) and clearing the four speed denominators. -/
theorem problem_16
    (a b c x firstSpeedSquare secondSpeedSquare : K)
    (upperNonzero : snellUpperPathQuadrance a x ≠ 0)
    (lowerNonzero : snellLowerPathQuadrance b c x ≠ 0)
    (firstSpeedNonzero : firstSpeedSquare ≠ 0)
    (upperSpreadNonzero : snellUpperSpread a x ≠ 0)
    (stationaryCleared :
      snellLowerPathQuadrance b c x * x ^ 2 * secondSpeedSquare =
        snellUpperPathQuadrance a x * (c - x) ^ 2 * firstSpeedSquare) :
    secondSpeedSquare * snellUpperSpread a x =
        firstSpeedSquare * snellLowerSpread b c x ∧
      secondSpeedSquare / firstSpeedSquare =
        snellLowerSpread b c x / snellUpperSpread a x := by
  let upper := snellUpperPathQuadrance a x
  let lower := snellLowerPathQuadrance b c x
  let firstSpread := snellUpperSpread a x
  let secondSpread := snellLowerSpread b c x
  have upperSpreadCleared : firstSpread * upper = x ^ 2 := by
    unfold firstSpread snellUpperSpread upper
    exact RFAP.ExplicitField.div_mul_cancel (x ^ 2) upperNonzero
  have lowerSpreadCleared : secondSpread * lower = (c - x) ^ 2 := by
    unfold secondSpread snellLowerSpread lower
    exact RFAP.ExplicitField.div_mul_cancel ((c - x) ^ 2) lowerNonzero
  have metricProductNonzero : upper * lower ≠ 0 :=
    RFAP.ExplicitField.mul_ne_zero upperNonzero lowerNonzero
  have speedSpreadRelation :
      secondSpeedSquare * firstSpread = firstSpeedSquare * secondSpread := by
    apply eq_of_mul_eq_mul_right metricProductNonzero
    calc
      (secondSpeedSquare * firstSpread) * (upper * lower) =
          lower * x ^ 2 * secondSpeedSquare := by
            rw [← upperSpreadCleared]
            ring1
      _ = upper * (c - x) ^ 2 * firstSpeedSquare := stationaryCleared
      _ = (firstSpeedSquare * secondSpread) * (upper * lower) := by
        rw [← lowerSpreadCleared]
        ring1
  constructor
  · exact speedSpreadRelation
  · apply div_eq_div_of_cross_mul
      firstSpeedNonzero upperSpreadNonzero
    calc
      secondSpeedSquare * firstSpread =
          firstSpeedSquare * secondSpread := speedSpreadRelation
      _ = secondSpread * firstSpeedSquare := by ring1

/-! ## Lorentzian addition of velocities -/

/-- Newtonian addition makes the three squared speeds a quad triple. -/
theorem newtonian_velocity_quadTriple
    (velocity firstVelocity secondVelocity : K)
    (addition : velocity = firstVelocity + secondVelocity) :
    QuadTriple (firstVelocity ^ 2) (secondVelocity ^ 2) (velocity ^ 2) := by
  unfold QuadTriple archimedesFunction
  rw [addition]
  ring1

/-- The unsquared rearrangement preceding equation (23.11). -/
theorem lorentzian_velocity_rearrangement
    (velocity firstVelocity secondVelocity : K)
    (additionCleared :
      velocity * (1 + firstVelocity * secondVelocity) =
        firstVelocity + secondVelocity) :
    velocity ^ 2 - firstVelocity ^ 2 - secondVelocity ^ 2 +
        firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2 =
      2 * firstVelocity * secondVelocity * (1 - velocity ^ 2) := by
  have squared := congrArg (fun value : K => value ^ 2) additionCleared
  have differenceZero :
      (velocity ^ 2 - firstVelocity ^ 2 - secondVelocity ^ 2 +
          firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) -
        2 * firstVelocity * secondVelocity * (1 - velocity ^ 2) = 0 := by
    calc
      (velocity ^ 2 - firstVelocity ^ 2 - secondVelocity ^ 2 +
            firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) -
          2 * firstVelocity * secondVelocity * (1 - velocity ^ 2) =
        (velocity * (1 + firstVelocity * secondVelocity)) ^ 2 -
          (firstVelocity + secondVelocity) ^ 2 := by ring1
      _ = 0 := by rw [squared]; ring1
  calc
    velocity ^ 2 - firstVelocity ^ 2 - secondVelocity ^ 2 +
        firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2 =
      ((velocity ^ 2 - firstVelocity ^ 2 - secondVelocity ^ 2 +
          firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) -
        2 * firstVelocity * secondVelocity * (1 - velocity ^ 2)) +
          2 * firstVelocity * secondVelocity * (1 - velocity ^ 2) := by ring1
    _ = 2 * firstVelocity * secondVelocity * (1 - velocity ^ 2) := by
      rw [differenceZero]
      ring1

/-- Equation (23.11) and its symmetric rewrite, both derived without choosing
signs or square roots from the quotient-free Lorentz addition equation. -/
theorem lorentzian_velocity_squares
    (velocity firstVelocity secondVelocity : K)
    (additionCleared :
      velocity * (1 + firstVelocity * secondVelocity) =
        firstVelocity + secondVelocity) :
    let V := velocity ^ 2
    let V₁ := firstVelocity ^ 2
    let V₂ := secondVelocity ^ 2
    (V₁ + V₂ - V - V₁ * V₂ * V) ^ 2 =
        4 * V₁ * V₂ * (1 - V) ^ 2 ∧
      (V₁ + V₂ + V - V₁ * V₂ * V) ^ 2 =
        4 * (V * V₁ + V * V₂ + V₁ * V₂ -
          2 * V * V₁ * V₂) := by
  dsimp only
  have rearrangement := lorentzian_velocity_rearrangement
    velocity firstVelocity secondVelocity additionCleared
  have squared := congrArg (fun value : K => value ^ 2) rearrangement
  have equation :
      (firstVelocity ^ 2 + secondVelocity ^ 2 - velocity ^ 2 -
          firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) ^ 2 =
        4 * firstVelocity ^ 2 * secondVelocity ^ 2 *
          (1 - velocity ^ 2) ^ 2 := by
    calc
      (firstVelocity ^ 2 + secondVelocity ^ 2 - velocity ^ 2 -
          firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) ^ 2 =
        (velocity ^ 2 - firstVelocity ^ 2 - secondVelocity ^ 2 +
          firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) ^ 2 := by
            ring1
      _ = (2 * firstVelocity * secondVelocity *
          (1 - velocity ^ 2)) ^ 2 := squared
      _ = 4 * firstVelocity ^ 2 * secondVelocity ^ 2 *
          (1 - velocity ^ 2) ^ 2 := by ring1
  constructor
  · exact equation
  · have symmetricDifferenceZero :
        (firstVelocity ^ 2 + secondVelocity ^ 2 + velocity ^ 2 -
              firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) ^ 2 -
            4 * (velocity ^ 2 * firstVelocity ^ 2 +
              velocity ^ 2 * secondVelocity ^ 2 +
              firstVelocity ^ 2 * secondVelocity ^ 2 -
              2 * velocity ^ 2 * firstVelocity ^ 2 * secondVelocity ^ 2) = 0 := by
      calc
        (firstVelocity ^ 2 + secondVelocity ^ 2 + velocity ^ 2 -
                firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) ^ 2 -
              4 * (velocity ^ 2 * firstVelocity ^ 2 +
                velocity ^ 2 * secondVelocity ^ 2 +
                firstVelocity ^ 2 * secondVelocity ^ 2 -
                2 * velocity ^ 2 * firstVelocity ^ 2 * secondVelocity ^ 2) =
            (firstVelocity ^ 2 + secondVelocity ^ 2 - velocity ^ 2 -
                firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) ^ 2 -
              4 * firstVelocity ^ 2 * secondVelocity ^ 2 *
                (1 - velocity ^ 2) ^ 2 := by ring1
        _ = 0 := by rw [equation]; ring1
    calc
      (firstVelocity ^ 2 + secondVelocity ^ 2 + velocity ^ 2 -
            firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) ^ 2 =
        ((firstVelocity ^ 2 + secondVelocity ^ 2 + velocity ^ 2 -
              firstVelocity ^ 2 * secondVelocity ^ 2 * velocity ^ 2) ^ 2 -
            4 * (velocity ^ 2 * firstVelocity ^ 2 +
              velocity ^ 2 * secondVelocity ^ 2 +
              firstVelocity ^ 2 * secondVelocity ^ 2 -
              2 * velocity ^ 2 * firstVelocity ^ 2 * secondVelocity ^ 2)) +
          4 * (velocity ^ 2 * firstVelocity ^ 2 +
            velocity ^ 2 * secondVelocity ^ 2 +
            firstVelocity ^ 2 * secondVelocity ^ 2 -
            2 * velocity ^ 2 * firstVelocity ^ 2 * secondVelocity ^ 2) := by
              ring1
      _ = 4 * (velocity ^ 2 * firstVelocity ^ 2 +
            velocity ^ 2 * secondVelocity ^ 2 +
            firstVelocity ^ 2 * secondVelocity ^ 2 -
            2 * velocity ^ 2 * firstVelocity ^ 2 * secondVelocity ^ 2) := by
              rw [symmetricDifferenceZero]
              ring1

end PhysicsApplications
end DivineProportions
