module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring

open Purelib.Algebra.Field (ExplicitField)

section
@[expose] public section

/-!
# Divine Proportions, Chapter 23: physics applications

The calculus passages in the source are retained through their finite
polynomial stationarity equations.  Extremum conclusions are separated from
those equations, so no completed real line, limit, or general derivative
operator enters the formalization.
-/

namespace Purelib.Physics.Mechanics.Projectile.Polynomial

section PhysicsApplications

variable {K : Type*} [ExplicitField K]

/-! ## Problem 14: projectile motion -/

open Purelib.Algebra.Field in
/-- Factor the vertical displacement into elapsed time and its remaining linear factor. -/
theorem projectile_landing_factorization (heightVelocity gravity
  time : K) :
    heightVelocity * time - gravity * time ^ 2 / 2 =
      time * (heightVelocity - gravity * time / 2) := by
  simp only [ExplicitField.div_eq_mul_inv]
  ring1

open Purelib.Algebra.Field in
open Purelib in
/-- A nonzero landing time satisfies gravity times time equals twice the initial vertical velocity.

The landing displacement is zero and two is nonzero in the explicit field. Decidable scalar equality supports the finite
factor cancellation. -/
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
        ((ExplicitField.mul_ne_zero timeNonzero factorZero) factored)
  have halfRelation : gravity * time / 2 = heightVelocity := by
    calc
      gravity * time / 2 =
          heightVelocity - (heightVelocity - gravity * time / 2) := by ring1
      _ = heightVelocity := by rw [secondFactor]; ring1
  calc
    gravity * time = (gravity * time / 2) * 2 :=
      (ExplicitField.div_mul_cancel (gravity * time) twoNonzero).symm
    _ = 2 * heightVelocity := by rw [halfRelation]; ring1

/-- The landing-time equation gives the gravity-scaled horizontal quadrance.

Multiplying squared horizontal displacement by gravity squared yields four times the product of the two initial velocity
squares; the statement uses no division. -/
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

open Purelib.Algebra.Field in
/-- An equal split of a nonzero total quadrance has ratio one half and the displayed range identity.

For nonzero gravity, multiplying V²/g² by g² recovers V². These are algebraic identities and do not themselves assert an
extremum. -/
theorem problem_14
    (V gravity : K) (VNonzero : V ≠ 0) (gravityNonzero : gravity ≠ 0)
    : (V / 2) / V = 1 / 2 ∧
      gravity ^ 2 * (V ^ 2 / gravity ^ 2) = V ^ 2 := by
  have VCancel : V * V⁻¹ = (1 : K) :=
    ExplicitField.mul_inv_cancel V VNonzero
  constructor
  · simp only [ExplicitField.div_eq_mul_inv]
    calc
      V * (2 : K)⁻¹ * V⁻¹ =
          (V * V⁻¹) * (2 : K)⁻¹ := by ring1
      _ = 1 * (2 : K)⁻¹ := by rw [VCancel]
      _ = 1 * (2 : K)⁻¹ := rfl
  · have gravitySquareNonzero : gravity ^ 2 ≠ 0 := by
      simpa only [pow_two] using
        ExplicitField.mul_ne_zero gravityNonzero gravityNonzero
    calc
      gravity ^ 2 * (V ^ 2 / gravity ^ 2) =
          (V ^ 2 / gravity ^ 2) * gravity ^ 2 := by ring1
      _ = V ^ 2 :=
        ExplicitField.div_mul_cancel (V ^ 2) gravitySquareNonzero

/-! ## Problem 15: projectile motion on a hill -/

/-- Eliminate the auxiliary hill-slope square from two cleared polynomial equations.

The supplied relation between hill spread and the auxiliary square turns the stationary equation into (2A − V)² = V²(1 −
r), without dividing by the hill spread. -/
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

section
open Purelib.Algebra.Field
/-- Recenter the cleared stationary equation at half the total quadrance.

When two is nonzero, four times the squared difference from V/2 equals the original stationary square, preserving the
supplied hill-spread relation. -/
theorem problem_15_stationary_reduction
    (horizontalSquare totalSquare hillSpread : K)
    (twoNonzero : (2 : K) ≠ 0)
    (stationary :
      (2 * horizontalSquare - totalSquare) ^ 2 =
        totalSquare ^ 2 * (1 - hillSpread)) :
    (horizontalSquare - totalSquare / 2) ^ 2 * 4 =
      totalSquare ^ 2 * (1 - hillSpread) := by
  simp only [ExplicitField.div_eq_mul_inv]
  have cancel : (2 : K) * (2 : K)⁻¹ = 1 :=
    ExplicitField.mul_inv_cancel 2 twoNonzero
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

/-- A normalized horizontal quadrance satisfies the second spread equation.

The total quadrance is nonzero and the supplied normalization and stationary equation imply r = 4s(1 − s) by cancelling
its square. -/
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
      ExplicitField.mul_ne_zero totalNonzero totalNonzero
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
    apply ExplicitField.eq_of_mul_eq_mul_right totalSquareNonzero
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

end

/-- The launch-spread candidate (1 − root)/2 from a displayed root. -/
def downhillLaunchSpread (root : K) : K := (1 - root) / 2
/-- The launch-spread candidate (1 + root)/2 from a displayed root. -/
def uphillLaunchSpread (root : K) : K := (1 + root) / 2

open Purelib.Algebra.Field in
open Purelib in
/-- A displayed root determines the two possible launch spreads.

If root² = 1 − r, two is nonzero and r = 4s(1 − s), then s equals one of (1 − root)/2 and (1 + root)/2. Decidable scalar
equality supplies the finite factor case split. -/
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
    apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    calc
      launchSpread * 2 = (2 * launchSpread - 1) + 1 := by ring1
      _ = root + 1 := by rw [equation]
      _ = 1 + root := by ring1
      _ = ((1 + root) / 2) * 2 :=
        (ExplicitField.div_mul_cancel (1 + root) twoNonzero).symm
  have solveNegative (equation : 2 * launchSpread - 1 = -root) :
      launchSpread = downhillLaunchSpread root := by
    unfold downhillLaunchSpread
    apply ExplicitField.eq_of_mul_eq_mul_right twoNonzero
    calc
      launchSpread * 2 = (2 * launchSpread - 1) + 1 := by ring1
      _ = -root + 1 := by rw [equation]
      _ = 1 - root := by ring1
      _ = ((1 - root) / 2) * 2 :=
        (ExplicitField.div_mul_cancel (1 - root) twoNonzero).symm
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
          ((ExplicitField.mul_ne_zero firstFactor zero) productZero)
    apply solveNegative
    calc
      2 * launchSpread - 1 =
          ((2 * launchSpread - 1) + root) - root := by ring1
      _ = -root := by rw [secondFactor]; ring1
end PhysicsApplications
end Purelib.Physics.Mechanics.Projectile.Polynomial

end
