module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.QuadTriple.Basic
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

namespace Purelib.Physics.Kinematics.Velocity.Polynomial

section PhysicsApplications

variable {K : Type*} [ExplicitField K]

/-! ## Lorentzian addition of velocities -/

open Purelib.Geometry.Trigonometry.QuadTriple in
/-- The squared speeds of an additive velocity triple satisfy the quad-triple identity.

The hypothesis identifies the resultant velocity with the sum of the two input velocities; polynomial expansion gives
the relation without extracting square roots. -/
theorem newtonian_velocity_quadTriple
    (velocity firstVelocity secondVelocity : K)
    (addition : velocity = firstVelocity + secondVelocity) :
    Purelib.Geometry.Trigonometry.QuadTriple (firstVelocity ^ 2) (secondVelocity ^ 2) (velocity ^ 2) := by
  unfold Purelib.Geometry.Trigonometry.QuadTriple Basic.archimedesFunction
  rw [addition]
  ring1

/-- Derive the squared-velocity rearrangement from cleared Lorentzian addition.

Squaring the supplied equation and collecting terms requires no nonzero denominator assumption and makes no choice of
velocity signs. -/
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

open Purelib in
/-- Squared velocities satisfy two symmetric polynomial forms of Lorentzian addition.

The cleared addition equation implies both identities; the claim is valid over the explicit field without choosing roots
or dividing by a potentially zero factor. -/
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
end Purelib.Physics.Kinematics.Velocity.Polynomial

end
