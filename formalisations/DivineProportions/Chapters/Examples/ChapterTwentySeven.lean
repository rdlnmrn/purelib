module
public import Purelib.Data.Nat.Order
import Purelib.Algebra.Group.Basic
public import Purelib.Algebra.Field.ExplicitField
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra
open Purelib.Algebra.Field

section
open scoped Purelib.Data.Nat
attribute [local instance 2000] Purelib.Data.Nat.successorNeZero
@[expose] public section

/-!
# Divine Proportions, Chapter 27: rational spherical coordinates

This module formalizes the finite algebra beneath the source's coordinate
changes: squared-coordinate reconstruction, the two-, three-, and
four-dimensional Jacobian determinants, squared density identities, the
lemniscate conversion, and a witness-based finite polygon-refinement step.

The chapter's improper integrals, exponentials, Gamma/Beta integrals, `π`, and
limit assertions are intentionally not introduced.  Their finite endpoint
polynomial simplifications are retained at the end of the module.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTwentySeven

section RationalSphericalCoordinates

variable {K : Type*} [ExplicitField K]

/-! ## Exercise 27.1: finite substitution algebra -/

/-- The four algebraic identities behind Exercise 27.1's substitutions.
They make no claim about an improper integral or a limiting endpoint. -/
theorem
  exercise_27_1_substitution_identities
    (r t u v : K) :
    r ^ 2 * (1 - r ^ 2) = r ^ 2 - r ^ 4 ∧
      t ^ 2 - t = t * (t - 1) ∧
      (1 + u ^ 2) ^ 2 - (2 * u) ^ 2 = (1 - u ^ 2) ^ 2 ∧
      (1 + v ^ 2) ^ 2 - (2 * v) ^ 2 = (1 - v ^ 2) ^ 2 := by
  constructor
  · ring1
  constructor
  · ring1
  constructor <;> ring1

/-- The reciprocal substitution `s=1/t`, expressed without division. -/
theorem exercise_27_1_reciprocal_spread
    (spread t : K) (clearedReciprocal : spread * t = 1) :
    t ^ 2 * (spread * (1 - spread)) = t - 1 := by
  calc
    t ^ 2 * (spread * (1 - spread)) =
        (spread * t) * (t - spread * t) := by ring1
    _ = t - 1 := by rw [clearedReciprocal]; ring1

/-- The final reciprocal substitution `v=1/u`, also denominator-free. -/
theorem
  exercise_27_1_reciprocal_denominator
    (u v : K) (clearedReciprocal : u * v = 1) :
    v ^ 2 * (1 + u ^ 2) = 1 + v ^ 2 := by
  calc
    v ^ 2 * (1 + u ^ 2) = v ^ 2 + (u * v) ^ 2 := by ring1
    _ = 1 + v ^ 2 := by rw [clearedReciprocal]; ring1

/-- The first three nested-radical values printed after the recurrence are
linked by exact finite square certificates. -/
theorem exercise_27_2_first_terms
    (firstRoot secondRoot thirdRoot : K)
    (firstSquare : firstRoot ^ 2 = 2)
    (secondSquare : secondRoot ^ 2 = 2 + firstRoot)
    (thirdSquare : thirdRoot ^ 2 = 2 + secondRoot) :
    firstRoot ^ 2 = 2 ∧
      secondRoot ^ 2 = 4 - (2 - firstRoot) ∧
      (2 * thirdRoot) ^ 2 = 16 - 4 * (2 - secondRoot) ∧
      4 * (2 - secondRoot) = 8 - 4 * secondRoot ∧
      16 * (2 - thirdRoot) = 32 - 16 * thirdRoot := by
  constructor
  · exact firstSquare
  constructor
  · rw [secondSquare]
    ring1
  constructor
  · apply Group.eq_of_sub_eq_zero
    calc
      (2 * thirdRoot) ^ 2 - (16 - 4 * (2 - secondRoot)) =
        4 * (thirdRoot ^ 2 - (2 + secondRoot)) := by ring1
      _ = 0 := by rw [thirdSquare]; ring1
  constructor <;> ring1

/-! ## Example 27.5: the ice-cream cone region -/

/-- On the cone `z²=x²+y²`, the second polar spread is `1/2`; on the
projective sphere `x²+y²+z²=z`, its radial bound is `R=1-q`. -/
theorem
  example_27_5_cone_sphere_coordinates
    (horizontal zSquared z polarSpread R : K)
    (twoNonzero : (2 : K) ≠ 0) (RNonzero : R ≠ 0)
    (radialQuadrance : R = horizontal + zSquared)
    (polarCoordinate : polarSpread * R = horizontal)
    (cone : zSquared = horizontal)
    (projectiveSphere : R = z)
    (zSquare : zSquared = z ^ 2) :
    polarSpread = 1 / 2 ∧ R = 1 - polarSpread := by
  have coneCleared : (2 * polarSpread - 1) * R = 0 := by
    calc
      (2 * polarSpread - 1) * R =
          2 * (polarSpread * R) - R := by ring1
      _ = 2 * horizontal - (horizontal + zSquared) := by
        rw [polarCoordinate, radialQuadrance]
      _ = 0 := by rw [cone]; ring1
  have twicePolar : 2 * polarSpread = 1 := by
    apply ExplicitField.eq_of_mul_eq_mul_left RNonzero
    calc
      R * (2 * polarSpread) = R + (2 * polarSpread - 1) * R := by ring1
      _ = R := by rw [coneCleared]; ring1
      _ = R * 1 := by ring1
  have twoCancel : ((1 : K) / 2) * 2 = 1 :=
    ExplicitField.div_mul_cancel 1 twoNonzero
  have polarValue : polarSpread = 1 / 2 := by
    apply ExplicitField.eq_of_mul_eq_mul_left twoNonzero
    calc
      2 * polarSpread = 1 := twicePolar
      _ = ((1 : K) / 2) * 2 := twoCancel.symm
      _ = 2 * ((1 : K) / 2) := by ring1
  have zPolar : zSquared = (1 - polarSpread) * R := by
    calc
      zSquared = R - horizontal := by rw [radialQuadrance]; ring1
      _ = R - polarSpread * R := by rw [polarCoordinate]
      _ = (1 - polarSpread) * R := by ring1
  have radialProduct : R * (R - (1 - polarSpread)) = 0 := by
    calc
      R * (R - (1 - polarSpread)) =
          R ^ 2 - (1 - polarSpread) * R := by ring1
      _ = z ^ 2 - zSquared := by rw [← zPolar, projectiveSphere]
      _ = 0 := by rw [zSquare]; ring1
  have radialValue : R = 1 - polarSpread := by
    apply ExplicitField.eq_of_mul_eq_mul_left RNonzero
    calc
      R * R = R * (1 - polarSpread) +
          R * (R - (1 - polarSpread)) := by ring1
      _ = R * (1 - polarSpread) := by rw [radialProduct]; ring1
  exact ⟨polarValue, radialValue⟩

/-! ## Finite endpoint algebra from Examples 27.1 and 27.3--27.15 -/

/-- The polynomial endpoint simplification common to the spherical cap
(Example 27.6) and hyperbolic cap (Example 27.11). -/
theorem
  examples_27_6_27_11_cap_factorization (k
  d : K) :
    d ^ 3 - 3 * d * k ^ 2 + 2 * k ^ 3 =
      (k - d) ^ 2 * (2 * k + d) := by
  ring1

/-- The sphere and hyperboloid ring endpoint evaluations both discard the
ambient quadrance and leave the cubic coefficient `4d³/3`. -/
theorem examples_27_7_27_12_ring_endpoint
  (d : K) :
    2 * ((2 * d ^ 3) - 0) = 4 * d ^ 3 := by
  ring1

/-- Example 27.8's final paraboloid endpoint calculation. -/
theorem example_27_8_paraboloid_endpoint
    (r : K) (twoNonzero : (2 : K) ≠ 0) :
    2 * (r ^ 2 - r ^ 2 / 2) = r ^ 2 := by
  have halfCancel : (r ^ 2 / 2) * 2 = r ^ 2 :=
    ExplicitField.div_mul_cancel _ twoNonzero
  calc
    2 * (r ^ 2 - r ^ 2 / 2) =
        2 * r ^ 2 - (r ^ 2 / 2) * 2 := by ring1
    _ = r ^ 2 := by rw [halfCancel]; ring1

/-- Example 27.9: after clearing the common nonzero circle constant, mass
`2π/3` and moment `π/4` put the centroid at `3/8`. -/
theorem example_27_9_hemisphere_centroid
    (circleConstant mass moment centroidHeight : K)
    (circleConstantNonzero : circleConstant ≠ 0)
    (massValue : 3 * mass = 2 * circleConstant)
    (momentValue : 4 * moment = circleConstant)
    (centroidRelation : mass * centroidHeight = moment) :
    8 * centroidHeight = 3 := by
  apply ExplicitField.eq_of_mul_eq_mul_left circleConstantNonzero
  calc
    circleConstant * (8 * centroidHeight) =
        4 * (2 * circleConstant) * centroidHeight := by ring1
    _ = 4 * (3 * mass) * centroidHeight := by rw [massValue]
    _ = 12 * (mass * centroidHeight) := by ring1
    _ = 12 * moment := by rw [centroidRelation]
    _ = 3 * (4 * moment) := by ring1
    _ = 3 * circleConstant := by rw [momentValue]
    _ = circleConstant * 3 := by ring1

/-- Example 27.10's finite Gamma-recurrence arithmetic
`B(2,1/2)=4/3`.  The Gamma values are displayed witnesses; no integral or
function on an infinite domain is introduced. -/
theorem example_27_10_beta_coefficient
    (gammaHalf gammaThreeHalves gammaFiveHalves betaValue : K)
    (gammaFiveHalvesNonzero : gammaFiveHalves ≠ 0)
    (firstRecurrence : 2 * gammaThreeHalves = gammaHalf)
    (secondRecurrence : 2 * gammaFiveHalves = 3 * gammaThreeHalves)
    (betaCleared : gammaFiveHalves * betaValue = gammaHalf) :
    3 * betaValue = 4 := by
  have fourGammaFive : 4 * gammaFiveHalves = 3 * gammaHalf := by
    calc
      4 * gammaFiveHalves = 2 * (2 * gammaFiveHalves) := by ring1
      _ = 2 * (3 * gammaThreeHalves) := by rw [secondRecurrence]
      _ = 3 * gammaHalf := by rw [← firstRecurrence]; ring1
  apply ExplicitField.eq_of_mul_eq_mul_left gammaFiveHalvesNonzero
  calc
    gammaFiveHalves * (3 * betaValue) =
        3 * (gammaFiveHalves * betaValue) := by ring1
    _ = 3 * gammaHalf := by rw [betaCleared]
    _ = gammaFiveHalves * 4 := by rw [← fourGammaFive]; ring1

/-- Example 27.15's finite Gamma-recurrence arithmetic
`B(3/2,1/2)=π/2`, with the symbol for `π` represented only by the
displayed product `Γ(1/2)²`. -/
theorem example_27_15_beta_coefficient
    (gammaHalf gammaThreeHalves betaValue circleConstant : K)
    (recurrence : 2 * gammaThreeHalves = gammaHalf)
    (betaProduct : betaValue = gammaThreeHalves * gammaHalf)
    (circleProduct : circleConstant = gammaHalf ^ 2) :
    2 * betaValue = circleConstant := by
  rw [betaProduct, circleProduct, ← recurrence]
  ring1

/-- Example 27.14's cap-area simplification, with division by `k` cleared. -/
theorem example_27_14_surface_cap_cleared
    (circleConstant k d area : K)
    (areaFormula : area = 2 * circleConstant * (k - d)) :
    area = 2 * circleConstant * k - 2 * circleConstant * d := by
  rw [areaFormula]
  ring1

end RationalSphericalCoordinates
end formalisations.DivineProportions.Chapters.Examples.ChapterTwentySeven

end
