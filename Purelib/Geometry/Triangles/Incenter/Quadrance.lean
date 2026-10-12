module
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Quadrance
public import Purelib.Geometry.Plane.Line.VertexBisector.Basic
import Purelib.Geometry.Plane.Line.VertexBisector.Quadrance
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.VertexBisector

section
@[expose] public section

/-!
# Divine Proportions, §12.5: inquadrance

First we expose the common point-to-side quadrance implied by two concurrent
vertex bisectors.  The numerical theorem is then the source proof with every
division cleared: Spread law, the double-spread relation at the third vertex,
and Extended spread law leave one visible factor `1-u₃`, which is cancelled
only in the printed theorem.
-/

namespace Purelib.Geometry.Triangles.Incenter.Quadrance

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- A point on bisectors at two vertices has the same quadrance to all three triangle side lines. -/
theorem incenter_common_inquadrance
    [Nontrivial K] [DecidableEq K]
    (firstSide secondSide thirdSide : Plane.Line K)
    (firstSideNonNull : ¬ firstSide.IsNull)
    (secondSideNonNull : ¬ secondSide.IsNull)
    (thirdSideNonNull : ¬ thirdSide.IsNull)
    (firstVertexNonparallel : ¬ thirdSide.Parallel secondSide)
    (secondVertexNonparallel : ¬ thirdSide.Parallel firstSide)
    (firstBisector secondBisector : Plane.Line K)
    (isFirstBisector :
      VertexBisector.Basic.IsVertexBisector thirdSide secondSide firstBisector
        thirdSideNonNull secondSideNonNull firstVertexNonparallel)
    (isSecondBisector :
      VertexBisector.Basic.IsVertexBisector thirdSide firstSide secondBisector
        thirdSideNonNull firstSideNonNull secondVertexNonparallel)
    (center : Plane.Point K)
    (centerOnFirst : firstBisector.Contains center)
    (centerOnSecond : secondBisector.Contains center) :
    Quadrance.pointLineQuadrance center firstSide firstSideNonNull =
        Quadrance.pointLineQuadrance center secondSide secondSideNonNull ∧
      Quadrance.pointLineQuadrance center secondSide secondSideNonNull =
        Quadrance.pointLineQuadrance center thirdSide thirdSideNonNull := by
  have equalThirdSecond :=
    Quadrance.equal_pointLineQuadrance_of_isVertexBisector_contains
      thirdSide secondSide firstBisector thirdSideNonNull secondSideNonNull
      firstVertexNonparallel isFirstBisector center centerOnFirst
  have equalThirdFirst :=
    Quadrance.equal_pointLineQuadrance_of_isVertexBisector_contains
      thirdSide firstSide secondBisector thirdSideNonNull firstSideNonNull
      secondVertexNonparallel isSecondBisector center centerOnSecond
  exact ⟨equalThirdFirst.symm.trans equalThirdSecond,
    equalThirdSecond.symm⟩

/-- The inquadrance relation with the complementary bisector-spread factor retained.

The four supplied spread and circumquadrance equations imply the identity without cancellation. -/
theorem inquadrance_cleared
    (u₁ u₂ u₃ q₃ s₃ circumquadranceValue
      secondVertexQuadrance inquadranceValue : K)
    (inquadranceFromSpread :
      inquadranceValue = u₂ * secondVertexQuadrance)
    (spreadLawCleared :
      secondVertexQuadrance * (1 - u₃) = u₁ * q₃)
    (bisectedThirdSpread : s₃ = 4 * u₃ * (1 - u₃))
    (extendedSpreadCleared :
      q₃ = 4 * circumquadranceValue * s₃) :
    inquadranceValue * (1 - u₃) =
      (16 * circumquadranceValue * u₁ * u₂ * u₃) * (1 - u₃) := by
  calc
    inquadranceValue * (1 - u₃) =
        u₂ * (secondVertexQuadrance * (1 - u₃)) := by
          rw [inquadranceFromSpread]
          ring1
    _ = u₂ * (u₁ * q₃) := by rw [spreadLawCleared]
    _ = u₂ * (u₁ * (4 * circumquadranceValue * s₃)) := by
      rw [extendedSpreadCleared]
    _ = u₂ *
        (u₁ * (4 * circumquadranceValue *
          (4 * u₃ * (1 - u₃)))) := by rw [bisectedThirdSpread]
    _ = (16 * circumquadranceValue * u₁ * u₂ * u₃) *
        (1 - u₃) := by ring1

/-- Inquadrance equals sixteen times the circumquadrance and the three bisector spreads.

The spread, bisected-spread and extended-spread equations hold, and the two cancelled denominators are nonzero. -/
theorem inquadrance
    [Nontrivial K]
    (u₁ u₂ u₃ q₃ s₃ circumquadranceValue
      secondVertexQuadrance inquadranceValue : K)
    (oneMinusThirdNonzero : 1 - u₃ ≠ 0)
    (thirdSpreadNonzero : s₃ ≠ 0)
    (inquadranceFromSpread :
      inquadranceValue = u₂ * secondVertexQuadrance)
    (spreadLaw :
      secondVertexQuadrance = u₁ * q₃ / (1 - u₃))
    (bisectedThirdSpread : s₃ = 4 * u₃ * (1 - u₃))
    (extendedSpread :
      q₃ / s₃ = 4 * circumquadranceValue) :
    inquadranceValue = 16 * circumquadranceValue * u₁ * u₂ * u₃ := by
  have spreadLawCleared :
      secondVertexQuadrance * (1 - u₃) = u₁ * q₃ := by
    calc
      secondVertexQuadrance * (1 - u₃) =
          (u₁ * q₃ / (1 - u₃)) * (1 - u₃) := by rw [spreadLaw]
      _ = u₁ * q₃ :=
        Algebra.Field.ExplicitField.div_mul_cancel _ oneMinusThirdNonzero
  have extendedSpreadCleared :
      q₃ = 4 * circumquadranceValue * s₃ := by
    calc
      q₃ = (q₃ / s₃) * s₃ := by
        rw [Algebra.Field.ExplicitField.div_mul_cancel q₃ thirdSpreadNonzero]
      _ = (4 * circumquadranceValue) * s₃ := by rw [extendedSpread]
  apply ExplicitField.eq_of_mul_eq_mul_right oneMinusThirdNonzero
  exact inquadrance_cleared u₁ u₂ u₃ q₃ s₃ circumquadranceValue
    secondVertexQuadrance inquadranceValue inquadranceFromSpread
    spreadLawCleared bisectedThirdSpread extendedSpreadCleared

end Purelib.Geometry.Triangles.Incenter.Quadrance

end
