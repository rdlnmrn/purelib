module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
import Purelib.Curves.Plane.Lemniscate.Basic
public import Purelib.Curves.Plane.Lemniscate.Tangent.Discriminant
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib.Curves.Plane.Lemniscate

open Purelib.Curves.Plane.Lemniscate.Tangent.Discriminant

open Purelib.Geometry

open Purelib.Geometry.Plane.Point

@[expose] public section

namespace Purelib.Curves.Plane.Lemniscate.Quadrance

section Lemniscate

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

open Purelib.Curves.Plane in
/-- Exercise 19.5: points on the lemniscate and discriminant conic lying on the same line through the origin have
constant quadrance product. The quotient-free constant is `4 Q(O,P) Q(O,R)=A²`. -/
theorem inverse_quadrance_product [Nontrivial K]
    (parameter scale : K) (lemniscatePoint discriminantPoint : Geometry.Plane.Point K)
    (eightNonzero : (8 : K) ≠ 0)
    (onLemniscate : Contains parameter lemniscatePoint)
    (onDiscriminant :
      (Tangent.Discriminant.discriminantConic parameter eightNonzero).Contains discriminantPoint)
    (sameOriginLine :
      discriminantPoint =
        ⟨scale * lemniscatePoint.x, scale * lemniscatePoint.y⟩) :
    4 * Purelib.Geometry.Plane.Point.Quadrance.quadrance ⟨0, 0⟩ lemniscatePoint *
        Purelib.Geometry.Plane.Point.Quadrance.quadrance ⟨0, 0⟩ discriminantPoint = parameter ^ 2 := by
  subst discriminantPoint
  have lemniscateEquation :
      (lemniscatePoint.x ^ 2 + lemniscatePoint.y ^ 2) ^ 2 =
        2 * parameter *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) := by
    unfold Lemniscate.Contains Lemniscate.evaluate at onLemniscate
    calc
      (lemniscatePoint.x ^ 2 + lemniscatePoint.y ^ 2) ^ 2 =
          ((lemniscatePoint.x ^ 2 + lemniscatePoint.y ^ 2) ^ 2 -
              2 * parameter *
                (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2)) +
            2 * parameter *
              (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) := by
        ring1
      _ = 2 * parameter *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) := by
        rw [onLemniscate]
        ring1
  have discriminantEquation :
      8 * scale ^ 2 *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) = parameter := by
    unfold Conic.Contains at onDiscriminant
    rw [Tangent.Discriminant.discriminantConic_evaluate] at onDiscriminant
    unfold Tangent.Discriminant.discriminantValue at onDiscriminant
    calc
      8 * scale ^ 2 *
            (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2) =
          (8 * ((scale * lemniscatePoint.x) ^ 2 -
              (scale * lemniscatePoint.y) ^ 2) - parameter) + parameter := by
        ring1
      _ = parameter := by rw [onDiscriminant]; ring1
  unfold Quadrance.quadrance
  dsimp only
  calc
    4 *
          ((lemniscatePoint.x - 0) ^ 2 +
            (lemniscatePoint.y - 0) ^ 2) *
          (((scale * lemniscatePoint.x - 0) ^ 2) +
            ((scale * lemniscatePoint.y - 0) ^ 2)) =
        4 * scale ^ 2 *
          (lemniscatePoint.x ^ 2 + lemniscatePoint.y ^ 2) ^ 2 := by ring1
    _ = 4 * scale ^ 2 *
        (2 * parameter *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2)) := by
      rw [lemniscateEquation]
    _ = parameter *
        (8 * scale ^ 2 *
          (lemniscatePoint.x ^ 2 - lemniscatePoint.y ^ 2)) := by ring1
    _ = parameter ^ 2 := by rw [discriminantEquation]; ring1

end Lemniscate

end Purelib.Curves.Plane.Lemniscate.Quadrance

end
