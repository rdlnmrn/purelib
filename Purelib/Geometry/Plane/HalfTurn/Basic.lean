module
-- Public numeral proofs and exposed line coefficients retain these exact owners.
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Geometry.Plane.Point.Affine

public import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Point.Basic
public import Purelib.Geometry.Plane.Point.Quadrance
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Transformation.Affine
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

section

open Purelib

open Purelib.Geometry

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Point

open Purelib.Geometry.Plane.Transformation

section
section
public section

/-!
# Divine Proportions, Chapter 4: point reflections

The reflection in a non-null line is defined exactly as in the book: find the
altitude foot and rotate the source point through that foot.  Theorem 13's
coordinate formula and the involution law are then derived by finite field
algebra.
-/

namespace Purelib.Geometry.Plane.HalfTurn.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Rotation in a point: `ρ_A(B) = 2A - B`. -/
@[expose] def rotateInPoint (center point : Point K) : Point K :=
  ⟨2 * center.x - point.x, 2 * center.y - point.y⟩

/-- Exercise 4.1: rotation in a point is affine. -/
theorem rotateInPoint_affine (center : Point K) :
    Affine.IsAffine (HalfTurn.Basic.rotateInPoint center) := by
  intro first second leftWeight rightWeight weights
  have rightFormula : rightWeight = 1 - leftWeight := by
    calc
      rightWeight = (leftWeight + rightWeight) - leftWeight := by ring1
      _ = 1 - leftWeight := by rw [weights]
  rw [rightFormula]
  apply Point.ext <;>
    unfold HalfTurn.Basic.rotateInPoint Affine.affineCombination <;>
    ring1

/-- Exercise 4.1: rotation in a point is its own inverse. -/
theorem rotateInPoint_involutive (center point : Point K) :
    HalfTurn.Basic.rotateInPoint center (HalfTurn.Basic.rotateInPoint center point) = point := by
  apply Point.ext <;>
    unfold HalfTurn.Basic.rotateInPoint <;>
    ring1

/-- The line formula associated to rotation in a point (Theorem 14). -/
@[expose] def rotateLineInPoint (center : Point K) (line : Line K) : Line K
  where
  a := line.a
  b := line.b
  c := -2 * center.x * line.a - 2 * center.y * line.b - line.c
  direction_nonzero := line.direction_nonzero

/-- Theorem 14 (Rotation of a line in a point): incidence is transported by the displayed associated lineation formula.
-/
theorem rotateLineInPoint_contains_iff (center point : Point K) (line : Line K) :
    (Geometry.Plane.HalfTurn.Basic.rotateLineInPoint center line).Contains (Geometry.Plane.HalfTurn.Basic.rotateInPoint
      center point) ↔
      line.Contains point := by
  constructor
  · intro rotatedContains
    change line.a * (2 * center.x - point.x) +
      line.b * (2 * center.y - point.y) +
      (-2 * center.x * line.a - 2 * center.y * line.b - line.c) = 0
      at rotatedContains
    change line.a * point.x + line.b * point.y + line.c = 0
    calc
      line.a * point.x + line.b * point.y + line.c =
          -(line.a * (2 * center.x - point.x) +
            line.b * (2 * center.y - point.y) +
            (-2 * center.x * line.a - 2 * center.y * line.b - line.c)) := by
        ring1
      _ = 0 := by rw [rotatedContains]; exact neg_zero
  · intro contains
    change line.a * point.x + line.b * point.y + line.c = 0 at contains
    change line.a * (2 * center.x - point.x) +
      line.b * (2 * center.y - point.y) +
      (-2 * center.x * line.a - 2 * center.y * line.b - line.c) = 0
    calc
      line.a * (2 * center.x - point.x) +
          line.b * (2 * center.y - point.y) +
          (-2 * center.x * line.a - 2 * center.y * line.b - line.c) =
        -(line.a * point.x + line.b * point.y + line.c) := by ring1
      _ = 0 := by rw [contains]; exact neg_zero

end Purelib.Geometry.Plane.HalfTurn.Basic

end

end

end

section
public section

/-!
# Divine Proportions, §16.1: diameters

The source's midpoint proof of Theorem 103 requires a non-null diameter side,
the same visible hypothesis as the already formalized midpoint-uniqueness
theorem.  The statement below exposes that characteristic-dependent omission.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Rotation in a point preserves the quadrance from that point. -/
theorem rotateInPoint_quadrance_center (center point : Geometry.Plane.Point K) :
    Quadrance.quadrance (HalfTurn.Basic.rotateInPoint center point) center =
      Quadrance.quadrance point center := by
  unfold Quadrance.quadrance HalfTurn.Basic.rotateInPoint
  ring1

/-- A line containing a point and the rotation center also contains the rotated point. -/
theorem line_contains_rotateInPoint (line : Geometry.Plane.Line K) (center point : Geometry.Plane.Point K)
    (containsCenter : line.Contains center)
    (containsPoint : line.Contains point) :
    line.Contains (HalfTurn.Basic.rotateInPoint center point) := by
  unfold Geometry.Plane.Line.Contains at containsCenter containsPoint ⊢
  unfold HalfTurn.Basic.rotateInPoint
  calc
    line.a * (2 * center.x - point.x) +
        line.b * (2 * center.y - point.y) + line.c =
      2 * (line.a * center.x + line.b * center.y + line.c) -
        (line.a * point.x + line.b * point.y + line.c) := by ring1
    _ = 0 := by rw [containsCenter, containsPoint]; ring1

end Purelib.Curves.Plane.Conic

end

section
public section

/-!
# Divine Proportions, regular polygon construction

The source uses a doubly infinite reflection sequence.  Here every line and
point is obtained from the already executable natural-number iterator.  A
request for vertex `k` computes exactly the first `k` reflection steps.

The point-reflection product identity below is the finite natural-index form
of Exercise 14.1.  It is then used to prove that the closed formula
`A₂ₖ = σ_{lₖ}(A₀)` agrees with the source's successive construction through
the intervening mirrors `l₂ₖ₊₁`.
-/

namespace Purelib.Geometry.Plane.HalfTurn.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- In characteristic different from two, rotation in a point fixes only that point. -/
theorem rotateInPoint_fixed_iff_center
    (center point : Point K) (twoNonzero : (2 : K) ≠ 0) :
    HalfTurn.Basic.rotateInPoint center point = point ↔ point = center := by
  constructor
  · intro fixed
    have xFixed := congrArg Point.x fixed
    have yFixed := congrArg Point.y fixed
    apply Point.ext
    · have twiceDifference :
          (2 : K) * (point.x - center.x) = 0 := by
        change 2 * center.x - point.x = point.x at xFixed
        calc
          (2 : K) * (point.x - center.x) =
              -(2 * center.x - point.x - point.x) := by ring1
          _ = 0 := by rw [xFixed]; ring1
      have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
        Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
      calc
        point.x = (point.x - center.x) + center.x := by ring1
        _ = (2 * (2 : K)⁻¹) * (point.x - center.x) + center.x := by
          rw [twoCancel]
          ring1
        _ = (2 : K)⁻¹ * (2 * (point.x - center.x)) + center.x := by ring1
        _ = center.x := by rw [twiceDifference]; ring1
    · have twiceDifference :
          (2 : K) * (point.y - center.y) = 0 := by
        change 2 * center.y - point.y = point.y at yFixed
        calc
          (2 : K) * (point.y - center.y) =
              -(2 * center.y - point.y - point.y) := by ring1
          _ = 0 := by rw [yFixed]; ring1
      have twoCancel : (2 : K) * (2 : K)⁻¹ = 1 :=
        Algebra.Field.ExplicitField.mul_inv_cancel 2 twoNonzero
      calc
        point.y = (point.y - center.y) + center.y := by ring1
        _ = (2 * (2 : K)⁻¹) * (point.y - center.y) + center.y := by
          rw [twoCancel]
          ring1
        _ = (2 : K)⁻¹ * (2 * (point.y - center.y)) + center.y := by ring1
        _ = center.y := by rw [twiceDifference]; ring1
  · intro pointCenter
    rw [pointCenter]
    apply Point.ext <;>
      unfold HalfTurn.Basic.rotateInPoint <;>
      ring1

end Purelib.Geometry.Plane.HalfTurn.Basic

end

end
