module
public import Purelib.Curves.Plane.Conic.Center
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.QuadraticPart
public import Purelib.Geometry.Conics.Grammola.Basic
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Intersection
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Geometry.Conics.Grammola

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

section
@[expose] public section

/-!
# Divine Proportions, §15.5: grammolas

A grammola is retained through its two explicit non-null diagonal lines and
associated quadrance.  Multiplying by the two line norms clears exactly the
two finite divisions and produces an executable conic.  The intersection of
the diagonals is then an explicit center.
-/

namespace Purelib.Geometry

namespace Conics.Grammola.Center

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- Exercise 15.15: every grammola is centered at the explicit intersection of its two nonparallel diagonal lines. -/
theorem exercise_15_15 [DecidableEq K]
    (firstDiagonal secondDiagonal : Plane.Line K) (associatedQuadrance : K)
    (presentation :
      Grammola.Presentation firstDiagonal secondDiagonal associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    (Grammola.conic firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull associatedQuadrance twoNonzero).IsCenter
        (Intersection.lineIntersection firstDiagonal secondDiagonal
          presentation.notParallel) := by
  let center :=
    Intersection.lineIntersection firstDiagonal secondDiagonal presentation.notParallel
  have onFirst : firstDiagonal.Contains center :=
    Intersection.lineIntersection_on_first firstDiagonal secondDiagonal
      presentation.notParallel
  have onSecond : secondDiagonal.Contains center :=
    Intersection.lineIntersection_on_second firstDiagonal secondDiagonal
      presentation.notParallel
  unfold Plane.Line.Contains at onFirst onSecond
  constructor
  · change
      2 * Grammola.conicD firstDiagonal secondDiagonal * center.x +
          Grammola.conicE firstDiagonal secondDiagonal * center.y +
          Grammola.conicA firstDiagonal secondDiagonal = 0
    calc
      2 * Grammola.conicD firstDiagonal secondDiagonal * center.x +
            Grammola.conicE firstDiagonal secondDiagonal * center.y +
            Grammola.conicA firstDiagonal secondDiagonal =
          2 * (Line.Basic.lineNorm secondDiagonal * firstDiagonal.a *
              (firstDiagonal.a * center.x + firstDiagonal.b * center.y +
                firstDiagonal.c) +
            Line.Basic.lineNorm firstDiagonal * secondDiagonal.a *
              (secondDiagonal.a * center.x + secondDiagonal.b * center.y +
                secondDiagonal.c)) := by
        unfold Grammola.conicD Grammola.conicE Grammola.conicA
        ring1
      _ = 0 := by rw [onFirst, onSecond]; ring1
  · change
      Grammola.conicE firstDiagonal secondDiagonal * center.x +
          2 * Grammola.conicF firstDiagonal secondDiagonal * center.y +
          Grammola.conicB firstDiagonal secondDiagonal = 0
    calc
      Grammola.conicE firstDiagonal secondDiagonal * center.x +
            2 * Grammola.conicF firstDiagonal secondDiagonal * center.y +
            Grammola.conicB firstDiagonal secondDiagonal =
          2 * (Line.Basic.lineNorm secondDiagonal * firstDiagonal.b *
              (firstDiagonal.a * center.x + firstDiagonal.b * center.y +
                firstDiagonal.c) +
            Line.Basic.lineNorm firstDiagonal * secondDiagonal.b *
              (secondDiagonal.a * center.x + secondDiagonal.b * center.y +
                secondDiagonal.c)) := by
        unfold Grammola.conicE Grammola.conicF Grammola.conicB
        ring1
      _ = 0 := by rw [onFirst, onSecond]; ring1
end Conics.Grammola.Center

end Purelib.Geometry

end

section
@[expose] public section

/-!
# Divine Proportions, Exercise 15.14

The quadratic coefficients of a grammola determine a binary quadratic whose
two factors are its diagonal directions.  This avoids diagonalizing a matrix
or selecting square roots.  The unique center then restores the affine line
offsets, and evaluation at that center restores the associated quadrance.
-/

namespace Purelib.Geometry

namespace Conics.Grammola.Center

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The center discriminant of a grammola is a nonzero scalar times the square of its diagonal direction determinant. -/
theorem conic_centerDiscriminant [DecidableEq K]
    (firstDiagonal secondDiagonal : Plane.Line K)
    (firstNonNull : ¬ firstDiagonal.IsNull)
    (secondNonNull : ¬ secondDiagonal.IsNull)
    (associatedQuadrance : K) (twoNonzero : (2 : K) ≠ 0) :
    (Grammola.conic firstDiagonal secondDiagonal firstNonNull secondNonNull
      associatedQuadrance twoNonzero).centerDiscriminant =
      -4 * Basic.lineNorm firstDiagonal * Basic.lineNorm secondDiagonal *
        (firstDiagonal.a * secondDiagonal.b -
          secondDiagonal.a * firstDiagonal.b) ^ 2 := by
  unfold Curves.Plane.Conic.centerDiscriminant Grammola.conic Grammola.conicD Grammola.conicE
    Grammola.conicF Basic.lineNorm
  ring1

/-- A valid grammola has a unique center because its quadratic center system has nonzero discriminant. -/
theorem conic_centerDiscriminant_nonzero [DecidableEq K]
    (firstDiagonal secondDiagonal : Plane.Line K) (associatedQuadrance : K)
    (presentation : Grammola.Presentation firstDiagonal secondDiagonal
      associatedQuadrance)
    (twoNonzero : (2 : K) ≠ 0) :
    (Grammola.conic firstDiagonal secondDiagonal presentation.firstNonNull
      presentation.secondNonNull associatedQuadrance
      twoNonzero).centerDiscriminant ≠ 0 := by
  rw [conic_centerDiscriminant]
  have fourNonzero : (4 : K) ≠ 0 := by
    have productNonzero : (2 : K) * 2 ≠ 0 :=
      Algebra.Field.ExplicitField.mul_ne_zero twoNonzero twoNonzero
    simpa only [show (4 : K) = 2 * 2 by ring1] using productNonzero
  have negativeFourNonzero : (-4 : K) ≠ 0 := by
    intro negativeFourZero
    apply fourNonzero
    calc
      (4 : K) = -(-4) := by ring1
      _ = 0 := by rw [negativeFourZero]; ring1
  have determinantNonzero :
      firstDiagonal.a * secondDiagonal.b -
          secondDiagonal.a * firstDiagonal.b ≠ 0 := by
    exact presentation.notParallel
  have determinantSquareNonzero :
      (firstDiagonal.a * secondDiagonal.b -
        secondDiagonal.a * firstDiagonal.b) ^ 2 ≠ 0 := by
    simpa only [pow_two] using Algebra.Field.ExplicitField.mul_ne_zero
      determinantNonzero determinantNonzero
  exact Algebra.Field.ExplicitField.mul_ne_zero
    (Algebra.Field.ExplicitField.mul_ne_zero
      (Algebra.Field.ExplicitField.mul_ne_zero negativeFourNonzero
        presentation.firstNonNull)
      presentation.secondNonNull)
    determinantSquareNonzero
end Conics.Grammola.Center

end Purelib.Geometry

end
