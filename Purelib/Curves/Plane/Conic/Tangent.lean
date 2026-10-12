module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Conic.Basic
public import Purelib.Curves.Plane.Conic.Translation
import Purelib.Geometry.Plane.Line.Basic
public import Purelib.Geometry.Plane.Line.Translation
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Curves.Plane

open Purelib.Geometry

open Purelib.Geometry.Plane

section
@[expose] public section

/-!
# Divine Proportions, Chapter 19: tangent lines and conics

Translations, Taylor conics, and tangent lines are retained as explicit
finite coefficient records.  A non-singular point carries the disjunction
that one of the two displayed linear coefficients is nonzero, so every line
construction remains executable and choice-free.
-/

namespace Purelib.Curves.Plane.Conic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

/-- The tangent at the origin of a non-singular standard conic is its linear part. -/
def standardTangentAtOrigin
    (conic : Conic K) (linearNonzero : conic.a ≠ 0 ∨ conic.b ≠ 0) :
    Plane.Line K where
  a := conic.a
  b := conic.b
  c := 0
  direction_nonzero := linearNonzero

/-- The explicit tangent-line representative printed in Theorem 119. -/
def tangentLine
    (conic : Conic K) (point : Plane.Point K)
    (nonSingular : conic.IsNonSingularAt point) : Plane.Line K where
  a := conic.a + 2 * conic.d * point.x + conic.e * point.y
  b := conic.b + conic.e * point.x + 2 * conic.f * point.y
  c := conic.a * point.x + conic.b * point.y + 2 * conic.c
  direction_nonzero := nonSingular

/-- The tangent formula always passes through its base point once the point lies on the conic. -/
theorem tangentLine_contains
    (conic : Conic K) (point : Plane.Point K)
    (onConic : conic.Contains point)
    (nonSingular : conic.IsNonSingularAt point) :
    (tangentLine conic point nonSingular).Contains point := by
  unfold tangentLine Plane.Line.Contains
  unfold Conic.Contains Conic.evaluate at onConic
  calc
    (conic.a + 2 * conic.d * point.x + conic.e * point.y) * point.x +
        (conic.b + conic.e * point.x + 2 * conic.f * point.y) * point.y +
        (conic.a * point.x + conic.b * point.y + 2 * conic.c) =
      2 * (conic.d * point.x ^ 2 +
        conic.e * point.x * point.y + conic.f * point.y ^ 2 +
        conic.a * point.x + conic.b * point.y + conic.c) := by ring1
    _ = 0 := by rw [onConic]; ring1

/-- Theorem 119 (Tangent to a conic): translating the linear part of the Taylor conic back to `A` gives the printed
tangent representative, up to the source's line proportion, and that representative contains `A`. -/
theorem tangent_to_conic
    (conic : Conic K) (point : Plane.Point K)
    (onConic : conic.Contains point)
    (nonSingular : conic.IsNonSingularAt point) :
    (Conic.translateLine
        (standardTangentAtOrigin (Conic.taylorConic conic point)
          (Conic.taylorConic_linear_nonzero conic point nonSingular))
        point).Equivalent
      (tangentLine conic point nonSingular) ∧
    (tangentLine conic point nonSingular).Contains point := by
  constructor
  · unfold Plane.Line.Equivalent
    dsimp only [Conic.translateLine, standardTangentAtOrigin,
      tangentLine,
      Conic.taylorConic, Conic.translateConic]
    unfold Conic.Contains Conic.evaluate at onConic
    have tangentConstant :
        conic.a * point.x + conic.b * point.y + 2 * conic.c =
          -(conic.a + 2 * conic.d * point.x + conic.e * point.y) *
              point.x -
            (conic.b + 2 * conic.f * point.y + conic.e * point.x) *
              point.y := by
      calc
        conic.a * point.x + conic.b * point.y + 2 * conic.c =
            -(conic.a + 2 * conic.d * point.x +
                conic.e * point.y) * point.x -
              (conic.b + 2 * conic.f * point.y +
                conic.e * point.x) * point.y +
              2 * (conic.d * point.x ^ 2 +
                conic.e * point.x * point.y +
                conic.f * point.y ^ 2 + conic.a * point.x +
                conic.b * point.y + conic.c) := by ring1
        _ = _ := by rw [onConic]; ring1
    rw [tangentConstant]
    exact ⟨by ring1, by ring1, by ring1⟩
  · exact tangentLine_contains conic point onConic nonSingular

end Purelib.Curves.Plane.Conic

end
