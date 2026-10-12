module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Curves.Plane.Conic.Basic
-- Conic.Basic publicly re-exports the retained numeral certificates.
import Purelib.Data.Nat.Order
-- Exposed translated coefficients retain this negation parent.
public import Purelib.Algebra.Group.Negation
public import Purelib.Geometry.Plane.Point.Affine
import Purelib.Geometry.Plane.Point.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

/-!
# Translation and Taylor records of conics

The translated conic retains its quadratic coefficients and nonzero
quadratic-part witness, while its linear and constant coefficients are explicit
polynomials in the offset. Negating a supplied point gives its Taylor conic and
the exact first-order coefficients at that point.
-/

section
namespace Purelib.Curves.Plane.Conic

open Purelib.Algebra
open Purelib.Curves.Plane
open Purelib.Geometry
open Purelib.Geometry.Plane.Point
open scoped Purelib.Data.Nat

open Purelib.Algebra.Group in
attribute [local instance high] Negation.subNegZeroMonoid

variable {K : Type*} [Field.ExplicitField K]

/-- The coefficient record of the translate `τ_B(q)` from Theorem 118.

The quadratic coefficients and their nonzero witness are retained.
Only the linear and constant coefficients are computed from the supplied
offset. -/
@[expose] public def translateConic (conic : Conic K) (offset : Geometry.Plane.Point K) :
  Conic K where
  d := conic.d
  e := conic.e
  f := conic.f
  a := conic.a - 2 * conic.d * offset.x - conic.e * offset.y
  b := conic.b - 2 * conic.f * offset.y - conic.e * offset.x
  c := conic.d * offset.x ^ 2 + conic.e * offset.x * offset.y +
    conic.f * offset.y ^ 2 - conic.a * offset.x -
    conic.b * offset.y + conic.c
  quadratic_nonzero := conic.quadratic_nonzero

/-- The polynomial identity in the proof of Theorem 118.

Evaluating the translated record at the point translated by that same offset
recovers evaluation of the original conic at the original point. -/
public theorem translateConic_evaluate
    (conic : Conic K) (offset point : Geometry.Plane.Point K) :
    (Conic.translateConic conic offset).evaluate
        (Affine.translationPoint offset.x offset.y point) =
      conic.evaluate point := by
  unfold Conic.translateConic Conic.evaluate Affine.translationPoint
  ring1

/-- Theorem 118 (Translate of a conic): translation of a point transports
incidence to the explicitly translated conic, in both directions.

The equality of the original polynomial evaluations transports incidence
without replacing either retained point or conic record. -/
public theorem translate_of_conic
    (conic : Conic K) (offset point : Geometry.Plane.Point K) :
    conic.Contains point ↔
      (Conic.translateConic conic offset).Contains
        (Affine.translationPoint offset.x offset.y point) := by
  unfold Conic.Contains
  rw [Conic.translateConic_evaluate]

/-- The Taylor conic `q_A=τ_{-A}(q)`, which moves `A` to the origin.

The translation operation is applied to the negated coordinates of
the supplied point, retaining the conic coefficients and nonzero witness. -/
@[expose] public def taylorConic (conic : Conic K) (point : Geometry.Plane.Point K) : Conic K
  :=
  Conic.translateConic conic ⟨-point.x, -point.y⟩

/-- A point on a conic moves to the origin of its standard Taylor conic.

The supplied incidence witness identifies the constant coefficient of the
retained Taylor conic with zero. -/
public theorem taylorConic_isStandard
    (conic : Conic K) (point : Geometry.Plane.Point K) (onConic : conic.Contains point) :
    (Conic.taylorConic conic point).IsStandard := by
  unfold Conic.IsStandard Conic.taylorConic Conic.translateConic
  unfold Conic.Contains Conic.evaluate at onConic
  calc
    conic.d * (-point.x) ^ 2 +
          conic.e * (-point.x) * (-point.y) +
          conic.f * (-point.y) ^ 2 - conic.a * (-point.x) -
          conic.b * (-point.y) + conic.c =
      conic.d * point.x ^ 2 + conic.e * point.x * point.y +
        conic.f * point.y ^ 2 + conic.a * point.x +
        conic.b * point.y + conic.c := by ring1
    _ = 0 := onConic

/-- The linear coefficients of the Taylor conic are the two first-order
coefficients at the base point.

The two equalities identify the translated linear coefficients with
their explicit scalar formulas at the supplied base point. -/
public theorem taylorConic_linear_coefficients
    (conic : Conic K) (point : Geometry.Plane.Point K) :
    (Conic.taylorConic conic point).a =
        conic.a + 2 * conic.d * point.x + conic.e * point.y ∧
      (Conic.taylorConic conic point).b =
        conic.b + conic.e * point.x + 2 * conic.f * point.y := by
  unfold Conic.taylorConic Conic.translateConic
  constructor <;> ring1

/-- Non-singularity at `A` is exactly non-singularity of the linear part of the
Taylor conic at the origin.

The original nonsingularity disjunction selects a nonzero displayed
coefficient; the coefficient identities transport that same witness to the
Taylor conic. -/
public theorem taylorConic_linear_nonzero
    (conic : Conic K) (point : Geometry.Plane.Point K)
    (nonSingular : conic.IsNonSingularAt point) :
    (Conic.taylorConic conic point).a ≠ 0 ∨
      (Conic.taylorConic conic point).b ≠ 0 := by
  rw [Conic.taylorConic_linear_coefficients conic point |>.1,
    Conic.taylorConic_linear_coefficients conic point |>.2]
  exact nonSingular
end Purelib.Curves.Plane.Conic
end
