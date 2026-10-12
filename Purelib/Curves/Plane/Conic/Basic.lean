module

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Plane.Point.Basic
-- Public first-order coefficients retain these original natural numeral certificates.
public import Purelib.Data.Nat.Order
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
meta import Mathlib.Tactic.Linter.Lint
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Displayed conic coefficients and incidence

A conic retains six coefficients and a constructive nonzero quadratic-part
witness. Its original evaluation, incidence, standardness and first-order
nonsingularity predicates read those same coefficients and supplied points.
-/

section
namespace Purelib.Curves.Plane

open Purelib.Algebra.Field
open Purelib.Geometry
open scoped Purelib.Data.Nat

set_option genInjectivity false in
/-- A displayed conic `⟨d : e : f : a : b : c⟩` with nonzero quadratic part.

The six retained coefficients retain their order and scalar carrier. The
quadratic-part witness certifies that at least one of the first three
coefficients is nonzero without adding executable fields.
-/
public structure Conic (K : Type*) [Zero K] where
  /-- The coefficient of x squared. -/ d : K
  /-- The coefficient of the mixed monomial x times y. -/ e : K
  /-- The coefficient of y squared. -/ f : K
  /-- The coefficient of x. -/ a : K
  /-- The coefficient of y. -/ b : K
  /-- The constant coefficient. -/ c : K
  /-- At least one displayed quadratic coefficient is nonzero. -/ quadratic_nonzero : d ≠ 0 ∨ e ≠ 0 ∨ f ≠ 0

constructive_injectivity Conic

namespace Conic

variable {K : Type*} [ExplicitField K]

/-- Evaluate the displayed quadratic polynomial at a point.

The six coefficients and supplied point coordinates determine the
finite sum of three quadratic, two linear and one constant term.
-/
@[expose] public def evaluate (conic : Conic K) (point : Geometry.Plane.Point K) : K :=
  conic.d * point.x ^ 2 + conic.e * point.x * point.y +
    conic.f * point.y ^ 2 + conic.a * point.x +
    conic.b * point.y + conic.c

/-- Incidence with a conic is the finite polynomial equation `q(X) = 0`.

The equation uses evaluation of the same coefficient record at the
supplied point, retaining both objects in its proposition.
-/
@[expose] public def Contains (conic : Conic K) (point : Geometry.Plane.Point K) : Prop :=
  conic.evaluate point = 0
/-- A conic is standard when it contains the origin.

For the coefficient polynomial this condition is exactly vanishing of
its retained constant coefficient.
-/
@[expose] public def IsStandard (conic : Conic K) : Prop := conic.c = 0

/-- Require a nonzero first-order coefficient at a displayed point.

The constructive disjunction uses the two gradient coefficients at
the supplied point. Its scalar numeral certificates retain the same field and
coefficient operations.
-/
@[expose] public def IsNonSingularAt (conic : Conic K) (point : Geometry.Plane.Point K) : Prop :=
  conic.a + 2 * conic.d * point.x + conic.e * point.y ≠ 0 ∨
    conic.b + conic.e * point.x + 2 * conic.f * point.y ≠ 0
end Conic
end Purelib.Curves.Plane
end
