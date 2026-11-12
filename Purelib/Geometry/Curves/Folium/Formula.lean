module
import Purelib.Curves.Plane.Folium.Basic
import Purelib.Curves.Plane.Folium.Parametrization
public import Purelib.Curves.Plane.Folium.Tangent.Discriminant

import Purelib.Algebra.Field.ExplicitField
import Purelib.Curves.Plane.Cubic.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs

open Purelib.Curves.Plane.Folium

open Purelib.Curves.Plane.Folium.Parametrization

open Purelib.Curves.Plane.Folium.Tangent.Discriminant

section
@[expose] public section

/-!
# Divine Proportions, Examples 19.5--19.8

The algebraic content of the decimal-field pictures is supplied by the
generic folium theorems.  The `F₁₃` pictures are checked here as closed
certificates on exactly the coordinates printed in the source.  We do not
install a field instance or enumerate the carrier to prove an exclusivity
claim.
-/

namespace Purelib.Geometry.Curves.Folium.Formula

open Purelib.Algebra

section

variable {K : Type*} [Field.ExplicitField K]

/-- The folium parametrization gives a point on the cubic when its denominator is nonzero. -/
theorem example_19_5 [Nontrivial K]
    (parameter : K)
    (denominatorNonzero : Parametrization.parameterDenominator parameter ≠ 0) :
    (Curves.Plane.Folium.curve (K := K)).Contains (Parametrization.parameterPoint
        parameter) :=
  Parametrization.parameterPoint_contains parameter denominatorNonzero

section
end

/-- The cleared tangent determinant equals the negative folium discriminant polynomial. -/
theorem example_19_8 (parameter : K) :
    4 * (3 * parameter * (3 * parameter ^ 2)) -
        (-(Parametrization.parameterDenominator parameter)) ^ 2 =
      -(Tangent.Discriminant.determinantPolynomial parameter) :=
  Tangent.Discriminant.four_mul_associatedMatrixDeterminant parameter

end

end Purelib.Geometry.Curves.Folium.Formula

end
