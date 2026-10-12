module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.LinearAlgebra.Coordinates3.Matrix

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

open Purelib

section
@[expose] public section

/-!
# Divine Proportions, Theorem 115: the Four point relation

The Euler function is the explicitly expanded three-by-three determinant from
the source.  Its coordinate proof is a direct polynomial identity for four
displayed points in a two-dimensional plane.  Exercises 17.3--17.6 record the
alternative expansion, the finite Cayley--Menger determinant, the quadratic
form of the relation, and the circumquadrance deduction.
-/

namespace Purelib.Geometry

variable {K : Type*} [ExplicitField K]

namespace Quadrilaterals.Basic.Quadrilateral

/-- An explicit four-by-four determinant, expanded along its first row. -/
def determinantFour
    (a₁₁ a₁₂ a₁₃ a₁₄
      a₂₁ a₂₂ a₂₃ a₂₄
      a₃₁ a₃₂ a₃₃ a₃₄
      a₄₁ a₄₂ a₄₃ a₄₄ : K) : K :=
  a₁₁ * Geometry.Quadrilaterals.Basic.Quadrilateral.determinantThree
      a₂₂ a₂₃ a₂₄ a₃₂ a₃₃ a₃₄ a₄₂ a₄₃ a₄₄ -
    a₁₂ * Geometry.Quadrilaterals.Basic.Quadrilateral.determinantThree
      a₂₁ a₂₃ a₂₄ a₃₁ a₃₃ a₃₄ a₄₁ a₄₃ a₄₄ +
    a₁₃ * Geometry.Quadrilaterals.Basic.Quadrilateral.determinantThree
      a₂₁ a₂₂ a₂₄ a₃₁ a₃₂ a₃₄ a₄₁ a₄₂ a₄₄ -
    a₁₄ * Geometry.Quadrilaterals.Basic.Quadrilateral.determinantThree
      a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ a₄₁ a₄₂ a₄₃
end Quadrilaterals.Basic.Quadrilateral

end Purelib.Geometry

end

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8: bordered-tridiagonal determinants

The determinant family in Exercise 8.8 is evaluated by its finite continuant
and last-column cofactor expansion.  The first four literal determinants from
the source are also checked independently.
-/

namespace Purelib.LinearAlgebra.Coordinates4.Determinant

variable {K : Type*} [ExplicitField K]

/-- Four-by-four determinant by its finite first-row cofactor expansion. -/
def determinantFour {R : Type*} [CommRing R]
    (a₀₀ a₀₁ a₀₂ a₀₃
      a₁₀ a₁₁ a₁₂ a₁₃
      a₂₀ a₂₁ a₂₂ a₂₃
      a₃₀ a₃₁ a₃₂ a₃₃ : R) : R :=
  a₀₀ * LinearAlgebra.Coordinates3.Matrix.determinantThree a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ -
    a₀₁ * LinearAlgebra.Coordinates3.Matrix.determinantThree a₁₀ a₁₂ a₁₃ a₂₀ a₂₂ a₂₃ a₃₀ a₃₂ a₃₃ +
    a₀₂ * LinearAlgebra.Coordinates3.Matrix.determinantThree a₁₀ a₁₁ a₁₃ a₂₀ a₂₁ a₂₃ a₃₀ a₃₁ a₃₃ -
    a₀₃ * LinearAlgebra.Coordinates3.Matrix.determinantThree a₁₀ a₁₁ a₁₂ a₂₀ a₂₁ a₂₂ a₃₀ a₃₁ a₃₂
end Purelib.LinearAlgebra.Coordinates4.Determinant

end
