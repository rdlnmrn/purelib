module
import Purelib.Algebra.Quadratic.Ternary.Basic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Algebra.Quadratic.Ternary.Minkowski
import Purelib.Data.Rat.Fraction.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Algebra.Field.ExplicitField
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.LinearAlgebra.Coordinates3.Vector
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra.Quadratic

open Purelib.Algebra.Quadratic.Ternary.Basic

open Purelib.Data.Rat

open Purelib.LinearAlgebra

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.RationalMinkowski
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section RationalMinkowski

/-- One is nonzero in the constructive rational field. -/
theorem oneNonzero : (1 :
  Fraction.Basic.Rational) ≠ 0 := by decide
end RationalMinkowski
end Purelib.Geometry.Quadratic.Ternary.RationalMinkowski

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.RationalMinkowski
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section RationalMinkowski

/-- The rational Minkowski form used by the split-matrix specialization. -/
def form : Ternary.Basic.TernaryForm
  Fraction.Basic.Rational := TernaryForm.minkowski
  oneNonzero
end RationalMinkowski
end Purelib.Geometry.Quadratic.Ternary.RationalMinkowski

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.RationalMinkowski
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section RationalMinkowski

/-- The rational Minkowski form evaluates to `t² + r² - s²`. -/
theorem quadrance (vector :
  Coordinates3.Vector Fraction.Basic.Rational) :
    form.quadrance vector =
      vector.t ^ 2 + vector.r ^ 2 - vector.s ^ 2 := by
  exact TernaryForm.quadrance_minkowski oneNonzero vector
end RationalMinkowski
end Purelib.Geometry.Quadratic.Ternary.RationalMinkowski

end

section
@[expose] public section
namespace Purelib.Geometry.Quadratic.Ternary.RationalMinkowski
variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
section RationalMinkowski

/-- Two is nonzero in the constructive rational field. -/
theorem twoNonzero : (2 :
  Fraction.Basic.Rational) ≠ 0 := by decide
end RationalMinkowski
end Purelib.Geometry.Quadratic.Ternary.RationalMinkowski

end
