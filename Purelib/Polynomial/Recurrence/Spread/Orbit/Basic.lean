module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Recurrence.Spread.Basic
import Mathlib.Algebra.Ring.Defs

open Purelib.Algebra.Field

open Purelib.Polynomial

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8 finite-field examples

Every table and orbit below is an executable bounded calculation in an
explicit finite carrier.  Periodicity at arbitrary requested indices is then
deduced from two checked recurrence seeds.
-/

namespace Purelib.Polynomial.Recurrence.Spread.Orbit.Basic

section

variable {K : Type*} [ExplicitField K]

/-- The requested finite prefix `[S₀(s),…,Sₙ₋₁(s)]`. -/
def spreadOrbitPrefix (length : Nat) (value : K) : List K :=
  List.ofFn (fun index : Fin length => Recurrence.Spread.Basic.spreadPolynomial index.1 value)

/-- A zero at the stated index with no preceding positive-index zero.

The bounded minimality condition checks exactly the indices from one through order minus one. Positivity of the supplied
order is not part of this predicate. -/
def HasSpreadOrder (value : K) (order : Nat) : Prop :=
  Recurrence.Spread.Basic.spreadPolynomial order value = 0 ∧
    ∀ index : Fin (order - 1),
      Recurrence.Spread.Basic.spreadPolynomial (index.1 + 1) value ≠ 0

end

end Purelib.Polynomial.Recurrence.Spread.Orbit.Basic

end
