module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Synchronized finite Legendre period jets

The ordinary period layer certifies differentials of the form `x^k dx/y`.
Parameter differentiation of the Legendre family also needs the odd powers
`y^3` and `y^5`.  This module adds only that narrow algebraic-integrand
interface.  A finite observation evaluates an explicit polynomial numerator,
uses the already certified sheet value, and builds the odd reciprocal power
from repeated constructive multiplication of `1/y`.

Value, first-derivative, and second-derivative programs are then locked to the
same displayed lifted cycle and exposed through one finite request table.
-/

namespace Purelib.Integration.Program.Comparison.Budget

open Purelib.Data.Rat in
set_option genInjectivity false in
/-- Four separate nonnegative error contributions for a retained integration-program comparison.

Algebraic, quadrature, primitive and synchronization errors remain distinct before their common eightfold total is
formed. -/
structure JetErrorBudget where
  /-- The retained algebraic error contribution. -/ algebraic : Fraction.Rational
  /-- The retained quadrature error contribution. -/ quadrature : Fraction.Rational
  /-- The retained primitive error contribution. -/ primitive : Fraction.Rational
  /-- The retained synchronization error contribution. -/ synchronization : Fraction.Rational
  /-- The original algebraic contribution is nonnegative. -/ algebraic_nonnegative : 0 <= algebraic
  /-- The original quadrature contribution is nonnegative. -/ quadrature_nonnegative : 0 <= quadrature
  /-- The original primitive contribution is nonnegative. -/ primitive_nonnegative : 0 <= primitive
  /-- The original synchronization contribution is nonnegative. -/ synchronization_nonnegative : 0 <= synchronization

constructive_injectivity JetErrorBudget

namespace JetErrorBudget

open Purelib
open Purelib.Data.Rat
/-- Eight times the sum of the four original retained error contributions. -/
def total (budget :
  Integration.Program.Comparison.Budget.JetErrorBudget) : Fraction.Rational :=
  8 * (budget.algebraic + budget.quadrature +
    budget.primitive + budget.synchronization)

/-- The retained comparison budget's total is nonnegative. -/
theorem total_nonnegative (budget :
  Integration.Program.Comparison.Budget.JetErrorBudget) : 0 <= budget.total :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (add_nonneg
        (add_nonneg budget.algebraic_nonnegative
          budget.quadrature_nonnegative)
        budget.primitive_nonnegative)
      budget.synchronization_nonnegative)

end JetErrorBudget

end Purelib.Integration.Program.Comparison.Budget

end
