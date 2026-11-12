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
open Purelib.Data.Rat.Fraction.Order
/-- The existing three-term original-carrier tail estimate with its unit finite bridge payment. -/
def synchronizationScale (leftScale rightScale : Fraction.Rational) : Fraction.Rational :=
  2 * (leftScale + 2 * (1 + rightScale))

/-- The retained original-carrier tail estimate has a nonnegative scale. -/
theorem synchronizationScale_nonnegative {leftScale rightScale : Fraction.Rational}
    (leftNonnegative : 0 ≤ leftScale) (rightNonnegative : 0 ≤ rightScale) :
    0 ≤ synchronizationScale leftScale rightScale :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg leftNonnegative (Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (by decide) rightNonnegative)))

/-- Eight times the sum of the four original retained error contributions. -/
def total (budget :
  Integration.Program.Comparison.Budget.JetErrorBudget) : Fraction.Rational :=
  8 * (budget.algebraic + budget.quadrature +
    budget.primitive + budget.synchronization)

/-- The retained comparison budget's total is nonnegative. -/
theorem total_nonnegative (budget :
  Integration.Program.Comparison.Budget.JetErrorBudget) : 0 <= budget.total :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg
      (add_nonneg
        (add_nonneg budget.algebraic_nonnegative
          budget.quadrature_nonnegative)
        budget.primitive_nonnegative)
      budget.synchronization_nonnegative)

/-- Retain numerical movement ceilings and the original closed-stage primitive payment.

The algebraic contribution concerns a checked exact coefficient identity.
The numerical model discrepancies belong to the supplied quadrature
ceiling; they are not set to zero by this constructor. The primitive unit
is the original closed-stage bound, and synchronization retains the actual
carrier tail-comparison ceiling. -/
def ofPrimitiveComparison (quadrature synchronization : Fraction.Rational)
    (quadratureNonnegative : 0 ≤ quadrature) (synchronizationNonnegative : 0 ≤ synchronization) :
    JetErrorBudget where
  algebraic := 0
  quadrature := quadrature
  primitive := 1
  synchronization := synchronization
  algebraic_nonnegative := by decide
  quadrature_nonnegative := quadratureNonnegative
  primitive_nonnegative := by decide
  synchronization_nonnegative := synchronizationNonnegative

/-- The original unit primitive payment fits inside the retained complete budget. -/
theorem one_le_total (budget : JetErrorBudget) (primitive : 1 ≤ budget.primitive) : 1 ≤ budget.total := by
  have first := Arithmetic.add_le_add_direct
    (add_nonneg budget.algebraic_nonnegative budget.quadrature_nonnegative) primitive
  rw [zero_add] at first
  have sum := Arithmetic.add_le_add_direct first budget.synchronization_nonnegative
  rw [add_zero] at sum
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct sum
    (by decide : (0 : Fraction.Rational) ≤ 8)
  rw [mul_one] at scaled
  exact (by decide : (1 : Fraction.Rational) ≤ 8).trans scaled

/-- The computed primitive-comparison budget is positive without an extra caller certificate. -/
theorem ofPrimitiveComparison_total_positive (quadrature synchronization : Fraction.Rational)
    (quadratureNonnegative : 0 ≤ quadrature) (synchronizationNonnegative : 0 ≤ synchronization) :
    0 < (ofPrimitiveComparison quadrature synchronization quadratureNonnegative synchronizationNonnegative).total :=
  (by decide : (0 : Fraction.Rational) < 1).trans_le (one_le_total _ (by exact le_refl 1))

end JetErrorBudget

end Purelib.Integration.Program.Comparison.Budget

end
