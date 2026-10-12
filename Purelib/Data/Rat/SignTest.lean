module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Order.PositiveScale
meta import Purelib.Elab.Deriving.Repr
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Rat.Fraction.Field

section
@[expose] public section

/-!
# Finite Hermitian formulas for raw CCL parser states

Every predicate in an arbitrary finite raw-parser state is compiled into a
finite Boolean formula whose atoms are signs of four-coefficient rational
Hermitian forms.  Unfinished sector prefixes use the direct finite
disjunction of their `8/4/2` candidate rows.  This keeps the implementation
small while preserving the exact weak/strict boundary convention.
-/

namespace Purelib

namespace Data.Rat

/-- The six decidable sign relations of a rational value to zero.

Each constructor denotes one of strict negativity, nonpositivity, zero, nonzero, nonnegativity or strict positivity.
Satisfaction is interpreted separately as a decidable proposition on the canonical rational carrier. -/
inductive SignTest where
  /-- Require a strictly negative rational. -/ | negative
  /-- Require a rational at most zero. -/ | nonpositive
  /-- Require rational equality to zero. -/ | zero
  /-- Require rational inequality to zero. -/ | nonzero
  /-- Require a rational at least zero. -/ | nonnegative
  /-- Require a strictly positive rational. -/ | positive
deriving DecidableEq

derive_exposed_repr SignTest

end Data.Rat
section SignTest

open Purelib.Data.Rat
namespace Data.Rat.SignTest

/-- Interpret a retained sign test as its exact rational equality or order proposition. -/
def Holds : SignTest → Fraction.Rational → Prop
  | .negative, value => value < 0
  | .nonpositive, value => value ≤ 0
  | .zero, value => value = 0
  | .nonzero, value => value ≠ 0
  | .nonnegative, value => 0 ≤ value
  | .positive, value => 0 < value

end Data.Rat.SignTest
namespace CCL.Boundary.Formula.SignTest

/-- Decide satisfaction of a sign test using the concrete rational equality and order decisions. -/
instance (test : Data.Rat.SignTest) (value : Fraction.Rational) :
    Decidable (test.Holds value) := by
  cases test <;> simp only [Data.Rat.SignTest.Holds] <;> infer_instance

end CCL.Boundary.Formula.SignTest
namespace Data.Rat.SignTest

/-- Multiplication by a positive rational preserves and reflects each of the six sign tests. -/
theorem holds_mul_pos_iff
    (test : SignTest) (factor value : Fraction.Rational) (positive : 0 < factor) :
    test.Holds (factor * value) ↔ test.Holds value := by
  have identity : factor * value = factor * (value - 0) := by ring1
  cases test with
  | negative =>
      exact (Order.PositiveScale.compare_lt_iff positive identity).symm
  | nonpositive =>
      exact (Order.PositiveScale.compare_le_iff positive identity).symm
  | zero =>
      exact (Order.PositiveScale.compare_eq_iff positive identity).symm
  | nonzero =>
      exact not_congr (Order.PositiveScale.compare_eq_iff positive identity).symm
  | nonnegative =>
      exact (Order.PositiveScale.compare_ge_iff positive identity).symm
  | positive =>
      exact (Order.PositiveScale.compare_gt_iff positive identity).symm

end Data.Rat.SignTest
end SignTest
end Purelib

end

section
@[expose] public section

/-!
# Box stability of finite CCL formulas

If every Hermitian atom in a finite branch formula has a strict box-sign
certificate, evaluating the formula at any one point decides it everywhere
in that box.  The certificate search is structural recursion over the finite
formula; it neither enumerates points nor forms a root set.
-/

namespace Purelib.Data.Rat.SignTest

open Purelib.Data.Rat
/-- Any two negative rationals satisfy exactly the same retained sign tests. -/
public theorem holds_iff_of_negative
    (test : SignTest) {left right : Fraction.Rational}
    (leftNegative : left < 0) (rightNegative : right < 0) :
    test.Holds left ↔ test.Holds right := by
  cases test with
  | negative => exact iff_of_true leftNegative rightNegative
  | nonpositive => exact iff_of_true leftNegative.le rightNegative.le
  | zero => exact iff_of_false (ne_of_lt leftNegative) (ne_of_lt rightNegative)
  | nonzero => exact iff_of_true (ne_of_lt leftNegative) (ne_of_lt rightNegative)
  | nonnegative =>
      exact iff_of_false (not_le_of_gt leftNegative) (not_le_of_gt rightNegative)
  | positive =>
      exact iff_of_false (not_lt_of_ge leftNegative.le)
        (not_lt_of_ge rightNegative.le)

/-- Any two positive rationals satisfy exactly the same retained sign tests. -/
public theorem holds_iff_of_positive
    (test : SignTest) {left right : Fraction.Rational}
    (leftPositive : 0 < left) (rightPositive : 0 < right) :
    test.Holds left ↔ test.Holds right := by
  cases test with
  | negative =>
      exact iff_of_false (not_lt_of_ge leftPositive.le)
        (not_lt_of_ge rightPositive.le)
  | nonpositive =>
      exact iff_of_false (not_le_of_gt leftPositive)
        (not_le_of_gt rightPositive)
  | zero =>
      exact iff_of_false (Ne.symm (ne_of_lt leftPositive))
        (Ne.symm (ne_of_lt rightPositive))
  | nonzero =>
      exact iff_of_true (Ne.symm (ne_of_lt leftPositive))
        (Ne.symm (ne_of_lt rightPositive))
  | nonnegative => exact iff_of_true leftPositive.le rightPositive.le
  | positive => exact iff_of_true leftPositive rightPositive

end Purelib.Data.Rat.SignTest

end
