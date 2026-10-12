module
import Purelib.Data.List.Reverse

import Purelib.Algebra.Field.ExplicitField
public import Purelib.Polynomial.Ascending.Integer.QuadraticTrace.Evaluation
public import Purelib.Polynomial.Dense.Rational.AscendingInteger.Basic
import Purelib.Polynomial.Dense.Rational.AscendingInteger.Certificate
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Algebra.Quadratic.TracePair.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Basic

open Purelib.Algebra.Field

open Purelib

open Purelib.Polynomial

section
@[expose] public section

/-!
# A finite quadratic trace norm on integer coefficient lists

For a displayed trace parameter `t`, let `a` satisfy
`a² = t*a - 1`.  Every integer polynomial in `a` reduces to a pair
`A(t) + B(t)*a`; its conjugate norm is
`A² + t*A*B + B²`.  All coefficient programs below are primitive
recursions on finite `List Int` values.
-/

namespace Purelib.Algebra.Quadratic.TracePair

section TracePair

variable {K : Type*} [ExplicitField K]

open Purelib.Data.List in
/-- A coefficient identity proved in the canonical rational embedding can
be evaluated at the formal quadratic generator over every explicit field.
Only finite list normalization is involved. -/
theorem eval_eq_of_ofAscending_eq
    {left right : List Int}
    (equal :
      Dense.Rational.AscendingInteger.Basic.ofAscending left =
        Dense.Rational.AscendingInteger.Basic.ofAscending right)
    (trace : K) :
    eval left trace = eval right
      trace := by
  have normalized :=
    Dense.Rational.AscendingInteger.Certificate.normalized_reverse_eq_of_ofAscending_eq equal
  calc
    eval left trace =
        eval ((left.reverse.dropWhile fun value => value = 0).reverse)
          trace := by
      rw [eval_reverse_dropWhile_zero left.reverse trace,
        Reverse.reverse_reverse]
    _ = eval ((right.reverse.dropWhile fun value => value = 0).reverse)
          trace := by rw [normalized]
    _ = eval right trace := by
      rw [eval_reverse_dropWhile_zero right.reverse trace,
        Reverse.reverse_reverse]
end TracePair

end Purelib.Algebra.Quadratic.TracePair

end
