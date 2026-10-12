module
public import Purelib.Data.Rat.Interval.Proper
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Rational.Basic
public import Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Reduced.Parity
import Mathlib.Algebra.Group.Even
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Data.Int.Arithmetic

open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)

open Purelib.Data.Rat

open Purelib.Polynomial

section
@[expose] public section

/-!
# Gcd-reduced constructive Sturm root counts

A univariate curve event is represented by the signed remainder chain of a
polynomial and its derivative after their executable common gcd has been
divided out.  This module packages that reduction using only the finite dense
Euclidean program.  It also constructs one bounded-search cut avoiding every
member of the reduced chain.

The doubled count is an integer endpoint-variation difference.  No roots,
ordered closure, or set of parameter values is formed.
-/

namespace Purelib.RootIsolation.Sturm.Count.Basic

/-- Doubled Sturm count for the squarefree part of a displayed polynomial. -/
def sturmRootCount2 (p : CoordinatePolynomial)
  (lower
  upper : Fraction.Rational) : Int :=
  Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2 (Dense.Derivative.derivative p) p lower upper

section
open Purelib.RootIsolation
/-- Split the doubled reduced Sturm count at any displayed intermediate parameter. -/
theorem sturmRootCount2_add
    (p : CoordinatePolynomial) (lower middle upper : Fraction.Rational) :
    sturmRootCount2 p lower upper =
      sturmRootCount2 p lower middle + sturmRootCount2 p middle upper :=
  Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2_add _ _ _ _ _

/-- Reversing the interval negates its doubled reduced Sturm count. -/
theorem sturmRootCount2_reverse
    (p : CoordinatePolynomial) (lower upper : Fraction.Rational) :
    sturmRootCount2 p upper lower = -sturmRootCount2 p lower upper :=
  Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2_reverse _ _ _ _

end

open Purelib.Data.Int in
open Purelib.RootIsolation in
/-- The doubled reduced Sturm count on a repeated endpoint is zero. -/
@[simp] theorem sturmRootCount2_refl
    (p : CoordinatePolynomial) (parameter : Fraction.Rational) :
    sturmRootCount2 p parameter parameter = 0 := by
  unfold sturmRootCount2 Dense.Rational.CauchyIndex.Reduced.reducedCauchyIndex2
  unfold Dense.Rational.CauchyIndex.Basic.Sturm.cauchyIndex2
  exact Arithmetic.sub_eq_zero_of_eq rfl

open Purelib.RootIsolation in
/-- Nonzero polynomial evaluations at both endpoints make the doubled reduced Sturm count even. -/
theorem sturmRootCount2_even
    {p : CoordinatePolynomial}
    {lower upper : Fraction.Rational}
    (lowerClear : p.eval lower ≠ 0) (upperClear : p.eval upper ≠ 0) :
    Even (sturmRootCount2 p lower upper) :=
  Dense.Rational.CauchyIndex.Reduced.Parity.reducedCauchyIndex2_even lowerClear upperClear
end Purelib.RootIsolation.Sturm.Count.Basic

end

namespace Purelib.RootIsolation.Sturm.Count.Basic

open Purelib

/-- The doubled Sturm count of a polynomial on the endpoints of one proper rational cell. -/
@[expose] public def cellCount2 (event :
  Dense.Basic.RationalPolynomial) (cell : Data.Rat.Interval.Proper.Cell) : Int :=
  sturmRootCount2 event cell.interval.lower cell.interval.upper

end Purelib.RootIsolation.Sturm.Count.Basic
