module

import Purelib.Polynomial.Dense.Basic
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field

/-!
# Positive degree of dense Gaussian polynomials

A positive natural degree excludes the empty normalized coefficient table.
The original Boolean zero test and coefficient count determine that conclusion.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Degree

open Purelib.Polynomial.Dense.Basic (DensePolynomial)
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

namespace Linear

/-- A Gaussian polynomial of positive natural degree has a false zero test.

If the original normalized coefficient table were empty, its coefficient count
and natural degree would both be zero, contradicting the retained positive bound. -/
public theorem isZero_false_of_natDegree_pos
    {p : Dense} (positive : 0 < p.natDegree) : p.isZero = false := by
  cases zeroTest : p.isZero with
  | false => rfl
  | true =>
      have countZero : p.degreeCount = 0 :=
        DensePolynomial.degreeCount_eq_zero_of_isZero zeroTest
      have degreeZero : p.natDegree = 0 :=
        congrArg (fun count : Nat => count - 1) countZero
      rw [degreeZero] at positive
      exact (Nat.not_lt_zero 0 positive).elim

end Linear

namespace Global

/-- A Gaussian polynomial of positive natural degree is nonzero.

Its original Boolean zero test is false because an empty normalized coefficient
list would force degree zero. The bound concerns the retained polynomial itself. -/
public theorem isZero_false_of_natDegree_pos
    {p : Dense} (degreePositive : 0 < p.natDegree) : p.isZero = false :=
  Linear.isZero_false_of_natDegree_pos degreePositive

end Global

end Purelib.Polynomial.Dense.Gaussian.Degree
