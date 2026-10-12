module
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Intervals

import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Basic

section
/-! Exact restoration of the canonical safe-cut grid. Saved reciprocals are
checked against the original Bézout majorants by multiplication. The finite
cut search and majorant arithmetic remain validation work; neither alternative
cuts nor merely sufficient clearance bounds identify the original grid. -/
@[expose] public section

namespace Purelib.Data.Rat.Inverse.Check

open Purelib.Data.Rat in
/-- A product equal to one with a positive rational factor identifies the other factor as its reciprocal. -/
theorem reciprocal_eq (bound majorant : Fraction.Rational) (positive : 0 <
  majorant)
    (product : bound * majorant = 1) : bound = 1 / majorant := by
  apply Fraction.Field.mul_right_cancel_of_ne (ne_of_gt positive)
  rw [Fraction.Field.div_mul_cancel_of_ne _ _ (ne_of_gt positive)]
  exact product
variable {p : (Purelib.Polynomial.Dense.Basic.DensePolynomial Purelib.Data.Gaussian.Basic.Canonical)} {degreeBound :
  Nat}
  (elimination : Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (box : Purelib.Geometry.Rational.Box) (proper : box.Proper)
end Purelib.Data.Rat.Inverse.Check

end
