module

public import Purelib.Polynomial.Dense.Gaussian.Squarefree.RootCofactor
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Exclusion.Uniform
public import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

/-! # Coefficient-derived nonvanishing neighborhoods of original squarefree root cofactors -/

public section

namespace Purelib.Polynomial.Dense.Gaussian.Squarefree.RootCofactor

open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Geometry.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat

/-- One quarter of the squared norm of the same retained nonzero cofactor point value. -/
@[expose] def margin {polynomial : CoefficientPolynomial} {point : Canonical}
    (certificate : RootCofactor polynomial point) : Fraction.Rational := normSq certificate.value / 4

/-- The retained cofactor point value supplies a strictly positive quarter-norm margin. -/
theorem margin_pos {polynomial : CoefficientPolynomial} {point : Canonical}
    (certificate : RootCofactor polynomial point) : 0 < certificate.margin :=
  Fraction.Order.Field.div_pos_direct (Purelib.Data.Gaussian.Norm.Basic.normSq_pos certificate.valueNonzero) (by decide)

/-- Compute the quotient's uniform nonvanishing radius from its original coefficients and cached point value. -/
@[expose] def radius {polynomial : CoefficientPolynomial} {point : Canonical}
    (certificate : RootCofactor polynomial point) (ambient : Box) : Fraction.Rational :=
  Bounds.Box.Exclusion.Uniform.uniformExclusionRadius certificate.result.quotient ambient (normSq certificate.value)

/-- The same retained nonzero point value makes the original coefficient-derived neighborhood radius positive. -/
theorem radius_pos {polynomial : CoefficientPolynomial} {point : Canonical}
    (certificate : RootCofactor polynomial point) (ambient : Box) : 0 < certificate.radius ambient :=
  Bounds.Box.Exclusion.Uniform.uniformExclusionRadius_pos certificate.result.quotient ambient
    (Purelib.Data.Gaussian.Norm.Basic.normSq_pos certificate.valueNonzero)

/-- Every ambient point in the computed neighborhood retains the same positive cofactor squared-norm lower bound.

The original quotient's box Lipschitz fold controls variation from its cached
point value. Four times that variation is below the retained leading quadrance;
the finite two-leg norm inequality gives its positive quarter-norm margin.
-/
theorem normSq_eval_lower {polynomial : CoefficientPolynomial} {point : Canonical}
    (certificate : RootCofactor polynomial point) {ambient : Box} {value : Canonical}
    (pointInside : ambient.Contains point) (valueInside : ambient.Contains value)
    (close : normSq (value - point) ≤ certificate.radius ambient ^ 2) :
    certificate.margin ≤ normSq (certificate.result.quotient.eval value) := by
  have variation := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound
    certificate.result.quotient valueInside pointInside
  rewrite [certificate.value_eq] at variation
  have bounded := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct variation
    (by decide : (0 : Fraction.Rational) ≤ 4)
  have radiusBound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct close
    (Bounds.Box.Exclusion.Uniform.exclusionCoefficient_pos certificate.result.quotient ambient).le
  have same : 4 * (Bounds.Box.denseLipschitzBound certificate.result.quotient ambient * normSq (value - point)) =
      Bounds.Box.Exclusion.Uniform.exclusionCoefficient certificate.result.quotient ambient * normSq (value - point) :=
    (Fraction.Field.mul_assoc _ _ _).symm
  have strict := Bounds.Box.Exclusion.Uniform.uniform_exclusion_margin certificate.result.quotient ambient
    (Purelib.Data.Gaussian.Norm.Basic.normSq_pos certificate.valueNonzero)
  have tail := bounded.trans (same.trans_le (radiusBound.trans strict.le))
  exact Purelib.Data.Gaussian.Norm.Bounds.lower_of_tail (certificate.result.quotient.eval value)
    certificate.value tail

end Purelib.Polynomial.Dense.Gaussian.Squarefree.RootCofactor

end
