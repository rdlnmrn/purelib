import mathlib.RFAP.ConstructiveGaussian
import mathlib.RFAP.ComputablePolynomial

/-!
# Dense polynomials over constructive Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

namespace RFAP.ConstructivePolynomial

abbrev Coordinate := RFAP.ConstructiveFraction.Rational
abbrev Gaussian := RFAP.ConstructiveGaussian.Gaussian
abbrev GaussianPolynomial :=
  RFAP.ComputablePolynomial.DensePolynomial Gaussian

open RFAP.ComputablePolynomial.DensePolynomial

theorem product_isZero_false {p q : GaussianPolynomial}
    (hp : p.isZero = false) (hq : q.isZero = false) :
    (p * q).isZero = false :=
  isZero_mul_eq_false hp hq

theorem division_evaluation_equation (p q : GaussianPolynomial) (z : Gaussian) :
    (p.divMod q).remainder.eval z +
        q.eval z * (p.divMod q).quotient.eval z = p.eval z :=
  divMod_eval_equation p q z

end RFAP.ConstructivePolynomial
