module
public import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Data.Gaussian.Basic
public import Purelib.Polynomial.Dense.Division.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Evaluation

open Purelib.Data

open Purelib.Polynomial

section
@[expose] public section

/-!
# Dense polynomials over Gaussian coordinates

This module fixes the generic finite dense-polynomial algorithms to the
choice-free Gaussian coordinate implementation.  The small wrapper theorems
are audit points: their declaration closures include the concrete arithmetic
and polynomial implementations, not merely abstract algebraic hypotheses.
-/

namespace Purelib.Polynomial.Dense.Gaussian.Division

/-- The Gaussian quotient and remainder reconstruct the dividend at every Gaussian point. -/
theorem division_evaluation_equation (p q :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (z : Gaussian.Basic.Canonical) :
    (p.divMod q).remainder.eval z +
        q.eval z * (p.divMod q).quotient.eval z = p.eval z :=
  Dense.Basic.DensePolynomial.divMod_eval_equation p q z

end Purelib.Polynomial.Dense.Gaussian.Division

end
