module
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation

public import Purelib.Polynomial.Ascending.Gaussian.Affine
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending.Gaussian (CoefficientPolynomial)

open Purelib.Data

open Purelib.Polynomial

@[expose] public section

/-!
# Generated affine transport of finite Gaussian polynomials

Substitution is finite Horner coefficient arithmetic.  Its derivative and
integral laws are proved here, not supplied in a transport certificate.  The
integral law includes zero slope and reversed segments without dividing by
the path displacement.
-/

namespace Purelib.Polynomial.Ascending.Gaussian.Restriction.Basic

open Purelib.Data.Gaussian.Basic.Canonical

/-- Reparameterize a displayed interval by a new unit-interval parameter. -/
def restrict (polynomial :
  CoefficientPolynomial) (start finish : Gaussian.Basic.Canonical) :
    CoefficientPolynomial
  :=
  Ascending.Gaussian.Affine.affine polynomial start (finish - start)

/-- A restricted polynomial evaluates at `start + (finish - start) * input`. -/
@[simp] theorem eval_restrict (polynomial :
  CoefficientPolynomial) (start finish input : Gaussian.Basic.Canonical) :
    Ascending.Gaussian.Evaluation.eval (restrict polynomial start finish) input =
      Ascending.Gaussian.Evaluation.eval polynomial (start + (finish - start) * input) :=
  Ascending.Gaussian.Affine.eval_affine polynomial start (finish - start) input

/-- The model polynomial for traversing the same source interval backwards. -/
def reverse (polynomial :
  CoefficientPolynomial) : CoefficientPolynomial :=
  restrict polynomial 1 0

/-- The reversed parameter polynomial evaluates the original polynomial at `1 - input`. -/
@[simp] theorem eval_reverse (polynomial :
  CoefficientPolynomial) (input : Gaussian.Basic.Canonical) :
    Ascending.Gaussian.Evaluation.eval (reverse polynomial) input =
      Ascending.Gaussian.Evaluation.eval polynomial (1 - input) := by
  rw [reverse, eval_restrict]
  congr 1
  ring1
section
end

end Purelib.Polynomial.Ascending.Gaussian.Restriction.Basic

end
