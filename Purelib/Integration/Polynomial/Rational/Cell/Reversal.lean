module

import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Polynomial.Rational.Cell.Basic
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Integral
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# General certified integration by finite path refinements

An integrand is supplied operationally: at each natural refinement it returns
one finite path of rational polynomial cell models and finite rational sample
certificates.  The integration program sums the exact polynomial cell
integrals.  A rational geometric modulus and a finite later-refinement
certificate turn those displayed sums into an ordinary productive CCL name.

There is no measure, completed partition, function-as-an-infinite-set, or
infinitesimal.  The only universal refinements are natural-number calls to the
supplied finite program.
-/

namespace Purelib.Integration.Polynomial.Rational.Cell.Basic
namespace CellModel

open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
set_option genInjectivity false in
/-- A retained replacement polynomial with the same unit-interval definite integral as the original cell polynomial.

The certificate specifies equality of integrals; it does not assert a pointwise variable-reversal formula. -/
structure ReversalCertificate (cell :
  Rational.Cell.Basic.CellModel) where
  /-- The supplied polynomial used on the reversed cell. -/ reversedPolynomial : Rational.Basic.CoefficientPolynomial
  /-- Its unit-interval definite integral equals the original cell polynomial's integral. -/ integral_eq :
    Rational.Integral.definiteIntegral reversedPolynomial 0 1 =
      Rational.Integral.definiteIntegral cell.polynomial 0 1

constructive_injectivity ReversalCertificate

open Purelib.Integration.Polynomial in
/-- Reverse the original cell endpoints using the supplied integral-preserving polynomial.

The local allowance and its nonnegativity proof are retained, while the observation list is empty. -/
def reverse (cell : Rational.Cell.Basic.CellModel)
  (certificate : ReversalCertificate cell) :
    Rational.Cell.Basic.CellModel :=
  { start := cell.finish
    finish := cell.start
    polynomial := certificate.reversedPolynomial
    localAllowance := cell.localAllowance
    localAllowance_nonneg := cell.localAllowance_nonneg
    observations := [] }

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
/-- Reversing the endpoints with an integral-preserving polynomial negates the cell's integral sample. -/
theorem reverse_integralSample (cell :
  Rational.Cell.Basic.CellModel)
    (certificate : ReversalCertificate cell) :
    (cell.reverse certificate).integralSample = -cell.integralSample := by
  unfold reverse Rational.Cell.Basic.CellModel.integralSample
    Rational.Cell.Basic.CellModel.displacement
  rw [certificate.integral_eq]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im] <;> ring1
end CellModel

end Purelib.Integration.Polynomial.Rational.Cell.Basic

end
