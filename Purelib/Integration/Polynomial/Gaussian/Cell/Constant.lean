module

import Purelib.Data.Gaussian.Basic
public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Basic
namespace CellModel

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial.Ascending in
set_option genInjectivity false in
/-- A retained Gaussian coefficient whose constant polynomial is the exact original cell polynomial. -/
structure ConstantCertificate (cell :
  Basic.CellModel) where
  /-- The retained Gaussian constant coefficient. -/ coefficient : Basic.Canonical
  /-- The original cell polynomial equals the constant polynomial of this coefficient. -/ polynomial_eq :
    cell.polynomial =
    Gaussian.Basic.constant coefficient

constructive_injectivity ConstantCertificate

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial.Ascending in
/-- Certify the supplied exact constant cell with its original coefficient. -/
def exactConstantCertificate (start finish
  coefficient : Basic.Canonical) :
    ConstantCertificate
      (Basic.CellModel.exact start finish (Gaussian.Basic.constant coefficient))
    where
  coefficient := coefficient
  polynomial_eq := rfl
end CellModel
namespace CellModel

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial.Ascending in
/-- A constant Gaussian polynomial cell integrates to its original displacement times its retained coefficient. -/
theorem integralSample_constant (cell :
  Basic.CellModel)
    (coefficient : Basic.Canonical)
    (polynomial_eq : cell.polynomial =
      Gaussian.Basic.constant coefficient) :
    cell.integralSample = cell.displacement * coefficient := by
  unfold Basic.CellModel.integralSample
  rw [polynomial_eq,
    Gaussian.Integral.definiteIntegral_constant]
  apply Basic.ext <;>
    simp only [Basic.CellModel.displacement, Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im,
      Basic.zero_re, Basic.zero_im, Basic.one_re, Basic.one_im] <;> ring1
end CellModel

end Purelib.Integration.Polynomial.Gaussian.Cell.Basic

end
