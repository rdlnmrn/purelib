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

namespace Purelib.Integration.Polynomial.Gaussian.Cell
section CellModel

open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial.Ascending in
set_option genInjectivity false in
/-- A retained replacement polynomial with the same unit-interval integral as the original cell polynomial. -/
structure Basic.CellModel.ReversalCertificate (cell :
  Basic.CellModel) where
  /-- The retained replacement polynomial for the reversed cell. -/ reversedPolynomial :
    Polynomial.Ascending.Gaussian.CoefficientPolynomial
  /-- Its unit-interval integral equals that of the original cell polynomial. -/ integral_eq :
    Gaussian.Integral.definiteIntegral reversedPolynomial 0 1 =
      Gaussian.Integral.definiteIntegral cell.polynomial 0 1

constructive_injectivity Basic.CellModel.ReversalCertificate

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Polynomial.Ascending in
/-- Certify the exact original constant polynomial as its own integral-preserving reversal polynomial. -/
def Reversal.CellModel.ReversalCertificate.constant (cell :
  Basic.CellModel) (value : Basic.Canonical)
    (polynomial_eq : cell.polynomial =
      Gaussian.Basic.constant value) :
    Basic.CellModel.ReversalCertificate cell where
  reversedPolynomial := Gaussian.Basic.constant value
  integral_eq := by rw [polynomial_eq]

open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- Reverse the original cell endpoints using its certified replacement polynomial and retained allowance.

The original nonnegative local allowance is preserved; the reversed model has an empty observation list. -/
def Basic.CellModel.reverse (cell : Basic.CellModel) (certificate :
  Basic.CellModel.ReversalCertificate cell) :
    Basic.CellModel :=
  { start := cell.finish
    finish := cell.start
    polynomial := certificate.reversedPolynomial
    localAllowance := cell.localAllowance
    localAllowance_nonneg := cell.localAllowance_nonneg
    observations := [] }

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
/-- The certified reversed cell's integral sample is the negative of its exact original sample. -/
theorem Basic.CellModel.reverse_integralSample (cell :
  Basic.CellModel)
    (certificate : Basic.CellModel.ReversalCertificate cell) :
    (cell.reverse certificate).integralSample = -cell.integralSample := by
  unfold Basic.CellModel.reverse Basic.CellModel.integralSample Basic.CellModel.displacement
  rw [certificate.integral_eq]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.neg_re, Basic.neg_im] <;> ring1

end CellModel

end Purelib.Integration.Polynomial.Gaussian.Cell

end
