module

import Purelib.Polynomial.Approximation.Gaussian.Arithmetic.Localization
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws
meta import Purelib.Polynomial.Approximation.Gaussian.Arithmetic.Localization
meta import Purelib.Data.Gaussian.Field
meta import Purelib.Approximation.Gaussian.Division.Prepared.Decision.Laws

/-! # Recursive original-channel polynomial arithmetic and computed decisions -/

namespace TestPurelib.Polynomial.RecursiveArithmetic

open Purelib
open Purelib.Polynomial.Approximation.Gaussian (Arithmetic Residual)
open Purelib.Polynomial.Dense.Companion (Operation)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Name.Coherent (CoherentNamed)
open Purelib.Data.Gaussian.Basic (Canonical)

example {firstPolynomial secondPolynomial : CoefficientPolynomial} {firstChannel secondChannel : CoherentNamed}
    (operation : Operation) (first : Residual firstPolynomial firstChannel)
    (second : Residual secondPolynomial secondChannel) :
    Residual (Arithmetic.ofResiduals operation first second).polynomial
      (Arithmetic.channel operation firstChannel secondChannel) :=
  (Arithmetic.ofResiduals operation first second).residualCertificate

example {firstPolynomial secondPolynomial : CoefficientPolynomial} {firstChannel secondChannel : CoherentNamed}
    (operation : Operation) (first : Residual firstPolynomial firstChannel)
    (second : Residual secondPolynomial secondChannel) :
    Division.Prepared.Decision (Arithmetic.channel operation firstChannel secondChannel) :=
  (Arithmetic.ofResiduals operation first second).select.decide

example {firstPolynomial secondPolynomial thirdPolynomial : CoefficientPolynomial}
    {firstChannel secondChannel thirdChannel : CoherentNamed}
    (first : Residual firstPolynomial firstChannel) (second : Residual secondPolynomial secondChannel)
    (third : Residual thirdPolynomial thirdChannel) :
    Residual
      (Arithmetic.ofResiduals .mul (Arithmetic.ofResiduals .add first second).residualCertificate third).polynomial
      (Arithmetic.channel .mul (Arithmetic.channel .add firstChannel secondChannel) thirdChannel) :=
  (Arithmetic.ofResiduals .mul (Arithmetic.ofResiduals .add first second).residualCertificate third).residualCertificate

/-- Execute a sum followed by a product using the same stored arithmetic result samples and coefficients. -/
private def checkRecursiveArithmetic : IO Unit := do
  let first := Residual.exact 2
  let second := Residual.exact 3
  let sum := Arithmetic.ofResiduals .add first second
  let retained := sum.residualCertificate
  let product := Arithmetic.ofResiduals .mul retained second
  unless sum.result.sample 3 = 5 ∧ retained.source.sample 4 = 5 ∧ product.result.sample 5 = 15 do
    throw (IO.userError "recursive arithmetic lost an original input or the same stored intermediate result")
  unless sum.polynomial.eval 5 = 0 ∧ product.polynomial.eval 15 = 0 do
    throw (IO.userError "computed recursive arithmetic polynomial failed its actual finite reading")
  unless product.first.source.sample 6 = retained.source.sample 6 ∧
      product.first.scale = retained.scale do
    throw (IO.userError "later arithmetic replaced its actual retained source or residual scale")
  let cancellation := Arithmetic.ofResiduals .add (Residual.exact (-2)) first
  unless cancellation.result.sample 7 = 0 ∧ cancellation.polynomial.eval 0 = 0 do
    throw (IO.userError "original cancellation samples or computed polynomial were lost")
  let selected := cancellation.select
  unless !selected.decide.isPrepared ∧ selected.selected.approximation.sample 6 = 0 do
    throw (IO.userError "computed recursive cancellation did not exclude its unchanged original operation")

#eval checkRecursiveArithmetic

end TestPurelib.Polynomial.RecursiveArithmetic
