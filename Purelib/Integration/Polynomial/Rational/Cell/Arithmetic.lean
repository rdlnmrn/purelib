module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Scale
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Polynomial.Rational.Cell.Basic
import Purelib.Polynomial.Ascending.Rational.Basic
import Purelib.Polynomial.Ascending.Rational.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

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

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
/-- Add the two cell polynomials on the retained left endpoints with a doubled sum of local allowances.

The constructed cell has an empty observation list; equality of both original endpoint pairs is required separately for
the integral-sample addition theorem. -/
def addIntegrand (left right :
  Rational.Cell.Basic.CellModel) : Rational.Cell.Basic.CellModel :=
  { start := left.start
    finish := left.finish
    polynomial := Rational.Basic.add
      left.polynomial right.polynomial
    localAllowance := 2 * (left.localAllowance + right.localAllowance)
    localAllowance_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (add_nonneg left.localAllowance_nonneg right.localAllowance_nonneg)
    observations := [] }

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
/-- Adding cell integrands with equal original endpoints adds their exact integral samples. -/
theorem addIntegrand_integralSample (left right :
  Rational.Cell.Basic.CellModel)
    (sameStart : right.start = left.start)
    (sameFinish : right.finish = left.finish) :
    (left.addIntegrand right).integralSample =
      left.integralSample + right.integralSample := by
  unfold addIntegrand Rational.Cell.Basic.CellModel.integralSample
    Rational.Cell.Basic.CellModel.displacement
  rw [Rational.Integral.definiteIntegral_add,
    sameStart, sameFinish]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im, Basic.mul_re, Basic.mul_im] <;> ring1

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
/-- Scale the retained polynomial by a rational factor and its allowance by the factor squared.

The original endpoints remain fixed and the constructed cell starts with an empty observation list. -/
def scaleIntegrand (factor : Fraction.Rational)
  (cell : Rational.Cell.Basic.CellModel) : Rational.Cell.Basic.CellModel :=
  { start := cell.start
    finish := cell.finish
    polynomial := Rational.Basic.scale factor cell.polynomial
    localAllowance := factor ^ 2 * cell.localAllowance
    localAllowance_nonneg :=
      Fraction.Order.Arithmetic.mul_nonneg_direct
        (Fraction.Order.Arithmetic.sq_nonneg_direct factor)
        cell.localAllowance_nonneg
    observations := [] }

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
open Purelib.Polynomial.Ascending in
/-- Scaling the integrand scales its exact Gaussian integral sample by the same rational factor. -/
theorem scaleIntegrand_integralSample (factor :
  Fraction.Rational)
    (cell : Rational.Cell.Basic.CellModel) :
    (cell.scaleIntegrand factor).integralSample =
      Scale.scale factor cell.integralSample := by
  unfold scaleIntegrand Rational.Cell.Basic.CellModel.integralSample
    Rational.Cell.Basic.CellModel.displacement
  rw [Rational.Integral.definiteIntegral_scale]
  apply Basic.ext <;>
    simp only [Scale.scale_re,
      Scale.scale_im, Basic.mul_re, Basic.mul_im] <;> ring1

open Purelib.Data.Rat in
open Purelib.Integration.Polynomial in
/-- Scaling the integrand multiplies its exact weighted allowance by the factor squared. -/
theorem scaleIntegrand_weightedAllowance (factor :
  Fraction.Rational)
    (cell : Rational.Cell.Basic.CellModel) :
    (cell.scaleIntegrand factor).weightedAllowance =
      factor ^ 2 * cell.weightedAllowance := by
  unfold scaleIntegrand Rational.Cell.Basic.CellModel.weightedAllowance
    Rational.Cell.Basic.CellModel.displacement
  ring1

end CellModel

end Purelib.Integration.Polynomial.Rational.Cell.Basic

end
