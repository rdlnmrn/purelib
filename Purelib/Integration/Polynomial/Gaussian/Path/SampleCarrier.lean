module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Integral
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Program.Gaussian.Basic
namespace RefinementProgram

open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial.Ascending in
/-- Represent the supplied Gaussian value by one exact constant-polynomial cell on the segment from zero to one. -/
def exactSamplePath (value : Basic.Canonical) :
  Basic.PathModel :=
  ⟨[Basic.CellModel.exact 0 1
    (Gaussian.Basic.constant value)]⟩

open Purelib.Data.Gaussian in
open Purelib.Integration in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Polynomial.Ascending in
/-- The exact single-cell carrier has integral sample equal to the original supplied value. -/
@[simp] theorem exactSamplePath_integralSample
  (value : Basic.Canonical) :
    (exactSamplePath value).integralSample = value := by
  unfold exactSamplePath Basic.PathModel.integralSample Basic.CellModel.exact
    Basic.CellModel.integralSample Basic.CellModel.displacement
  simp only [List.foldr_cons, List.foldr_nil,
    Gaussian.Integral.definiteIntegral_constant]
  apply Basic.ext <;>
    simp only [Basic.sub_re, Basic.sub_im, Basic.mul_re, Basic.mul_im, Basic.add_re, Basic.add_im,
      Basic.zero_re, Basic.zero_im, Basic.one_re, Basic.one_im] <;>
    ring1

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration in
open Purelib.Integration.Polynomial.Gaussian.Cell in
open Purelib.Integration.Polynomial.Gaussian.Path in
/-- The exact single-cell carrier has zero aggregate allowance.

Its retained cell allowance is zero, and the original weighted aggregation preserves that exact scalar value. -/
@[simp] theorem exactSamplePath_aggregateAllowance
  (value : Basic.Canonical) :
    (exactSamplePath value).aggregateAllowance = 0 := by
  unfold exactSamplePath Basic.PathModel.aggregateAllowance
    Basic.PathModel.totalWeightedAllowance Basic.CellModel.exact Basic.CellModel.weightedAllowance
  simp only [List.foldr_cons, List.foldr_nil,
    Fraction.Field.mul_zero_direct,
    Fraction.Field.zero_add, -eq_self, -iff_self]
  rfl

open Purelib.Integration
open Purelib.Integration.Polynomial.Gaussian.Path
/-- Build an exact single-cell carrier for the product of the two original path samples. -/
def productSamplePath (left right : Basic.PathModel)
  : Basic.PathModel :=
  exactSamplePath (left.integralSample * right.integralSample)

/-- The product carrier's sample is the product of the two original path samples. -/
@[simp] theorem productSamplePath_integralSample
  (left right : Basic.PathModel) :
    (productSamplePath left right).integralSample =
      left.integralSample * right.integralSample :=
  exactSamplePath_integralSample _

/-- The exact product sample carrier has zero aggregate allowance. -/
@[simp] theorem productSamplePath_aggregateAllowance
    (left right : Basic.PathModel) :
    (productSamplePath left right).aggregateAllowance = 0 :=
  exactSamplePath_aggregateAllowance _
end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
