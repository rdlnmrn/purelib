module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Program.Gaussian.Arithmetic
import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic

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

open Purelib.Approximation.Rational in
open Purelib.Integration.Program in
/-- The original concatenated path models obey geometric decay at twice the combined error scale.

The certificate retains both program sequences and checks their exact stagewise model concatenations. -/
structure ConcatenationAllowance (left right :
  Gaussian.Basic.RefinementProgram) where
  /-- Every original concatenated stage model obeys the combined geometric allowance bound. -/ aggregate_le : forall
    index,
    ((left.model index).concat (right.model index)).aggregateAllowance <=
      Geometric.Basic.quarterRadius
        (2 * (left.errorScale + right.errorScale)) index

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
/-- Build the integration program for the exact stagewise concatenation of two original model sequences.

The supplied concatenation allowance and exact sample-addition theorem certify the retained concatenated models through
the original sum-program constructor. -/
def concat (left right :
  Gaussian.Basic.RefinementProgram)
    (allowance : ConcatenationAllowance left right) : Gaussian.Basic.RefinementProgram
      :=
  Gaussian.Basic.RefinementProgram.add left right
    { model := fun index => (left.model index).concat (right.model index)
      integral_eq := by
        intro index
        exact Basic.PathModel.integralSample_concat _ _
      aggregate_le := allowance.aggregate_le }

open Purelib.Integration.Program in
/-- The concatenated program's original stage model is the concatenation of the two input stage models. -/
@[simp] theorem concat_model (left right :
  Gaussian.Basic.RefinementProgram)
    (allowance : ConcatenationAllowance left right) (index : Nat) :
    (concat left right allowance).model index =
      (left.model index).concat (right.model index) :=
  rfl

open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
/-- The concatenated model sample equals the sum of the two original stage samples. -/
theorem concat_integralSample (left right :
  Gaussian.Basic.RefinementProgram)
    (allowance : ConcatenationAllowance left right) (index : Nat) :
    ((concat left right allowance).model index).integralSample =
      (left.model index).integralSample +
        (right.model index).integralSample :=
  Basic.PathModel.integralSample_concat _ _
end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
