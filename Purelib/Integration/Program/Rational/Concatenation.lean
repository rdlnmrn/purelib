module
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Polynomial.Rational.Path.Basic
public import Purelib.Integration.Program.Rational.Arithmetic
import Purelib.Integration.Program.Rational.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic

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

namespace Purelib.Integration.Program.Rational.Basic
namespace RefinementProgram

open Purelib.Approximation.Rational in
open Purelib.Integration.Program.Rational in
/-- The original concatenated rational path models satisfy decay at twice the combined error scale.

The certificate retains both original program sequences and bounds their exact stagewise concatenations. -/
structure ConcatenationAllowance (left right :
  Basic.RefinementProgram) where
  /-- Every original stagewise concatenation satisfies the retained combined geometric allowance. -/ aggregate_le : ∀
    index,
    ((left.model index).concat (right.model index)).aggregateAllowance ≤
      Geometric.Basic.quarterRadius
        (2 * (left.errorScale + right.errorScale)) index

open Purelib.Integration.Polynomial.Rational.Path in
open Purelib.Integration.Program.Rational in
/-- Build the refinement program for the original stagewise concatenated rational path models.

The supplied allowance and exact sample-addition equality certify the retained concatenated models through the original
sum constructor. -/
def concat (left right : Basic.RefinementProgram)
    (allowance : ConcatenationAllowance left right) : Basic.RefinementProgram :=
  Basic.RefinementProgram.add left right
    { model := fun index => (left.model index).concat (right.model index)
      integral_eq := by
        intro index
        exact Basic.PathModel.integralSample_concat _ _
      aggregate_le := allowance.aggregate_le }

open Purelib.Integration.Program.Rational in
/-- The concatenated program stage retains the exact concatenation of the two original models. -/
@[simp] theorem concat_model (left right :
  Basic.RefinementProgram)
    (allowance : ConcatenationAllowance left right) (index : Nat) :
    (concat left right allowance).model index =
      (left.model index).concat (right.model index) :=
  rfl

open Purelib.Integration.Polynomial.Rational.Path in
open Purelib.Integration.Program.Rational in
/-- The original concatenated stage model sample is the sum of the two original samples. -/
theorem concat_integralSample (left right :
  Basic.RefinementProgram)
    (allowance : ConcatenationAllowance left right) (index : Nat) :
    ((concat left right allowance).model index).integralSample =
      (left.model index).integralSample +
        (right.model index).integralSample :=
  Basic.PathModel.integralSample_concat _ _
end RefinementProgram

end Purelib.Integration.Program.Rational.Basic

end
