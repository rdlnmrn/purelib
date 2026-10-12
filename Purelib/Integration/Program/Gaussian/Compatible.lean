module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-!
# Compatible Gaussian refinement programs

The retained model sequence carries exact ordered refinements and independent
comparison, model and sample bounds.
-/

namespace Purelib.Integration.Program.Gaussian.Compatible

open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Integration.Program

set_option backward.match.sparseCases false

set_option genInjectivity false in
/-- A retained model sequence with compatible constant refinements and separate comparison-allowance decay.

Every later model remains linked to its original earlier cells; model allowance, comparison allowance and uniform sample
magnitude keep their exact original bounds. -/
structure CompatibleConstantRefinementProgram where
  /-- The retained original path model at every stage. -/ model : Nat -> Basic.PathModel
  /-- Each original ordered stage pair carries its exact compatible constant-path refinement. -/ refinements : forall
    {earlier later : Nat}, earlier <= later ->
    Basic.PathModel.CompatibleConstantPathRefinement
      (model earlier).cells (model later).cells
  /-- The retained common geometric error scale. -/ errorScale : Fraction.Rational
  /-- The retained error scale is nonnegative. -/ errorScale_nonneg : 0 <= errorScale
  /-- Every original model allowance obeys the retained geometric scale. -/ modelAllowance_le : forall index,
    (model index).aggregateAllowance <=
      Geometric.Basic.quarterRadius errorScale index
  /-- Each exact original refinement's comparison allowance obeys the earlier-stage geometric scale. -/
    comparisonAllowance_le : forall {earlier later : Nat}
      (order : earlier <= later),
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (refinements order)) <=
      Geometric.Basic.quarterRadius errorScale earlier
  /-- The retained common sample magnitude bound. -/ centerBound : Fraction.Rational
  /-- The retained center bound is nonnegative. -/ centerBound_nonneg : 0 <= centerBound
  /-- Every original model sample satisfies the retained center bound. -/ sample_bounded : forall index,
    Basic.Canonical.normSq (model index).integralSample <= centerBound

constructive_injectivity CompatibleConstantRefinementProgram

namespace CompatibleConstantRefinementProgram

/-- Read the original compatible constant model sequence as a Gaussian refinement program.

The exact comparison-refinement certificate supplies later-sample closeness; all retained models, scales and center
bounds are reused. -/
@[expose] def toRefinementProgram (program : Gaussian.Compatible.CompatibleConstantRefinementProgram) :
    Gaussian.Basic.RefinementProgram where
  model := program.model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := by
    intro earlier later order
    calc
      Basic.Canonical.normSq
          ((program.model later).integralSample -
            (program.model earlier).integralSample) <=
        (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (program.refinements
          order)) :=
        (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.integral_difference_le (program.refinements
          order))
      _ <= Geometric.Basic.quarterRadius program.errorScale earlier :=
        program.comparisonAllowance_le order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

end CompatibleConstantRefinementProgram

end Purelib.Integration.Program.Gaussian.Compatible

end
