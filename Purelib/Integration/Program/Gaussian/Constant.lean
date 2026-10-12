module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.ConstantRefinement
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_antitone)

section
public section

/-!
# Progressive finite integration with Gaussian coefficients

This is the period-facing integration kernel.  Every model is still a finite
list of rationally parameterized cells, but its local polynomial coefficients
are Gaussian rationals.  Hence a cell can approximate a genuinely complex
coefficient before multiplication by the complex path displacement.
-/

namespace Purelib.Integration.Program.Gaussian.Constant

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
set_option genInjectivity false in
/-- A retained path-model sequence with exact constant refinements, geometric allowance decay and bounded samples.

Each original stage refinement keeps both original cell lists while the same error scale and center bound apply
throughout the sequence. -/
structure ConstantRefinementProgram where
  /-- The retained original path model at every stage. -/ model : Nat -> Basic.PathModel
  /-- Each original ordered stage pair carries its exact constant-path refinement. -/ refinements : forall {earlier
    later : Nat}, earlier <= later ->
    Basic.PathModel.ConstantPathRefinement (model earlier).cells (model later).cells
  /-- The retained common geometric error scale. -/ errorScale : Fraction.Rational
  /-- The retained error scale is nonnegative. -/ errorScale_nonneg : 0 <= errorScale
  /-- Every original model allowance obeys the retained geometric scale. -/ modelAllowance_le : forall index,
    (model index).aggregateAllowance <=
      Geometric.Basic.quarterRadius errorScale index
  /-- The retained common sample magnitude bound. -/ centerBound : Fraction.Rational
  /-- The retained center bound is nonnegative. -/ centerBound_nonneg : 0 <= centerBound
  /-- Every original model sample satisfies the retained center bound. -/ sample_bounded : forall index,
    Basic.Canonical.normSq (model index).integralSample <= centerBound

constructive_injectivity ConstantRefinementProgram

namespace ConstantRefinementProgram

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
/-- Read the original constant model sequence as a Gaussian refinement program.

The original refinement bound and geometric antitonicity certify later-sample closeness; every retained model and
quantitative bound is reused. -/
@[expose] def toRefinementProgram
  (program : Gaussian.Constant.ConstantRefinementProgram) :
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
        (program.model later).aggregateAllowance :=
        (ConstantRefinement.PathModel.ConstantPathRefinement.integral_difference_le (program.refinements order))
      _ <= Geometric.Basic.quarterRadius program.errorScale later :=
        program.modelAllowance_le later
      _ <= Geometric.Basic.quarterRadius program.errorScale earlier :=
        quarterRadius_antitone
          program.errorScale_nonneg order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := program.sample_bounded

end ConstantRefinementProgram

end Purelib.Integration.Program.Gaussian.Constant

end
