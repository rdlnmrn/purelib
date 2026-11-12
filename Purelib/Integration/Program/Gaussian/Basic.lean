module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Gaussian.Basic
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

namespace Purelib.Integration.Program.Gaussian.Basic

open Purelib.Approximation.Rational in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Integration.Polynomial.Gaussian.Path in
set_option genInjectivity false in
/-- An original Gaussian polynomial path at each stage with certified geometric allowances and sample comparisons.

The retained error scale bounds each path allowance and every later-versus-earlier sample difference; a separate
nonnegative center bound controls all samples. -/
structure RefinementProgram where
  /-- The original Gaussian polynomial path model at each stage. -/ model : Nat -> Basic.PathModel
  /-- The retained geometric error scale. -/ errorScale : Fraction.Rational
  /-- The retained error scale is nonnegative. -/ errorScale_nonneg : 0 <= errorScale
  /-- Each original path's aggregate allowance lies below the corresponding quarter-radius bound. -/ modelAllowance_le :
    forall index,
    (model index).aggregateAllowance <=
      Geometric.Basic.quarterRadius errorScale index
  /-- Each later sample differs from the original earlier sample by at most its quarter-radius squared allowance. -/
    later_close : forall {earlier later : Nat}, earlier <= later ->
    Basic.Canonical.normSq ((model later).integralSample - (model earlier).integralSample) <=
      Geometric.Basic.quarterRadius errorScale earlier
  /-- The retained common squared-norm bound for path samples. -/ centerBound : Fraction.Rational
  /-- The common sample bound is nonnegative. -/ centerBound_nonneg : 0 <= centerBound
  /-- Every original path sample obeys the retained common bound. -/ sample_bounded : forall index,
    Basic.Canonical.normSq (model index).integralSample <= centerBound

constructive_injectivity RefinementProgram

namespace RefinementProgram

open Purelib.Approximation.Rational.Geometric
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

/-- Retain supplied original models with the same stage samples and certified allowances.

The movement scale, center bound and their proofs come from the original
program. Only the retained model sequence changes; scalar sample readbacks
transport those same guarantees to the supplied cells. -/
def withModels (program : RefinementProgram) (models : Nat → PathModel)
    (samples : ∀ index, (models index).integralSample = (program.model index).integralSample)
    (allowances : ∀ index, (models index).aggregateAllowance ≤ Basic.quarterRadius program.errorScale index) :
    RefinementProgram where
  model := models
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := allowances
  later_close := by
    intro earlier later order
    rw [samples later, samples earlier]
    exact program.later_close order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [samples index]
    exact program.sample_bounded index

/-- Replacing the model sequence retains each supplied original model literally. -/
theorem withModels_model (program : RefinementProgram) (models : Nat → PathModel)
    (samples : ∀ index, (models index).integralSample = (program.model index).integralSample)
    (allowances : ∀ index, (models index).aggregateAllowance ≤ Basic.quarterRadius program.errorScale index)
    (index : Nat) : (program.withModels models samples allowances).model index = models index := rfl

end RefinementProgram

end Purelib.Integration.Program.Gaussian.Basic

end
