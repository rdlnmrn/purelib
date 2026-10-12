module

import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Rational.Path.Basic
public import Purelib.Integration.Polynomial.Rational.Path.Reversal
public import Purelib.Integration.Program.Rational.Basic
import Purelib.Integration.Polynomial.Rational.Path.Allowance
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

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

namespace Purelib.Integration.Program.Rational
section RefinementProgram

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Rational.Path in
open Purelib.Integration.Program.Rational in
set_option genInjectivity false in
/-- A retained rational path-model sequence realizing negatives of the original program samples.

The exact sample identities and allowance certificates retain the original program and its unchanged geometric error
scale. -/
structure Basic.RefinementProgram.ReversalModels (program :
  Basic.RefinementProgram) where
  /-- The retained original-indexed reversal model sequence. -/ model : Nat → Basic.PathModel
  /-- Every retained reversal sample is the negative of its exact original program sample. -/ integral_eq : ∀ index,
    (model index).integralSample = -(program.model index).integralSample
  /-- The retained reversed model allowance satisfies the original geometric bound. -/ aggregate_le : ∀ index,
    (model index).aggregateAllowance ≤
      Geometric.Basic.quarterRadius program.errorScale index

constructive_injectivity Basic.RefinementProgram.ReversalModels

namespace Reversal.RefinementProgram.ReversalModels

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Rational.Path in
open Purelib.Integration.Program.Rational in
/-- Build retained program reversal models from the exact original path reversals and allowance bounds. -/
def ofPathReversals (program :
  Basic.RefinementProgram)
    (reversals : ∀ index, Basic.PathModel.Reversal (program.model index))
    (aggregate_le : ∀ index,
      ((program.model index).reverse (reversals index)).aggregateAllowance ≤
        Geometric.Basic.quarterRadius
          program.errorScale index) : Basic.RefinementProgram.ReversalModels program :=
  { model := fun index => (program.model index).reverse (reversals index)
    integral_eq := by
      intro index
      exact Basic.PathModel.reverse_integralSample _ _
    aggregate_le := aggregate_le }

end Reversal.RefinementProgram.ReversalModels

open Purelib.Data.Gaussian in
open Purelib.Integration.Program.Rational in
/-- Build the rational refinement program using the retained reversal models.

The exact sample negations preserve the original closeness and center bounds, while the supplied models keep their
original allowance certificates. -/
def Basic.RefinementProgram.reverse (program : Basic.RefinementProgram)
  (models : Basic.RefinementProgram.ReversalModels program) :
    Basic.RefinementProgram :=
  { model := models.model
    errorScale := program.errorScale
    errorScale_nonneg := program.errorScale_nonneg
    modelAllowance_le := models.aggregate_le
    later_close := by
      intro earlier later order
      rw [models.integral_eq, models.integral_eq]
      have identity :
          -(program.model later).integralSample -
              -(program.model earlier).integralSample =
            -((program.model later).integralSample -
              (program.model earlier).integralSample) := by
        apply Basic.ext <;>
          simp only [Basic.neg_re, Basic.neg_im, Basic.sub_re, Basic.sub_im] <;> ring1
      rw [identity, Basic.Canonical.normSq_neg]
      exact program.later_close order
    centerBound := program.centerBound
    centerBound_nonneg := program.centerBound_nonneg
    sample_bounded := by
      intro index
      rw [models.integral_eq, Basic.Canonical.normSq_neg]
      exact program.sample_bounded index }

open Purelib.Integration.Program.Rational in
/-- The retained reversed stage sample is the negative of the exact original stage sample. -/
@[simp] theorem Basic.RefinementProgram.reverse_integralSample (program :
  Basic.RefinementProgram)
    (models : Basic.RefinementProgram.ReversalModels program) (index : Nat) :
    ((Basic.RefinementProgram.reverse program models).model index).integralSample =
      -(program.model index).integralSample :=
  models.integral_eq index
end RefinementProgram

end Purelib.Integration.Program.Rational

end
