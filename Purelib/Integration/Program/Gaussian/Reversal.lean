module

import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Reversal
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
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

namespace Purelib.Integration.Program.Gaussian
section RefinementProgram

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
set_option genInjectivity false in
/-- A retained model sequence with negated original samples and the original program's geometric allowance bound. -/
structure Basic.RefinementProgram.ReversalModels (program :
  Gaussian.Basic.RefinementProgram) where
  /-- The retained reversed model sequence for this exact original program. -/ model : Nat -> Basic.PathModel
  /-- Every retained reversed model sample is the negative original stage sample. -/ integral_eq : forall index,
    (model index).integralSample = -(program.model index).integralSample
  /-- Each retained model allowance obeys the original program's geometric error scale. -/ aggregate_le : forall index,
    (model index).aggregateAllowance <=
      Geometric.Basic.quarterRadius program.errorScale index

constructive_injectivity Basic.RefinementProgram.ReversalModels

namespace Reversal.RefinementProgram.ReversalModels

open Purelib.Approximation.Rational in
open Purelib.Integration.Polynomial.Gaussian.Path in
open Purelib.Integration.Program in
/-- Build retained reversal models from exact stagewise path reversals and their supplied allowance certificates. -/
def ofPathReversals (program :
  Gaussian.Basic.RefinementProgram)
    (reversals : forall index, Basic.PathModel.Reversal (program.model index))
    (aggregate_le : forall index,
      ((program.model index).reverse (reversals index)).aggregateAllowance <=
        Geometric.Basic.quarterRadius program.errorScale index) :
    Gaussian.Basic.RefinementProgram.ReversalModels program where
  model := fun index => (program.model index).reverse (reversals index)
  integral_eq := by
    intro index
    exact Basic.PathModel.reverse_integralSample _ _
  aggregate_le := aggregate_le

end Reversal.RefinementProgram.ReversalModels

open Purelib.Data.Gaussian in
open Purelib.Integration.Program in
/-- Build the program with retained reversal models while preserving the original error scale and center bound.

The supplied sample-negation equations transfer the original later-close and sample-size certificates without changing
either numerical scale. -/
def Basic.RefinementProgram.reverse (program :
  Gaussian.Basic.RefinementProgram) (models : Basic.RefinementProgram.ReversalModels program) :
    Gaussian.Basic.RefinementProgram where
  model := models.model
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
    exact program.sample_bounded index

open Purelib.Integration.Program in
/-- Each retained reversed-program sample is the negative of its exact original stage sample. -/
@[simp] theorem Basic.RefinementProgram.reverse_integralSample (program :
  Gaussian.Basic.RefinementProgram)
    (models : Basic.RefinementProgram.ReversalModels program) (index : Nat) :
    ((Basic.RefinementProgram.reverse program models).model index).integralSample =
      -(program.model index).integralSample :=
  models.integral_eq index
end RefinementProgram

end Purelib.Integration.Program.Gaussian

end
