module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Scale
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement
public import Purelib.Integration.Program.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Mathlib.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib.Approximation.Rational.Geometric.Scale (quarterRadius_four_mul quarterRadius_four_mul_succ)

public section

/-!
# Consecutive compatible Gaussian refinements

Consecutive retained path models carry comparison certificates with geometric
step bounds. Finite telescoping controls later samples and their uniform magnitude.
-/

namespace Purelib.Integration.Program.Gaussian.Sequential

open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement.PathModel
open Purelib.Integration.Program.Gaussian
open Purelib.Data.Gaussian

set_option backward.match.sparseCases false

/-! ## Consecutive compatible refinements -/

set_option genInjectivity false in
/-- A sequence of exact path models with retained consecutive refinements and geometric comparison bounds.

The nonnegative step scale controls every retained comparison allowance, and the initial model allowance is bounded by
four times that scale. -/
structure SequentialCompatibleConstantRefinementProgram where
  /-- The original path model at each retained stage index. -/ model : Nat -> Basic.PathModel
  /-- The exact compatible constant refinement between each consecutive pair of original models. -/ steps : forall
    index,
    Basic.PathModel.CompatibleConstantPathRefinement
      (model index).cells (model (index + 1)).cells
  /-- The retained common scale for consecutive comparison bounds. -/ stepScale : Fraction.Rational
  /-- The original step scale is nonnegative. -/ stepScale_nonneg : 0 <= stepScale
  /-- The original initial model allowance is at most four times the step scale. -/ initialAllowance_le :
    (model 0).aggregateAllowance <= 4 * stepScale
  /-- Each retained step comparison meets its exact step-scale quarter radius. -/ comparisonAllowance_le : forall index,
    (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (steps index)) <=
      Geometric.Basic.quarterRadius stepScale index

constructive_injectivity SequentialCompatibleConstantRefinementProgram

namespace SequentialCompatibleConstantRefinementProgram

/-- Four times the original nonnegative step scale. -/
@[expose] def errorScale (program : Sequential.SequentialCompatibleConstantRefinementProgram) :
    Fraction.Rational :=
  4 * program.stepScale

/-- The retained error scale is nonnegative. -/
theorem errorScale_nonneg
    (program : Sequential.SequentialCompatibleConstantRefinementProgram) :
    0 <= program.errorScale :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    program.stepScale_nonneg

/-- Every exact retained model allowance meets its error-scale quarter radius. -/
theorem modelAllowance_le
    (program : Sequential.SequentialCompatibleConstantRefinementProgram) (index : Nat) :
    (program.model index).aggregateAllowance <=
      Geometric.Basic.quarterRadius program.errorScale index := by
  cases index with
  | zero =>
      simpa only [Sequential.SequentialCompatibleConstantRefinementProgram.errorScale,
        Geometric.Basic.quarterRadius_eq_mul_pow,
        pow_zero, Fraction.Field.mul_one_direct] using
        program.initialAllowance_le
  | succ index =>
      calc
        (program.model (index + 1)).aggregateAllowance <=
            (CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonAllowance (program.steps index))
              :=

            (
              CompatibleConstantPathRefinement.childAggregateAllowance_le_comparisonAllowance
            (program.steps index))
        _ <= Geometric.Basic.quarterRadius program.stepScale index :=
          program.comparisonAllowance_le index
        _ = Geometric.Basic.quarterRadius program.errorScale
            (index + 1) := by
          exact (quarterRadius_four_mul_succ
            program.stepScale index).symm

/-- Consecutive retained integral samples meet the original step-scale quarter-radius bound. -/
theorem step_difference_le
    (program : Sequential.SequentialCompatibleConstantRefinementProgram) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq
        ((program.model (index + 1)).integralSample -
          (program.model index).integralSample) <=
      Geometric.Basic.quarterRadius program.stepScale index := by
  exact (Norm.Basic.normSq_eq_canonical _).trans_le
    ((CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.integral_difference_le (program.steps
      index)).trans
      (program.comparisonAllowance_le index))

/-- A finite sequence of retained refinement steps bounds the final-minus-initial sample by the earlier error radius. -/
private theorem later_difference_le_extra
    (program : Sequential.SequentialCompatibleConstantRefinementProgram) :
    forall (extra earlier : Nat),
      Data.Gaussian.Norm.Basic.normSq
          ((program.model (earlier + extra)).integralSample -
            (program.model earlier).integralSample) <=
        Geometric.Basic.quarterRadius program.errorScale earlier
  | 0, earlier => by
      simp only [Nat.add_zero,
        Basic.sub_self,
        Norm.Basic.normSq_zero]
      exact Geometric.Basic.quarterRadius_nonneg
        program.errorScale_nonneg earlier
  | extra + 1, earlier => by
      let laterSample := (program.model (earlier + (extra + 1))).integralSample
      let nextSample := (program.model (earlier + 1)).integralSample
      let earlierSample := (program.model earlier).integralSample
      have indexEqual : earlier + (extra + 1) = (earlier + 1) + extra := by
        omega
      have tailBound :
          Data.Gaussian.Norm.Basic.normSq (laterSample - nextSample) <=
            Geometric.Basic.quarterRadius program.errorScale
              (earlier + 1) := by
        simpa only [laterSample, nextSample, indexEqual] using

            later_difference_le_extra
            program extra (earlier + 1)
      have headBound :
          Data.Gaussian.Norm.Basic.normSq (nextSample - earlierSample) <=
            Geometric.Basic.quarterRadius program.stepScale earlier := by
        simpa only [nextSample, earlierSample] using
          program.step_difference_le earlier
      have decomposition : laterSample - earlierSample =
          (laterSample - nextSample) + (nextSample - earlierSample) := by
        apply Basic.ext <;>
          simp only [Basic.sub_re,
            Basic.sub_im,
            Basic.add_re,
            Basic.add_im] <;> ring1
      rw [decomposition]
      calc
        Data.Gaussian.Norm.Basic.normSq
            ((laterSample - nextSample) +
              (nextSample - earlierSample)) <=
            2 * (Data.Gaussian.Norm.Basic.normSq (laterSample - nextSample) +
              Data.Gaussian.Norm.Basic.normSq (nextSample - earlierSample)) :=
          Norm.Bounds.normSq_add_le_two _ _
        _ <= 2 *
            (Geometric.Basic.quarterRadius program.errorScale
                (earlier + 1) +
              Geometric.Basic.quarterRadius program.stepScale earlier) :=
          Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
            (Fraction.Order.Arithmetic.add_le_add_direct tailBound headBound) (by decide)
        _ = Geometric.Basic.quarterRadius program.errorScale earlier := by
          rw [show program.errorScale = 4 * program.stepScale from rfl,
            quarterRadius_four_mul_succ,
              quarterRadius_four_mul]
          ring1

/-- Every later retained sample differs from the earlier sample by at most the earlier error-scale quarter radius.

The retained weak stage bound supplies the explicit finite difference between the two indices. Its index equality
transports the finite consecutive-step estimate to the original later model. -/
theorem later_close (program : Sequential.SequentialCompatibleConstantRefinementProgram)
    {earlier later : Nat} (order : earlier <= later) :
    Data.Gaussian.Norm.Basic.normSq
        ((program.model later).integralSample -
          (program.model earlier).integralSample) <=
      Geometric.Basic.quarterRadius program.errorScale earlier := by
  have readback : earlier + (later - earlier) = later := by omega0
  have bounded := Sequential.SequentialCompatibleConstantRefinementProgram.later_difference_le_extra
    program (later - earlier) earlier
  rewrite [readback] at bounded
  exact bounded

/-- Twice the sum of the original initial sample's squared norm and retained error scale. -/
@[expose] def centerBound (program : Sequential.SequentialCompatibleConstantRefinementProgram) :
    Fraction.Rational :=
  2 * (Data.Gaussian.Norm.Basic.normSq (program.model 0).integralSample + program.errorScale)

/-- The retained uniform sample bound is nonnegative. -/
theorem centerBound_nonneg
    (program : Sequential.SequentialCompatibleConstantRefinementProgram) :
    0 <= program.centerBound := by
  unfold Sequential.SequentialCompatibleConstantRefinementProgram.centerBound
  exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (Norm.Basic.normSq_nonneg _) program.errorScale_nonneg)

/-- Every retained model sample meets the original initial-sample-based uniform bound. -/
theorem sample_bounded
    (program : Sequential.SequentialCompatibleConstantRefinementProgram) (index : Nat) :
    Data.Gaussian.Norm.Basic.normSq (program.model index).integralSample <= program.centerBound := by
  let current := (program.model index).integralSample
  let initial := (program.model 0).integralSample
  have movement : Data.Gaussian.Norm.Basic.normSq (current - initial) <= program.errorScale :=
    (program.later_close (Nat.zero_le index)).trans
      (Geometric.Basic.quarterRadius_le_scale
        program.errorScale_nonneg 0)
  have identity : (current - initial) + initial = current := by
    apply Basic.ext <;>
      simp only [Basic.sub_re,
        Basic.sub_im,
        Basic.add_re,
        Basic.add_im] <;> ring1
  have sumBound :=
    Norm.Bounds.normSq_add_le_two
      (current - initial) initial
  rw [identity] at sumBound
  exact sumBound.trans (by
    apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _
      (show (0 : Fraction.Rational) <= 2 by decide)
    calc
      Data.Gaussian.Norm.Basic.normSq (current - initial) + Data.Gaussian.Norm.Basic.normSq initial <=
          program.errorScale + Data.Gaussian.Norm.Basic.normSq initial :=
        Fraction.Order.Arithmetic.add_le_add_direct movement (Fraction.Order.Basic.le_refl _)
      _ = Data.Gaussian.Norm.Basic.normSq initial + program.errorScale := by ring1)

/-- Retain the original exact models as a refinement program with certified geometric errors and bounded samples. -/
@[expose] def toRefinementProgram
    (program : Sequential.SequentialCompatibleConstantRefinementProgram) :
    Basic.RefinementProgram where
  model := program.model
  errorScale := program.errorScale
  errorScale_nonneg := program.errorScale_nonneg
  modelAllowance_le := program.modelAllowance_le
  later_close := by
    intro earlier later order
    rw [← Norm.Basic.normSq_eq_canonical]
    exact program.later_close (earlier := earlier) (later := later) order
  centerBound := program.centerBound
  centerBound_nonneg := program.centerBound_nonneg
  sample_bounded := by
    intro index
    rw [← Norm.Basic.normSq_eq_canonical]
    exact program.sample_bounded index

end SequentialCompatibleConstantRefinementProgram

end Purelib.Integration.Program.Gaussian.Sequential

end
