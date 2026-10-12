module
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Nat.Order
import Purelib.Approximation.Gaussian.Equivalence.Sampling
import Purelib.Approximation.Gaussian.Exponential.Horner.Sample
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Nat.Schedule.PositiveStride
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Integration.Exponential.Program
import Purelib.Integration.Exponential.Selection
import Purelib.Integration.Exponential.Geometry.Policy

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Exponential.Equivalence.Reference
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Integration.CertifiedProgram
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Integration.CCL.Program
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Data.Gaussian.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Approximation.Gaussian.Sequence.Name
import Mathlib.Order.Basic
import Mathlib.Data.Nat.Basic
import Purelib.Tactic.Ring

open Purelib.Integration

public section

/-!
# The integrated exponential family agrees with the existing `exp(1)-1` name

The right side below is the ordinary stateful subtraction of the existing
finite exponential name and exact one.  Its actual sampler retains the
exponential source index as the first component of its state.  We compare
through that index and its requested radius, rather than assuming equality
of independently selected samples or introducing a completed exponential.
-/

namespace Purelib.Integration.Exponential.Equivalence.Existing

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian
open Purelib.Data.Nat
open Purelib.Data.Rat
open Purelib.Integration.Exponential
open Purelib.Integration.Exponential.Equivalence
open Purelib.Integration.Polynomial

/-- Compare the exact policy-controlled integration approximation with the retained exponential-minus-one reference
name.

The finite comparison preserves both original starting stages, selects a shared Horner source floor and pays the
separate two-sided error through a quarter-target bound. -/
@[expose] def approximation_equivalent_existing (policy :
  Exponential.Geometry.Policy) (schedule : Data.Nat.Schedule.PositiveStride)
  (extraDepth : Nat) :
    Equivalence.Equivalent
      (Program.program policy schedule extraDepth).approximation
      (Name.Sampling.approximation Reference.exponentialMinusOne) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let rightIndex := Geometric.Search.firstQuarterBelow 1 rightStart smallTarget
    let sourceIndex := Reference.referenceSourceIndex rightIndex
    let leftIndex := max leftStart sourceIndex
    have sourceSmall : Geometric.Basic.quarterRadius 10 sourceIndex < smallTarget :=
      (Reference.reference_source_radius rightIndex).trans
        (Geometric.Search.firstQuarterBelow_accurate 1 (by decide) rightStart smallTarget smallPositive)
    exact
      { leftIndex := leftIndex
        rightIndex := rightIndex
        left_ge := by
          change leftStart ≤ max leftStart sourceIndex
          rw [Purelib.Data.Nat.Order.max_eq_natMax]
          exact Purelib.Data.Nat.Order.le_max_left _ _
        right_ge := Geometric.Search.firstQuarterBelow_ge 1 rightStart smallTarget
        close := by
          intro leftLater rightLater leftOrder rightOrder
          let leftSource := (Integration.Exponential.Selection.selection policy schedule leftLater).depth + 1
          let rightSource := Reference.referenceSourceIndex rightLater
          have leftSourceOrder : sourceIndex ≤ leftSource :=
            Nat.le_trans (by
              change sourceIndex ≤ max leftStart sourceIndex
              rw [Purelib.Data.Nat.Order.max_eq_natMax]
              exact Purelib.Data.Nat.Order.le_max_right leftStart sourceIndex)
              (Nat.le_trans leftOrder (Nat.le_trans (Integration.Exponential.Selection.selection policy schedule
                leftLater).stage_le_depth (Nat.le_succ _)))
          have rightSourceOrder : sourceIndex ≤ rightSource := Reference.referenceSourceIndex_monotone rightOrder
          have leftBound := Exponential.Horner.Sample.sample_later_close 1 (by decide) leftSourceOrder
          have rightBound : Data.Gaussian.Norm.Basic.normSq (Exponential.Horner.Sample.sample 1 sourceIndex -
              Exponential.Horner.Sample.sample 1 rightSource) ≤ Geometric.Basic.quarterRadius 10 sourceIndex := by
            have reverse : Exponential.Horner.Sample.sample 1 sourceIndex - Exponential.Horner.Sample.sample 1
              rightSource =
                -(Exponential.Horner.Sample.sample 1 rightSource - Exponential.Horner.Sample.sample 1 sourceIndex) := by
                  ring1
            rw [reverse, Norm.Basic.normSq_neg]
            have scalar := Exponential.Horner.Sample.sample_later_close 1 (by decide) rightSourceOrder
            simpa only [Norm.Basic.normSq_eq_canonical] using scalar
          rw [Program.program_sample, Reference.reference_sample, Program.shifted_samples_cancel]
          calc
            Data.Gaussian.Norm.Basic.normSq (Exponential.Horner.Sample.sample 1 leftSource -
              Exponential.Horner.Sample.sample
              1 rightSource) ≤
                2 * (Data.Gaussian.Norm.Basic.normSq (Exponential.Horner.Sample.sample 1 leftSource -
                  Exponential.Horner.Sample.sample 1 sourceIndex) +
                  Data.Gaussian.Norm.Basic.normSq (Exponential.Horner.Sample.sample 1 sourceIndex -
                    Exponential.Horner.Sample.sample 1 rightSource)) :=
              Norm.Bounds.normSq_sub_le_via _ _ _
            _ ≤ 2 * (Geometric.Basic.quarterRadius 10 sourceIndex + Geometric.Basic.quarterRadius 10 sourceIndex) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (Fraction.Order.Arithmetic.add_le_add_direct leftBound rightBound) (by decide)
            _ < 2 * (smallTarget + smallTarget) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct sourceSmall sourceSmall)
            _ = target := by
              calc
                2 * (smallTarget + smallTarget) = (target / 4) * 4 := by
                  dsimp only [smallTarget]
                  ring1
                _ = target := Fraction.Field.div_mul_cancel_of_ne target 4 (by decide) }

/-- The policy-controlled integration output is equivalent to the retained exponential-minus-one reference name.

The sampling transport retains both output names. Its finite comparison uses
the same policy, positive-stride schedule and extra observation depth. -/
@[expose] def output_equivalent_existing (policy : Exponential.Geometry.Policy)
  (schedule : Data.Nat.Schedule.PositiveStride) (extraDepth : Nat) :
    Equivalence.NamedEquivalent (Program.program policy schedule extraDepth).output.name
      Reference.exponentialMinusOne :=
  (Equivalence.Equivalent.toNamed_sampling
    (Program.program policy schedule extraDepth).approximation).trans
      (Existing.approximation_equivalent_existing policy schedule extraDepth)

end Purelib.Integration.Exponential.Equivalence.Existing
end
