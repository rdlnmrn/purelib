module
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Approximation.Gaussian.Sequence.Process
public import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Data.Nat.Order
import Purelib.Data.Nat.Subtraction

/-!
# Sampling readback and operational comparison transport

Canonical process sampling retains the approximation's selected natural indices.
Tail comparisons transport through those exact indices and observations to the
CCL names constructed from the original approximation owners.
-/

namespace Purelib.Approximation.Gaussian.Equivalence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Nat

/-- The index of the original approximation selected by the canonical sampling path of the CCL name generated from it.

The canonical sampling trajectory starts the original approximation process
at index zero. This readback returns its exact selected natural state,
retaining the original refinement requests and index cache. -/
@[expose] public def Sampling.emittedSampleIndex (approximation : ApproximationData)
  (index : Nat) : Nat :=
  Gaussian.Process.Sampling.stateAt approximation.toProcess
    (show approximation.toProcess.State from (0 : Nat)) index

/-- The original approximation index selected by canonical resampling does not decrease at the next sample.

The next canonical state calls the original refinement-index function
with the next sampling request. Its retained start-bound certificate gives
the displayed monotonicity without selecting another state. -/
public theorem Sampling.emittedSampleIndex_step (approximation : ApproximationData)
  (index : Nat) :
    Sampling.emittedSampleIndex approximation index ≤
      Sampling.emittedSampleIndex approximation (index + 1) := by
  change Sampling.emittedSampleIndex approximation index ≤
    approximation.refineIndex (Sampling.emittedSampleIndex approximation index)
      (Gaussian.Process.Sampling.refinementTarget (index + 1))
      (Gaussian.Process.Sampling.refinementTarget_pos (index + 1))
  exact approximation.refineIndex_ge _ _ _

/-- The original approximation indices selected by canonical resampling are monotone.

The retained natural stage order gives an explicit finite difference.
Induction across that many original successor refinements relates the
exact earlier and later approximation indices. -/
public theorem Sampling.emittedSampleIndex_mono (approximation : ApproximationData)
    {earlier later : Nat} (order : earlier ≤ later) :
    Sampling.emittedSampleIndex approximation earlier ≤
      Sampling.emittedSampleIndex approximation later := by
  have extended : ∀ extra : Nat,
      Sampling.emittedSampleIndex approximation earlier ≤
        Sampling.emittedSampleIndex approximation (earlier + extra) := by
    intro extra
    induction extra with
    | zero => exact Nat.le_refl _
    | succ extra inductionHypothesis =>
        exact inductionHypothesis.trans (by
          simpa only [Nat.add_assoc] using
            Sampling.emittedSampleIndex_step approximation (earlier + extra))
  have atExtended := extended (later - earlier)
  rw [Subtraction.add_sub_of_le order] at atExtended
  exact atExtended

/-- The canonical sample of an emitted name is the original approximation sample at its retained selected index.

The controller uses the original approximation process, whose witness
at each selected natural state is the original sample. Both readbacks
therefore use that same retained index and sample function. -/
public theorem Sampling.emittedSample_eq (approximation : ApproximationData) (index :
  Nat) :
    (Gaussian.Name.Sampling.approximation
      approximation.toNamed).sample index =
        approximation.sample (Sampling.emittedSampleIndex approximation index) := by
  change approximation.sample
      (Gaussian.Process.Sampling.stateAt approximation.toProcess
        (show approximation.toProcess.State from (0 : Nat)) index) =
    approximation.sample (Sampling.emittedSampleIndex approximation index)
  rfl

/-- Passing a finite approximation through the ordinary productive CCL controller and then sampling that CCL name
preserves its operational value. The controller may choose different displayed indices, but all comparisons remain
finite and are synchronized through one explicitly accurate emitted index.

The comparison refines the canonical sampling trajectory at the displayed
quarter tolerance, reads its retained approximation index, and retains the
maximum of that index and the original right start for the other comparison index. -/
@[expose] public def Equivalent.toNamed_sampling (approximation : ApproximationData) :
    Equivalent
      (Gaussian.Name.Sampling.approximation
        approximation.toNamed)
      approximation where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 4
    have smallPositive : 0 < smallTarget := Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let leftIndex := Search.firstQuarterBelow
      1 leftStart smallTarget
    let baseIndex := Sampling.emittedSampleIndex approximation leftIndex
    let rightIndex := max rightStart baseIndex
    have rightMaximum : rightStart ≤ rightIndex := by
      change rightStart ≤ max rightStart baseIndex
      rw [Order.max_eq_natMax]
      exact Order.le_max_left _ _
    have baseMaximum : baseIndex ≤ rightIndex := by
      change baseIndex ≤ max rightStart baseIndex
      rw [Order.max_eq_natMax]
      exact Order.le_max_right _ _
    have emittedRadius :
        approximation.radiusSq baseIndex <
          Gaussian.Process.Sampling.refinementTarget leftIndex := by
      exact Gaussian.Process.Sampling.stateAt_accurate
        approximation.toProcess
          (show approximation.toProcess.State from (0 : Nat)) leftIndex
    have targetRadius :
        Gaussian.Process.Sampling.refinementTarget leftIndex <
          smallTarget := by
      exact Search.firstQuarterBelow_accurate
        1 (by decide) leftStart smallTarget smallPositive
    have radiusSmall : approximation.radiusSq baseIndex < smallTarget :=
      emittedRadius.trans targetRadius
    exact
      { leftIndex := leftIndex
        rightIndex := rightIndex
        left_ge := Search.firstQuarterBelow_ge
          1 leftStart smallTarget
        right_ge := rightMaximum
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have baseToLeft : baseIndex ≤
              Sampling.emittedSampleIndex approximation leftLater :=
            Sampling.emittedSampleIndex_mono approximation leftOrder
          have baseToRight : baseIndex ≤ rightLater :=
            baseMaximum.trans rightOrder
          have leftClose := approximation.later_close baseToLeft
          have rightCloseForward := approximation.later_close baseToRight
          have rightClose :
              Data.Gaussian.Norm.Basic.normSq
                  (approximation.sample baseIndex -
                    approximation.sample rightLater) ≤
                approximation.radiusSq baseIndex := by
            have identity :
                approximation.sample baseIndex -
                    approximation.sample rightLater =
                  -(approximation.sample rightLater -
                    approximation.sample baseIndex) := by
              apply Basic.ext <;>
                simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im] <;> ring1
            rw [identity, Norm.Basic.normSq_neg]
            exact rightCloseForward
          rw [Sampling.emittedSample_eq]
          calc
            Data.Gaussian.Norm.Basic.normSq
                (approximation.sample
                    (Sampling.emittedSampleIndex approximation leftLater) -
                  approximation.sample rightLater) ≤
              2 * (Data.Gaussian.Norm.Basic.normSq
                  (approximation.sample
                      (Sampling.emittedSampleIndex approximation leftLater) -
                    approximation.sample baseIndex) +
                Data.Gaussian.Norm.Basic.normSq
                  (approximation.sample baseIndex -
                    approximation.sample rightLater)) :=
                Norm.Bounds.normSq_sub_le_via _ _ _
            _ ≤ 2 * (approximation.radiusSq baseIndex +
                approximation.radiusSq baseIndex) :=
              Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                (add_le_add leftClose rightClose) (by decide)
            _ < 2 * (smallTarget + smallTarget) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  radiusSmall radiusSmall)
            _ = target := by
              dsimp only [smallTarget]
              have quarterSum : target / 4 + target / 4 = target / 2 := by
                apply Fraction.Field.mul_right_cancel_of_ne
                  (show (4 : Fraction.Rational) ≠ 0 by decide)
                calc
                  (target / 4 + target / 4) * 4 =
                      (target / 4) * 4 + (target / 4) * 4 := by rw [add_mul]
                  _ = target + target := by
                    rw [show target / 4 * 4 = target from
                      Fraction.Field.div_mul_cancel_of_ne target 4 (by decide)]
                  _ = target * 2 := by ring1
                  _ = ((target / 2) * 2) * 2 := by
                    rw [show target / 2 * 2 = target from
                      Fraction.Field.div_mul_cancel_of_ne target 2 (by decide)]
                  _ = (target / 2) * (2 * 2) :=
                    Fraction.Field.mul_assoc (target / 2) 2 2
                  _ = (target / 2) * 4 := by
                    rw [show (2 : Fraction.Rational) * 2 = 4 by decide]
              rw [quarterSum, Fraction.Field.mul_comm]
              exact Fraction.Field.div_mul_cancel_of_ne target 2 (by decide) }

/-- Lift an operational equivalence between two finite approximations through their ordinary productive CCL wrappers.
This bridge belongs to the core operational layer: it uses only the two sampler equivalences and does not depend on any
transcendental operation.

Each original approximation is related to its own canonical resampling.
Those two retained round-trip comparisons compose with the supplied
finite approximation equivalence through the same original owners. -/
@[expose] public def Equivalent.toNamed {left right : ApproximationData}
    (equivalent : Equivalent left right) :
    NamedEquivalent left.toNamed right.toNamed :=
  Equivalent.trans
    (Equivalent.toNamed_sampling left)
    (Equivalent.trans equivalent
      (Equivalent.symm (Equivalent.toNamed_sampling right)))

end Purelib.Approximation.Gaussian.Equivalence
