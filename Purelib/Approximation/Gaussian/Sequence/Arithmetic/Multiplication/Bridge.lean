module
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Gaussian.Equivalence
public import Purelib.Approximation.Gaussian.Equivalence.Sampling
public import Purelib.Approximation.Gaussian.Name.Arithmetic
import Purelib.Approximation.Gaussian.Name.Sampling
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Approximation.Gaussian.Request.Basic
import Purelib.Approximation.Gaussian.Request.Multiplication
public import Purelib.Approximation.Gaussian.Sampling.Dyadic
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Purelib.Data.Nat.Order
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Approximation.Gaussian.Process.Multiplication
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Approximation.Gaussian.Sequence.Process
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction.Order

/-!
# Arithmetic-process bridges for Gaussian sample products

The comparison retains both operand approximations and the arithmetic product
process. Its coefficient, request payment and selected component indices bound
the same finite sampled product observations.
-/

namespace Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Name
open Purelib.Approximation.Gaussian.Name.Basic
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Approximation.Gaussian.Sequence
open Purelib.Approximation.Rational.Geometric
open Purelib.Data.Rat
open Purelib.Data.Nat

/-- A positive product refinement request below both operand accuracy requests makes both retained operand radii smaller
than the target.

The arithmetic product refines both retained operand states with its computed positive input target. The two component
accuracy certificates bound these same operand radii by the requested output target. -/
private theorem approximationMul_refine_component_radius_lt
    (left right : ApproximationData)
    (state : left.toProcess.State × right.toProcess.State)
    (target : Fraction.Rational) (positive : 0 < target) :
    let refined := (left.toProcess.mul right.toProcess).refine
      state target positive
    left.radiusSq refined.1 < target ∧ right.radiusSq refined.2 < target := by
  let leftName := Name.centerOnly
    (left.sample state.1) left.centerBound left.centerBound_nonneg
      (left.sample_bounded state.1)
  let rightName := Name.centerOnly
    (right.sample state.2) right.centerBound right.centerBound_nonneg
      (right.sample_bounded state.2)
  let inputTarget :=
    Name.multiplicativeInputTarget
      leftName rightName target
  have inputPositive : 0 < inputTarget :=
    Name.multiplicativeInputTarget_pos
      leftName rightName positive
  have inputLt : inputTarget < target :=
    Process.Coherence.Basic.Coherent.processMultiplicativeInputTarget_lt_target
      leftName rightName positive
  change left.radiusSq
        (left.refineIndex state.1 inputTarget inputPositive) < target ∧
      right.radiusSq
        (right.refineIndex state.2 inputTarget inputPositive) < target
  exact ⟨(left.refineIndex_accurate state.1 inputTarget inputPositive).trans
      inputLt,
    (right.refineIndex_accurate state.2 inputTarget inputPositive).trans
      inputLt⟩

/-- A canonical product sample satisfying both operand request bounds has both component radii below the positive
target.

The canonical finite sample follows the product process from the supplied starting pair. Its last refinement bounds both
retained operand radii by that index's positive refinement target. -/
public theorem approximationMul_stateAt_component_radius_lt
    (left right : ApproximationData)
    (start : left.toProcess.State × right.toProcess.State) (index : Nat) :
    let state := Process.Sampling.stateAt
      (left.toProcess.mul right.toProcess) start index
    left.radiusSq state.1 <
        Process.Sampling.refinementTarget index ∧
      right.radiusSq state.2 <
        Process.Sampling.refinementTarget index := by
  cases index with
  | zero =>
      exact approximationMul_refine_component_radius_lt left right start _ _
  | succ index =>
      exact approximationMul_refine_component_radius_lt left right
        (Process.Sampling.stateAt
          (left.toProcess.mul right.toProcess) start index) _ _

/-- The canonical product witness is the product of the original operand samples at the two retained component indices.

The product process reads the two retained component states at the same finite sample index. Its multiplication
operation returns their Gaussian product directly. -/
private theorem approximationMul_witnessAt_eq
    (left right : ApproximationData)
    (start : left.toProcess.State × right.toProcess.State) (index : Nat) :
    Process.Sampling.witnessAt
        (left.toProcess.mul right.toProcess) start index =
      left.sample
          (Process.Sampling.stateAt
            (left.toProcess.mul right.toProcess) start index).1 *
        right.sample
          (Process.Sampling.stateAt
            (left.toProcess.mul right.toProcess) start index).2 :=
  rfl

/-- The positive rational product comparison coefficient determined by the two operand center bounds.

The operand center bounds determine this same rational coefficient, including zero center bounds. Both original
approximations remain its inputs. -/
@[expose] public def approximationMulBridgeCoefficient
    (left right : ApproximationData) : Fraction.Rational :=
  8 + 4 * (left.centerBound + right.centerBound)

/-- The original product comparison coefficient pays two equal operand tolerances with their actual magnitude ceilings.

The two positive unit margins are bounded by the retained constant eight;
the doubled actual operand ceilings are bounded by its retained factor four.
No nonzero magnitude assumption is needed for either operand.
-/
public theorem approximationMulBridgeCoefficient_pair_bound (left right : ApproximationData)
    (target : Fraction.Rational) (nonnegative : 0 ≤ target) :
    2 * (target * left.centerBound + right.centerBound * target) + target + target ≤
      target * approximationMulBridgeCoefficient left right := by
  apply Arithmetic.le_of_sub_nonneg_direct
  change 0 ≤ target * (8 + 4 * (left.centerBound + right.centerBound)) - _
  have same : target * (8 + 4 * (left.centerBound + right.centerBound)) -
      (2 * (target * left.centerBound + right.centerBound * target) + target + target) =
      target * (6 + 2 * (left.centerBound + right.centerBound)) := by ring1
  rewrite [same]
  exact Arithmetic.mul_nonneg_direct nonnegative
    (add_nonneg (by decide : (0 : Fraction.Rational) ≤ 6)
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2)
        (add_nonneg left.centerBound_nonneg right.centerBound_nonneg)))

/-- The product comparison coefficient is strictly positive.

The constant eight is positive and the two retained center bounds are nonnegative. Their scaled sum therefore preserves
strict positivity of the displayed coefficient. -/
public theorem approximationMulBridgeCoefficient_pos
    (left right : ApproximationData) :
    0 < approximationMulBridgeCoefficient left right := by
  unfold approximationMulBridgeCoefficient
  exact Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
    (Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg left.centerBound_nonneg right.centerBound_nonneg))

/-- The operand comparison tolerance obtained by dividing the output target by one plus its retained product comparison
coefficient.

The target is divided by one plus the retained positive comparison coefficient. The original operand approximations and
rational division operation are preserved. -/
@[expose] public def approximationMulBridgeTarget
    (left right : ApproximationData) (target : Fraction.Rational) : Fraction.Rational :=
  target / (1 + approximationMulBridgeCoefficient left right)

/-- The operand comparison tolerance is positive for a positive output target.

The comparison coefficient is positive, so adding one keeps its denominator positive. Dividing the supplied positive
output target preserves strict positivity. -/
public theorem approximationMulBridgeTarget_pos (left right : ApproximationData)
    {target : Fraction.Rational} (positive : 0 < target) :
    0 < approximationMulBridgeTarget left right target :=
  Field.div_pos_direct positive
    (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide)
      (approximationMulBridgeCoefficient_pos left right).le)

open Purelib.Approximation.Rational.Budget in
/-- The scaled operand comparison tolerance stays strictly below the requested positive product tolerance.

The coefficient is strictly smaller than one plus itself. Multiplication by the supplied positive output target
transfers this strict ratio bound to the retained tolerance payment. -/
public theorem approximationMulBridgeTarget_budget_lt
    (left right : ApproximationData) {target : Fraction.Rational}
    (positive : 0 < target) :
    approximationMulBridgeTarget left right target *
        approximationMulBridgeCoefficient left right < target := by
  have paid := Weighted.mul_allowance_lt positive (approximationMulBridgeCoefficient_pos left right).le
  rewrite [Weighted.allowance_eq_div_one_add] at paid
  exact (Fraction.Field.mul_comm _ _).trans_lt paid

/-- The actual arithmetic product process agrees operationally with the supplied pointwise sample product.

The finite comparison retains both component sample indices, their original approximation owners and the requested
tolerance. The supplied pointwise product equation links these exact observations to the supplied product approximation.
-/
@[expose] public def mulToNamed_equivalent_pointwise (left right product : ApproximationData)
    (sample_eq : ∀ index,
      product.sample index = left.sample index * right.sample index) :
    NamedEquivalent
      (Named.mul
        left.toNamed right.toNamed)
      product.toNamed := by
  let process := left.toProcess.mul right.toProcess
  let start : process.State :=
    (show left.toProcess.State from (0 : Nat),
      show right.toProcess.State from (0 : Nat))
  let bridge : Equivalent
      (Sampling.approximation
        (Named.mul
          left.toNamed right.toNamed)) product :=
    { compare := by
        intro leftStart rightStart target positive
        let smallTarget := approximationMulBridgeTarget left right target
        have smallPositive : 0 < smallTarget :=
          approximationMulBridgeTarget_pos left right positive
        let leftIndex := Search.firstQuarterBelow
          1 leftStart smallTarget
        have leftIndexGe : leftStart ≤ leftIndex :=
          Search.firstQuarterBelow_ge
            1 leftStart smallTarget
        have outerSmall :
            Process.Sampling.refinementTarget leftIndex <
              smallTarget :=
          Search.firstQuarterBelow_accurate
            1 (by decide) leftStart smallTarget smallPositive
        let baseState := Process.Sampling.stateAt
          process start leftIndex
        let baseLeft : Nat := baseState.1
        let baseRight : Nat := baseState.2
        have componentSmall :
            left.radiusSq baseLeft <
                Process.Sampling.refinementTarget leftIndex ∧
              right.radiusSq baseRight <
                Process.Sampling.refinementTarget leftIndex :=
          approximationMul_stateAt_component_radius_lt
            left right start leftIndex
        let rightIndex := max rightStart (max baseLeft baseRight)
        exact
          { leftIndex := leftIndex
            rightIndex := rightIndex
            left_ge := leftIndexGe
            right_ge := Order.le_max_left _ _
            close := by
              intro leftLater rightLater leftOrder rightOrder
              have leftComponentOrder : baseLeft ≤ rightLater :=
                (Order.le_max_left baseLeft baseRight).trans
                  ((Order.le_max_right rightStart
                    (max baseLeft baseRight)).trans rightOrder)
              have rightComponentOrder : baseRight ≤ rightLater :=
                (Order.le_max_right baseLeft baseRight).trans
                  ((Order.le_max_right rightStart
                    (max baseLeft baseRight)).trans rightOrder)
              have leftMovementForward := left.later_close leftComponentOrder
              have rightMovementForward := right.later_close rightComponentOrder
              have leftMovement :
                  Basic.normSq
                      (left.sample baseLeft -
                        left.sample rightLater) ≤
                    left.radiusSq baseLeft := by
                have identity :
                    left.sample baseLeft - left.sample rightLater =
                      -(left.sample rightLater - left.sample baseLeft) := by
                  apply Data.Gaussian.Basic.ext <;>
                    simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                      Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
                rw [identity, Basic.normSq_neg]
                exact leftMovementForward
              have rightMovement :
                  Basic.normSq
                      (right.sample baseRight -
                        right.sample rightLater) ≤
                    right.radiusSq baseRight := by
                have identity :
                    right.sample baseRight - right.sample rightLater =
                      -(right.sample rightLater - right.sample baseRight) := by
                  apply Data.Gaussian.Basic.ext <;>
                    simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                      Data.Gaussian.Basic.neg_re, Data.Gaussian.Basic.neg_im] <;> ring1
                rw [identity, Basic.normSq_neg]
                exact rightMovementForward
              have firstTerm :
                  Basic.normSq
                      ((left.sample baseLeft - left.sample rightLater) *
                        right.sample baseRight) ≤
                    left.radiusSq baseLeft * right.centerBound := by
                rw [Basic.normSq_mul]
                exact Arithmetic.mul_le_mul_direct
                  leftMovement (right.sample_bounded baseRight)
                  (Basic.normSq_nonneg _) (left.radiusSq_nonneg baseLeft)
              have secondTerm :
                  Basic.normSq
                      (left.sample rightLater *
                        (right.sample baseRight -
                          right.sample rightLater)) ≤
                    left.centerBound * right.radiusSq baseRight := by
                rw [Basic.normSq_mul]
                exact Arithmetic.mul_le_mul_direct
                  (left.sample_bounded rightLater) rightMovement
                  (Basic.normSq_nonneg _) left.centerBound_nonneg
              have productIdentity :
                  left.sample baseLeft * right.sample baseRight -
                      left.sample rightLater * right.sample rightLater =
                    (left.sample baseLeft - left.sample rightLater) *
                        right.sample baseRight +
                      left.sample rightLater *
                        (right.sample baseRight -
                          right.sample rightLater) := by
                apply Data.Gaussian.Basic.ext <;>
                  simp only [Data.Gaussian.Basic.sub_re, Data.Gaussian.Basic.sub_im,
                    Data.Gaussian.Basic.add_re, Data.Gaussian.Basic.add_im,
                    Data.Gaussian.Basic.mul_re, Data.Gaussian.Basic.mul_im] <;>
                    ring1
              have pointwiseBound :
                  Basic.normSq
                      (left.sample baseLeft * right.sample baseRight -
                        product.sample rightLater) ≤
                    2 *
                      (Process.Sampling.refinementTarget
                          leftIndex * right.centerBound +
                        left.centerBound *
                          Process.Sampling.refinementTarget
                            leftIndex) := by
                rw [sample_eq, productIdentity]
                calc
                  Basic.normSq
                      ((left.sample baseLeft - left.sample rightLater) *
                          right.sample baseRight +
                        left.sample rightLater *
                          (right.sample baseRight -
                            right.sample rightLater)) ≤
                    2 *
                      (Basic.normSq
                          ((left.sample baseLeft -
                              left.sample rightLater) *
                            right.sample baseRight) +
                        Basic.normSq
                          (left.sample rightLater *
                            (right.sample baseRight -
                              right.sample rightLater))) :=
                    Bounds.normSq_add_le_two _ _
                  _ ≤ 2 *
                      (left.radiusSq baseLeft * right.centerBound +
                        left.centerBound * right.radiusSq baseRight) :=
                    Arithmetic.mul_le_mul_of_nonneg_left_direct
                      (add_le_add firstTerm secondTerm) (by decide)
                  _ ≤ 2 *
                      (Process.Sampling.refinementTarget
                          leftIndex * right.centerBound +
                        left.centerBound *
                          Process.Sampling.refinementTarget
                            leftIndex) :=
                    Arithmetic.mul_le_mul_of_nonneg_left_direct
                      (add_le_add
                        (Arithmetic.mul_le_mul_of_nonneg_right_direct
                          componentSmall.1.le right.centerBound_nonneg)
                        (Arithmetic.mul_le_mul_of_nonneg_left_direct
                          componentSmall.2.le left.centerBound_nonneg))
                      (by decide)
              have actualTail :
                  Basic.normSq
                      (Process.Sampling.witnessAt
                          process start leftLater -
                        Process.Sampling.witnessAt
                          process start leftIndex) ≤
                    4 * Process.Sampling.refinementTarget
                      leftIndex := by
                rw [← Sampling.Dyadic.quarterRadius_four_eq_four_refinementTarget]
                exact Process.Sampling.witnessAt_later_close
                  process start leftOrder
              change Basic.normSq
                  (Process.Sampling.witnessAt
                      process start leftLater - product.sample rightLater) <
                target
              calc
                Basic.normSq
                    (Process.Sampling.witnessAt
                        process start leftLater - product.sample rightLater) ≤
                  2 *
                    (Basic.normSq
                        (Process.Sampling.witnessAt
                            process start leftLater -
                          Process.Sampling.witnessAt
                            process start leftIndex) +
                      Basic.normSq
                        (Process.Sampling.witnessAt
                            process start leftIndex -
                          product.sample rightLater)) :=
                    Bounds.normSq_sub_le_via _ _ _
                _ ≤ 2 *
                    (4 *
                        Process.Sampling.refinementTarget
                          leftIndex +
                      2 *
                        (Process.Sampling.refinementTarget
                            leftIndex * right.centerBound +
                          left.centerBound *
                            Process.Sampling.refinementTarget
                              leftIndex)) := by
                  apply Arithmetic.mul_le_mul_of_nonneg_left_direct
                  · apply add_le_add actualTail
                    rw [approximationMul_witnessAt_eq]
                    exact pointwiseBound
                  · decide
                _ = Process.Sampling.refinementTarget
                      leftIndex *
                    approximationMulBridgeCoefficient left right := by
                  unfold approximationMulBridgeCoefficient
                  ring1
                _ < smallTarget *
                    approximationMulBridgeCoefficient left right :=
                  Arithmetic.mul_lt_mul_of_pos_right_direct
                    outerSmall
                    (approximationMulBridgeCoefficient_pos left right)
                _ < target :=
                  approximationMulBridgeTarget_budget_lt left right positive } }
  exact Equivalent.trans bridge
    (Equivalent.symm
      (Equivalent.toNamed_sampling
        product))

end Purelib.Approximation.Gaussian.Sequence.Arithmetic.Multiplication.Bridge
