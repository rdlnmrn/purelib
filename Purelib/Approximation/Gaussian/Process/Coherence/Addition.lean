module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Coherence.Basic
import Purelib.Approximation.Gaussian.Request.Addition
public import Purelib.Approximation.Rational.Request.Common
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Approximation.Gaussian.Process.Addition
import Init.Prelude
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

public section

/-!
# Finite coherence certificates for progressive CCL processes

`Process` deliberately permits branching refinement strategies: it promises
that every requested branch becomes accurate, but does not by itself say that
two independently refined branches describe one operational value.  This
module adds exactly that missing, finite certificate.

A coherent process assigns a nonnegative rational squared allowance to every
finite state.  The current enclosure radius is no larger than that allowance,
every pair of explicitly possible Gaussian-rational readings is close at the
sum of their allowances, and one ordinary refinement makes the allowance
smaller than any requested positive rational target.  There is no completed
value, infinite carrier, limit, or choice of a value common to all states.
-/

namespace Purelib.Approximation.Gaussian.Process.Coherence.Basic

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Enclosure
open Purelib.Approximation.Gaussian.Request.Basic
open Purelib.Data.Rat

namespace Coherent

/-- Certify coherence of the original stateful sum process.

The semantic allowance is twice the sum of operand allowances; the computed common request pays both operand coherence
thresholds. -/
@[expose] public def add {left right :
  Process} (leftCoherent : Gaussian.Process.Coherence.Basic.Coherent left)
    (rightCoherent : Gaussian.Process.Coherence.Basic.Coherent right) : Gaussian.Process.Coherence.Basic.Coherent
      (left.add right) where
  allowance state :=
    2 * (leftCoherent.allowance state.1 + rightCoherent.allowance state.2)
  allowance_nonneg state :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg (leftCoherent.allowance_nonneg state.1)
        (rightCoherent.allowance_nonneg state.2))
  ball_radius_le state := by
    change 2 *
        ((left.ball state.1).radiusSq + (right.ball state.2).radiusSq) ≤
      2 *
        (leftCoherent.allowance state.1 +
          rightCoherent.allowance state.2)
    exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (leftCoherent.ball_radius_le state.1)
        (rightCoherent.ball_radius_le state.2)) (by decide)
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftX, leftY, leftXPossible, leftYPossible, rfl⟩
      ⟨rightX, rightY, rightXPossible, rightYPossible, rfl⟩
    have leftClose := leftCoherent.possible_close
      leftXPossible rightXPossible
    have rightClose := rightCoherent.possible_close
      leftYPossible rightYPossible
    have difference :
        leftX + leftY - (rightX + rightY) =
          (leftX - rightX) + (leftY - rightY) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.add_re, Purelib.Data.Gaussian.Basic.add_im] <;> ring1
    rw [difference]
    calc
      Data.Gaussian.Norm.Basic.normSq ((leftX - rightX) + (leftY - rightY)) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq (leftX - rightX) + Data.Gaussian.Norm.Basic.normSq
            (leftY - rightY)) :=
        Data.Gaussian.Norm.Bounds.normSq_add_le_two _ _
      _ ≤ 2 *
          (4 * (leftCoherent.allowance leftState.1 +
              leftCoherent.allowance rightState.1) +
            4 * (rightCoherent.allowance leftState.2 +
              rightCoherent.allowance rightState.2)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add leftClose rightClose) (by decide)
      _ = 4 *
          (2 * (leftCoherent.allowance leftState.1 +
              rightCoherent.allowance leftState.2) +
            2 * (leftCoherent.allowance rightState.1 +
              rightCoherent.allowance rightState.2)) := by ring1
  accuracyRequest target :=
    let semanticInputTarget :=
      Name.additiveInputTarget target
    4 * Gaussian.Process.Coherence.Basic.Coherent.commonRequest
      (leftCoherent.accuracyRequest semanticInputTarget)
      (rightCoherent.accuracyRequest semanticInputTarget)
  accuracyRequest_pos := by
    intro target positive
    let semanticInputTarget :=
      Name.additiveInputTarget target
    have semanticPositive : 0 < semanticInputTarget :=
      Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    exact Fraction.Order.Arithmetic.mul_pos_direct (by decide)
      (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_pos
        (leftCoherent.accuracyRequest_pos semanticPositive)
        (rightCoherent.accuracyRequest_pos semanticPositive))
  refine_accurate := by
    intro state target positive request requestPositive requestSmall
    let semanticInputTarget :=
      Name.additiveInputTarget target
    have semanticPositive : 0 < semanticInputTarget :=
      Purelib.Data.Rat.Bounds.Quarter.quarter_pos positive
    let leftRequest := leftCoherent.accuracyRequest semanticInputTarget
    let rightRequest := rightCoherent.accuracyRequest semanticInputTarget
    have leftRequestPositive : 0 < leftRequest :=
      leftCoherent.accuracyRequest_pos semanticPositive
    have rightRequestPositive : 0 < rightRequest :=
      rightCoherent.accuracyRequest_pos semanticPositive
    let sharedRequest := Gaussian.Process.Coherence.Basic.Coherent.commonRequest leftRequest rightRequest
    have sharedPositive : 0 < sharedRequest :=
      Gaussian.Process.Coherence.Basic.Coherent.commonRequest_pos leftRequestPositive rightRequestPositive
    let processInputTarget :=
      Name.additiveInputTarget request
    have processInputPositive : 0 < processInputTarget :=
      Purelib.Data.Rat.Bounds.Quarter.quarter_pos requestPositive
    have processInputSmall : processInputTarget < sharedRequest := by
      apply (Fraction.Order.Field.div_lt_iff_pos
        (show (0 : Fraction.Rational) < 4 by decide)).2
      calc
        request < 4 * sharedRequest := requestSmall
        _ = sharedRequest * 4 :=
          Fraction.Field.mul_comm _ _
    have leftInputSmall : processInputTarget < leftRequest :=
      processInputSmall.trans
        (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_left leftRequestPositive rightRequestPositive)
    have rightInputSmall : processInputTarget < rightRequest :=
      processInputSmall.trans
        (Gaussian.Process.Coherence.Basic.Coherent.commonRequest_lt_right leftRequestPositive rightRequestPositive)
    let leftAllowance : Enclosure.Ball :=
      { center := 0
        radiusSq := leftCoherent.allowance
          (left.refine state.1
            processInputTarget processInputPositive)
        radiusSq_nonneg := leftCoherent.allowance_nonneg _ }
    let rightAllowance : Enclosure.Ball :=
      { center := 0
        radiusSq := rightCoherent.allowance
          (right.refine state.2
            processInputTarget processInputPositive)
        radiusSq_nonneg := rightCoherent.allowance_nonneg _ }
    change (leftAllowance.add rightAllowance).radiusSq < target
    apply Name.add_radius_lt
    · exact leftCoherent.refine_accurate state.1 semanticInputTarget
        semanticPositive processInputTarget processInputPositive leftInputSmall
    · exact rightCoherent.refine_accurate state.2 semanticInputTarget
        semanticPositive processInputTarget processInputPositive rightInputSmall

/-- Certify coherence of the original negated process while retaining its semantic allowance and request function. -/
@[expose] public def neg {process :
  Process} (coherent : Gaussian.Process.Coherence.Basic.Coherent process) :
    Gaussian.Process.Coherence.Basic.Coherent process.neg where
  allowance := coherent.allowance
  allowance_nonneg := coherent.allowance_nonneg
  ball_radius_le := coherent.ball_radius_le
  possible_close := by
    rintro leftState rightState leftValue rightValue
      ⟨leftSource, leftPossible, rfl⟩
      ⟨rightSource, rightPossible, rfl⟩
    have close := coherent.possible_close leftPossible rightPossible
    have difference :
        -leftSource - -rightSource = -(leftSource - rightSource) := by
      apply Data.Gaussian.Basic.ext <;>
        simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
          Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
    rw [difference, Data.Gaussian.Norm.Basic.normSq_neg]
    exact close
  accuracyRequest := coherent.accuracyRequest
  accuracyRequest_pos := coherent.accuracyRequest_pos
  refine_accurate := coherent.refine_accurate

/-- Certify coherence of the original difference process by composing sum and negation certificates. -/
@[expose] public def sub {left right :
  Process} (leftCoherent : Gaussian.Process.Coherence.Basic.Coherent left)
    (rightCoherent : Gaussian.Process.Coherence.Basic.Coherent right) : Gaussian.Process.Coherence.Basic.Coherent
      (left.sub right) :=
  add leftCoherent
    (neg rightCoherent)
end Coherent

end Purelib.Approximation.Gaussian.Process.Coherence.Basic

end
