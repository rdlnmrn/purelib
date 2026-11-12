module
import Purelib.Data.Rat.Fraction
import Purelib.Approximation.Gaussian.Enclosure.Sector.Budget
import Purelib.Approximation.Gaussian.Process.Basic
public import Purelib.Approximation.Gaussian.Process.Gamma.Upscale
import Purelib.Data.CCL.Transducer.Emission.Initial.Budget
public import Purelib.Data.CCL.Transducer.Emission.Initial.Preparation
import Purelib.Data.CCL.Transducer.Emission.Low.Budget
public import Purelib.Data.CCL.Transducer.Mode.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Gaussian.Power
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

section
@[expose] public section

/-!
# Productive progressive CCL output transducer

This is the finite-prefix controller for the redundant arithmetic layer.  A
loop mode represents a normalized progressive tail.  A residual mode is used
after a sector has been emitted but before equality with its representative
can be decided.  It either emits finite unary padding or, once apartness is
visible, changes to the exact normalized inverse chart.

The canonical terminating rational encoder is not changed.  This controller
only produces the progressive, potentially non-returning arithmetic word.
-/

namespace Purelib.Data.CCL.Transducer.Emission.Low.Preparation

open Purelib.Approximation.Gaussian in
open Purelib.Data.CCL.Transducer in
open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
/-- The exact initial refinement of a low state has center squared norm strictly below 13/6.

A retained possible witness supplies the old 43/20 bound. The initial radius budget and fixed low-center weight bound
the center error without replacing the process or its refined state. -/
theorem low_center_lt_extended_upper
    (current : Mode.Basic.LowState) :
    Norm.Basic.normSq
        (current.process.ball
          (Initial.Preparation.initialRefinedState current.process current.state)).center <
      13 / 6 := by
  let refined := Initial.Preparation.initialRefinedState current.process current.state
  rcases current.process.witness refined with ⟨witness, possible⟩
  have possibleAtOld : current.process.Possible current.state witness :=
    current.process.refine_persists current.state _ _ possible
  have witnessUpper : Norm.Basic.normSq witness < 43 / 20 :=
    current.upperBound possibleAtOld
  have errorNorm :
      Norm.Basic.normSq ((current.process.ball refined).center - witness) ≤
        (current.process.ball refined).radiusSq := by
    have reversed :
        (current.process.ball refined).center - witness =
          -(witness - (current.process.ball refined).center) := by
      apply Basic.ext <;>
        simp only [Basic.sub_re, Basic.sub_im, Basic.neg_re, Basic.neg_im] <;> ring1
    rw [reversed, Norm.Basic.normSq_neg]
    exact current.process.possible_inside possible
  have radiusUpper := Initial.Preparation.initialRefined_accurate current.process current.state
  have weightPlusPositive : 0 < Budget.lowCenterWeight + 1 :=
    add_pos_of_pos_of_nonneg Budget.lowCenterWeight_pos (by decide)
  have errorScaled : (Budget.lowCenterWeight + 1) *
      Norm.Basic.normSq ((current.process.ball refined).center - witness) <
      Budget.lowCenterSlack := by
    have first : (Budget.lowCenterWeight + 1) *
        Norm.Basic.normSq ((current.process.ball refined).center - witness) <
        (Budget.lowCenterWeight + 1) * Initial.Budget.initialRadiusSq :=
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        errorNorm weightPlusPositive.le).trans_lt
        (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
          weightPlusPositive radiusUpper)
    have second : (Budget.lowCenterWeight + 1) * Initial.Budget.initialRadiusSq <
        2 * Enclosure.Sector.Budget.uniformRadiusSq := by
      calc
        (Budget.lowCenterWeight + 1) * Initial.Budget.initialRadiusSq =
            Budget.lowCenterWeight * Initial.Budget.initialRadiusSq +
              Emission.Initial.Budget.initialRadiusSq := by ring1
        _ = Enclosure.Sector.Budget.uniformRadiusSq +
            Emission.Initial.Budget.initialRadiusSq := by rw [Budget.lowCenterWeight_mul_initial]
        _ = Initial.Budget.initialRadiusSq +
            Enclosure.Sector.Budget.uniformRadiusSq := by ring1
        _ < Enclosure.Sector.Budget.uniformRadiusSq +
            Enclosure.Sector.Budget.uniformRadiusSq :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct
            Initial.Budget.initialRadiusSq_lt_uniform Enclosure.Sector.Budget.uniformRadiusSq
        _ = 2 * Enclosure.Sector.Budget.uniformRadiusSq := by ring1
    exact first.trans (second.trans Budget.two_uniform_lt_lowCenterSlack)
  have witnessDivWeight : Norm.Basic.normSq witness / Budget.lowCenterWeight <
      Budget.lowCenterSlack := by
    apply (Fraction.Order.Field.div_lt_iff_pos
      Budget.lowCenterWeight_pos).2
    rw [Budget.lowCenterSlack_mul_weight]
    have fortyThreeTwentiethsLtFive : (43 / 20 : Fraction.Rational) < 5 := by
      apply (Fraction.Order.Field.div_lt_iff_pos
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 20) (by decide))).2
      calc
        (43 : Fraction.Rational) < 100 :=
          Fraction.Cast.Order.natCast_lt_direct (by decide)
        _ = 5 * 20 := by ring1
    exact witnessUpper.trans fortyThreeTwentiethsLtFive
  have ratioIdentity :
      ((Budget.lowCenterWeight + 1) / Budget.lowCenterWeight) *
        Norm.Basic.normSq witness =
        Norm.Basic.normSq witness + Norm.Basic.normSq witness /
          Budget.lowCenterWeight := by
    have weightNonzero := Budget.lowCenterWeight_pos.ne'
    apply Fraction.Field.mul_right_cancel_of_ne
      Budget.lowCenterWeight_pos.ne'
    calc
      (((Budget.lowCenterWeight + 1) / Budget.lowCenterWeight) *
        Norm.Basic.normSq witness) *
          Budget.lowCenterWeight =
          Norm.Basic.normSq witness *
            (((Budget.lowCenterWeight + 1) / Budget.lowCenterWeight) *
              Budget.lowCenterWeight) := by ring1
      _ = Norm.Basic.normSq witness * (Budget.lowCenterWeight + 1) := by
        have cancellation :
            (Budget.lowCenterWeight + 1) / Budget.lowCenterWeight *
              Budget.lowCenterWeight =
              Budget.lowCenterWeight + 1 :=
          Fraction.Field.div_mul_cancel_of_ne _ _ weightNonzero
        rw [cancellation]
      _ = (Norm.Basic.normSq witness + Norm.Basic.normSq witness /
        Budget.lowCenterWeight) *
          Emission.Low.Budget.lowCenterWeight := by
        have cancellation : Norm.Basic.normSq witness / Budget.lowCenterWeight *
            Budget.lowCenterWeight = Norm.Basic.normSq witness :=
          Fraction.Field.div_mul_cancel_of_ne _ _ weightNonzero
        rw [show (Norm.Basic.normSq witness + Norm.Basic.normSq witness /
          Budget.lowCenterWeight) *
            Budget.lowCenterWeight = Norm.Basic.normSq witness *
              Budget.lowCenterWeight +
              (Norm.Basic.normSq witness / Budget.lowCenterWeight) *
                Budget.lowCenterWeight by ring1,
          cancellation]
        ring1
  have witnessScaled :
      ((Budget.lowCenterWeight + 1) / Budget.lowCenterWeight) *
        Norm.Basic.normSq witness <
        (43 / 20 : Fraction.Rational) + Budget.lowCenterSlack := by
    rw [ratioIdentity]
    exact Fraction.Order.Arithmetic.add_lt_add_direct witnessUpper
      witnessDivWeight
  have decomposition :
      (current.process.ball refined).center =
        ((current.process.ball refined).center - witness) + witness := by
    apply Basic.ext <;>
      simp only [Basic.sub_re, Basic.sub_im, Basic.add_re, Basic.add_im] <;> ring1
  rw [decomposition]
  exact (Norm.Weighted.normSq_add_le_parameter Budget.lowCenterWeight
    Budget.lowCenterWeight_pos
      ((current.process.ball refined).center - witness) witness).trans_lt (calc
    (Budget.lowCenterWeight + 1) *
          Norm.Basic.normSq ((current.process.ball refined).center - witness) +
        ((Budget.lowCenterWeight + 1) / Budget.lowCenterWeight) *
          Norm.Basic.normSq witness <
      Budget.lowCenterSlack + ((43 / 20 : Fraction.Rational) +
        Budget.lowCenterSlack) :=
        Fraction.Order.Arithmetic.add_lt_add_direct errorScaled witnessScaled
    _ = (43 / 20 : Fraction.Rational) + Budget.lowCenterSlack +
      Emission.Low.Budget.lowCenterSlack := by
      ring1
    _ < 13 / 6 := Budget.lowCenter_budget)

open Purelib.Approximation.Gaussian
open Purelib.Data.CCL.Transducer
open Purelib.Data.Gaussian
/-- Scale the exact supplied accurate small-center state by gamma and retain it as a low state at the requested count.

The constructed process is based at the same supplied state. Its possible-value semantics and the retained initial
radius budget establish the low squared-norm bound 43/20. -/
def nextLowState (process : Process) (base :
  process.State)
    (accurate : (process.ball base).radiusSq < Initial.Budget.initialRadiusSq)
    (centerSmall : Norm.Basic.normSq (process.ball base).center < 1)
    (count : Nat) : Mode.Basic.LowState := by
  let nextProcess := Process.Gamma.Upscale.upscaledProcess process base 1
  let nextState := Process.Gamma.Upscale.upscaledInitial process base 1
  exact
    { count := count
      process := nextProcess
      state := nextState
      upperBound := by
        intro value possible
        rcases Process.Gamma.Upscale.upscaled_candidate_semantics process base 1 possible with
          ⟨sourceValue, sourcePossible, valueEqual⟩
        rw [valueEqual, Power.natPow_succ, Power.natPow_zero,
          Basic.one_mul]
        exact Initial.Preparation.scaled_candidate_norm_lt_low_upper accurate centerSmall
          sourcePossible }

/-- The constructed next low state keeps exactly the supplied normalization count. -/
@[simp] theorem nextLowState_count (process :
  Approximation.Gaussian.Process) (base : process.State)
    (accurate : (process.ball base).radiusSq < Initial.Budget.initialRadiusSq)
    (centerSmall : Norm.Basic.normSq (process.ball base).center < 1) (count : Nat) :
    (nextLowState process base accurate centerSmall count).count = count := by
  rfl

end Purelib.Data.CCL.Transducer.Emission.Low.Preparation

end
