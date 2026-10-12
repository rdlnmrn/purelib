module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Process.Apart.Possible
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Weighted
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Finite loop-domain normalization

A loop domain retains a uniform lower quadrance for possible process readings
and a positive rational triangle-estimate weight. A lower bound above one
constructs the original weight by exact division. Its retained slack supplies
the squared-error request that certifies a centre norm at least one.

The process states, possible-reading witnesses and ball observations remain
the original finite owners; no completed value is selected.
-/

namespace Purelib.Approximation.Gaussian.Process.Normalization.Basic

open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Process.Apart
open Purelib.Data
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat

@[expose] public section

set_option genInjectivity false in
/-- Finite lower-norm data and a positive weight for a loop chart.

Every possible reading meets the retained lower quadrance. The displayed
weight has a centre coefficient strictly below that same lower bound. -/
structure LoopDomain (process : Process) where
  /-- The retained rational lower quadrance of every possible process reading. -/ lowerSq : Fraction.Rational
  /-- Every possible reading at every retained state meets the same lower quadrance. -/ lower : ∀ (state :
    process.State) {value : Gaussian.Basic.Canonical},
    process.Possible state value → lowerSq ≤ Data.Gaussian.Norm.Basic.normSq value
  /-- The displayed rational triangle-estimate weight. -/ weight : Fraction.Rational
  /-- The retained triangle weight is strictly positive. -/ weightPositive : 0 < weight
  /-- The weight's centre coefficient lies strictly below the retained lower quadrance. -/ coefficient_lt : (weight + 1)
    / weight < lowerSq

constructive_injectivity LoopDomain

end

namespace LoopDomain

/-- Construct a loop domain from a possible-reading lower quadrance strictly above one.

The original gap is lower quadrance minus one, and the displayed weight
is exactly two divided by that positive gap. No finite witness is replaced. -/
@[expose] public def ofLower {process : Process} (apart : Possible.PossibleApart process)
    (aboveOne : 1 < apart.lowerSq) : LoopDomain process := by
  let gap := apart.lowerSq - 1
  have gapPositive : 0 < gap :=
    Fraction.Order.Arithmetic.sub_pos_direct aboveOne
  let weight := 2 / gap
  have weightPositive : 0 < weight :=
    Fraction.Order.Field.div_pos_direct (by decide) gapPositive
  have weightGap : weight * gap = 2 := by
    dsimp only [weight]
    exact Fraction.Field.div_mul_cancel_of_ne 2 gap
      gapPositive.ne'
  have coefficientLt : (weight + 1) / weight < apart.lowerSq := by
    apply (Fraction.Order.Field.div_lt_iff_pos weightPositive).2
    apply Fraction.Order.Arithmetic.lt_of_mul_lt_mul_right_direct
      (c := gap) _ gapPositive
    have gapLtTwice : gap < 2 * gap := by
      calc
        gap = 0 + gap := (zero_add gap).symm
        _ < gap + gap :=
          Fraction.Order.Arithmetic.add_lt_add_right_direct gapPositive gap
        _ = 2 * gap := by ring1
    calc
      (weight + 1) * gap = 2 + gap := by
        calc
          (weight + 1) * gap = weight * gap + gap := by ring1
          _ = 2 + gap := by rw [weightGap]
      _ < 2 + 2 * gap :=
        calc
          2 + gap = gap + 2 := add_comm _ _
          _ < 2 * gap + 2 :=
            Fraction.Order.Arithmetic.add_lt_add_right_direct gapLtTwice 2
          _ = 2 + 2 * gap := add_comm _ _
      _ = (apart.lowerSq * weight) * gap := by
        calc
          2 + 2 * gap = (1 + gap) * 2 := by ring1
          _ = apart.lowerSq * 2 := by
            dsimp only [gap]
            ring1
          _ = apart.lowerSq * (weight * gap) := by rw [weightGap]
          _ = (apart.lowerSq * weight) * gap :=
            (mul_assoc _ _ _).symm
  exact
    { lowerSq := apart.lowerSq
      lower := apart.lower
      weight := weight
      weightPositive := weightPositive
      coefficient_lt := coefficientLt }

/-- The positive margin between the retained lower quadrance and weighted centre coefficient.

Subtracting the retained weighted centre coefficient from the original
lower quadrance gives this exact rational margin. -/
@[expose] public def slack {process : Process} (domain : LoopDomain process) : Fraction.Rational :=
  domain.lowerSq - (domain.weight + 1) / domain.weight

/-- The retained loop-domain margin is strictly positive.

The original loop-domain coefficient inequality makes its displayed
lower-minus-coefficient difference strictly positive. -/
public theorem slack_pos {process : Process} (domain : LoopDomain process) :
    0 < domain.slack :=
  Fraction.Order.Arithmetic.sub_pos_direct domain.coefficient_lt

/-- The loop-domain squared-error request obtained by dividing its margin by weight plus one.

The original positive slack is divided by the retained weight plus one.
This is the exact rational request used for the loop-domain error bound. -/
@[expose] public def normalizationTarget {process : Process}
    (domain : LoopDomain process) : Fraction.Rational :=
  domain.slack / (domain.weight + 1)

/-- The positive loop-domain weight remains positive after adding one.

The original weight is positive and rational one is nonnegative. The
direct mixed positive-sum law gives positivity of the same denominator. -/
public theorem weight_add_one_pos {process : Process}
    (domain : LoopDomain process) : 0 < domain.weight + 1 :=
  Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
    domain.weightPositive (show (0 : Fraction.Rational) ≤ 1 by decide)

/-- The finite loop normalization squared-error target is strictly positive.

Both the retained slack and weight-plus-one denominator are positive,
so their original quotient is a strictly positive rational request. -/
public theorem normalizationTarget_pos {process : Process}
    (domain : LoopDomain process) : 0 < domain.normalizationTarget :=
  Fraction.Order.Field.div_pos_direct domain.slack_pos
    domain.weight_add_one_pos

/-- A fine enough ball around one admitted rational candidate has normalized centre norm at least one.

An original possible-reading witness and the weighted Gaussian estimate
compare the retained candidate lower norm with the same ball centre and radius. -/
public theorem center_normalized_of_fine {process : Process}
    (domain : LoopDomain process) (state : process.State)
    (fine : (process.ball state).radiusSq < domain.normalizationTarget) :
    1 ≤ Data.Gaussian.Norm.Basic.normSq (process.ball state).center := by
  rcases process.witness state with ⟨witness, possible⟩
  have inside := process.possible_inside possible
  have witnessLower := domain.lower state possible
  let error := witness - (process.ball state).center
  have decomposition : witness = error + (process.ball state).center := by
    dsimp only [error]
    apply Gaussian.Basic.ext <;>
      simp only [Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.add_re, Gaussian.Basic.add_im] <;> ring1
  by_cases normalized : 1 ≤ Data.Gaussian.Norm.Basic.normSq (process.ball state).center
  · exact normalized
  · have centerLt : Data.Gaussian.Norm.Basic.normSq (process.ball state).center < 1 :=
      lt_of_not_ge normalized
    have coefficientPositive :
        0 < (domain.weight + 1) / domain.weight :=
      Fraction.Order.Field.div_pos_direct domain.weight_add_one_pos
        domain.weightPositive
    have errorNorm : Data.Gaussian.Norm.Basic.normSq error ≤ (process.ball state).radiusSq := by
      exact inside
    have errorTerm :
        (domain.weight + 1) * Data.Gaussian.Norm.Basic.normSq error < domain.slack := by
      have errorSmall : Data.Gaussian.Norm.Basic.normSq error < domain.normalizationTarget :=
        errorNorm.trans_lt fine
      have scaled := (Fraction.Order.Field.lt_div_iff_pos
        domain.weight_add_one_pos).1 errorSmall
      calc
        (domain.weight + 1) * Data.Gaussian.Norm.Basic.normSq error =
            Data.Gaussian.Norm.Basic.normSq error * (domain.weight + 1) :=
          Fraction.Field.mul_comm _ _
        _ < domain.slack := scaled
    have centerTerm :
        ((domain.weight + 1) / domain.weight) *
            Data.Gaussian.Norm.Basic.normSq (process.ball state).center <
          (domain.weight + 1) / domain.weight := by
      have scaled := Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
        coefficientPositive centerLt
      simpa only [Fraction.Field.mul_one_direct] using scaled
    have strictUpper : Data.Gaussian.Norm.Basic.normSq witness < domain.lowerSq := by
      rw [decomposition]
      calc
        Data.Gaussian.Norm.Basic.normSq (error + (process.ball state).center) ≤
            (domain.weight + 1) * Data.Gaussian.Norm.Basic.normSq error +
              ((domain.weight + 1) / domain.weight) *
                Data.Gaussian.Norm.Basic.normSq (process.ball state).center :=
          Weighted.normSq_add_le_parameter domain.weight domain.weightPositive _ _
        _ < domain.slack +
            (domain.weight + 1) / domain.weight :=
          Fraction.Order.Arithmetic.add_lt_add_direct errorTerm centerTerm
        _ = domain.lowerSq := by
          unfold LoopDomain.slack
          ring1
    exact ((not_lt_of_ge witnessLower) strictUpper).elim
end LoopDomain
end Purelib.Approximation.Gaussian.Process.Normalization.Basic
