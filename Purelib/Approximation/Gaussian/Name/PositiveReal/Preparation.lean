module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Approximation.Gaussian.Name.Basic
public import Purelib.Approximation.Gaussian.Name.PositiveReal.Basic
import Purelib.Data.Gaussian.Norm.Coordinates
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Gaussian.Name.Basic (Named)
open Purelib.Approximation.Gaussian.Name (PositiveReal)
open Purelib.Data.Gaussian.Basic (Canonical)

open Purelib

open Purelib.Approximation

open Purelib.Approximation.Gaussian.Name

open Purelib.Data.Gaussian.Norm

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction

section
@[expose] public section

/-!
# Automatic positive-real charting for a CCL logarithm

The input certificate supplies a displayed positive rational lower bound for
the real coordinate of every candidate at the current finite state.  One
explicit refinement makes the current ball small relative to that bound.
The rational real coordinate of the refined ball centre is then normalized
by a bounded dyadic scan, and every explicitly possible candidate at the
refined state is proved to land in the overlapping local logarithm chart.
The geometric ball may of course contain irrelevant non-real points; the
separate positive-real certificate excludes those from the process semantics.

This is branch data and finite error accounting only.  It neither selects a
point common to all refinements nor asserts a completed logarithm.  Its
purpose is to make positive-real logarithm an automatic CCL-to-CCL operator
on this certified domain: chart preparation, local logarithm, the finite
`log 2` correction, and every correction addition remain arithmetic CCL
names.
-/

namespace Purelib.Approximation.Gaussian.Name.PositiveReal.Preparation

/-- The rational constant sixteen used to budget positive-real coordinate refinement. -/
def refinementDenominator : Fraction.Rational := (2
  * 2) * (2 * 2)

/-- The positive-real refinement denominator is strictly positive. -/
theorem refinementDenominator_pos : 0 <
  refinementDenominator := by
  unfold refinementDenominator
  exact Fraction.Order.Arithmetic.mul_pos_direct
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) (by decide))
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) (by decide))

/-- One sixteenth of the original positive-real coordinate lower bound. -/
def refinementSlack {input :
  Named} (positive : PositiveReal input) : Fraction.Rational :=
  positive.lower / refinementDenominator

/-- The coordinate refinement margin is strictly positive. -/
theorem refinementSlack_pos {input :
  Named} (positive : PositiveReal input) :
    0 < refinementSlack positive :=
  Fraction.Order.Field.div_pos_direct positive.lowerPositive
    refinementDenominator_pos

/-- The squared coordinate margin used as the positive-real process refinement request. -/
def refinementTarget {input :
  Named} (positive : PositiveReal input) : Fraction.Rational :=
  refinementSlack positive ^ 2

/-- The positive-real squared-error refinement request is strictly positive. -/
theorem refinementTarget_pos {input :
  Named} (positive : PositiveReal input) :
    0 < refinementTarget positive :=
  Fraction.Order.Arithmetic.pow_pos_direct (refinementSlack_pos
    positive) 2

/-- Refine the original named state at its lower-bound-dependent squared-error request. -/
def refinedState {input : Named}
  (positive : PositiveReal input) :
    input.process.State :=
  input.process.refine input.state (refinementTarget positive)
    (refinementTarget_pos positive)

/-- Retain the original process with the newly refined positive-real state. -/
def refinedInput {input : Named}
  (positive : PositiveReal input) : Named :=
  { process := input.process
    state := refinedState positive }

/-- Every reading possible at the refined positive-real state was possible at the original named state. -/
theorem refined_possible_at_start {input :
  Named} (positive : PositiveReal input)
    {value : Canonical}
    (possible : input.process.Possible (refinedState positive)
      value) :
    input.process.Possible input.state value :=
  input.process.refine_persists input.state (refinementTarget
    positive)
    (refinementTarget_pos positive) possible

/-- Every reading possible after refinement remains real and meets the original positive coordinate lower bound. -/
theorem refined_possible_real_lower {input :
  Named}
    (positive : PositiveReal input) {value : Canonical}
    (possible : input.process.Possible (refinedState positive)
      value) :
    value.im = 0 ∧ positive.lower ≤ value.re :=
  positive.possible_real_lower (refined_possible_at_start positive
    possible)

/-- The Gaussian rational ball centre observed at the refined positive-real state. -/
def refinedCenter {input :
  Named} (positive : PositiveReal input) : Canonical
      :=
  (input.process.ball (refinedState positive)).center

/-- Every possible refined reading's real-coordinate squared deviation from the centre is bounded by the squared
refinement margin. -/
theorem candidate_deviation_sq {input :
  Named}
    (positive : PositiveReal input) {value : Canonical}
    (possible : input.process.Possible (refinedState positive)
      value) :
    (value.re - (refinedCenter positive).re) ^ 2 ≤
      refinementSlack positive ^ 2 := by
  have bound := (Coordinates.re_sub_sq_le_normSq value
    (refinedCenter positive))
  have inside := (input.process.possible_inside possible).trans
      (input.process.accurate input.state (refinementTarget
        positive)
        (refinementTarget_pos positive)).le
  rw [Data.Gaussian.Norm.Basic.normSq_eq_canonical] at inside
  exact bound.trans inside

/-- Every possible refined reading's real-coordinate deviation lies between the two signed refinement margins. -/
theorem candidate_deviation {input :
  Named} (positive : PositiveReal input)
    {value : Canonical}
    (possible : input.process.Possible (refinedState positive)
      value) :
    -refinementSlack positive ≤ value.re -
      (refinedCenter positive).re ∧
      value.re - (refinedCenter positive).re ≤
        refinementSlack positive := by
  have squares := candidate_deviation_sq positive possible
  exact
    ⟨Fraction.Order.Arithmetic.neg_le_of_sq_le_sq_direct
        (refinementSlack_pos positive).le squares,
      Fraction.Order.Arithmetic.le_of_sq_le_sq_direct
        (refinementSlack_pos positive).le squares⟩

/-- Eight times the refinement margin is half the original positive-real lower bound. -/
theorem refinementSlack_mul_eight {input :
  Named}
    (positive : PositiveReal input) :
    refinementSlack positive * 8 = positive.lower / 2 := by
  apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
  calc
    (refinementSlack positive * 8) * 2 =
        refinementSlack positive *
          refinementDenominator := by
      unfold refinementDenominator
      ring1
    _ = positive.lower :=
      Fraction.Field.div_mul_cancel_of_ne positive.lower
        refinementDenominator
          refinementDenominator_pos.ne'
    _ = (positive.lower / 2) * 2 :=
      (Fraction.Field.div_mul_cancel_of_ne positive.lower 2
        (by decide)).symm

/-- The refinement margin is at most half the retained positive-real lower bound. -/
theorem refinementSlack_le_half {input :
  Named} (positive : PositiveReal input) :
    refinementSlack positive ≤ positive.lower / 2 := by
  calc
    refinementSlack positive =
      refinementSlack positive * 1 :=
      (Fraction.Field.mul_one_direct _).symm
    _ ≤ refinementSlack positive * 8 :=
      Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide)
        (refinementSlack_pos positive).le
    _ = positive.lower / 2 := refinementSlack_mul_eight positive

/-- The refined centre's real coordinate is at least half the original positive-real lower bound.

The retained positivity witness and the refinement error bound place the new real
centre above half the original lower bound. -/
theorem half_lower_le_refinedCenter {input :
  Named}
    (positive : PositiveReal input) :
    positive.lower / 2 ≤ (refinedCenter positive).re := by
  let witness := (input.process.witness (refinedState
    positive)).val
  have witnessPossible :
      input.process.Possible (refinedState positive) witness :=
    (input.process.witness (refinedState positive)).property
  have witnessLower : positive.lower ≤ witness.re :=
    (refined_possible_real_lower positive witnessPossible).2
  have deviationUpper :
      witness.re - (refinedCenter positive).re ≤
        refinementSlack positive :=
    (candidate_deviation positive witnessPossible).2
  have lowerLeCenterSlack :
      positive.lower ≤
        (refinedCenter positive).re +
          refinementSlack positive := by
    calc
      positive.lower ≤ witness.re := witnessLower
      _ = (witness.re - (refinedCenter positive).re) +
          (refinedCenter positive).re := by ring1
      _ ≤ refinementSlack positive +
        (refinedCenter positive).re :=
        Fraction.Order.Arithmetic.add_le_add_right_direct deviationUpper _
      _ = (refinedCenter positive).re +
        refinementSlack positive := by
        ring1
  apply Fraction.Order.Arithmetic.le_of_add_le_add_right_direct
    (c := refinementSlack positive)
  calc
    positive.lower / 2 + refinementSlack positive =
        refinementSlack positive + positive.lower / 2 := by ring1
    _ ≤ positive.lower / 2 + positive.lower / 2 :=
      Fraction.Order.Arithmetic.add_le_add_right_direct
        (refinementSlack_le_half positive) _
    _ = positive.lower := Field.two_halves positive.lower
    _ ≤ (refinedCenter positive).re +
      refinementSlack positive :=
      lowerLeCenterSlack

/-- The refined centre's real coordinate is strictly positive. -/
theorem refinedCenter_pos {input :
  Named} (positive : PositiveReal input) :
    0 < (refinedCenter positive).re :=
  (Fraction.Order.Field.div_pos_direct positive.lowerPositive
    (by decide)).trans_le (half_lower_le_refinedCenter positive)
end Purelib.Approximation.Gaussian.Name.PositiveReal.Preparation

end
