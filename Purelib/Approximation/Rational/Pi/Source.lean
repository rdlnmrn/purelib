module

public import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Approximation.Rational.Uniform.Modulus
public import Purelib.Integration.Cell.Source.Continuous.Producer
import Purelib.Integration.Cell.Source.Continuous.Comparison
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-!
# Rational source for the finite circle integral

The source is `4 / (1 + t²)` on rational parameters. Its finite bounds and
variation laws are stated on the unit interval without introducing a completed
integral or a real-number constant.
-/

namespace Purelib.Approximation.Rational.Pi.Source

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- The rational denominator used by the circle source. -/
@[expose] public def denominator (time : Fraction.Rational) : Fraction.Rational := 1 + time ^ 2

/-- The exact rational source for the finite circle integral. -/
@[expose] public def value (time : Fraction.Rational) : Fraction.Rational := 4 / denominator time

/-- The denominator is at least one at every rational parameter. -/
public theorem denominator_lower (time : Fraction.Rational) : 1 ≤ denominator time := by
  have shifted := Arithmetic.add_le_add_right_direct (Arithmetic.sq_nonneg_direct time) 1
  calc
    (1 : Fraction.Rational) = 0 + 1 := by ring1
    _ ≤ time ^ 2 + 1 := shifted
    _ = denominator time := by unfold denominator; ring1

/-- The source denominator is strictly positive at every rational parameter. -/
public theorem denominator_pos (time : Fraction.Rational) : 0 < denominator time :=
  (show (0 : Fraction.Rational) < 1 by decide).trans_le (denominator_lower time)

/-- A rational unit-interval parameter has square at most one. -/
public theorem square_le_one {time : Fraction.Rational} (lower : 0 ≤ time) (upper : time ≤ 1) :
    time ^ 2 ≤ 1 := by
  calc
    time ^ 2 = time * time := by ring1
    _ ≤ 1 * time := Arithmetic.mul_le_mul_of_nonneg_right_direct upper lower
    _ = time := by ring1
    _ ≤ 1 := upper

/-- The source never exceeds four. -/
public theorem value_le_four (time : Fraction.Rational) : value time ≤ 4 := by
  unfold value
  exact Field.divide_le_self (by decide) (denominator_lower time)

/-- The source is at least two for every rational unit-interval parameter. -/
public theorem two_le_value {time : Fraction.Rational} (lower : 0 ≤ time) (upper : time ≤ 1) :
    2 ≤ value time := by
  apply (Field.le_div_iff_pos (denominator_pos time)).mpr
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct (square_le_one lower upper)
    (show (0 : Fraction.Rational) ≤ 2 by decide)
  have shifted := Arithmetic.add_le_add_right_direct scaled 2
  calc
    2 * denominator time = 2 * time ^ 2 + 2 := by unfold denominator; ring1
    _ ≤ 2 * 1 + 2 := shifted
    _ = 4 := by decide

/-- The circle source decreases between ordered nonnegative parameters. -/
public theorem value_antitone {first second : Fraction.Rational} (lower : 0 ≤ first)
    (ordered : first ≤ second) : value second ≤ value first := by
  have squares := Arithmetic.pow_le_pow_direct lower ordered 2
  have shifted := Arithmetic.add_le_add_right_direct squares 1
  have denominators : denominator first ≤ denominator second := by
    calc
      denominator first = first ^ 2 + 1 := by unfold denominator; ring1
      _ ≤ second ^ 2 + 1 := shifted
      _ = denominator second := by unfold denominator; ring1
  exact Field.div_le_div_of_nonneg_left_direct (by decide) (denominator_pos first) denominators

/-- Ordered unit-interval source readings differ by at most eight times the parameter gap.

The proof clears the original two positive denominators. Their product is at
least one, while the sum of the two retained parameters is at most two. -/
public theorem difference_le {first second : Fraction.Rational} (lower : 0 ≤ first)
    (ordered : first ≤ second) (upper : second ≤ 1) :
    value first - value second ≤ 8 * (second - first) := by
  have secondLower : 0 ≤ second := lower.trans ordered
  have firstUpper : first ≤ 1 := ordered.trans upper
  have gap : 0 ≤ second - first := Arithmetic.sub_nonneg_direct ordered
  have sumNonnegative : 0 ≤ first + second := by
    have both := Arithmetic.add_le_add_direct lower secondLower
    calc
      (0 : Fraction.Rational) = 0 + 0 := by ring1
      _ ≤ first + second := both
  have sumBound : first + second ≤ 2 := by
    have both := Arithmetic.add_le_add_direct firstUpper upper
    calc
      first + second ≤ 1 + 1 := both
      _ = 2 := by decide
  have productLower : 1 ≤ denominator first * denominator second := by
    have both := Arithmetic.mul_le_mul_direct (denominator_lower first) (denominator_lower second)
      (by decide : (0 : Fraction.Rational) ≤ 1) (denominator_pos first).le
    calc
      (1 : Fraction.Rational) = 1 * 1 := by decide
      _ ≤ denominator first * denominator second := both
  have numeratorNonnegative : 0 ≤ 4 * (second - first) * (first + second) :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide) gap) sumNonnegative
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct sumBound
    (Arithmetic.mul_nonneg_direct (show (0 : Fraction.Rational) ≤ 4 by decide) gap)
  calc
    value first - value second =
        (4 * (second - first) * (first + second)) / (denominator first * denominator second) := by
      unfold value
      rw [Fraction.Field.div_sub_div_direct _ _ _ _ (denominator_pos first).ne' (denominator_pos second).ne']
      congr 1
      unfold denominator
      ring1
    _ ≤ 4 * (second - first) * (first + second) := Field.divide_le_self numeratorNonnegative productLower
    _ ≤ 4 * (second - first) * 2 := scaled
    _ = 8 * (second - first) := by ring1

/-- An executable uniform variation modulus for the exact rational circle source.

The positive distance is one eighth of the requested variation. Ordered points
within that distance satisfy both source-difference inequalities. -/
@[expose] public def modulus : Uniform.Modulus value where
  radius := fun variation => variation / 8
  radius_pos := fun _ positive => Field.div_pos_direct positive (by decide)
  variation := by
    intro variation positive first second lower ordered upper small
    have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct small.le
      (show (0 : Fraction.Rational) ≤ 8 by decide)
    have budget : 8 * (second - first) ≤ variation := by
      calc
        _ ≤ 8 * (variation / 8) := paid
        _ = (variation / 8) * 8 := by ring1
        _ = variation := Fraction.Field.div_mul_cancel_of_ne variation 8 (by decide)
    have firstDifference := (difference_le lower ordered upper).trans budget
    have secondNonpositive : value second - value first ≤ 0 := by
      calc
        value second - value first ≤ value first - value first :=
          Arithmetic.sub_le_sub_right_direct (value_antitone lower ordered) _
        _ = 0 := by ring1
    have secondDifference : value second - value first ≤ variation := secondNonpositive.trans positive.le
    have firstAdded := Arithmetic.sub_le_iff_le_add_direct.mp firstDifference
    have secondAdded := Arithmetic.sub_le_iff_le_add_direct.mp secondDifference
    have firstCommute : variation + value second = value second + variation := by ring1
    have secondCommute : variation + value first = value first + variation := by ring1
    rw [firstCommute] at firstAdded
    rw [secondCommute] at secondAdded
    exact ⟨Arithmetic.sub_le_iff_le_add_direct.mpr firstAdded, secondAdded⟩

/-- The original persistent source-frontier producer for the circle source.

Each request retains its actual preparation, normalized partition, source
readings and frontier. Continuations reuse the producer's original cached
readings and common-refinement machinery. -/
@[expose] public def producer : Integration.SourceFrontier.Producer value :=
  Integration.SourceFrontier.Continuous.producer modulus

/-- The finite rational bound process generated by the original circle-source producer. -/
@[expose] public def boundProcess := producer.boundProcess

/-- Independently requested source answers agree within their two paid widths.

The comparison uses the original frontiers' common refinement; it does not
assume either independently selected answer belongs to the other frontier. -/
public theorem answers_close
    (first second : Integration.SourceFrontier.Continuous.Result modulus) :
    Fraction.abs (first.answer - second.answer) <
      first.preparation.request.tolerance + second.preparation.request.tolerance :=
  Integration.SourceFrontier.Continuous.Result.answer_difference_lt_of_same first second
    (fun _ _ _ => rfl)

end Purelib.Approximation.Rational.Pi.Source
