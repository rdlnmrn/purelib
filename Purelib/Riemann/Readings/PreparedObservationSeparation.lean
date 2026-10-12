module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Fin
import Purelib.Data.Rat.Fraction.Order.Basic
public import Purelib.Riemann.Readings.PreparedObservationPoints
import Purelib.Data.Rat.Fraction
public import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Tactic.Ring
public import Purelib.Geometry.Rational.Box.Separation

@[expose] public section

/-!
# Finite common radii and separation of observation squares

Positive minima are computed by structural finite recursion.  Coordinate
comparisons give explicit separation radii for distinct Gaussian rationals.
Neither construction uses a completed minimum or a choice of coordinates.
-/

namespace Purelib.Riemann.Readings.PreparedObservationSeparation

open Purelib.Data.Rat.Fraction.Order

open Purelib.Riemann.Readings.PreparedObservationPoints (ObservationBank)
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense

section
open Purelib.Data
/-- Compute the minimum of a finite radius bank capped at one, including the empty bank. -/
def minimumRadius : (count : Nat) -> (Fin count -> Rat.Fraction.Rational) -> Rat.Fraction.Rational
  | 0, _ => 1
  | count + 1, values => min (values 0) (minimumRadius count (fun index => values index.succ))

/-- The capped minimum of strictly positive finite radii is strictly positive.

The original recursion selects each supplied radius and the positive cap one.
Its retained comparison preserves the strict positive bound through every
successor tail, including the empty bank. -/
theorem minimumRadius_positive {count : Nat} (values : Fin count -> Rat.Fraction.Rational)
    (positive : forall index, 0 < values index) : 0 < minimumRadius count values := by
  induction count with
  | zero => exact (by decide : (0 : Rat.Fraction.Rational) < 1)
  | succ count inductionHypothesis =>
      exact Basic.lt_min (positive 0) (inductionHypothesis _ (fun index => positive index.succ))

/-- The capped finite minimum is at most each retained radius.

The first finite position reads the displayed head radius. Successor positions
retain their original tail index, so the recursive minimum bound applies to the
same supplied radius without changing the finite enumeration. -/
theorem minimumRadius_le {count : Nat} (values : Fin count -> Rat.Fraction.Rational) (index : Fin count) :
    minimumRadius count values <= values index := by
  induction count with
  | zero => exact Fin.elim0 index
  | succ count inductionHypothesis =>
      refine Fin.cases_induction ?_ (fun index => ?_) index
      · exact Basic.min_le_left _ _
      · exact (Basic.min_le_right _ _).trans (inductionHypothesis _ index)

/-- Positive intervals of radius at most one quarter of the coordinate gap are strictly separated. -/
public theorem interval_separated {left right radius : Rat.Fraction.Rational}
    (positive : 0 < radius) (bound : radius <= (right - left) / 4) :
    left + radius < right - radius := by
  have multiplied : radius * 4 <= right - left :=
    (Rat.Fraction.Order.Field.le_div_iff_pos (by decide : (0 : Rat.Fraction.Rational) < 4)).1 bound
  have twice : radius * 2 < right - left :=
    (Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct positive
      (by decide : (2 : Rat.Fraction.Rational) < 4)).trans_le multiplied
  have translated := Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct twice (left - radius)
  exact (show left + radius = radius * 2 + (left - radius) by ring1).trans_lt
    (translated.trans_eq (by ring1))

end

open Purelib.Data in
open Purelib.Geometry in
set_option genInjectivity false in
/-- An explicit positive radius separating two centered squares.

The certificate applies to every smaller positive half-width at the same retained centers. -/
structure PointSeparationRadius (left right : Gaussian.Basic.Canonical) where
  /-- The retained separating half-width. -/ radius : Rat.Fraction.Rational
  /-- The separating half-width is strictly positive. -/ positive : 0 < radius
  /-- Every smaller positive half-width gives strictly separated closed squares. -/ separated : forall (small :
    Rat.Fraction.Rational) (positive : 0 < small), small <= radius ->
    (Rational.Box.Square.Centered.BoxTransport.centeredBox left small positive.le).Separated
      (Rational.Box.Square.Centered.BoxTransport.centeredBox right small positive.le)

constructive_injectivity PointSeparationRadius

open Purelib.Data in
/-- Construct a separating radius for distinct Gaussian rational points.

Decidable coordinate comparisons select a nonzero gap; one quarter of that gap separates all smaller centered squares.
-/
def pointSeparationRadius (left right : Gaussian.Basic.Canonical) (distinct : left ≠ right) :
    PointSeparationRadius left right := by
  by_cases realForward : left.re < right.re
  · exact
      { radius := (right.re - left.re) / 4
        positive := Rat.Fraction.Order.Field.div_pos_direct
          (Rat.Fraction.Order.Arithmetic.sub_pos_direct realForward) (by decide)
        separated := fun _ positive bound => Or.inl (interval_separated positive bound) }
  · by_cases realBackward : right.re < left.re
    · exact
        { radius := (left.re - right.re) / 4
          positive := Rat.Fraction.Order.Field.div_pos_direct
            (Rat.Fraction.Order.Arithmetic.sub_pos_direct realBackward) (by decide)
          separated := fun _ positive bound => Or.inr (Or.inl (interval_separated positive bound)) }
    · by_cases imaginaryForward : left.im < right.im
      · exact
          { radius := (right.im - left.im) / 4
            positive := Rat.Fraction.Order.Field.div_pos_direct
              (Rat.Fraction.Order.Arithmetic.sub_pos_direct imaginaryForward) (by decide)
            separated := fun _ positive bound =>
              Or.inr (Or.inr (Or.inl (interval_separated positive bound))) }
      · have imaginaryBackward : right.im < left.im := by
          refine lt_of_le_of_ne (le_of_not_gt imaginaryForward) ?_
          intro equal
          exact distinct (Gaussian.Basic.ext
            (le_antisymm (le_of_not_gt realBackward) (le_of_not_gt realForward)) equal.symm)
        exact
          { radius := (left.im - right.im) / 4
            positive := Rat.Fraction.Order.Field.div_pos_direct
              (Rat.Fraction.Order.Arithmetic.sub_pos_direct imaginaryBackward) (by decide)
            separated := fun _ positive bound =>
              Or.inr (Or.inr (Or.inr (interval_separated positive bound))) }

namespace ObservationBank

variable {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {count : Nat}

open Purelib.Data in
/-- Equal bounded entries in a list without duplicates have equal indices.

The retained duplicate-free list excludes a repeated head in the original tail.
Structural index splitting then compares the same tail entries with their
explicit original bounds. -/
private theorem nodup_getElem_indices {values : List Gaussian.Basic.Canonical} (distinct : values.Nodup)
    {left right : Nat} (leftBound : left < values.length) (rightBound : right < values.length)
    (equal : values[left]'leftBound = values[right]'rightBound) : left = right := by
  induction values generalizing left right with
  | nil => exact (Nat.not_lt_zero left leftBound).elim
  | cons head tail inductionHypothesis =>
      have facts : head ∉ tail ∧ tail.Nodup := by
        cases distinct with
        | cons apart tailDistinct =>
            exact ⟨fun member => apart head member rfl, tailDistinct⟩
      cases left with
      | zero =>
          cases right with
          | zero => rfl
          | succ right =>
              have member : head ∈ tail := by
                change head = tail[right]'(Nat.lt_of_succ_lt_succ rightBound) at equal
                rw [equal]
                exact List.getElem_mem _
              exact (facts.1 member).elim
      | succ left =>
          cases right with
          | zero =>
              have member : head ∈ tail := by
                change tail[left]'(Nat.lt_of_succ_lt_succ leftBound) = head at equal
                rw [<- equal]
                exact List.getElem_mem _
              exact (facts.1 member).elim
          | succ right =>
              exact congrArg Nat.succ (inductionHypothesis facts.2
                (Nat.lt_of_succ_lt_succ leftBound) (Nat.lt_of_succ_lt_succ rightBound) equal)

/-- Distinct bounded indices of an observation bank have distinct points. -/
theorem pointAt_ne (bank : ObservationBank polynomial count) {left right : Fin count}
    (different : left ≠ right) : bank.pointAt left ≠ bank.pointAt right := by
  intro equal
  exact different (Fin.ext (nodup_getElem_indices bank.distinct _ _ equal))

section
open Purelib.Data
/-- Use a separating radius for distinct bank points and the cap one on the diagonal. -/
def pairRadius (bank : ObservationBank polynomial count) (left right : Fin count) : Rat.Fraction.Rational :=
  if equal : left = right then 1
  else (pointSeparationRadius (bank.pointAt left) (bank.pointAt right) (pointAt_ne bank equal)).radius

/-- Every retained pair radius is strictly positive. -/
theorem pairRadius_positive (bank : ObservationBank polynomial count) (left right : Fin count) :
    0 < pairRadius bank left right := by
  unfold pairRadius
  split
  · exact (by decide : (0 : Rat.Fraction.Rational) < 1)
  · exact (pointSeparationRadius _ _ _).positive

/-- Compute one common radius for all distinct point pairs in an observation bank.

The nested finite minima are capped at one and give an explicit positive value even for an empty bank. -/
def separationRadius (bank : ObservationBank polynomial count) : Rat.Fraction.Rational :=
  minimumRadius count (fun left => minimumRadius count (pairRadius bank left))

end

/-- The common finite observation-bank radius is strictly positive. -/
theorem separationRadius_positive (bank : ObservationBank polynomial count) :
    0 < separationRadius bank :=
  minimumRadius_positive _ (fun left => minimumRadius_positive _ (pairRadius_positive bank left))

open Purelib.Data in
open Purelib.Geometry in
/-- Any smaller positive radius separates the squares at distinct retained observation points. -/
theorem separated_of_radius_le (bank : ObservationBank polynomial count)
    (radius : Rat.Fraction.Rational) (positive : 0 < radius) (bound : radius <= separationRadius bank)
    {left right : Fin count} (different : left ≠ right) :
    (Rational.Box.Square.Centered.BoxTransport.centeredBox (bank.pointAt left) radius positive.le).Separated
      (Rational.Box.Square.Centered.BoxTransport.centeredBox (bank.pointAt right) radius positive.le) := by
  have pairBound : radius <= pairRadius bank left right :=
    bound.trans ((minimumRadius_le _ left).trans (minimumRadius_le _ right))
  unfold pairRadius at pairBound
  rw [dif_neg different] at pairBound
  exact (pointSeparationRadius _ _ _).separated radius positive pairBound

end ObservationBank

end Purelib.Riemann.Readings.PreparedObservationSeparation
