module
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Map
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Algebra.NatCast

open Purelib.Data.Rat

open Purelib.Data.Rat.Fraction
open Purelib.Algebra

/-!
# Finite norm inequalities over constructive Gaussian coordinates

The finite Cauchy--Schwarz bound below is derived from the exact identity

`n * Σ xᵢ² - (Σ xᵢ)² = Σ_{i<j} (xᵢ-xⱼ)²`.

Every sum is structural recursion on an explicit list.  In particular, the
proof uses neither a finite-support wrapper nor any infinite carrier.
-/

namespace Purelib.Algebra.FiniteSum.Rational.Squares

open Purelib.Data.List
open Purelib.Data

/-- Sum a finite list of rational coordinates.

Structural recursion adds each head to the sum of the remaining list, starting from zero. -/
@[expose] public def coordinateSum : List Fraction.Rational → Fraction.Rational
  | [] => 0
  | value :: values => value + coordinateSum values

/-- The coordinate sum of a concatenation is the sum of both coordinate sums.

Structural recursion follows the retained left spine and leaves the supplied
right suffix unchanged. Rational associativity preserves each displayed
coordinate and its order, including repeated entries.
-/
public theorem coordinateSum_append (left right : List Fraction.Rational) :
    coordinateSum (left ++ right) = coordinateSum left + coordinateSum right := by
  induction left with
  | nil => exact (_root_.zero_add _).symm
  | cons value rest ih =>
      change value + coordinateSum (rest ++ right) = _
      rw [ih]
      exact (Fraction.Field.add_assoc _ _ _).symm

/-- Sum the squares of a finite list of rational coordinates.

Each coordinate contributes its square once, including repeated list entries. -/
@[expose] public def coordinateSquareSum : List Fraction.Rational → Fraction.Rational
  | [] => 0
  | value :: values => value ^ 2 + coordinateSquareSum values

/-- Sum squared distances from one rational value to a finite list.

Every list entry contributes the square of its difference from the fixed value. -/
@[expose] public def squareDistanceSum (value : Fraction.Rational) : List Fraction.Rational → Fraction.Rational
  | [] => 0
  | other :: others =>
      (value - other) ^ 2 + squareDistanceSum value others

/-- Sum squared differences over all ordered positions with the first earlier.

Each pair of distinct list positions contributes once; equal coordinate values contribute zero. -/
@[expose] public def pairSquareDistanceSum : List Fraction.Rational → Fraction.Rational
  | [] => 0
  | value :: values =>
      squareDistanceSum value values + pairSquareDistanceSum values

/-- The sum of squared rational coordinates is nonnegative.

The claim holds for every finite list, including the empty list. -/
public theorem coordinateSquareSum_nonneg (values : List Fraction.Rational) :
    0 ≤ coordinateSquareSum values := by
  induction values with
  | nil => exact le_rfl
  | cons value values inductionHypothesis =>
      exact add_nonneg
        (Order.Arithmetic.sq_nonneg_direct value)
        inductionHypothesis

/-- A finite sum of squared rational distances is nonnegative.

The fixed value and every list entry are arbitrary rational numbers. -/
public theorem squareDistanceSum_nonneg (value : Fraction.Rational)
    (values : List Fraction.Rational) :
    0 ≤ squareDistanceSum value values := by
  induction values with
  | nil => exact le_rfl
  | cons other others inductionHypothesis =>
      exact add_nonneg
        (Order.Arithmetic.sq_nonneg_direct (value - other))
        inductionHypothesis

/-- The total squared difference over pairs of list positions is nonnegative.

Each pair contributes a nonnegative rational square. -/
public theorem pairSquareDistanceSum_nonneg (values : List Fraction.Rational) :
    0 ≤ pairSquareDistanceSum values := by
  induction values with
  | nil => exact le_rfl
  | cons value values inductionHypothesis =>
      exact add_nonneg (squareDistanceSum_nonneg value values)
        inductionHypothesis

/-- Expand a finite sum of squared distances.

The expression uses the list length, the sum of its coordinates, and the sum of their squares. -/
public theorem squareDistanceSum_eq (value : Fraction.Rational) :
    ∀ values : List Fraction.Rational,
      squareDistanceSum value values =
        (values.length : Fraction.Rational) * value ^ 2 -
          2 * value * coordinateSum values + coordinateSquareSum values
  | [] => by
      change (0 : Fraction.Rational) = 0 * value ^ 2 - 2 * value * 0 + 0
      ring1
  | other :: others => by
      rw [squareDistanceSum, squareDistanceSum_eq value others,
        coordinateSum, coordinateSquareSum]
      rw [List.length_cons, NatCast.add, Nat.cast_one]
      ring1

/-- Relate rational coordinate sums to pairwise squared differences.

The list length times the sum of squares, minus the square of the sum, equals the sum of squared differences over pairs
of distinct positions. -/
public theorem sum_sq_identity : ∀ values : List Fraction.Rational,
    (values.length : Fraction.Rational) * coordinateSquareSum values -
        coordinateSum values ^ 2 =
      pairSquareDistanceSum values
  | [] => by
      change (0 : Fraction.Rational) * 0 - 0 ^ 2 = 0
      ring1
  | value :: values => by
      rw [coordinateSquareSum, coordinateSum, pairSquareDistanceSum,
        squareDistanceSum_eq value values, ← sum_sq_identity values]
      rw [List.length_cons, NatCast.add, Nat.cast_one]
      ring1

/-- Bound the square of a rational coordinate sum by its sum of squares.

The multiplier is the explicit list length, and the bound also covers the empty list. -/
public theorem coordinateSum_sq_le (values : List Fraction.Rational) :
    coordinateSum values ^ 2 ≤
      (values.length : Fraction.Rational) * coordinateSquareSum values := by
  apply Order.Arithmetic.le_of_sub_nonneg_direct
  rw [sum_sq_identity]
  exact pairSquareDistanceSum_nonneg values
/-- The coordinate sum of nonnegative mapped weights is nonnegative.

Each retained list entry supplies its own nonnegativity certificate; the
structural sum retains those entries in their original order. -/
public theorem coordinateSum_map_nonnegative {Entry : Type} (weight : Entry → Fraction.Rational)
    (entries : List Entry) (positive : ∀ entry ∈ entries, 0 ≤ weight entry) :
    0 ≤ coordinateSum (entries.map weight) := by
  induction entries with
  | nil => exact le_rfl
  | cons entry tail ih =>
      exact add_nonneg (positive entry List.mem_cons_self)
        (ih (fun other member => positive other (List.mem_cons_of_mem _ member)))

/-- A retained nonnegative entry weight is bounded by the complete coordinate sum.

The membership witness selects an actual occurrence, and nonnegative weights
on every retained entry ensure the remaining occurrences cannot decrease its bound. -/
public theorem coordinate_le_coordinateSum_map {Entry : Type} (weight : Entry → Fraction.Rational)
    (entries : List Entry) (positive : ∀ entry ∈ entries, 0 ≤ weight entry)
    (entry : Entry) (member : entry ∈ entries) :
    weight entry ≤ coordinateSum (entries.map weight) := by
  induction entries with
  | nil => exact (List.not_mem_nil member).elim
  | cons head tail ih =>
      have tailPositive := fun other belongs => positive other (List.mem_cons_of_mem head belongs)
      rcases Membership.mem_cons.mp member with rfl | member
      · exact le_add_of_nonneg_right (coordinateSum_map_nonnegative weight tail tailPositive)
      · exact (ih tailPositive member).trans (le_add_of_nonneg_left (positive head List.mem_cons_self))

/-- The coordinate sum of mapped entries equals the sum over their original bounded list indices.

Every index retains its original strict length bound and selects the same displayed entry, including repeated
coordinates. Structural recursion separates the head from the retained tail. -/
public theorem coordinateSum_map_eq_sumFin {Alpha : Type} (items : List Alpha) (value : Alpha → Fraction.Rational) :
    coordinateSum (items.map value) = FiniteSum.Fin.sumFin (fun index : Fin items.length => value
      (items[index.val]'index.isLt)) := by
  induction items with
  | nil => rfl
  | cons first rest ih =>
      rw [FiniteSum.Fin.sumFin_succ]
      change value first + coordinateSum (rest.map value) = value first + FiniteSum.Fin.sumFin (fun index : Fin
        rest.length => value (rest[index.val]'index.isLt))
      rw [ih]

/-- The coordinate sum of a mapped finite enumeration equals its original indexed sum.

The same entry and coordinate functions are evaluated at each original finite index. The successor equation preserves
the zero entry and exact bounded tail. -/
public theorem coordinateSum_map_ofFn {Alpha : Type} {count : Nat} (items : Fin count → Alpha) (value : Alpha →
  Fraction.Rational) :
    coordinateSum ((List.ofFn items).map value) = FiniteSum.Fin.sumFin (fun index => value (items index)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.OfFn.Basic.ofFn_succ, FiniteSum.Fin.sumFin_succ]
      change value (items 0) + coordinateSum ((List.ofFn fun index : Fin count => items index.succ).map value) = _
      rw [ih]

/-- The coordinate sum of flattened finite groups equals the indexed sum of their group sums.

Flattening retains every original group and ordered occurrence. The append certificate separates each displayed group
from the remaining indexed groups. -/
public theorem coordinateSum_map_flatten_ofFn {Alpha : Type} {count : Nat} (groups : Fin count → List Alpha) (value :
  Alpha → Fraction.Rational) :
    coordinateSum ((List.ofFn groups).flatten.map value) = FiniteSum.Fin.sumFin (fun index => coordinateSum ((groups
      index).map value)) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [List.OfFn.Basic.ofFn_succ, List.flatten_cons, List.Map.map_append, coordinateSum_append,
        FiniteSum.Fin.sumFin_succ, ih]

end Purelib.Algebra.FiniteSum.Rational.Squares
