module
meta import Purelib.Elab.ConstructiveInjectivity
-- The exposed finite builder retains this original duplicate-free table certificate.
public import Purelib.Data.List.OfFn.Nodup
-- The exposed bank builder retains its original finite table readback proofs.
public import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.Polynomial.Dense.Basic
public import Purelib.Riemann.Readings.PreparedObservationPoints
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Dimensions
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Multiplication
import Purelib.Polynomial.Dense.Multiplication

import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Fixed observation points inside a supplied clear rectangle

A rational progression supplies every point at once, independently of the
numerator coefficients. Clearance of the containing rectangle replaces a
nonzero-evaluation search. The result retains the ordinary interpolation bank
and its exclusion polynomial, together with actual geometric containment.
-/

namespace Purelib.Riemann.Readings.ContainedObservationPoints

open Purelib.Data.List
open Purelib.Data.Rat.Fraction.Order

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Riemann.Readings.PreparedObservationPoints (ObservationBank exclusionFactor exclusionFactor_nonzero
  exclusionFactor_eval)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial -> Dense
open Purelib.Geometry.Rational (Box)
open Purelib.Data.Rat.Fraction (Rational)

section
open Purelib.Data
open Purelib.Polynomial
/-- Multiply a polynomial by one linear exclusion factor for each listed point. -/
public def excluded (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) : List
  Gaussian.Basic.Canonical →
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial
  | [] => polynomial
  | point :: remaining => exclusionFactor point * excluded polynomial remaining

/-- A nonzero polynomial remains nonzero after adjoining the finite exclusion factors. -/
public theorem excluded_nonzero (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero : polynomial.isZero =
  false)
    (points : List Gaussian.Basic.Canonical) : (excluded polynomial points).isZero = false := by
  induction points with
  | nil => exact nonzero
  | cons point remaining ih =>
    exact Dense.Gaussian.Multiplication.product_isZero_false (exclusionFactor_nonzero point) ih

/-- The exclusion product vanishes at every listed point.

Structural membership identifies the original head or retained tail occurrence.
The same exclusion factor makes the evaluation vanish in either case. -/
public theorem excluded_zero (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (points : List
  Gaussian.Basic.Canonical)
    (point : Gaussian.Basic.Canonical) (member : point ∈ points) : (excluded polynomial points).eval point = 0 := by
  induction points with
  | nil => exact (List.not_mem_nil member).elim
  | cons first remaining ih =>
    rw [excluded, Dense.Basic.DensePolynomial.eval_mul]
    rcases Membership.mem_cons.mp member with rfl | member
    · rw [exclusionFactor_eval, Gaussian.Basic.sub_self, Gaussian.Basic.zero_mul]
    · rw [ih member, Gaussian.Basic.mul_zero]

/-- A point clear of the exclusion product is clear of the original polynomial. -/
public theorem excluded_clear (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (points : List
  Gaussian.Basic.Canonical)
    (point : Gaussian.Basic.Canonical) (clear : (excluded polynomial points).eval point ≠ 0) : polynomial.eval point ≠ 0
      := by
  induction points with
  | nil => exact clear
  | cons first remaining ih =>
    apply ih
    intro zero
    apply clear
    rw [excluded, Dense.Basic.DensePolynomial.eval_mul, zero, Gaussian.Basic.mul_zero]

end

open Purelib.Data in
open Purelib.Polynomial in
/-- Build an observation bank from explicit distinct points with certified nonzero evaluations.

Cache their exclusion product once and retain its nonvanishing and point-exclusion certificates. -/
def ObservationBank.ofPoints (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (nonzero : polynomial.isZero = false)
    (points : List Gaussian.Basic.Canonical) (distinct : points.Nodup)
    (clear : ∀ point ∈ points, polynomial.eval point ≠ 0) : ObservationBank polynomial points.length :=
  ⟨points, rfl, distinct, clear, excluded polynomial points, excluded_nonzero polynomial nonzero points,
    excluded_zero polynomial points, excluded_clear polynomial points⟩

open Purelib.Polynomial in
/-- Transporting a bank across a count equality preserves its retained point list. -/
public theorem cast_points {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
  {first last : Nat} (equal : first = last)
    (bank : ObservationBank polynomial first) : (equal ▸ bank).points = bank.points := by cases equal; rfl

open Purelib.Polynomial in
open Purelib.Geometry in
set_option genInjectivity false in
/-- An interpolation observation bank strictly contained in a fixed rectangle.

The record retains the ordinary polynomial bank and geometric containment for every original bounded index. -/
structure BoxObservationPoints (polynomial :
  Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Rational.Box)
  (count : Nat) where
  /-- The retained polynomial observation bank of the requested size. -/ bank : ObservationBank polynomial count
  /-- Every retained bank point lies strictly inside the same box. -/ inside : ∀ index, box.StrictContains (bank.pointAt
    index)

constructive_injectivity BoxObservationPoints

namespace BoxObservationPoints

section
open Purelib.Approximation
open Purelib.Data
open Purelib.Geometry
/-- The horizontal spacing for the requested number of interior observation points. -/
public def step (box : Rational.Box) (count : Nat) : Rat.Fraction.Rational :=
  box.widthX / (Rational.Budget.Aggregate.countCoordinate count + 1)

/-- The interior-point spacing is positive in a proper rectangle. -/
public theorem step_positive {box : Rational.Box} (proper : box.Proper) (count : Nat) : 0 < step box
  count := by
  unfold step
  rw [Rational.Budget.Aggregate.countCoordinate_eq]
  exact Rat.Fraction.Order.Field.div_pos_direct (Rat.Fraction.Order.Arithmetic.sub_pos_direct proper.1)
    (Arithmetic.add_pos_of_nonneg_of_pos_direct (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) (by
      decide))

end

open Purelib.Approximation in
open Purelib.Geometry in
/-- The indexed horizontal-progression point at the box's vertical midpoint. -/
public def point (box : Rational.Box) (count : Nat) (index : Fin count) : Gaussian :=
  ⟨box.xLower + (Rational.Budget.Aggregate.countCoordinate index.val + 1) * step box count,
    box.yLower + box.widthY / 2⟩

section
open Purelib.Approximation
open Purelib.Data
open Purelib.Geometry
/-- Every bounded progression point lies strictly inside a proper rectangle.

The bounded index places the original horizontal progression between both
sides, while the exact vertical midpoint lies between its original lower and
upper sides. Direct scalar translation preserves those coordinates. -/
public theorem point_inside {box : Rational.Box} (proper : box.Proper) (count : Nat) (index : Fin
  count) :
    box.StrictContains (point box count index) := by
  have stepPositive := step_positive proper count
  have indexPositive : (0 : Rat.Fraction.Rational) < (index.val : Rat.Fraction.Rational) + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) (by decide)
  have upper := Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    (Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct (Rat.Fraction.Cast.Order.natCast_lt_direct index.isLt) 1)
      stepPositive
  have total : ((count : Rat.Fraction.Rational) + 1) * step box count = box.widthX := by
    rw [step, Rational.Budget.Aggregate.countCoordinate_eq, Rat.Fraction.Field.mul_comm]
    exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _
      (Arithmetic.add_pos_of_nonneg_of_pos_direct (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) (by
        decide)).ne'
  rw [total] at upper
  have yPositive : 0 < box.widthY / 2 := Rat.Fraction.Order.Field.div_pos_direct
    (Rat.Fraction.Order.Arithmetic.sub_pos_direct proper.2) (by decide)
  have twice : box.widthY / 2 + box.widthY / 2 = box.widthY := by
    calc
      _ = (box.widthY / 2) * 2 := by ring1
      _ = _ := Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  unfold point
  rw [Rational.Budget.Aggregate.countCoordinate_eq]
  refine ⟨(show box.xLower = box.xLower + 0 from (add_zero _).symm).trans_lt
      (Arithmetic.add_lt_add_left_direct (Rat.Fraction.Order.Arithmetic.mul_pos_direct indexPositive stepPositive)
        box.xLower), ?_,
    (show box.yLower = box.yLower + 0 from (add_zero _).symm).trans_lt
      (Arithmetic.add_lt_add_left_direct yPositive box.yLower), ?_⟩
  · exact (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct upper box.xLower).trans_eq (by
      unfold Rational.Box.widthX; ring1)
  · have less := Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct ((show box.widthY / 2 = box.widthY / 2 + 0 from
      (add_zero _).symm).trans_lt
      (Arithmetic.add_lt_add_left_direct yPositive (box.widthY / 2))) box.yLower
    rw [twice] at less
    exact less.trans_eq (by unfold Rational.Box.widthY; ring1)

/-- Distinct bounded indices give distinct progression points in a proper rectangle.

Equality of the retained points gives equality of their horizontal coordinates.
Cancellation of the original positive spacing recovers the same natural index,
so the bounded finite positions agree. -/
public theorem point_injective {box : Rational.Box} (proper : box.Proper) (count : Nat) :
    Function.Injective (point box count) := by
  intro first last equal
  have real := congrArg Gaussian.Basic.re equal
  dsimp only [point] at real
  rw [Rational.Budget.Aggregate.countCoordinate_eq, Rational.Budget.Aggregate.countCoordinate_eq] at real
  have products : ((first.val : Rat.Fraction.Rational) + 1) * step box count = ((last.val : Rat.Fraction.Rational) + 1)
    * step box count := by
    calc
      _ = (box.xLower + ((first.val : Rat.Fraction.Rational) + 1) * step box count) - box.xLower := by ring1
      _ = (box.xLower + ((last.val : Rat.Fraction.Rational) + 1) * step box count) - box.xLower := congrArg (· -
        box.xLower) real
      _ = _ := by ring1
  have shifted := Rat.Fraction.Field.mul_right_cancel_of_ne (step_positive proper count).ne' products
  have indices : (first.val : Rat.Fraction.Rational) = (last.val : Rat.Fraction.Rational) := by
    calc
      _ = ((first.val : Rat.Fraction.Rational) + 1) - 1 := by ring1
      _ = ((last.val : Rat.Fraction.Rational) + 1) - 1 := congrArg (· - 1) shifted
      _ = _ := by ring1
  apply Fin.ext
  exact Rat.Fraction.Cast.Compatibility.natCast_injective_direct indices

end

open Purelib.Polynomial in
open Purelib.Geometry in
/-- Construct the requested number of observation points inside a fixed clear box.

Use an explicit horizontal rational progression and the supplied clearance proof; retain the resulting interpolation
bank and containment certificates, including for an empty request. -/
def build (polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (nonzero :
  polynomial.isZero = false) (box :
  Rational.Box) (proper : box.Proper)
    (clear : ∀ point, box.Contains point → polynomial.eval point ≠ 0) (count : Nat) :
      BoxObservationPoints polynomial box count := by
  let points := List.ofFn (point box count)
  let bank := ObservationBank.ofPoints polynomial nonzero points (OfFn.Nodup.nodup_ofFn_of_injective
    (point_injective proper count))
    (fun value member => by
      obtain ⟨index, equal⟩ := OfFn.Basic.mem_ofFn.mp member
      rw [← equal]
      exact clear _ (point_inside proper count index).contains)
  have lengthEq : points.length = count := OfFn.Basic.length_ofFn
  refine ⟨lengthEq ▸ bank, ?_⟩
  intro index
  have member := (lengthEq ▸ bank).pointAt_mem index
  have bankPoints : (lengthEq ▸ bank).points = points := cast_points lengthEq bank
  rw [bankPoints] at member
  obtain ⟨position, equal⟩ := OfFn.Basic.mem_ofFn.mp member
  rw [← equal]
  exact point_inside proper count position

end BoxObservationPoints
end Purelib.Riemann.Readings.ContainedObservationPoints
