module

public import Purelib.Polynomial.Geometry.ClearPath
public import Purelib.Approximation.AccuracyRequest
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Computed parameter widths paying an original physical segment request

The same actual affine segment supplies its exact displacement. A positive
physical quadrance request yields an internally computed finite parameter
depth, including stationary segments, without changing its clearance owner.
-/

public section

namespace Purelib.Polynomial.Geometry.ClearPath.ClearSegment

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational (Box)

variable {polynomial : GaussianPolynomial} {box : Box} {start finish : Canonical}

/-- The original segment's exact squared displacement computes a positive sufficient parameter-width request. -/
def widthRequest (_segment : ClearSegment polynomial box start finish) (physical : AccuracyRequest) :
    AccuracyRequest :=
  ⟨physical.tolerance / (1 + Norm.Basic.normSq (finish - start)),
    Fraction.Order.Field.div_pos_direct physical.positive
      (Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
        (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (Norm.Basic.normSq_nonneg _))⟩

/-- The exact original affine parameter-width identity pays the chosen physical request on the SAME segment. -/
theorem distance_le_of_width (segment : ClearSegment polynomial box start finish) (physical : AccuracyRequest)
    {first last : Fraction.Rational}
    (paid : (first - last) ^ 2 ≤ (segment.widthRequest physical).tolerance) :
    Norm.Basic.normSq (segment.pointAt first - segment.pointAt last) ≤ physical.tolerance := by
  rewrite [segment.normSq_pointAt_sub_pointAt,
    Fraction.Field.mul_comm ((first - last) ^ 2) (Norm.Basic.normSq (finish - start))]
  have denominator := Fraction.Order.Arithmetic.add_pos_of_pos_of_nonneg_direct
    (of_decide_eq_true rfl : (0 : Fraction.Rational) < 1) (Norm.Basic.normSq_nonneg (finish - start))
  have ratio : Norm.Basic.normSq (finish - start) / (1 + Norm.Basic.normSq (finish - start)) ≤ 1 := by
    apply (Fraction.Order.Field.div_le_iff_pos denominator).mpr
    exact (show Norm.Basic.normSq (finish - start) = 0 + Norm.Basic.normSq (finish - start) by ring1).trans_le
      ((Fraction.Order.Arithmetic.add_le_add_direct (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1)
        (Fraction.Order.Basic.le_refl _)).trans_eq (by ring1))
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct paid
    (Norm.Basic.normSq_nonneg (finish - start))
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct ratio physical.positive.le
  exact scaled.trans ((show Norm.Basic.normSq (finish - start) * (segment.widthRequest physical).tolerance =
    physical.tolerance * (Norm.Basic.normSq (finish - start) / (1 + Norm.Basic.normSq (finish - start))) by
      change Norm.Basic.normSq (finish - start) *
        (physical.tolerance / (1 + Norm.Basic.normSq (finish - start))) = _
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      ring1).trans_le (bound.trans_eq (Fraction.Field.mul_one_direct _)))

/-- The original finite quarter search computes a sufficient parameter depth before physical observations. -/
def widthMinimum (segment : ClearSegment polynomial box start finish) (physical : AccuracyRequest) : Nat :=
  Geometric.Search.firstQuarterBelow 1 0 (segment.widthRequest physical).tolerance

/-- The computed depth uses the exact width request's retained tolerance in the original finite search. -/
theorem widthMinimum_eq (segment : ClearSegment polynomial box start finish) (physical : AccuracyRequest) :
    segment.widthMinimum physical =
      Geometric.Search.firstQuarterBelow 1 0 (segment.widthRequest physical).tolerance := by
  unfold widthMinimum
  rfl

/-- A parameter cell at that internally computed sufficient depth pays its SAME original segment's physical request. -/
theorem distance_le_of_depth (segment : ClearSegment polynomial box start finish) (physical : AccuracyRequest)
    {first last : Fraction.Rational}
    (paid : (first - last) ^ 2 ≤ Geometric.Basic.quarterRadius 1 (segment.widthMinimum physical)) :
    Norm.Basic.normSq (segment.pointAt first - segment.pointAt last) ≤ physical.tolerance :=
  segment.distance_le_of_width physical
    (paid.trans (Geometric.Search.firstQuarterBelow_accurate 1
      (of_decide_eq_true rfl : (0 : Fraction.Rational) ≤ 1) 0
      (segment.widthRequest physical).tolerance (segment.widthRequest physical).positive).le)

end Purelib.Polynomial.Geometry.ClearPath.ClearSegment

end
