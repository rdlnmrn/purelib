module

public import Purelib.Calculus.Linear.Euler
public import Purelib.Approximation.AccuracyRequest.Scaling
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Algebra.NatCast
import Purelib.Algebra.FiniteSum.Prefix
import Purelib.Data.Vector.Basic
import Purelib.LinearAlgebra.Gaussian.Norm
import Purelib.LinearAlgebra.Matrix.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Computed coarse intervals for finite Euler stability

A fixed matrix quadrance ceiling determines one original positive accuracy
request. The original bounded quarter-radius search computes a positive
integer interval count whose actual reciprocal width pays the growth
budget. The same coarse width can contain any admitted finer partition;
no chosen endpoint or desired growth inequality defines the schedule.
-/

public section

namespace Purelib.Calculus.Linear.Euler

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational.Geometric
open Purelib.Algebra.FiniteSum.Prefix (coordinateSum)
open Purelib.Data renaming Vector → Vec
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Vector (zipWith)
open Purelib.LinearAlgebra
open Purelib.LinearAlgebra.Gaussian

/-- The original linear Euler growth coefficient at one fixed dimension and matrix ceiling. -/
@[expose] def intervalRate (size : Nat) (ceiling : Rational) : Rational :=
  3 + 4 * ((size : Rational) * ceiling)

/-- A nonnegative matrix ceiling gives a nonnegative growth coefficient, including dimension zero. -/
theorem intervalRate_nonnegative (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    0 ≤ intervalRate size ceiling :=
  (Order.Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide : (0 : Rational) < 3)
    (Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Rational) ≤ 4)
      (Order.Arithmetic.mul_nonneg_direct
        (Cast.Order.natCast_le_direct (m := 0) (n := size) (Nat.zero_le size)) nonnegative))).le

/-- Compute one positive coarse-width request from the original fixed coefficient ceiling.

The retained request is the minimum of one and half divided by the
original growth coefficient plus one. Its positive added unit keeps the
construction total for zero coefficients and dimension zero.
-/
def intervalRequest (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) : AccuracyRequest :=
  (⟨1, by decide⟩ : AccuracyRequest).minimum
    ((⟨1 / 2, by decide⟩ : AccuracyRequest).divide (intervalRate size ceiling + 1)
      (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct
        (intervalRate_nonnegative size ceiling nonnegative) (by decide)))

/-- The retained request tolerance is the actual displayed minimum for the same dimension and ceiling. -/
theorem intervalRequest_tolerance (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    (intervalRequest size ceiling nonnegative).tolerance =
      min 1 ((1 / 2 : Rational) / (intervalRate size ceiling + 1)) := by rfl

/-- The computed coarse request is at most one. -/
theorem intervalRequest_le_one (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    (intervalRequest size ceiling nonnegative).tolerance ≤ 1 := by
  rewrite [intervalRequest_tolerance]
  exact Order.Basic.min_le_left _ _

/-- The actual coarse-width request strictly pays one half of the original Euler growth budget. -/
theorem intervalRequest_growth_lt (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    intervalRate size ceiling * (intervalRequest size ceiling nonnegative).tolerance < (1 / 2 : Rational) :=
  (congrArg (fun width : Rational => intervalRate size ceiling * width)
    (intervalRequest_tolerance size ceiling nonnegative)).trans_lt
      (Order.Field.mul_min_one_div_lt (intervalRate_nonnegative size ceiling nonnegative) (by decide))

/-- Compute the original bounded quarter-radius search depth for the same positive coarse request. -/
def intervalDepth (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) : Nat :=
  Search.firstQuarterBelow 1 0 (intervalRequest size ceiling nonnegative).tolerance

/-- Compute the positive integer number of equal coarse intervals covering one unit parameter interval.

Its exponent is the original finite search depth. The count is an actual
natural power, so a retained count can be passed directly to an interval
executor without running the search again to obtain its reciprocal width.
-/
def intervalCount (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) : Nat :=
  4 ^ intervalDepth size ceiling nonnegative

/-- The complete count is the natural fourth power selected by the original quarter-radius procedure. -/
theorem intervalCount_eq (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    intervalCount size ceiling nonnegative =
      4 ^ Search.firstQuarterBelow 1 0 (intervalRequest size ceiling nonnegative).tolerance := by rfl

/-- The computed actual interval count is strictly positive in every finite dimension. -/
theorem intervalCount_positive (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    0 < intervalCount size ceiling nonnegative :=
  Nat.pow_pos (by decide : 0 < 4)

/-- The actual count's canonical rational cast is the same fourth power at the original retained depth. -/
theorem intervalCount_cast (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    (intervalCount size ceiling nonnegative : Rational) =
      (4 : Rational) ^ intervalDepth size ceiling nonnegative :=
  Algebra.NatCast.pow 4 (intervalDepth size ceiling nonnegative)

/-- The reciprocal of the actual computed integer count is exactly the original searched quarter-radius. -/
theorem intervalCount_reciprocal (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    1 / (intervalCount size ceiling nonnegative : Rational) =
      Basic.quarterRadius 1 (intervalDepth size ceiling nonnegative) :=
  congrArg (fun denominator : Rational => 1 / denominator) (intervalCount_cast size ceiling nonnegative)

/-- The actual computed reciprocal interval width is strictly below the same original positive request. -/
theorem intervalCount_width_lt (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    1 / (intervalCount size ceiling nonnegative : Rational) <
      (intervalRequest size ceiling nonnegative).tolerance :=
  (intervalCount_reciprocal size ceiling nonnegative).trans_lt
    (Search.firstQuarterBelow_accurate 1 (by decide) 0
      (intervalRequest size ceiling nonnegative).tolerance (intervalRequest size ceiling nonnegative).positive)

/-- The original computed interval width is positive from the actual integer count. -/
theorem intervalCount_width_positive (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    0 < 1 / (intervalCount size ceiling nonnegative : Rational) :=
  Order.Field.div_pos_direct (by decide)
    (Cast.Order.natCast_pos_direct (intervalCount_positive size ceiling nonnegative))

/-- The computed reciprocal coarse width lies in the original Euler unit-width range. -/
theorem intervalCount_width_le_one (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    1 / (intervalCount size ceiling nonnegative : Rational) ≤ 1 :=
  (intervalCount_width_lt size ceiling nonnegative).le.trans (intervalRequest_le_one size ceiling nonnegative)

/-- The computed count and reciprocal width cover exactly one unit interval. -/
theorem intervalCount_totalWidth (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    (intervalCount size ceiling nonnegative : Rational) *
      (1 / (intervalCount size ceiling nonnegative : Rational)) = 1 :=
  (Field.mul_comm _ _).trans (Field.div_mul_cancel_of_ne 1 _
    (Cast.Order.natCast_pos_direct (intervalCount_positive size ceiling nonnegative)).ne')

/-- The same actual reciprocal width strictly pays the coarse interval's growth budget. -/
theorem intervalCount_growth_lt (size : Nat) (ceiling : Rational) (nonnegative : 0 ≤ ceiling) :
    intervalRate size ceiling * (1 / (intervalCount size ceiling nonnegative : Rational)) < (1 / 2 : Rational) :=
  (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (intervalCount_width_lt size ceiling nonnegative).le
    (intervalRate_nonnegative size ceiling nonnegative)).trans_lt
      (intervalRequest_growth_lt size ceiling nonnegative)

/-- The original actual one-step Euler growth is paid by the computed coarse interval width. -/
theorem growth_at_interval_lt {size : Nat} (coefficients : Matrix Canonical size) (ceiling : Rational)
    (nonnegative : 0 ≤ ceiling) (bounded : Norm.matrix coefficients ≤ ceiling) :
    growth coefficients (1 / (intervalCount size ceiling nonnegative : Rational)) < (1 / 2 : Rational) :=
  (growth_le coefficients _ ceiling (intervalCount_width_positive size ceiling nonnegative).le
    (intervalCount_width_le_one size ceiling nonnegative) bounded).trans_lt
      (intervalCount_growth_lt size ceiling nonnegative)

/-- Any genuine finer partition of the computed coarse width pays the original total-growth condition.

Only its actual nonnegative unit widths, exact total-width readback and
actual matrix ceiling are supplied. The original growth-sum theorem and
the computed count derive the strict half-budget; a final growth bound is
not a caller input. Refining the same interval introduces no count factor.
-/
theorem growth_on_interval_lt {size : Nat} (coefficients : Nat → Matrix Canonical size)
    (widths : Nat → Rational) (ceiling : Rational) (nonnegativeCeiling : 0 ≤ ceiling) (count : Nat)
    (nonnegative : ∀ index, index < count → 0 ≤ widths index)
    (unit : ∀ index, index < count → widths index ≤ 1)
    (bounded : ∀ index, index < count → Norm.matrix (coefficients index) ≤ ceiling)
    (total : coordinateSum widths count = 1 / (intervalCount size ceiling nonnegativeCeiling : Rational)) :
    coordinateSum (fun index => growth (coefficients index) (widths index)) count < (1 / 2 : Rational) :=
  (growth_sum_le coefficients widths ceiling count nonnegative unit bounded).trans_lt
    ((congrArg (fun width : Rational => intervalRate size ceiling * width) total).trans_lt
      (intervalCount_growth_lt size ceiling nonnegativeCeiling))

/-- Actual local defects on a finer partition of the computed coarse interval give the original Euler stability bound.

The original trace, sample vectors and local defect factors are retained.
Their interval identity is the actual sum of the displayed widths. The
coefficient ceiling computes the sufficient interval count and discharges
the original growth hypothesis internally, including dimension zero.
-/
theorem stability_on_interval {size : Nat} (coefficients : Nat → Matrix Canonical size)
    (widths factors : Nat → Rational) (initial : Vec Canonical size) (samples : Nat → Vec Canonical size)
    (ceiling : Rational) (nonnegativeCeiling : 0 ≤ ceiling) (count : Nat)
    (positive : ∀ index, index < count → 0 < widths index)
    (unit : ∀ index, index < count → widths index ≤ 1)
    (bounded : ∀ index, index < count → Norm.matrix (coefficients index) ≤ ceiling)
    (factorNonnegative : ∀ index, index < count → 0 ≤ factors index)
    (total : coordinateSum widths count = 1 / (intervalCount size ceiling nonnegativeCeiling : Rational))
    (remainders : ∀ index, index < count →
      Norm.vector (defect (coefficients index) (widths index) (samples index) (samples (index + 1))) ≤
        factors index * widths index ^ 4) :
    Norm.vector (zipWith (fun first last => first - last) (samples count) (trace coefficients widths initial count)) ≤
      2 * (Norm.vector (zipWith (fun first last => first - last) (samples 0) initial) +
        coordinateSum (fun index => factors index * (widths index + 1) * widths index ^ 3) count) :=
  stability_of_total_width coefficients widths factors initial samples ceiling count positive unit bounded
    factorNonnegative
    ((congrArg (fun width : Rational => intervalRate size ceiling * width) total).trans_lt
      (intervalCount_growth_lt size ceiling nonnegativeCeiling)).le remainders

end Purelib.Calculus.Linear.Euler

end
