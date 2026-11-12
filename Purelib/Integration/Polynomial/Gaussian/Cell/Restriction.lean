module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
public import Purelib.Polynomial.Ascending.Gaussian.Restriction.Cached
public import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Polynomial.Ascending

/-! # Original polynomial cells on retained parameter subintervals

The original cell and an existing affine-restriction cache determine a new
physical child cell. Its polynomial consumes the cached table and its local
allowance is unchanged. Exact point and integral readbacks concern those
same data, including repeated or reversed parameter endpoints.
-/

public section

open Purelib.Data.Rat.Fraction

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)

/-- The exact physical point at a displayed rational parameter of the original cell. -/
@[expose] def point (cell : CellModel) (parameter : Rational) : Canonical :=
  cell.start + Cast.Path.ofCoordinate parameter * cell.displacement

/-- Parameter zero gives the original cell's starting endpoint. -/
theorem point_zero (cell : CellModel) : cell.point 0 = cell.start := by
  change cell.start + (0 : Canonical) * cell.displacement = cell.start
  rewrite [Basic.zero_mul, Basic.add_zero]
  rfl

/-- Parameter one gives the original cell's finishing endpoint. -/
theorem point_one (cell : CellModel) : cell.point 1 = cell.finish := by
  change cell.start + (1 : Canonical) * (cell.finish - cell.start) = cell.finish
  rewrite [Basic.one_mul]
  ring1

/-- An original retained observation uses exactly the physical point at its own stored parameter. -/
theorem observationPoint_eq (cell : CellModel) (observation : LocalObservation cell.polynomial cell.localAllowance) :
    cell.observationPoint observation = cell.point observation.parameter := by
  unfold observationPoint point
  exact congrArg (fun movement : Canonical => cell.start + movement)
    (Scale.scalar_mul_eq_scale observation.parameter cell.displacement).symm

end Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel

namespace Purelib.Integration.Polynomial.Gaussian.Cell.Restriction

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Polynomial.Ascending.Gaussian

/-- Map a child-local parameter to the original displayed parent interval, preserving its orientation. -/
@[expose] def parameter (first last input : Rational) : Rational := first + input * (last - first)

/-- Endpoints in the parent unit interval keep every child unit parameter inside that same interval. -/
theorem parameter_inside {first last input : Rational}
    (first_inside : 0 ≤ first ∧ first ≤ 1) (last_inside : 0 ≤ last ∧ last ≤ 1)
    (inside : 0 ≤ input ∧ input ≤ 1) : 0 ≤ parameter first last input ∧ parameter first last input ≤ 1 :=
  Geometry.Rational.Box.coordinate_between first_inside last_inside inside

/-- An ordered subinterval and a nonnegative child fraction never precede the original left endpoint. -/
theorem parameter_ge_left {first last input : Rational} (ordered : first ≤ last) (nonnegative : 0 ≤ input) :
    first ≤ parameter first last input := by
  apply Order.Arithmetic.le_of_sub_nonneg_direct
  exact (Order.Arithmetic.mul_nonneg_direct nonnegative
    (Order.Arithmetic.sub_nonneg_direct ordered)).trans_eq (by unfold parameter; ring1)

/-- An ordered original interval preserves the order of any two admitted child fractions. -/
theorem parameter_le {first last left right : Rational} (ordered : first ≤ last) (inside : left ≤ right) :
    parameter first last left ≤ parameter first last right := by
  change first + left * (last - first) ≤ first + right * (last - first)
  exact Order.Arithmetic.add_le_add_direct
    (Data.Rat.Fraction.Order.Basic.le_refl first)
    (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct inside
      (Order.Arithmetic.sub_nonneg_direct ordered))

/-- Construct the physical child model from the SAME cached restriction of its original parent polynomial.

Only the existing cached coefficient table is read. The original allowance
is preserved; uniform child observations are obtained by transporting the
parent's actual query records at the corresponding parameter.
-/
@[expose] def model (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) : CellModel :=
  { start := cell.point first
    finish := cell.point last
    polynomial := cached.polynomial
    localAllowance := cell.localAllowance
    localAllowance_nonneg := cell.localAllowance_nonneg
    observations := [] }

/-- The child starts at the original parent's first displayed parameter endpoint. -/
theorem model_start (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) :
    (model cell cached).start = cell.point first := rfl

/-- The child finishes at the original parent's last displayed parameter endpoint. -/
theorem model_finish (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) :
    (model cell cached).finish = cell.point last := rfl

/-- Restriction retains the exact original local allowance without a smaller replacement request. -/
theorem model_allowance (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) :
    (model cell cached).localAllowance = cell.localAllowance := rfl

/-- The child cell uses the identical original cached polynomial table. -/
theorem model_polynomial (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) :
    (model cell cached).polynomial = cached.polynomial := rfl

/-- The actual child displacement retains the original parent direction and oriented parameter difference. -/
theorem displacement_eq (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) :
    (model cell cached).displacement =
      (Cast.Path.ofCoordinate last - Cast.Path.ofCoordinate first) * cell.displacement := by
  change cell.point last - cell.point first = _
  unfold CellModel.point
  ring1

/-- The physical child query is exactly the original parent query at the mapped rational parameter. -/
theorem point_eq (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) (input : Rational) :
    (model cell cached).point input = cell.point (parameter first last input) := by
  unfold CellModel.point
  rewrite [displacement_eq]
  change cell.start + Cast.Path.ofCoordinate first * cell.displacement +
    Cast.Path.ofCoordinate input *
      ((Cast.Path.ofCoordinate last - Cast.Path.ofCoordinate first) * cell.displacement) = _
  change _ = cell.start + Cast.CoordinateTaylor.ofCoordinate (first + input * (last - first)) * cell.displacement
  rewrite [Cast.ofCoordinate_add, Cast.ofCoordinate_mul, Cast.ofCoordinate_sub]
  unfold Cast.Path.ofCoordinate Cast.CoordinateTaylor.ofCoordinate
  ring1

/-- The SAME cached child polynomial reads the original parent polynomial at the exact mapped parameter. -/
theorem eval_eq (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) (input : Rational) :
    Evaluation.eval (model cell cached).polynomial (Cast.Path.ofCoordinate input) =
      Evaluation.eval cell.polynomial (Cast.Path.ofCoordinate (parameter first last input)) := by
  rewrite [model_polynomial, cached.eval_eq]
  apply congrArg (Evaluation.eval cell.polynomial)
  change _ = Cast.CoordinateTaylor.ofCoordinate (first + input * (last - first))
  rewrite [Cast.ofCoordinate_add, Cast.ofCoordinate_mul, Cast.ofCoordinate_sub]
  unfold Cast.Path.ofCoordinate Cast.CoordinateTaylor.ofCoordinate
  ring1

/-- The actual child integral equals the original parent polynomial integral over the same displayed subinterval.

The proof consumes the existing cached unit-integral readback and affine
transport identity. This exact readback makes no claim that evaluating the
original CellModel.integralSample procedure reuses a separate integral cache.
-/
theorem integralSample_eq (cell : CellModel) {first last : Rational}
    (cached : Gaussian.Restriction.Cached cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last)) :
    (model cell cached).integralSample = cell.displacement * Integral.definiteIntegral cell.polynomial
      (Cast.Path.ofCoordinate first) (Cast.Path.ofCoordinate last) := by
  unfold CellModel.integralSample
  rewrite [displacement_eq, model_polynomial, ← cached.sample_eq]
  calc
    _ = cell.displacement *
        ((Cast.Path.ofCoordinate last - Cast.Path.ofCoordinate first) * cached.sample) := by ring1
    _ = _ := congrArg (fun value : Canonical => cell.displacement * value) cached.transported_sample

/-- Two actual adjacent child models recover the SAME original parent's whole integral sample. -/
theorem split_integralSample (cell : CellModel) (cut : Rational)
    (left : Gaussian.Restriction.Cached cell.polynomial 0 (Cast.Path.ofCoordinate cut))
    (right : Gaussian.Restriction.Cached cell.polynomial (Cast.Path.ofCoordinate cut) 1) :
    (model cell left).integralSample + (model cell right).integralSample = cell.integralSample := by
  rewrite [integralSample_eq, integralSample_eq]
  change cell.displacement * Integral.definiteIntegral cell.polynomial 0 (Cast.Path.ofCoordinate cut) +
    cell.displacement * Integral.definiteIntegral cell.polynomial (Cast.Path.ofCoordinate cut) 1 = _
  calc
    _ = cell.displacement * (Integral.definiteIntegral cell.polynomial 0 (Cast.Path.ofCoordinate cut) +
        Integral.definiteIntegral cell.polynomial (Cast.Path.ofCoordinate cut) 1) := by ring1
    _ = cell.displacement * Integral.definiteIntegral cell.polynomial 0 1 :=
      congrArg (fun value : Canonical => cell.displacement * value)
        (Integral.definiteIntegral_concat cell.polynomial 0 (Cast.Path.ofCoordinate cut) 1).symm
    _ = cell.integralSample := rfl

end Purelib.Integration.Polynomial.Gaussian.Cell.Restriction
