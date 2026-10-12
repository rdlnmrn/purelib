module
import Purelib.Algebra.Ring.IntCast
public import Purelib.Algebra.Group.Negation

import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
public import Purelib.Approximation.Gaussian.Geometric
public import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Indexed
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Vector.Basic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

public section
open Purelib.Algebra.Ring

/-!
# Cached integer combinations of synchronized period samples

The coefficient bank retains Gaussian values and their squared norms.
Finite Cauchy--Schwarz pays the actual term count and squared coefficients;
neither repeated operational addition nor a recursively doubled error bound
is used. The same bank combines finite samples and their error budgets.
-/

section

open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero sumFin_sub sumFin_mul_right)
open Purelib.Data.Gaussian.Basic.Canonical

namespace Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Data in
/-- The rational scalar type for cached coefficient masses and error bounds. -/
abbrev Coordinate := Rat.Fraction.Rational

end Purelib.Riemann.Periods.WeightedPeriods

namespace Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Data in
/-- The executable Gaussian rational type for weighted period values. -/
abbrev Gaussian := Gaussian.Basic.Canonical

end Purelib.Riemann.Periods.WeightedPeriods

namespace Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Data in
/-- The retained fixed-length vector type for coefficient and source banks. -/
abbrev Vector := Data.Vector

end Purelib.Riemann.Periods.WeightedPeriods

namespace Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Approximation in
/-- The Gaussian approximation type with explicit geometric error and center bounds. -/
abbrev GeometricApproximation := Gaussian.Geometric.GeometricApproximation

end Purelib.Riemann.Periods.WeightedPeriods

namespace Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Data in
/-- Convert an integer to a Gaussian rational using the executable binary rational conversion. -/
@[expose] def integer (value : Int) : Gaussian := ⟨Rat.Fraction.Cast.fromInt value, 0⟩

end Purelib.Riemann.Periods.WeightedPeriods

namespace Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Data in
/-- The binary Gaussian integer conversion agrees with the canonical ring cast. -/
theorem integer_eq (value : Int) : integer value = (value : Gaussian) := by
  have coordinates : (value : Gaussian) = (⟨(value : Coordinate), 0⟩ : Gaussian) := by
    cases value with
    | ofNat value =>
        exact Gaussian.Basic.ext (Gaussian.Cast.natCast_re value) (Gaussian.Cast.natCast_im value)
    | negSucc value =>
        change -(↑(value + 1) : Gaussian) = ⟨-(↑(value + 1) : Coordinate), 0⟩
        exact Gaussian.Basic.ext (by rw [Gaussian.Basic.neg_re, Gaussian.Cast.natCast_re]) (by
            rw [Gaussian.Basic.neg_im, Gaussian.Cast.natCast_im, neg_zero])
  rw [coordinates, Rat.Fraction.Cast.intCast_eq_fromInt]
  rfl

end Purelib.Riemann.Periods.WeightedPeriods

namespace Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Algebra in
/-- A finite sum of pointwise nonnegative rational values is nonnegative. -/
private theorem sum_nonnegative {count : Nat} (values : Fin count → Coordinate)
    (nonnegative : ∀ index, 0 ≤ values index) : 0 ≤ FiniteSum.Fin.sumFin values := by
  have bound := FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ => 0) values nonnegative
  rw [FiniteSum.Fin.sumFin_zero] at bound
  exact bound

end Purelib.Riemann.Periods.WeightedPeriods

namespace Purelib.Riemann.Periods.WeightedPeriods

open Purelib.Algebra in
set_option genInjectivity false in
/-- Cached Gaussian coefficients, their quadrances, finite count and aggregate error mass.

Every cache has an exact readback equation to the same retained integer weight vector. The mass is count times the sum
of squared coefficient magnitudes. -/
structure Coefficients {count : Nat} (weights : Vector Int count) where
  /-- The cached Gaussian rational representation of each integer coefficient. -/ values : Vector Gaussian count
  /-- The cached coefficient equals the corresponding integer ring cast. -/ values_eq : ∀ index, values index = (weights
    index : Gaussian)
  /-- The cached quadrance of each retained Gaussian coefficient. -/ norms : Vector Coordinate count
  /-- Each cached norm is the quadrance of that exact cached coefficient. -/ norms_eq : ∀ index, norms index = normSq
    (values index)
  /-- The cached rational representation of the finite coefficient count. -/ countValue : Coordinate
  /-- The cached count equals the natural count cast to the rational scalar type. -/ countValue_eq : countValue = (count
    : Coordinate)
  /-- The cached finite-count weighted coefficient quadrance sum. -/ mass : Coordinate
  /-- The cached mass equals countValue times the exact sum of cached norms. -/ mass_eq : mass = countValue *
    FiniteSum.Fin.sumFin norms

constructive_injectivity Coefficients

end Purelib.Riemann.Periods.WeightedPeriods

variable {count : Nat} {weights : Vector Int count}

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
open Purelib.Approximation in
open Purelib.Data in
/-- Cache the integer coefficient conversions, their quadrances, count and aggregate mass once. -/
@[expose] def build (weights : Vector Int count) : Coefficients weights :=
  let values := Vector.Basic.vectorOfFn fun index => integer (weights index)
  let norms := Vector.Basic.vectorOfFn fun index => normSq (values index)
  let countValue := Rational.Budget.Aggregate.countCoordinate count
  ⟨values, fun index => by rw [Vector.Basic.vectorOfFn_apply, integer_eq], norms, Vector.Basic.vectorOfFn_apply _,
    countValue, Rational.Budget.Aggregate.countCoordinate_eq count, countValue * FiniteSum.Fin.sumFin norms, rfl⟩

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- Every retained coefficient quadrance is nonnegative. -/
theorem norms_nonnegative (coefficients : Coefficients weights) (index : Fin count) : 0 ≤ coefficients.norms index := by
  rw [coefficients.norms_eq]; exact Gaussian.Basic.Canonical.normSq_nonneg _

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- The retained rational coefficient count is nonnegative. -/
theorem countValue_nonnegative (coefficients : Coefficients weights) : 0 ≤ coefficients.countValue := by
  rw [coefficients.countValue_eq]
  exact Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- The retained aggregate coefficient mass is nonnegative. -/
theorem mass_nonnegative (coefficients : Coefficients weights) : 0 ≤ coefficients.mass := by
  rw [coefficients.mass_eq]
  exact Rat.Fraction.Order.Arithmetic.mul_nonneg_direct coefficients.countValue_nonnegative
    (sum_nonnegative _ coefficients.norms_nonnegative)

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
/-- Form the finite linear combination using the exact cached Gaussian coefficients. -/
@[expose] def combine (coefficients : Coefficients weights) (values : Fin count → Gaussian) : Gaussian :=
  FiniteSum.Fin.sumFin fun index => coefficients.values index * values index

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
/-- The cached combination equals the finite sum using the original integer weights. -/
theorem combine_eq (coefficients : Coefficients weights) (values : Fin count → Gaussian) :
    coefficients.combine values = FiniteSum.Fin.sumFin (fun index => (weights index : Gaussian) * values index) :=
  FiniteSum.Fin.sumFin_congr fun index => congrArg (fun scalar => scalar * values index) (coefficients.values_eq index)

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
/-- Taking a difference commutes with the retained coefficient combination. -/
theorem combine_sub (coefficients : Coefficients weights) (left right : Fin count → Gaussian) :
    coefficients.combine left - coefficients.combine right = coefficients.combine (fun index => left index - right
      index) := by
  rw [combine, combine, ← FiniteSum.Fin.sumFin_sub]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  ring1

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
/-- Compute a finite-count weighted error allowance from cached coefficient quadrances and component bounds. -/
@[expose] def charge (coefficients : Coefficients weights) (bounds : Fin count → Coordinate) : Coordinate :=
  coefficients.countValue * FiniteSum.Fin.sumFin (fun index => coefficients.norms index * bounds index)

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- Pointwise nonnegative component bounds give a nonnegative weighted allowance. -/
theorem charge_nonnegative (coefficients : Coefficients weights) (bounds : Fin count → Coordinate)
    (nonnegative : ∀ index, 0 ≤ bounds index) : 0 ≤ coefficients.charge bounds :=
  Rat.Fraction.Order.Arithmetic.mul_nonneg_direct coefficients.countValue_nonnegative
    (sum_nonnegative _ fun index => Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
      (coefficients.norms_nonnegative index) (nonnegative index))

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- The cached coefficient combination has quadrance at most its weighted component allowance.

Each input value satisfies its displayed quadrance bound; the estimate pays the actual finite count and every cached
coefficient quadrance. -/
theorem normSq_combine_le (coefficients : Coefficients weights) (values : Fin count → Gaussian)
    (bounds : Fin count → Coordinate) (bounded : ∀ index, normSq (values index) ≤ bounds index) :
    normSq (coefficients.combine values) ≤ coefficients.charge bounds := by
  rw [charge, coefficients.countValue_eq]
  rw [combine, ← Gaussian.Norm.Basic.normSq_eq_canonical]
  apply Gaussian.Norm.Sum.Indexed.normSq_sumFin_le_count_mul_sumFin
  intro index
  rw [Gaussian.Norm.Basic.normSq_eq_canonical, Gaussian.Basic.Canonical.normSq_mul, coefficients.norms_eq]
  exact Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounded index)
    (Gaussian.Basic.Canonical.normSq_nonneg _)

/-- Weighted component difference bounds control the difference of the two cached combinations. -/
theorem normSq_difference_le (coefficients : Coefficients weights) (left right : Fin count → Gaussian)
    (bounds : Fin count → Coordinate) (bounded : ∀ index, normSq (left index - right index) ≤ bounds index) :
    normSq (coefficients.combine left - coefficients.combine right) ≤ coefficients.charge bounds := by
  rw [coefficients.combine_sub]
  exact coefficients.normSq_combine_le _ bounds bounded

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
/-- A constant component bound is charged as aggregate mass times that bound. -/
theorem charge_constant (coefficients : Coefficients weights) (bound : Coordinate) :
    coefficients.charge (fun _ => bound) = coefficients.mass * bound := by
  rw [charge, FiniteSum.Fin.sumFin_mul_right, coefficients.mass_eq]
  ring1

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
open Purelib.Approximation in
/-- The common quarter-radius decay factor commutes with the cached weighted allowance. -/
theorem charge_quarter (coefficients : Coefficients weights) (bounds : Fin count → Coordinate) (stage : Nat) :
    coefficients.charge (fun index => Rational.Geometric.Basic.quarterRadius (bounds index) stage) =
      Rational.Geometric.Basic.quarterRadius (coefficients.charge bounds) stage := by
  change coefficients.countValue * FiniteSum.Fin.sumFin (fun index => coefficients.norms index *
    Rational.Geometric.Basic.quarterRadius (bounds index) stage) =
      Rational.Geometric.Basic.quarterRadius (coefficients.countValue *
        FiniteSum.Fin.sumFin (fun index => coefficients.norms index * bounds index)) stage
  calc
    _ = coefficients.countValue * FiniteSum.Fin.sumFin (fun index => (coefficients.norms index * bounds index) * ((1 / 4
      : Coordinate) ^ stage)) := by
      apply congrArg (fun value => coefficients.countValue * value)
      exact FiniteSum.Fin.sumFin_congr fun _ => by rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow]; ring1
    _ = _ := by rw [FiniteSum.Fin.sumFin_mul_right, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]; ring1

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- Combine geometric approximation sources with one retained coefficient bank.

Only sample readbacks vary with the stage. Both global error and center bounds are computed once from the exact cached
coefficient quadrances. -/
@[expose] def approximation (coefficients : Coefficients weights) (sources : Vector GeometricApproximation count) :
    GeometricApproximation where
  sample := fun stage => coefficients.combine (fun index => (sources index).sample stage)
  errorScale := coefficients.charge (fun index => (sources index).errorScale)
  errorScale_nonneg := coefficients.charge_nonnegative _ (fun index => (sources index).errorScale_nonneg)
  later_close := fun order => by
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    have scalar := coefficients.normSq_difference_le _ _ _
      (fun index => by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self]
            using (sources index).later_close order)
    exact scalar.trans_eq (coefficients.charge_quarter _ _)
  centerBound := coefficients.charge (fun index => (sources index).centerBound)
  centerBound_nonneg := coefficients.charge_nonnegative _ (fun index => (sources index).centerBound_nonneg)
  sample_bounded := fun stage => by
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact coefficients.normSq_combine_le _ _
      (fun index => by
          simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self]
            using (sources index).sample_bounded stage)

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
/-- The combined sample is the finite integer-weighted sum of source samples at the same stage. -/
theorem approximation_sample (coefficients : Coefficients weights) (sources : Vector GeometricApproximation count)
  (stage : Nat) :
    (coefficients.approximation sources).sample stage =
      FiniteSum.Fin.sumFin (fun index => (weights index : Gaussian) * (sources index).sample stage) :=
        coefficients.combine_eq _

/-- Divide a target by one plus the retained aggregate coefficient mass. -/
@[expose] def perComponent (coefficients : Coefficients weights) (target : Coordinate) : Coordinate :=
  target / (coefficients.mass + 1)

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- A positive target gives a positive component allowance, including empty or zero-weight rows. -/
theorem perComponent_positive (coefficients : Coefficients weights) {target : Coordinate} (positive : 0 < target) :
    0 < coefficients.perComponent target :=
  Rat.Fraction.Order.Field.div_pos_direct positive
    (Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct coefficients.mass_nonnegative (by decide))

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- Charging the component allowance by the retained mass stays strictly below a positive target. -/
theorem mass_mul_perComponent_lt (coefficients : Coefficients weights) {target : Coordinate} (positive : 0 < target) :
    coefficients.mass * coefficients.perComponent target < target := by
  have paid : (coefficients.mass + 1) * coefficients.perComponent target = target := by
    rw [perComponent, Rat.Fraction.Field.mul_comm]
    exact Rat.Fraction.Field.div_mul_cancel_of_ne _ _
      (Rat.Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct coefficients.mass_nonnegative (by decide)).ne'
  calc
    _ < (coefficients.mass + 1) * coefficients.perComponent target :=
      Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_right_direct
        (by
          have raised := Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct
            (by decide : (0 : Coordinate) < 1) coefficients.mass
          rewrite [add_zero] at raised
          exact raised) (coefficients.perComponent_positive positive)
    _ = target := paid

/-- Component differences within the common allowance give combined quadrance strictly below the positive target. -/
theorem normSq_difference_lt (coefficients : Coefficients weights) (left right : Fin count → Gaussian)
    {target : Coordinate} (positive : 0 < target)
    (bounded : ∀ index, normSq (left index - right index) ≤ coefficients.perComponent target) :
    normSq (coefficients.combine left - coefficients.combine right) < target := by
  have estimate := coefficients.normSq_difference_le left right (fun _ => coefficients.perComponent target) bounded
  rw [coefficients.charge_constant] at estimate
  exact estimate.trans_lt (coefficients.mass_mul_perComponent_lt positive)

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Data in
/-- Negate the retained coefficient bank while reusing its cached norms, count and aggregate mass.

The resulting bank is indexed by the exact pointwise-negated integer vector. -/
@[expose] def negate (coefficients : Coefficients weights) : Coefficients (Vector.Basic.vectorOfFn fun index => -weights
  index) :=
  { values := Vector.Basic.vectorOfFn fun index => -coefficients.values index
    values_eq := fun index => by
      rw [Vector.Basic.vectorOfFn_apply, Vector.Basic.vectorOfFn_apply, coefficients.values_eq]
      exact (IntCast.neg (R := Gaussian) (weights index)).symm
    norms := coefficients.norms
    norms_eq := fun index => by rw [Vector.Basic.vectorOfFn_apply, Gaussian.Basic.Canonical.normSq_neg,
      coefficients.norms_eq]
    countValue := coefficients.countValue
    countValue_eq := coefficients.countValue_eq
    mass := coefficients.mass
    mass_eq := coefficients.mass_eq }

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

namespace Purelib.Riemann.Periods.WeightedPeriods.Coefficients

open Purelib.Algebra in
open Purelib.Data in
/-- Negating the coefficient bank negates its combined value. -/
theorem negate_combine (coefficients : Coefficients weights) (values : Fin count → Gaussian) :
    coefficients.negate.combine values = -coefficients.combine values := by
  rw [combine, combine, ← FiniteSum.Fin.sumFin_neg]
  apply FiniteSum.Fin.sumFin_congr
  intro index
  change Vector.Basic.vectorOfFn (fun index => -coefficients.values index) index * values index = _
  rw [Vector.Basic.vectorOfFn_apply]
  ring1

end Purelib.Riemann.Periods.WeightedPeriods.Coefficients

end
