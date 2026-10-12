module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.NatCast
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
public import Purelib.Approximation.Rational.Budget.Weighted
public import Purelib.Data.Rat.Fraction.Cast.Order
public import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Integration.Path.WeightedPathArea
import Purelib.Data.Rat.Fraction
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Pay all finite trace junction errors by a requested total length allowance.
The tolerance shrinks with the actual edge count; the resulting area estimate
uses only the total geometric length and the supplied allowance. -/
namespace Purelib.Integration.Path.NoisyPathArea
open Purelib.Algebra
open Purelib.Integration.Path
open Purelib.Data.Rat
open Purelib.Riemann.Periods

open Purelib.Data.Rat.Fraction.Compatibility

set_option genInjectivity false in
/-- A retained positive per-edge padding and its squared tolerance within an original total allowance.

The edge count times padding is paid by the supplied allowance, and the tolerance equality links the noise bound to that
exact padding. -/
structure LengthErrorBudget (count : Nat) (allowance : CenteredBilinearPath.Coordinate) where
  /-- The retained positive padding added to every original edge length. -/ padding : CenteredBilinearPath.Coordinate
  /-- The retained edge padding is strictly positive. -/ padding_positive : 0 < padding
  /-- The original edge count times padding is within the supplied allowance. -/ paid : (count :
    CenteredBilinearPath.Coordinate) * padding ≤ allowance
  /-- The retained squared noise tolerance. -/ tolerance : CenteredBilinearPath.Coordinate
  /-- The retained noise tolerance is strictly positive. -/ tolerance_positive : 0 < tolerance
  /-- The tolerance is exactly the square of the retained padding. -/ tolerance_eq : tolerance = padding^2

constructive_injectivity LengthErrorBudget

namespace LengthErrorBudget
variable {count : Nat} {allowance : Purelib.Riemann.Periods.CenteredBilinearPath.Coordinate}

open Purelib.Approximation.Rational in
/-- Choose a positive padding from the original count and allowance, retaining its square as tolerance.

The weighted rational allowance supplies the count payment and the returned certificate keeps the original count and
positive target. -/
@[expose] def build (count : Nat) (allowance : CenteredBilinearPath.Coordinate) (positive : 0 < allowance) :
  NoisyPathArea.LengthErrorBudget count allowance :=
  let padding := Budget.Weighted.allowance allowance count
  have nonnegative : (0 : CenteredBilinearPath.Coordinate) ≤ count := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le
    count)
  have paddingPositive := Budget.Weighted.allowance_positive positive nonnegative
  ⟨padding, paddingPositive, Budget.Weighted.mul_allowance_le positive.le nonnegative,
    padding^2, by simpa only [pow_two] using Fraction.Order.Arithmetic.mul_pos_direct paddingPositive paddingPositive,
      rfl⟩

/-- The finite sum of a constant rational equals the retained count times that constant.

Each successor contributes the same original summand. The owned natural-cast
addition certificate preserves that count and the scalar multiplication. -/
private theorem sum_constant (count : Nat) (value : CenteredBilinearPath.Coordinate) :
    FiniteSum.Fin.sumFin (fun _ : Fin count => value) = (count : CenteredBilinearPath.Coordinate) * value := by
  induction count with
  | zero => change 0 = 0 * value; ring1
  | succ count ih =>
      rw [FiniteSum.Fin.sumFin_succ, ih]
      have successor : ((count + 1 : Nat) : CenteredBilinearPath.Coordinate) =
          (count : CenteredBilinearPath.Coordinate) + 1 := Purelib.Algebra.NatCast.add count 1
      rewrite [successor]
      ring1

/-- Adding the retained padding to every original edge length increases total weight by at most the allowance. -/
theorem total_weight_le (budget : NoisyPathArea.LengthErrorBudget count allowance) (lengths : Fin count →
  CenteredBilinearPath.Coordinate) :
    FiniteSum.Fin.sumFin (fun edge => lengths edge + budget.padding) ≤ FiniteSum.Fin.sumFin lengths + allowance := by
  rw [FiniteSum.Fin.sumFin_add, NoisyPathArea.LengthErrorBudget.sum_constant]
  exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl budget.paid

/-- The retained squared tolerance is absorbed by the padded edge length under nonnegative density and length. -/
theorem increment_bound (budget : NoisyPathArea.LengthErrorBudget count allowance) {density length :
  CenteredBilinearPath.Coordinate}
    (densityNonnegative : 0 ≤ density) (lengthNonnegative : 0 ≤ length) :
    3 * budget.tolerance + 4 * density * length^2 ≤
      (4 * density + 3) * (length + budget.padding)^2 := by
  rw [budget.tolerance_eq]
  have first := Fraction.Order.Arithmetic.pow_le_pow_direct budget.padding_positive.le
    (show budget.padding ≤ length + budget.padding from le_add_of_nonneg_left lengthNonnegative) 2
  have second := Fraction.Order.Arithmetic.pow_le_pow_direct lengthNonnegative
    (show length ≤ length + budget.padding from le_add_of_nonneg_right budget.padding_positive.le) 2
  exact (Fraction.Order.Arithmetic.add_le_add_direct (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct first
    (by decide))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct second (Fraction.Order.Arithmetic.mul_nonneg_direct (by
      decide) densityNonnegative))).trans_eq (by ring1)

open Purelib.Data.Gaussian in
open Purelib.Riemann.Readings in
open Purelib.Topology.Polygon in
/-- Bound the original centered sample area using noisy increments and the retained length budget.

Each original edge keeps its length and noise tolerance; the estimate uses total length plus allowance and the common
centered magnitude and density. -/
theorem centered_area_bound (budget : NoisyPathArea.LengthErrorBudget count allowance)
    {values : Fin (count + 1) → Stokes.PrimitivePoint} (sample : CenteredBilinearPath.Sample values)
    (lengths : Fin count → CenteredBilinearPath.Coordinate) {magnitude density : CenteredBilinearPath.Coordinate}
    (magnitudeNonnegative : 0 ≤ magnitude) (densityNonnegative : 0 ≤ density)
    (nonnegative : ∀ edge, 0 ≤ lengths edge)
    (bounded : ∀ vertex, (PrimitiveAreaBounds.PrimitivePoint.Bounded (sample.centered vertex)) magnitude)
    (increments : ∀ edge : Fin count, (PrimitiveAreaBounds.PrimitivePoint.Bounded ((Stokes.PrimitivePoint.sub (values
      edge.succ)) (values edge.castSucc)))
      (3 * budget.tolerance + 4 * density * (lengths edge)^2)) :
    Data.Gaussian.Norm.Basic.normSq sample.centeredArea ≤ 4 * magnitude * (4 * density + 3) * (FiniteSum.Fin.sumFin
      lengths +
      allowance)^2 := by
  have weightsNonnegative : ∀ edge, 0 ≤ lengths edge + budget.padding :=
    fun edge => add_nonneg (nonnegative edge) budget.padding_positive.le
  have weighted := WeightedPathArea.Sample.centered_weighted_bound sample (fun edge => lengths edge + budget.padding)
    weightsNonnegative bounded (fun edge =>
      ⟨(increments edge).1.trans (budget.increment_bound densityNonnegative (nonnegative edge)),
       (increments edge).2.trans (budget.increment_bound densityNonnegative (nonnegative edge))⟩)
  have sumNonnegative : 0 ≤ FiniteSum.Fin.sumFin (fun edge => lengths edge + budget.padding) := by
    have sumPositive {n : Nat} (weights : Fin n → CenteredBilinearPath.Coordinate) (hn : ∀ i, 0 ≤ weights i) : 0 ≤
      FiniteSum.Fin.sumFin weights := by
      induction n with
      | zero => exact le_rfl
      | succ n ih => rw [FiniteSum.Fin.sumFin_succ]; exact add_nonneg (hn 0) (ih _ (fun i => hn i.succ))
    exact sumPositive _ weightsNonnegative
  exact weighted.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.pow_le_pow_direct sumNonnegative (budget.total_weight_le lengths) 2)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      magnitudeNonnegative)
      (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) densityNonnegative) (by decide))))

end LengthErrorBudget
end Purelib.Integration.Path.NoisyPathArea

end
