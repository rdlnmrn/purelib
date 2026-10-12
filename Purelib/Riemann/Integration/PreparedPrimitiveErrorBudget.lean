module
import Purelib.Algebra.Field.ExplicitField
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

public import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Numeric budget for sheet-equivalent prepared primitive comparisons

The operational-equivalence comparison pays larger constants than the
nested-root-box comparison.  This shared finite algebra consumes the same
cached request budget, independently of the construction of its sheet proof.
-/

namespace Purelib.Riemann.Integration.PreparedPrimitiveErrorBudget

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (Request movement rootScale errorWeight)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Algebra in
open Purelib.Approximation in
open Purelib.Data in
/-- Express the inverse-root contribution as twice the request's geometric root scale. -/
private theorem rootTerm_eq (patch : ContinuedNeighborhood curve.polynomial count)
    (numeratorBound distance : Rat.Fraction.Rational) (index : Nat) :
    4 * numeratorBound * Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale index * distance =
      2 * Rational.Geometric.Basic.quarterRadius (rootScale patch numeratorBound distance) index := by
  have half : (128 : Rat.Fraction.Rational)⁻¹ = 2 * (256 : Rat.Fraction.Rational)⁻¹ := by decide +kernel
  simp only [ContinuedNeighborhood.inverseErrorScale, rootScale, Rational.Geometric.Basic.quarterRadius,
    Field.ExplicitField.div_eq_mul_inv]
  rw [half]
  ring1

open Purelib.Riemann in
open Purelib.Data in
/-- Bound forty movement-weighted model errors by five request error charges.

The numerator bound, movement and error are nonnegative; the request's weight includes the extra inverse-root
contribution. -/
private theorem preparedCharge_le (patch : ContinuedNeighborhood curve.polynomial count)
    {numeratorBound distance error : Rat.Fraction.Rational}
    (numeratorNonnegative : 0 ≤ numeratorBound) (distanceNonnegative : 0 ≤ distance) (errorNonnegative : 0 ≤ error) :
    40 * error * distance ≤ 5 * (errorWeight patch numeratorBound distance * error) := by
  have scaled : 0 ≤ 64 * numeratorBound := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    numeratorNonnegative
  have divided := Rat.Fraction.Order.Field.div_nonneg_direct scaled
    (Readings.PreparedPrimitiveRequests.denominatorLower_positive patch).le
  have extra := Rat.Fraction.Order.Field.div_nonneg_direct divided patch.rootLower_positive.le
  have weight : 8 * distance ≤ errorWeight patch numeratorBound distance :=
    Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (le_add_of_nonneg_left extra) distanceNonnegative
  calc
    _ = (8 * distance) * (5 * error) := by ring1
    _ ≤ errorWeight patch numeratorBound distance * (5 * error) :=
      Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct weight
        (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) errorNonnegative)
    _ = _ := by ring1

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- The operational primitive comparison budget is strictly below eight times its positive target.

The retained Taylor, polynomial and prepared error bounds pay their respective terms using the same request index, depth
and model. -/
theorem Request.operational_bound_lt {parent : CenteredEdge curve differential}
    {patch : ContinuedNeighborhood curve.polynomial count} {target : Rat.Fraction.Rational}
    (request : Request parent patch target) (positive : 0 < target) :
    2 * request.model.primitive.remainderBound * movement parent * Rational.Geometric.Basic.quarterRadius (movement
      parent) request.budget.depth +
      (4 * request.numeratorBound * Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale request.index + 40 *
        request.budget.error) * movement parent <
        8 * target := by
  have distanceNonnegative := Readings.PreparedPrimitiveRequests.movement_nonnegative parent
  have spatialNonnegative := Rational.Geometric.Basic.quarterRadius_nonneg distanceNonnegative request.budget.depth
  have taylorNonnegative := Rat.Fraction.Order.Arithmetic.mul_nonneg_direct
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct request.model.primitive.remainderBound_nonnegative
      distanceNonnegative) spatialNonnegative
  have taylorLe : 2 * request.model.primitive.remainderBound * movement parent * Rational.Geometric.Basic.quarterRadius
    (movement parent) request.budget.depth ≤ target / 3 := by
    calc
      _ = 2 * (request.model.primitive.remainderBound * movement parent * Rational.Geometric.Basic.quarterRadius
        (movement parent) request.budget.depth) := by
        ring1
      _ ≤ 4 * (request.model.primitive.remainderBound * movement parent * Rational.Geometric.Basic.quarterRadius
        (movement parent) request.budget.depth) :=
        Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide) taylorNonnegative
      _ = 4 * request.model.primitive.remainderBound * movement parent * Rational.Geometric.Basic.quarterRadius
        (movement parent) request.budget.depth := by
        ring1
      _ ≤ _ := request.budget.taylor_le
  have rootLt : 4 * request.numeratorBound * Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale
    request.index * movement parent < 2 * (target / 3) := by
    rw [rootTerm_eq]
    exact Rat.Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide) request.polynomial_accurate
  have preparedLe : 40 * request.budget.error * movement parent ≤ 5 * (target / 3) :=
    (preparedCharge_le patch request.numerator_nonnegative distanceNonnegative request.budget.error_positive.le).trans
      (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct request.budget.error_le (by decide))
  have first := (Rat.Fraction.Order.Arithmetic.add_lt_add_left_direct rootLt
    (2 * request.model.primitive.remainderBound * movement parent * Rational.Geometric.Basic.quarterRadius (movement
      parent) request.budget.depth)).trans_le
      (add_le_add taylorLe le_rfl)
  have total := (Rat.Fraction.Order.Arithmetic.add_lt_add_right_direct first (40 * request.budget.error * movement
    parent)).trans_le
    (add_le_add le_rfl preparedLe)
  have thirdLe : target / 3 ≤ target := by
    apply (Rat.Fraction.Order.Field.div_le_iff_pos (by decide)).mpr
    have scaled := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (by decide : (1 : Rat.Fraction.Rational) ≤ 3) positive.le
    simpa only [Rat.Fraction.Field.mul_one_direct] using scaled
  calc
    _ = (2 * request.model.primitive.remainderBound * movement parent * Rational.Geometric.Basic.quarterRadius (movement
      parent) request.budget.depth +
        4 * request.numeratorBound * Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale request.index *
          movement parent) +
          40 * request.budget.error * movement parent := by ring1
    _ < (target / 3 + 2 * (target / 3)) + 5 * (target / 3) := total
    _ = 8 * (target / 3) := by ring1
    _ ≤ 8 * target := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct thirdLe (by decide)

end Purelib.Riemann.Integration.PreparedPrimitiveErrorBudget
