module

public import Purelib.RationalFunctions.Curve.Canonical.Circle.Coverage
import Purelib.RationalFunctions.Curve.Canonical.Circle.Inverse
public import Purelib.RationalFunctions.Curve.Substitution.Retained
public import Purelib.Polynomial.Clearance.Pair.Basic
public import Purelib.Polynomial.Clearance.Pair.Cover.Retained
public import Purelib.Polynomial.Clearance.Pair.Cover.Leaves
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Interval.Bounds
import Purelib.Polynomial.Dense.Gaussian.Components
import Purelib.Algebra.Field.ExplicitField
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# The whole rational unit-circle boundary

The primary chart runs from minus the imaginary unit to the imaginary unit;
the reciprocal chart runs in reverse parameter order back to the starting
point. Both closed parameter cells are retained, including their joins and
the exceptional point of the other chart.
-/

namespace Purelib.RationalFunctions.Curve.Canonical.Circle.Boundary

open Purelib.Data
open Purelib.Polynomial
open Purelib.Polynomial.Clearance
open Purelib.Algebra.Field
open Rat.Fraction.Order
open Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Rat.Fraction (Rational)

/-- The closed parameter cell used by both unit-circle charts. -/
@[expose] public def parameters : Rat.Interval.Bounds := ⟨-1, 1, by decide⟩

/-- The primary chart starts at minus the imaginary unit. -/
public theorem primary_start : (circle 1).point (-1) = -Gaussian.Constants.imaginaryUnit := by decide

/-- The primary chart ends at the imaginary unit. -/
public theorem primary_stop : (circle 1).point 1 = Gaussian.Constants.imaginaryUnit := by decide

/-- The reversed reciprocal chart starts at the imaginary unit. -/
public theorem reciprocal_start :
    (reciprocalCircle 1).point 1 = Gaussian.Constants.imaginaryUnit := by decide

/-- The reversed reciprocal chart ends at minus the imaginary unit. -/
public theorem reciprocal_stop :
    (reciprocalCircle 1).point (-1) = -Gaussian.Constants.imaginaryUnit := by decide

/-- The primary chart contains the reciprocal chart's exceptional point. -/
public theorem primary_exception : (circle 1).point 0 = 1 := by decide

/-- The reciprocal chart contains the primary chart's exceptional point. -/
public theorem reciprocal_exception : (reciprocalCircle 1).point 0 = -1 := by decide

/-- The common real chart denominator is strictly positive. -/
private theorem denominator_positive (parameter : Rational) : 0 < parameter ^ 2 + 1 := by
  have bound := Arithmetic.add_le_add_right_direct
    (Arithmetic.sq_nonneg_direct parameter) 1
  rw [Rat.Fraction.Field.zero_add] at bound
  exact (show (0 : Rational) < 1 by decide).trans_le bound

/-- The retained primary half-circle has nonnegative real coordinate. -/
public theorem primary_nonnegative {parameter : Rational} (inside : parameters.Contains parameter) :
    0 ≤ ((circle 1).point parameter).re := by
  have square : parameter ^ 2 ≤ 1 :=
    (Rat.Interval.Bounds.sq_le_squareBound inside).trans_eq (by decide)
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := parameter ^ 2 + 1) _
    (denominator_positive parameter)
  rw [Rat.Fraction.Field.zero_mul_direct, (circle_one_coordinate_products parameter).1]
  exact Arithmetic.sub_nonneg_direct square

/-- The retained reciprocal half-circle has nonpositive real coordinate. -/
public theorem reciprocal_nonpositive {parameter : Rational} (inside : parameters.Contains parameter) :
    ((reciprocalCircle 1).point parameter).re ≤ 0 := by
  have square : parameter ^ 2 ≤ 1 :=
    (Rat.Interval.Bounds.sq_le_squareBound inside).trans_eq (by decide)
  apply Arithmetic.le_of_mul_le_mul_right_direct (c := parameter ^ 2 + 1) _
    (denominator_positive parameter)
  rw [Rat.Fraction.Field.zero_mul_direct, (reciprocalCircle_one_coordinate_products parameter).1]
  calc
    parameter ^ 2 - 1 = parameter ^ 2 + (-1) := by ring1
    _ ≤ 1 + (-1) := Arithmetic.add_le_add_right_direct square (-1)
    _ = 0 := by decide

/-- The bounded chart cells overlap precisely at their two displayed joins.

The parameter is unchanged at each join; reversing the reciprocal parameter
orientation therefore gives one closed boundary traversal. -/
public theorem overlap {primaryParameter reciprocalParameter : Rational}
    (primaryInside : parameters.Contains primaryParameter)
    (reciprocalInside : parameters.Contains reciprocalParameter)
    (equal : (circle 1).point primaryParameter = (reciprocalCircle 1).point reciprocalParameter) :
    (primaryParameter = -1 ∧ reciprocalParameter = -1) ∨
      (primaryParameter = 1 ∧ reciprocalParameter = 1) := by
  have realZero : ((circle 1).point primaryParameter).re = 0 := by
    apply le_antisymm
    · rw [equal]
      exact reciprocal_nonpositive reciprocalInside
    · exact primary_nonnegative primaryInside
  have square : 1 - primaryParameter ^ 2 = 0 := by
    have products := (circle_one_coordinate_products primaryParameter).1
    rw [realZero, Rat.Fraction.Field.zero_mul_direct] at products
    exact products.symm
  have factored : (primaryParameter - 1) * (primaryParameter + 1) = 0 := by
    calc
      (primaryParameter - 1) * (primaryParameter + 1) = -(1 - primaryParameter ^ 2) := by ring1
      _ = 0 := by rw [square]; decide
  have endpoints : primaryParameter = -1 ∨ primaryParameter = 1 := by
    by_cases plus : primaryParameter = 1
    · exact Or.inr plus
    · have minusNonzero : primaryParameter - 1 ≠ 0 := by
        intro zero
        apply plus
        calc
          primaryParameter = (primaryParameter - 1) + 1 := by ring1
          _ = 1 := by rw [zero]; ring1
      have sumZero := ExplicitField.eq_zero_of_mul_eq_zero_left minusNonzero factored
      exact Or.inl (by
        calc
          primaryParameter = (primaryParameter + 1) - 1 := by ring1
          _ = -1 := by rw [sumZero]; ring1)
  cases endpoints with
  | inl endpoint =>
      apply Or.inl
      refine ⟨endpoint, reciprocalCircle_one_point_injective ?_⟩
      calc
        (reciprocalCircle 1).point reciprocalParameter = (circle 1).point primaryParameter := equal.symm
        _ = (reciprocalCircle 1).point (-1) := by rw [endpoint, primary_start, reciprocal_stop]
  | inr endpoint =>
      apply Or.inr
      refine ⟨endpoint, reciprocalCircle_one_point_injective ?_⟩
      calc
        (reciprocalCircle 1).point reciprocalParameter = (circle 1).point primaryParameter := equal.symm
        _ = (reciprocalCircle 1).point 1 := by rw [endpoint, primary_stop, reciprocal_start]

/-- Every rational unit-circle point belongs to at least one retained chart cell.

The half-plane decision supplies an explicit parameter and includes both joins. -/
public theorem covers (point : Gaussian.Basic.Canonical)
    (unit : Gaussian.Basic.Canonical.normSq point = 1) :
    (∃ parameter, parameters.Contains parameter ∧ (circle 1).point parameter = point) ∨
      (∃ parameter, parameters.Contains parameter ∧ (reciprocalCircle 1).point parameter = point) := by
  have norm : Gaussian.Norm.Basic.normSq point = 1 :=
    (Gaussian.Norm.Basic.normSq_eq_canonical point).trans unit
  by_cases nonnegative : 0 ≤ point.re
  · have covered := primaryUnitCircle_covers point norm nonnegative
    exact Or.inl ⟨_, ⟨covered.1, covered.2.1⟩, covered.2.2⟩
  · have covered := reciprocalUnitCircle_covers point norm (le_of_lt (lt_of_not_ge nonnegative))
    exact Or.inr ⟨_, ⟨covered.1, covered.2.1⟩, covered.2.2⟩

set_option genInjectivity false in
/-- The two once-computed original substitutions on the complete circle charts. -/
public structure Substitutions (polynomial : CoefficientPolynomial) where
  /-- The retained primary-chart substitution. -/ primary : Substitution.Retained polynomial (circle 1)
  /-- The retained reciprocal-chart substitution. -/ reciprocal : Substitution.Retained polynomial (reciprocalCircle 1)

constructive_injectivity Substitutions

namespace Substitutions

/-- Compute each original chart substitution once. -/
@[expose] public def prepare (polynomial : CoefficientPolynomial) : Substitutions polynomial :=
  ⟨Substitution.Retained.prepare polynomial (circle 1),
    Substitution.Retained.prepare polynomial (reciprocalCircle 1)⟩

/-- Both original cleared substitutions have the same Gaussian value at either circle join. -/
public theorem cleared_endpoint_eq (polynomial : CoefficientPolynomial) (parameter : Rational)
    (endpoint : parameter = -1 ∨ parameter = 1) :
    (clearedEval polynomial (circle 1)).eval (Gaussian.Cast.Path.ofCoordinate parameter) =
      (clearedEval polynomial (reciprocalCircle 1)).eval (Gaussian.Cast.Path.ofCoordinate parameter) := by
  have pointEqual : (circle 1).point parameter = (reciprocalCircle 1).point parameter := by
    cases endpoint with
    | inl equal => rw [equal, primary_start, reciprocal_stop]
    | inr equal => rw [equal, primary_stop, reciprocal_start]
  rw [eval_clearedEval polynomial (circle 1) parameter (circle_denominator_ne 1 parameter),
    eval_clearedEval polynomial (reciprocalCircle 1) parameter (reciprocalCircle_denominator_ne 1 parameter),
    eval_denominatorPower, eval_denominatorPower, circle_denominatorAt, reciprocalCircle_denominatorAt, pointEqual]

/-- Both retained real coordinate tables agree at either original circle join. -/
public theorem endpoint_real_eq {polynomial : CoefficientPolynomial} (paths : Substitutions polynomial)
    (parameter : Rational) (endpoint : parameter = -1 ∨ parameter = 1) :
    paths.primary.real.eval parameter = paths.reciprocal.real.eval parameter := by
  rw [paths.primary.real_readback, paths.reciprocal.real_readback,
    clearedReal, clearedReal, Dense.Gaussian.Components.eval_realPart, Dense.Gaussian.Components.eval_realPart,
    cleared_endpoint_eq polynomial parameter endpoint]

/-- Both retained imaginary coordinate tables agree at either original circle join. -/
public theorem endpoint_imaginary_eq {polynomial : CoefficientPolynomial} (paths : Substitutions polynomial)
    (parameter : Rational) (endpoint : parameter = -1 ∨ parameter = 1) :
    paths.primary.imaginary.eval parameter = paths.reciprocal.imaginary.eval parameter := by
  rw [paths.primary.imaginary_readback, paths.reciprocal.imaginary_readback,
    clearedImag, clearedImag, Dense.Gaussian.Components.eval_imagPart, Dense.Gaussian.Components.eval_imagPart,
    cleared_endpoint_eq polynomial parameter endpoint]

end Substitutions

set_option genInjectivity false in
/-- Uniform positive clearance on both complete chart cells.

The polynomial and the exact retained substitution tables remain indexed;
clearance on a selected subarc does not inhabit this certificate. -/
public structure Clearance {polynomial : CoefficientPolynomial} (paths : Substitutions polynomial) where
  /-- Positive clearance for the primary chart on its whole closed cell. -/ primary :
    Pair.Basic.Certificate paths.primary.real paths.primary.imaginary parameters
  /-- Positive clearance for the reciprocal chart on its whole closed cell. -/ reciprocal :
    Pair.Basic.Certificate paths.reciprocal.real paths.reciprocal.imaginary parameters

constructive_injectivity Clearance

namespace Clearance

/-- Whole-boundary clearance excludes a polynomial zero at every rational unit-circle point. -/
public theorem nonzero {polynomial : CoefficientPolynomial} {paths : Substitutions polynomial}
    (clearance : Clearance paths) (point : Gaussian.Basic.Canonical)
    (unit : Gaussian.Basic.Canonical.normSq point = 1) : polynomial.eval point ≠ 0 := by
  intro zero
  rcases covers point unit with ⟨parameter, inside, equal⟩ | ⟨parameter, inside, equal⟩
  · have coordinateZero := (paths.primary.zero_iff parameter (circle_denominator_ne 1 parameter)).mpr
      (equal ▸ zero)
    rcases clearance.primary.eval_ne_zero inside with realNonzero | imaginaryNonzero
    · exact realNonzero coordinateZero.1
    · exact imaginaryNonzero coordinateZero.2
  · have coordinateZero :=
      (paths.reciprocal.zero_iff parameter (reciprocalCircle_denominator_ne 1 parameter)).mpr (equal ▸ zero)
    rcases clearance.reciprocal.eval_ne_zero inside with realNonzero | imaginaryNonzero
    · exact realNonzero coordinateZero.1
    · exact imaginaryNonzero coordinateZero.2

end Clearance

set_option genInjectivity false in
/-- A bounded whole-boundary attempt retaining both original refinement trees.

The exact construction equations bind the original tables, budget and all
cached leaves to the actual refinement procedure. -/
public structure Attempt (polynomial : CoefficientPolynomial) where
  /-- Both original chart substitutions, shared by every subsequent calculation. -/ paths : Substitutions polynomial
  /-- The actual maximum depth of either bounded refinement. -/ depth : Nat
  /-- The original retained primary cover. -/ primary :
    Pair.Cover.Retained paths.primary.real paths.primary.imaginary parameters
  /-- The primary cover is the actual bounded preparation. -/ primary_eq : primary =
    Pair.Cover.Retained.prepare paths.primary.real paths.primary.imaginary parameters depth
  /-- The original retained reciprocal cover. -/ reciprocal :
    Pair.Cover.Retained paths.reciprocal.real paths.reciprocal.imaginary parameters
  /-- The reciprocal cover is the actual bounded preparation. -/ reciprocal_eq : reciprocal =
    Pair.Cover.Retained.prepare paths.reciprocal.real paths.reciprocal.imaginary parameters depth

constructive_injectivity Attempt

namespace Attempt

/-- Prepare both chart covers from the same retained substitutions and supplied finite depth. -/
@[expose] public def prepare (polynomial : CoefficientPolynomial) (depth : Nat) : Attempt polynomial :=
  let paths := Substitutions.prepare polynomial
  { paths, depth
    primary := Pair.Cover.Retained.prepare
      paths.primary.real paths.primary.imaginary parameters depth, primary_eq := rfl
    reciprocal := Pair.Cover.Retained.prepare
      paths.reciprocal.real paths.reciprocal.imaginary parameters depth, reciprocal_eq := rfl }

end Attempt

set_option genInjectivity false in
/-- An explained result of checking the actual cached whole-boundary attempt.

An inconclusive result identifies every unresolved terminal leaf through the
retained trees and proves that at least one such obligation remains. -/
public inductive Outcome {polynomial : CoefficientPolynomial} (attempt : Attempt polynomial) where
  /-- Both original aggregate floors certify the entire boundary. -/ | clear (certificate : Clearance attempt.paths)
  /-- An exact displayed unit-circle zero proves failure of boundary nonvanishing. -/ | contact
    (point : Gaussian.Basic.Canonical) (unit : Gaussian.Basic.Canonical.normSq point = 1)
    (zero : polynomial.eval point = 0)
  /-- The finite depth was insufficient; all unresolved leaves remain in the actual trees. -/ | inconclusive
    (primaryLeaves : List (Pair.Cover.UnresolvedLeaf attempt.primary.source))
    (reciprocalLeaves : List (Pair.Cover.UnresolvedLeaf attempt.reciprocal.source))
    (primary_eq : primaryLeaves = attempt.primary.result.cover.unresolved)
    (reciprocal_eq : reciprocalLeaves = attempt.reciprocal.result.cover.unresolved)
    (remaining : primaryLeaves ≠ [] ∨ reciprocalLeaves ≠ [])

constructive_injectivity Outcome

namespace Attempt

/-- Read a whole-boundary certificate from the two positive cached aggregate floors. -/
@[expose] public def clearance {polynomial : CoefficientPolynomial} (attempt : Attempt polynomial)
    (primaryPositive : 0 < attempt.primary.result.normFloor)
    (reciprocalPositive : 0 < attempt.reciprocal.result.normFloor) : Clearance attempt.paths :=
  { primary := ⟨attempt.primary.result.normFloor, primaryPositive,
      fun _ inside => attempt.primary.result.cover.norm_le inside⟩
    reciprocal := ⟨attempt.reciprocal.result.normFloor, reciprocalPositive,
      fun _ inside => attempt.reciprocal.result.cover.norm_le inside⟩ }

/-- Check the retained cover floors and a displayed exact contact at the primary chart midpoint.

Failed finite separation returns both exact unresolved-leaf lists and never
asserts a zero. The contact branch proves the actual polynomial vanishes at one. -/
@[expose] public def check {polynomial : CoefficientPolynomial} (attempt : Attempt polynomial) : Outcome attempt :=
  if contact : polynomial.eval 1 = 0 then .contact 1 Gaussian.Basic.Canonical.normSq_one contact
  else if primaryPositive : 0 < attempt.primary.result.normFloor then
    if reciprocalPositive : 0 < attempt.reciprocal.result.normFloor then
      .clear (attempt.clearance primaryPositive reciprocalPositive)
    else .inconclusive _ _ rfl rfl
      (Or.inr (attempt.reciprocal.result.cover.unresolved_ne_nil reciprocalPositive))
  else .inconclusive _ _ rfl rfl
    (Or.inl (attempt.primary.result.cover.unresolved_ne_nil primaryPositive))

end Attempt

/-- Prepare and check a complete bounded boundary attempt, retaining its exact data in either outcome. -/
@[expose] public def prepare (polynomial : CoefficientPolynomial) (depth : Nat) :
    Sigma (Outcome (polynomial := polynomial)) :=
  let attempt := Attempt.prepare polynomial depth
  ⟨attempt, attempt.check⟩

end Purelib.RationalFunctions.Curve.Canonical.Circle.Boundary
