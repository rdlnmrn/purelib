module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
public import Purelib.Curves.Legendre.Periods.Fibre
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-! # One parameter range for every actual query on a fixed original patch

The retained whole-box movement ceiling and the original seed's four
ambient line margins give a positive floor on every actual acquired
contour. A finite Horner bound for the same physical box then gives one
positive squared increment bound, independent of query point and stage.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point

open Purelib
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Curves.Legendre.Periods
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Integration
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.RootIsolation.SquareRoot.Clearance
open Purelib.Polynomial.Dense.Gaussian

variable {parameter point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}

set_option genInjectivity false in
/-- Retained scalar bounds for the actual acquisition factory on one original continued box.

The movement ceiling, contour floor and affine-coefficient Horner bound are
computed once. Their defining equations retain the original seed owner and
physical box; there is no replacement root owner or point query in this cache.
-/
structure Range (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) where
  /-- The one computed whole-box radicand movement ceiling. -/ movement : Rational
  /-- The ceiling consumes the identical original neighborhood. -/ movement_eq :
    movement = CheckedPrimitiveNeighborhoods.movementCeiling patch
  /-- The original continuation allowance strictly exceeds this computed ceiling. -/ movement_small :
    movement < patch.continuationAllowance
  /-- The one computed common floor on actual acquired contour clearances. -/ contour : Rational
  /-- The floor consumes the original seed owner and retained movement ceiling. -/ contour_eq :
    contour = ExactQuadraticOwnerClearance.transportFloor patch.base.seed.owner movement
  /-- The original four ambient margins make this common contour floor positive. -/ contour_positive : 0 < contour
  /-- The finite original-box bound on the affine parameter coefficient. -/ coefficient : Rational
  /-- The coefficient bound uses the original Legendre numerator and identical physical box. -/ coefficient_eq :
    coefficient = Bounds.Box.denseEvalNormBound Polynomials.basePolynomial patch.box
  /-- The original finite Horner fold has a nonnegative value component. -/ coefficient_nonnegative : 0 ≤ coefficient

constructive_injectivity Range

namespace Range

/-- The original allowance pays all four source ambient margins for the computed common contour floor. -/
private theorem transportFloor_positive {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (movement : Rational) (small : movement < patch.continuationAllowance) :
    0 < ExactQuadraticOwnerClearance.transportFloor patch.base.seed.owner movement := by
  apply ExactQuadraticOwnerClearance.transportFloor_positive
  all_goals apply small.trans_le
  all_goals rewrite [patch.continuationAllowance_eq]
  · exact (Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _)
  · exact (Order.Basic.min_le_right _ _).trans ((Order.Basic.min_le_right _ _).trans
      (Order.Basic.min_le_left _ _))
  · exact (Order.Basic.min_le_right _ _).trans ((Order.Basic.min_le_right _ _).trans
      ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_left _ _)))
  · exact (Order.Basic.min_le_right _ _).trans ((Order.Basic.min_le_right _ _).trans
      ((Order.Basic.min_le_right _ _).trans (Order.Basic.min_le_right _ _)))

/-- Cache the finite scalar range of an original neighborhood with its certified whole-box allowance payment. -/
def ofNeighborhood (patch : ContinuedNeighborhood (Paths.polynomial parameter) count)
    (small : CheckedPrimitiveNeighborhoods.movementCeiling patch < patch.continuationAllowance) : Range patch :=
  let movement := CheckedPrimitiveNeighborhoods.movementCeiling patch
  let contour := ExactQuadraticOwnerClearance.transportFloor patch.base.seed.owner movement
  let coefficient := Bounds.Box.denseEvalNormBound Polynomials.basePolynomial patch.box
  ⟨movement, rfl, small, contour, rfl, transportFloor_positive movement small,
    coefficient, rfl, (Bounds.Box.denseHornerNormBounds_nonneg Polynomials.basePolynomial patch.box).1⟩

/-- Derive and cache the parameter range on the actual prepared patch, including accepted or rejected growth.

The existing original neighborhood factory supplies its own strict
movement payment. No pointwise minimum or caller-provided movement
inequality is needed by this concrete construction.
-/
def ofPreparedPatch {frame : Paths.Frame parameter}
    {basis : Curves.Hyperelliptic.Differentials.Basic.Differential 1}
    {parent : PreparedSubdivisionModelCore.CenteredEdge (Fibre.frameCurve frame) basis}
    (prepared : PreparedPatch parent) (count : Nat) : Range (prepared.neighborhood count) :=
  ofNeighborhood (prepared.neighborhood count) (prepared.movementCeiling_lt count)

variable (range : Range patch)

/-- The original site's denominator floor is positive on the identical continued physical box. -/
private theorem parameterFloor_positive (patch : ContinuedNeighborhood (Paths.polynomial parameter) count) :
    0 < patch.base.site.denominatorValue / 4 :=
  Order.Field.div_pos_direct patch.base.site.denominatorValue_positive (by decide +kernel)

/-- The cached contour and original radicand floor give one common squared parameter-increment bound. -/
@[expose] def bound : Rational :=
  min 1 (min range.contour (patch.base.site.denominatorValue / 4) / (range.coefficient + 1))

/-- The computed whole-box parameter-increment bound is strictly positive. -/
theorem bound_positive : 0 < range.bound :=
  Order.Basic.lt_min (by decide +kernel)
    (Order.Field.div_pos_direct (Order.Basic.lt_min range.contour_positive (parameterFloor_positive patch))
      (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct range.coefficient_nonnegative (by decide +kernel)))

/-- Every actual acquisition on this original box retains the same computed positive contour floor. -/
theorem contour_lower (inside : patch.box.Contains point) :
    range.contour ≤ (ContinuedNeighborhood.Point.acquire patch point inside).owner.track.initial.clearance.bound := by
  rewrite [range.contour_eq]
  apply ContinuedNeighborhood.Point.acquire_clearance_lower patch range.movement range.movement_small inside
  rewrite [range.movement_eq]
  exact CheckedPrimitiveNeighborhoods.movement_le_ceiling patch inside

/-- The retained finite physical-box fold bounds the original affine parameter coefficient at every admitted point. -/
theorem coefficient_upper (inside : patch.box.Contains point) :
    Norm.Basic.normSq (Polynomials.baseValue point) ≤ range.coefficient := by
  rewrite [range.coefficient_eq]
  unfold Polynomials.baseValue
  rewrite [← Polynomials.basePolynomial_eval]
  exact Bounds.Box.normSq_eval_le_denseEvalNormBound Polynomials.basePolynomial inside

/-- Scalar lower and upper bounds imply the original point owner's own admitted increment bound. -/
private theorem bound_le_of_bounds (source : ContinuedNeighborhood.Point patch point)
    {contour coefficient : Rational} (lower : contour ≤ source.owner.track.initial.clearance.bound)
    (parameterLower : patch.base.site.denominatorValue / 4 ≤ source.parameterNorm)
    (upper : Norm.Basic.normSq (Polynomials.baseValue point) ≤ coefficient)
    (nonnegative : 0 ≤ coefficient) :
    min 1 (min contour (patch.base.site.denominatorValue / 4) / (coefficient + 1)) ≤ incrementBound source := by
  unfold incrementBound
  apply Order.Basic.min_le_min (Order.Basic.le_refl 1)
  have numerator : min contour (patch.base.site.denominatorValue / 4) ≤ transportBudget source :=
    Order.Basic.min_le_min lower parameterLower
  have denominator : Norm.Basic.normSq (Polynomials.baseValue point) + 1 ≤ coefficient + 1 :=
    Order.Arithmetic.add_le_add_direct upper (Order.Basic.le_refl 1)
  exact (Order.Field.divide_mono numerator
    (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct nonnegative (by decide +kernel))).trans
    (Order.Field.div_le_div_of_nonneg_left_direct (transportBudget_positive source).le
      (Order.Arithmetic.add_pos_of_nonneg_of_pos_direct (Norm.Basic.normSq_nonneg _) (by decide +kernel)) denominator)

/-- One computed bound admits the original point continuation at every actual acquisition on this fixed patch. -/
theorem bound_le_incrementBound (inside : patch.box.Contains point) :
    range.bound ≤ incrementBound (ContinuedNeighborhood.Point.acquire patch point inside) := by
  apply bound_le_of_bounds _ (range.contour_lower inside)
  · rewrite [(ContinuedNeighborhood.Point.acquire patch point inside).parameterNorm_eq]
    exact patch.parameter_lower inside
  · exact range.coefficient_upper inside
  · exact range.coefficient_nonnegative

/-- Exact acquisition identity transports the uniform admission to the complete already retained source point. -/
theorem admitted_of_acquire (source : ContinuedNeighborhood.Point patch point) (inside : patch.box.Contains point)
    (same : source = ContinuedNeighborhood.Point.acquire patch point inside) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.bound) :
    Norm.Basic.normSq increment ≤ incrementBound source := by
  rewrite [same]
  exact admitted.trans (range.bound_le_incrementBound inside)

/-- Continue an already retained actual source acquisition using the computed whole-box parameter payment. -/
def advance (source : ContinuedNeighborhood.Point patch point) (inside : patch.box.Contains point)
    (same : source = ContinuedNeighborhood.Point.acquire patch point inside) (increment : Canonical)
    (admitted : Norm.Basic.normSq increment ≤ range.bound) : Step source increment :=
  Point.advance source increment (range.admitted_of_acquire source inside same increment admitted)

end Range

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point

end
