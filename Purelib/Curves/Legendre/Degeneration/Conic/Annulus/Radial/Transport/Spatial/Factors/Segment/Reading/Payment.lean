module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Movement
public import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Data.Fin.Two
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Computed residual and physical-width payments for the actual product

The original seed radius, cofactor square and quadratic sensitivity determine
positive residual and spatial requests. The actual product movement splits
into their three separately paid terms. A finite geometric depth pays the
original segment's physical displacement, including zero-length segments,
without asserting that an existing covered request already meets that depth.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Approximation
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Rational
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.RootContinuation

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {reference : Fraction.Rational} {referenceInside : FixedRootBoxPath.Inside reference}
variable {source : Transport.Reading actual reference referenceInside}

/-- The identical retained original source radius square. -/
@[expose] def radiusSq (anchor : Parameter.Anchor source.lift) := anchor.seed.separation.radius ^ 2

/-- The actual source radius square is strictly positive. -/
theorem radiusSq_positive (anchor : Parameter.Anchor source.lift) : 0 < radiusSq anchor :=
  Arithmetic.pow_pos_direct anchor.seed.separation.positive 2

/-- The same original signed-square full-product norm floor. -/
@[expose] def floor (anchor : Parameter.Anchor source.lift) := radiusSq anchor / 4

/-- The internally derived full-product norm floor is positive. -/
theorem floor_positive (anchor : Parameter.Anchor source.lift) : 0 < floor anchor :=
  Fraction.Order.Field.div_pos_direct (radiusSq_positive anchor) (by decide +kernel)

/-- The unchanged original cofactor square's endpoint-based magnitude ceiling. -/
@[expose] def unitCeiling (site : Fin 2) := (UnitRoot.box site).normSqBound

/-- The original signed cofactor box gives the same positive ceiling at both labelled collisions. -/
theorem unitCeiling_eq (site : Fin 2) : unitCeiling site = (9 / 2 : Fraction.Rational) := by
  rcases Data.Fin.Two.finTwo_cases site with zero | one
  · subst site
    decide +kernel
  · subst site
    decide +kernel

/-- The unchanged original cofactor magnitude ceiling is strictly positive. -/
theorem unitCeiling_positive (site : Fin 2) : 0 < unitCeiling site := by
  rewrite [unitCeiling_eq]
  decide +kernel

/-- The actual normalized spatial sensitivity retained from the original half-gap. -/
@[expose] def sensitivity (site : Fin 2) (parameter : Canonical) :=
  (Fraction.Cast.fromInt 801 / 64) * Norm.Basic.normSq (halfGap site parameter)

/-- The original normalized sensitivity is nonnegative. -/
theorem sensitivity_nonnegative (site : Fin 2) (parameter : Canonical) : 0 ≤ sensitivity site parameter :=
  Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)

/-- The normalized residual coefficient of the actual full-product movement. -/
@[expose] def normalCoefficient (anchor : Parameter.Anchor source.lift) :=
  2 * unitCeiling site / radiusSq anchor

/-- The normalized residual coefficient is positive on the original signed source window. -/
theorem normalCoefficient_positive (anchor : Parameter.Anchor source.lift) : 0 < normalCoefficient anchor :=
  Fraction.Order.Field.div_pos_direct
    (Arithmetic.mul_pos_direct (by decide +kernel) (unitCeiling_positive site))
    (radiusSq_positive anchor)

/-- The cofactor residual coefficient of the same full-product movement. -/
@[expose] def unitCoefficient (anchor : Parameter.Anchor source.lift) := 160 * radiusSq anchor

/-- The original cofactor residual coefficient is strictly positive. -/
theorem unitCoefficient_positive (anchor : Parameter.Anchor source.lift) : 0 < unitCoefficient anchor :=
  Arithmetic.mul_pos_direct
    (Fraction.Cast.Order.natCast_pos_direct (n := 160) (by decide +kernel)) (radiusSq_positive anchor)

/-- The physical displacement coefficient retains both original factor sensitivities. -/
@[expose] def spatialCoefficient (anchor : Parameter.Anchor source.lift) :=
  unitCeiling site * sensitivity site parameter / radiusSq anchor + 80 * radiusSq anchor

/-- The physical displacement coefficient is positive without dividing by a spatial edge length. -/
theorem spatialCoefficient_positive (anchor : Parameter.Anchor source.lift) : 0 < spatialCoefficient anchor :=
  Arithmetic.add_pos_of_nonneg_of_pos_direct
    (Fraction.Order.Field.div_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (unitCeiling_positive site).le (sensitivity_nonnegative site parameter))
      (radiusSq_positive anchor).le)
    (Arithmetic.mul_pos_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 80) (by decide +kernel)) (radiusSq_positive anchor))

/-- One positive original normalized residual request paying half of its two-observation allowance. -/
@[expose] def normalResidual (anchor : Parameter.Anchor source.lift) : AccuracyRequest :=
  ⟨floor anchor / (32 * normalCoefficient anchor), Fraction.Order.Field.div_pos_direct (floor_positive anchor)
    (Arithmetic.mul_pos_direct (by decide +kernel) (normalCoefficient_positive anchor))⟩

/-- One positive original cofactor residual request paying half of its independent two-observation allowance. -/
@[expose] def unitResidual (anchor : Parameter.Anchor source.lift) : AccuracyRequest :=
  ⟨floor anchor / (32 * unitCoefficient anchor), Fraction.Order.Field.div_pos_direct (floor_positive anchor)
    (Arithmetic.mul_pos_direct (by decide +kernel) (unitCoefficient_positive anchor))⟩

/-- The computed physical-displacement request pays one eighth of the same original full-product floor. -/
@[expose] def spatialRequest (anchor : Parameter.Anchor source.lift) : AccuracyRequest :=
  ⟨floor anchor / (8 * spatialCoefficient anchor), Fraction.Order.Field.div_pos_direct (floor_positive anchor)
    (Arithmetic.mul_pos_direct (by decide +kernel) (spatialCoefficient_positive anchor))⟩

/-- The actual spatial request retains its original computed floor and physical-displacement coefficient. -/
theorem spatialRequest_tolerance (anchor : Parameter.Anchor source.lift) :
    (spatialRequest anchor).tolerance = floor anchor / (8 * spatialCoefficient anchor) := by
  rfl

/-- A positive coefficient pays an original scalar request by exact common-factor quotient cancellation. -/
private theorem coefficient_payment (coefficient target scale : Fraction.Rational) (positive : 0 < coefficient) :
    coefficient * (target / (scale * coefficient)) = target / scale := by
  rewrite [Fraction.Field.mul_comm coefficient, Fraction.Field.quotient_mul_reorder]
  rewrite [Fraction.Field.mul_comm target coefficient, Fraction.Field.mul_comm scale coefficient]
  exact Fraction.Field.mul_div_mul_left_direct coefficient target scale positive.ne'

/-- Two residual requests at one thirty-second of the coefficient-scaled floor pay one sixteenth of that floor. -/
private theorem residual_payment (coefficient target : Fraction.Rational) (positive : 0 < coefficient) :
    coefficient * (target / (32 * coefficient) + target / (32 * coefficient)) = target / 16 := by
  calc
    _ = 2 * (coefficient * (target / (32 * coefficient))) := by ring1
    _ = 2 * (target / 32) := congrArg (fun value => 2 * value) (coefficient_payment coefficient target 32 positive)
    _ = _ := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = target * (2 * (32 : Fraction.Rational)⁻¹) := by ring1
        _ = _ := by
          rewrite [show (2 * (32 : Fraction.Rational)⁻¹) = (16 : Fraction.Rational)⁻¹ by decide +kernel]
          rfl

variable {anchor : Parameter.Anchor source.lift} {budgets : Budgets anchor} {start finish : Canonical}
variable {segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish}
variable {time lastTime : Fraction.Rational}
variable {firstUnit firstNormal lastUnit lastNormal : AccuracyRequest}

/-- The exact original product movement splits into its two residual terms and actual spatial-displacement term. -/
theorem movement_eq :
    productMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
      (firstUnit := firstUnit) (firstNormal := firstNormal) (lastUnit := lastUnit) (lastNormal := lastNormal) =
    normalCoefficient anchor * (firstNormal.tolerance + lastNormal.tolerance) +
      unitCoefficient anchor * (firstUnit.tolerance + lastUnit.tolerance) +
        spatialCoefficient anchor * Norm.Basic.normSq (segment.pointAt time - segment.pointAt lastTime) := by
  unfold productMovement normalMovement unitMovement normalCoefficient unitCoefficient spatialCoefficient
    sensitivity unitCeiling radiusSq
  simp only [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.inv_mul_direct, -eq_self, -iff_self]
  calc
    _ = ((4 : Fraction.Rational) * (4 : Fraction.Rational)⁻¹) *
        ((2 * (UnitRoot.box site).normSqBound * (anchor.seed.separation.radius ^ 2)⁻¹) *
            (firstNormal.tolerance + lastNormal.tolerance) +
          ((UnitRoot.box site).normSqBound *
            ((Fraction.Cast.fromInt 801 * (64 : Fraction.Rational)⁻¹) *
              Norm.Basic.normSq (halfGap site parameter)) *
              (anchor.seed.separation.radius ^ 2)⁻¹) *
            Norm.Basic.normSq (segment.pointAt time - segment.pointAt lastTime)) +
        160 * anchor.seed.separation.radius ^ 2 * (firstUnit.tolerance + lastUnit.tolerance) +
        80 * anchor.seed.separation.radius ^ 2 *
          Norm.Basic.normSq (segment.pointAt time - segment.pointAt lastTime) := by ring1
    _ = _ := by
      rewrite [Fraction.Field.mul_inv_cancel _ (by decide +kernel)]
      ring1

/-- Paid actual residuals and the computed physical displacement give one quarter of the original product floor. -/
theorem movement_le
    (firstUnitPaid : firstUnit.tolerance ≤ (unitResidual anchor).tolerance)
    (lastUnitPaid : lastUnit.tolerance ≤ (unitResidual anchor).tolerance)
    (firstNormalPaid : firstNormal.tolerance ≤ (normalResidual anchor).tolerance)
    (lastNormalPaid : lastNormal.tolerance ≤ (normalResidual anchor).tolerance)
    (spatialPaid : Norm.Basic.normSq (segment.pointAt time - segment.pointAt lastTime) ≤
      (spatialRequest anchor).tolerance) :
    productMovement (time := time) (lastTime := lastTime) (anchor := anchor) (segment := segment)
      (firstUnit := firstUnit) (firstNormal := firstNormal) (lastUnit := lastUnit) (lastNormal := lastNormal) ≤
        floor anchor / 4 := by
  rewrite [movement_eq]
  have normal := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct firstNormalPaid lastNormalPaid)
    (normalCoefficient_positive anchor).le
  have unit := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct firstUnitPaid lastUnitPaid) (unitCoefficient_positive anchor).le
  have spatial := Arithmetic.mul_le_mul_of_nonneg_left_direct spatialPaid
    (spatialCoefficient_positive anchor).le
  have normalBound := normal.trans_eq (residual_payment (normalCoefficient anchor) (floor anchor)
    (normalCoefficient_positive anchor))
  have unitBound := unit.trans_eq (residual_payment (unitCoefficient anchor) (floor anchor)
    (unitCoefficient_positive anchor))
  have spatialBound := spatial.trans_eq (coefficient_payment (spatialCoefficient anchor) (floor anchor) 8
    (spatialCoefficient_positive anchor))
  exact (Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct normalBound unitBound) spatialBound).trans_eq (by
      simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
      calc
        _ = floor anchor * ((16 : Fraction.Rational)⁻¹ + (16 : Fraction.Rational)⁻¹ + (8 : Fraction.Rational)⁻¹) :=
          by ring1
        _ = _ := by
          rewrite [show ((16 : Fraction.Rational)⁻¹ + (16 : Fraction.Rational)⁻¹ + (8 : Fraction.Rational)⁻¹) =
            (4 : Fraction.Rational)⁻¹ by decide +kernel]
          rfl)

/-- One positive physical-parameter width request for the original segment, valid also when its length is zero. -/
@[expose] def widthRequest (anchor : Parameter.Anchor source.lift)
    (_segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish) : AccuracyRequest :=
  ⟨(spatialRequest anchor).tolerance / (1 + Norm.Basic.normSq (finish - start)),
    Fraction.Order.Field.div_pos_direct (spatialRequest anchor).positive
      (Arithmetic.add_pos_of_pos_of_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))⟩

/-- An actual original segment parameter-width payment implies the computed physical spatial-displacement payment. -/
theorem spatial_paid_of_width
    (width : (time - lastTime) ^ 2 ≤ (widthRequest anchor segment).tolerance) :
    Norm.Basic.normSq (segment.pointAt time - segment.pointAt lastTime) ≤ (spatialRequest anchor).tolerance := by
  rewrite [segment.normSq_pointAt_sub_pointAt,
    Fraction.Field.mul_comm ((time - lastTime) ^ 2) (Norm.Basic.normSq (finish - start))]
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct width
    (Norm.Basic.normSq_nonneg (finish - start))
  have coefficient : Norm.Basic.normSq (finish - start) / (1 + Norm.Basic.normSq (finish - start)) ≤ 1 := by
    apply (Fraction.Order.Field.div_le_iff_pos
      (Arithmetic.add_pos_of_pos_of_nonneg_direct
        (by decide +kernel) (Norm.Basic.normSq_nonneg _))).mpr
    exact (show Norm.Basic.normSq (finish - start) = 0 + Norm.Basic.normSq (finish - start) by ring1).trans_le
      ((Arithmetic.add_le_add_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 1)
        (Fraction.Order.Basic.le_refl _)).trans_eq (by ring1))
  exact scaled.trans (by
    change Norm.Basic.normSq (finish - start) *
      ((spatialRequest anchor).tolerance / (1 + Norm.Basic.normSq (finish - start))) ≤ _
    have same : Norm.Basic.normSq (finish - start) *
        ((spatialRequest anchor).tolerance / (1 + Norm.Basic.normSq (finish - start))) =
        (spatialRequest anchor).tolerance *
          (Norm.Basic.normSq (finish - start) / (1 + Norm.Basic.normSq (finish - start))) := by
      simp only [Fraction.Field.div_eq_mul_inv_direct, -eq_self, -iff_self]
      ring1
    rewrite [same]
    exact (Arithmetic.mul_le_mul_of_nonneg_left_direct coefficient
      (spatialRequest anchor).positive.le).trans_eq (Fraction.Field.mul_one_direct _))

/-- The original finite quarter-radius search computes a depth paying the same physical segment width request. -/
def widthMinimum (anchor : Parameter.Anchor source.lift)
    (segment : ClearSegment (Paths.polynomial parameter) (sourceBox anchor) start finish) : Nat :=
  Approximation.Rational.Geometric.Search.firstQuarterBelow 1 0 (widthRequest anchor segment).tolerance

/-- A displayed edge fitting that exact computed depth pays the original physical displacement request. -/
theorem spatial_paid_of_depth
    (width : (time - lastTime) ^ 2 ≤
      Approximation.Rational.Geometric.Basic.quarterRadius 1 (widthMinimum anchor segment)) :
    Norm.Basic.normSq (segment.pointAt time - segment.pointAt lastTime) ≤ (spatialRequest anchor).tolerance :=
  spatial_paid_of_width (width.trans
    (Approximation.Rational.Geometric.Search.firstQuarterBelow_accurate 1 (by decide +kernel) 0
      (widthRequest anchor segment).tolerance (widthRequest anchor segment).positive).le)

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
