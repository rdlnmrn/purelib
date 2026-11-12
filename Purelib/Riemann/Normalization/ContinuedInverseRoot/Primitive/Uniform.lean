module

public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
public import Purelib.Polynomial.Clearance.Box.Region
public import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Uniform original-sheet odd-reading requests

The original polynomial clearance bounds the reciprocal parameter norm
throughout the retained continuation box. Cancellation of the actual parameter
norm and its reciprocal makes the inverse-reading scale independent of a
query point. A fixed finite model depth therefore pays every later query.
-/

public section

namespace Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood

open Purelib
open Purelib.Algebra.Quadratic.Pair.Polynomial (Coefficients)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Approximation.Rational.Geometric
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Model)

variable {polynomial : Coefficients} {count : Nat}

set_option genInjectivity false in
/-- Cached point-independent odd-reading scales on one original continued neighborhood.

The clearance comes from the same original seeded neighborhood. All scales
use its retained root floor, inverse error and initial residual bound, without
constructing a later polynomial or choosing a different root owner. -/
structure UniformBounds (patch : ContinuedNeighborhood polynomial count) where
  /-- The original seeded-box polynomial clearance. -/
  clearance : RegionClearance polynomial patch.base.box
  /-- The clearance is the canonical construction from this original seed. -/
  clearance_eq : clearance = Readings.SeededPrimitiveBounds.clearance patch.base
  /-- The cached reciprocal of the original root-norm floor. -/
  lowerInverse : Fraction.Rational
  /-- The reciprocal consumes the original retained root floor. -/
  lowerInverse_eq : lowerInverse = patch.rootLower⁻¹
  /-- The uniform reciprocal-parameter norm ceiling. -/
  inverseNormUpper : Fraction.Rational
  /-- The ceiling consumes the retained positive polynomial clearance. -/
  inverseNormUpper_eq : inverseNormUpper = clearance.bound⁻¹
  /-- The shared inverse-model value ceiling. -/
  valueCeiling : Fraction.Rational
  /-- The value ceiling uses the original inverse error and retained reciprocal floor. -/
  valueCeiling_eq : valueCeiling = 2 * (patch.inverseErrorScale + lowerInverse)
  /-- The common inverse-reading geometric scale. -/
  inverseScale : Fraction.Rational
  /-- The original parameter and reciprocal norms cancel in this scale. -/
  inverseScale_eq : inverseScale = 2 * (patch.inverseErrorScale + lowerInverse * (1 / 4096))
  /-- The common cubic-reading geometric scale. -/
  cubeScale : Fraction.Rational
  /-- The cubic scale pays the original residual and inverse norm ceiling. -/
  cubeScale_eq : cubeScale = 2 * (inverseScale + valueCeiling * patch.base.model.bound) * inverseNormUpper
  /-- The common fifth-power-reading geometric scale. -/
  fifthScale : Fraction.Rational
  /-- The fifth scale pays both original residual contributions and the squared inverse norm ceiling. -/
  fifthScale_eq : fifthScale =
    2 * (inverseScale + valueCeiling * ((8 + 2 * patch.base.model.bound) * patch.base.model.bound)) *
      inverseNormUpper ^ 2

constructive_injectivity UniformBounds

namespace UniformBounds

variable {patch : ContinuedNeighborhood polynomial count}

/-- Cache uniform source scales while reusing the original retained seeded-box clearance. -/
@[expose] def ofClearance (patch : ContinuedNeighborhood polynomial count)
    (clearance : RegionClearance polynomial patch.base.box)
    (original : clearance = Readings.SeededPrimitiveBounds.clearance patch.base) : UniformBounds patch :=
  let lowerInverse := patch.rootLower⁻¹
  let inverseNormUpper := clearance.bound⁻¹
  let valueCeiling := 2 * (patch.inverseErrorScale + lowerInverse)
  let inverseScale := 2 * (patch.inverseErrorScale + lowerInverse * (1 / 4096))
  let cubeScale := 2 * (inverseScale + valueCeiling * patch.base.model.bound) * inverseNormUpper
  let fifthScale :=
    2 * (inverseScale + valueCeiling * ((8 + 2 * patch.base.model.bound) * patch.base.model.bound)) *
      inverseNormUpper ^ 2
  ⟨clearance, original, lowerInverse, rfl, inverseNormUpper, rfl, valueCeiling, rfl,
    inverseScale, rfl, cubeScale, rfl, fifthScale, rfl⟩

/-- Compute the uniform source scales once, before any model refinement or point query. -/
@[expose] def build (patch : ContinuedNeighborhood polynomial count) : UniformBounds patch :=
  ofClearance patch (Readings.SeededPrimitiveBounds.clearance patch.base) rfl

/-- The original reciprocal root floor is nonnegative. -/
theorem lowerInverse_nonnegative (bounds : UniformBounds patch) : 0 ≤ bounds.lowerInverse := by
  rewrite [bounds.lowerInverse_eq]
  exact (Fraction.Order.Field.inv_pos_direct patch.rootLower_positive).le

/-- The retained uniform reciprocal-parameter ceiling is nonnegative. -/
theorem inverseNormUpper_nonnegative (bounds : UniformBounds patch) : 0 ≤ bounds.inverseNormUpper := by
  rewrite [bounds.inverseNormUpper_eq]
  exact (Fraction.Order.Field.inv_pos_direct bounds.clearance.positive).le

/-- The retained inverse-model value ceiling is nonnegative. -/
theorem valueCeiling_nonnegative (bounds : UniformBounds patch) : 0 ≤ bounds.valueCeiling := by
  rewrite [bounds.valueCeiling_eq]
  exact Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg patch.inverseErrorScale_positive.le bounds.lowerInverse_nonnegative)

/-- The retained uniform inverse-reading scale is nonnegative. -/
theorem inverseScale_nonnegative (bounds : UniformBounds patch) : 0 ≤ bounds.inverseScale := by
  rewrite [bounds.inverseScale_eq]
  exact Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg patch.inverseErrorScale_positive.le
      (Order.Arithmetic.mul_nonneg_direct bounds.lowerInverse_nonnegative (by decide +kernel)))

/-- The retained uniform cubic-reading scale is nonnegative. -/
theorem cubeScale_nonnegative (bounds : UniformBounds patch) : 0 ≤ bounds.cubeScale := by
  rewrite [bounds.cubeScale_eq]
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg bounds.inverseScale_nonnegative
        (Order.Arithmetic.mul_nonneg_direct
          bounds.valueCeiling_nonnegative patch.base.model.bound_nonnegative)))
    bounds.inverseNormUpper_nonnegative

/-- The retained uniform fifth-power-reading scale is nonnegative. -/
theorem fifthScale_nonnegative (bounds : UniformBounds patch) : 0 ≤ bounds.fifthScale := by
  rewrite [bounds.fifthScale_eq]
  exact Order.Arithmetic.mul_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg bounds.inverseScale_nonnegative
        (Order.Arithmetic.mul_nonneg_direct bounds.valueCeiling_nonnegative
          (Order.Arithmetic.mul_nonneg_direct
            (add_nonneg (by decide) (Order.Arithmetic.mul_nonneg_direct (by decide)
              patch.base.model.bound_nonnegative)) patch.base.model.bound_nonnegative))))
    (Order.Arithmetic.pow_nonneg_direct bounds.inverseNormUpper_nonnegative 2)

/-- Select one cached scale for the original inverse, cube or fifth-power channel. -/
@[expose] def scale (bounds : UniformBounds patch) (pairs : Fin 3) : Fraction.Rational :=
  if pairs.val = 0 then bounds.inverseScale else if pairs.val = 1 then bounds.cubeScale else bounds.fifthScale

/-- Every original odd channel has a nonnegative uniform scale. -/
theorem scale_nonnegative (bounds : UniformBounds patch) (pairs : Fin 3) : 0 ≤ bounds.scale pairs := by
  unfold scale
  split
  · exact bounds.inverseScale_nonnegative
  · split
    · exact bounds.cubeScale_nonnegative
    · exact bounds.fifthScale_nonnegative

/-- The actual parameter norm cancels its retained reciprocal norm at every original admitted point. -/
theorem parameter_inverse_cancel {point : Canonical} {sample : Point patch point}
    (localBounds : Point.PrimitiveBounds sample) : sample.parameterNorm * localBounds.inverseNorm = 1 := by
  rewrite [sample.parameterNorm_eq, localBounds.inverseNorm_eq, localBounds.parameterInverse_eq,
    Field.inv_eq, Field.normSq_inv _ sample.owner.parameterNonzero]
  rewrite [Norm.Basic.normSq_eq_canonical]
  have positive := sample.parameterNorm_positive
  rewrite [sample.parameterNorm_eq] at positive
  exact Fraction.Field.mul_inv_cancel _ positive.ne'

/-- The same original point's reciprocal norm lies below the cached uniform clearance ceiling. -/
theorem inverseNorm_le (bounds : UniformBounds patch) {point : Canonical} {sample : Point patch point}
    (localBounds : Point.PrimitiveBounds sample) (inside : patch.box.Contains point) :
    localBounds.inverseNorm ≤ bounds.inverseNormUpper := by
  rewrite [localBounds.inverseNorm_eq, localBounds.parameterInverse_eq, Field.inv_eq,
    Field.normSq_inv _ sample.owner.parameterNonzero, bounds.inverseNormUpper_eq]
  exact Fraction.Order.Field.inv_le_inv_of_pos_direct bounds.clearance.positive
    (bounds.clearance.lower point (patch.box_refines.contains inside))

/-- The point's inverse-reading scale is exactly the common cached uniform scale. -/
theorem inverseScale_eq_point (bounds : UniformBounds patch) {point : Canonical} {sample : Point patch point}
    (localBounds : Point.PrimitiveBounds sample) : localBounds.inverseScale = bounds.inverseScale := by
  rewrite [localBounds.inverseScale_eq, bounds.inverseScale_eq, localBounds.lowerInverse_eq,
    ← bounds.lowerInverse_eq]
  have cancel := parameter_inverse_cancel localBounds
  calc
    _ = 2 * (patch.inverseErrorScale + bounds.lowerInverse * (1 / 4096) *
      (sample.parameterNorm * localBounds.inverseNorm)) := by ring1
    _ = _ := by rewrite [cancel, Fraction.Field.mul_one_direct]; rfl

/-- The actual cubic-reading scale is bounded by the common original-source scale. -/
theorem cubeScale_le (bounds : UniformBounds patch) {point : Canonical} {sample : Point patch point}
    (localBounds : Point.PrimitiveBounds sample) (inside : patch.box.Contains point) :
    localBounds.cubeScale ≤ bounds.cubeScale := by
  have ceiling : localBounds.valueCeiling = bounds.valueCeiling := by
    rewrite [localBounds.valueCeiling_eq, bounds.valueCeiling_eq,
      localBounds.lowerInverse_eq, bounds.lowerInverse_eq]
    rfl
  rewrite [localBounds.cubeScale_eq, bounds.cubeScale_eq, bounds.inverseScale_eq_point localBounds, ceiling]
  exact Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (bounds.inverseNorm_le localBounds inside)
    (Order.Arithmetic.mul_nonneg_direct (by decide)
      (add_nonneg bounds.inverseScale_nonnegative
        (Order.Arithmetic.mul_nonneg_direct
          bounds.valueCeiling_nonnegative patch.base.model.bound_nonnegative)))

/-- The actual fifth-power-reading scale is bounded by the common original-source scale. -/
theorem fifthScale_le (bounds : UniformBounds patch) {point : Canonical} {sample : Point patch point}
    (localBounds : Point.PrimitiveBounds sample) (inside : patch.box.Contains point) :
    localBounds.fifthScale ≤ bounds.fifthScale := by
  have ceiling : localBounds.valueCeiling = bounds.valueCeiling := by
    rewrite [localBounds.valueCeiling_eq, bounds.valueCeiling_eq,
      localBounds.lowerInverse_eq, bounds.lowerInverse_eq]
    rfl
  rewrite [localBounds.fifthScale_eq, bounds.fifthScale_eq, bounds.inverseScale_eq_point localBounds, ceiling]
  apply Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.pow_le_pow_direct localBounds.inverseNorm_nonnegative
      (bounds.inverseNorm_le localBounds inside) 2)
  exact Order.Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg bounds.inverseScale_nonnegative
      (Order.Arithmetic.mul_nonneg_direct bounds.valueCeiling_nonnegative
        (Order.Arithmetic.mul_nonneg_direct
          (add_nonneg (by decide) (Order.Arithmetic.mul_nonneg_direct (by decide)
            patch.base.model.bound_nonnegative)) patch.base.model.bound_nonnegative)))

/-- Each actual point's selected odd-reading scale is paid by the matching original-source uniform scale. -/
theorem scale_le (bounds : UniformBounds patch) {point : Canonical} {sample : Point patch point}
    (localBounds : Point.PrimitiveBounds sample) (inside : patch.box.Contains point) (pairs : Fin 3) :
    localBounds.scale pairs ≤ bounds.scale pairs := by
  unfold Point.PrimitiveBounds.scale scale
  split
  · exact (bounds.inverseScale_eq_point localBounds).le
  · split
    · exact bounds.cubeScale_le localBounds inside
    · exact bounds.fifthScale_le localBounds inside

end UniformBounds

set_option genInjectivity false in
/-- A fixed finite request paying an original numerator's odd-reading residual at every point of the continued box.

The numerator's Horner ceiling is cached once. Its product with the uniform
odd scale chooses a stage before the later model or query points are built. -/
structure UniformRequest {patch : ContinuedNeighborhood polynomial count} (bounds : UniformBounds patch)
    (pairs : Fin 3) (numerator : Coefficients) (floor : Nat) (target : Fraction.Rational) where
  /-- The original numerator's retained box-wide squared-norm ceiling. -/
  numeratorUpper : Fraction.Rational
  /-- The ceiling comes from the exact original numerator and continued box. -/
  numeratorUpper_eq : numeratorUpper = Bounds.Box.denseEvalNormBound numerator patch.box
  /-- The retained common residual scale for this original numerator and odd power. -/
  scale : Fraction.Rational
  /-- The common scale consumes the same retained numerator and original-source odd bounds. -/
  scale_eq : scale = numeratorUpper * bounds.scale pairs
  /-- The certified finite selection for the actual common scale, floor and target. -/
  selection : Search.Selection scale floor target

constructive_injectivity UniformRequest

namespace UniformBounds

/-- Choose one finite model depth paying this exact original numerator at all later admitted query points. -/
@[expose] def request {patch : ContinuedNeighborhood polynomial count} (bounds : UniformBounds patch)
    (pairs : Fin 3) (numerator : Coefficients) (floor : Nat) (target : Fraction.Rational) (positive : 0 < target) :
    UniformRequest bounds pairs numerator floor target :=
  let numeratorUpper := Bounds.Box.denseEvalNormBound numerator patch.box
  let scale := numeratorUpper * bounds.scale pairs
  let selection := Search.Selection.build scale
    (Order.Arithmetic.mul_nonneg_direct
      (Bounds.Box.denseHornerNormBounds_nonneg numerator patch.box).1 (bounds.scale_nonnegative pairs))
    floor target positive
  ⟨numeratorUpper, rfl, scale, rfl, selection⟩

end UniformBounds

namespace UniformRequest

/-- Transport the numerator index of an original uniform request along an exact retained coefficient identity.

Equality elimination preserves the original scale, finite selection and
numerator ceiling. It performs no new box-bound evaluation or depth search. -/
@[expose] def castNumerator {patch : ContinuedNeighborhood polynomial count} {bounds : UniformBounds patch}
    {pairs : Fin 3} {numerator : Coefficients} {floor : Nat} {target : Fraction.Rational}
    (request : UniformRequest bounds pairs numerator floor target) (replacement : Coefficients)
    (equal : numerator = replacement) : UniformRequest bounds pairs replacement floor target := by
  cases equal
  exact request

/-- Numerator-index transport preserves the actual retained selected model stage. -/
theorem castNumerator_stage {patch : ContinuedNeighborhood polynomial count} {bounds : UniformBounds patch}
    {pairs : Fin 3} {numerator : Coefficients} {floor : Nat} {target : Fraction.Rational}
    (request : UniformRequest bounds pairs numerator floor target) (replacement : Coefficients)
    (equal : numerator = replacement) :
    (request.castNumerator replacement equal).selection.stage = request.selection.stage := by
  cases equal
  rfl

/-- The fixed source request bounds the actual primitive residual at every later common stage. -/
theorem residual_lt {patch : ContinuedNeighborhood polynomial count} {bounds : UniformBounds patch}
    {pairs : Fin 3} {numerator : Coefficients} {floor : Nat} {target : Fraction.Rational}
    (request : UniformRequest bounds pairs numerator floor target) {point : Canonical}
    {sample : Point patch point} (localBounds : Point.PrimitiveBounds sample)
    {depth : Nat} {model : Model polynomial patch.base.box} {powers : OddPowers model.value}
    {reading : Point.PrimitiveReading sample depth model powers}
    {original : Point.PrimitiveDenotation sample pairs numerator} {source : Coefficients}
    (value : Point.PrimitiveValue reading pairs numerator original source)
    (inside : patch.box.Contains point) (stage : request.selection.stage ≤ depth) :
    Norm.Basic.normSq value.residual < target := by
  have numeratorBound := Bounds.Box.normSq_eval_le_denseEvalNormBound numerator inside
  rewrite [← request.numeratorUpper_eq] at numeratorBound
  have scaleBound : Norm.Basic.normSq (numerator.eval point) * localBounds.scale pairs ≤ request.scale := by
    rewrite [request.scale_eq]
    exact Order.Arithmetic.mul_le_mul_direct numeratorBound (bounds.scale_le localBounds inside pairs)
      (localBounds.scale_nonnegative pairs)
      (request.numeratorUpper_eq.symm ▸ (Bounds.Box.denseHornerNormBounds_nonneg numerator patch.box).1)
  exact (value.residual_le localBounds inside).trans_lt
    ((Basic.quarterRadius_scale_mono scaleBound depth).trans_lt (request.selection.later_accurate stage))

end UniformRequest

end Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood

end
