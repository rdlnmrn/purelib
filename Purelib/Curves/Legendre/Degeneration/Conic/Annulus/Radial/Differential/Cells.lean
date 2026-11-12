module

import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Bounds.Variation
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
public import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Tangent
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Data.Gaussian.Norm.Reciprocal
import Purelib.Algebra.Field.Inverse
import Purelib.Data.Gaussian.Power
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive
public import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
public import Purelib.Riemann.Normalization.InverseRootPrimitive
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport
public import Purelib.Riemann.RootContinuation.CertifiedSquareRoot.Sampling.Admission
public import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Interval.Radius
import Purelib.Data.Rat.Fraction.Order
import Purelib.Approximation.Gaussian.Process.Sampling
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Approximation.Gaussian.Equivalence.Observation
import Purelib.Polynomial.Ascending.Gaussian.Evaluation
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Paid original odd-power cells on the retained regular parallel chart

Every numerical cell retains an actual requested-time reading of the original
prepared curved quarter. Its cofactor observation is sampled once from that
reading's identical cached certificate. The coefficient is a scalar chart
reading, distinct from an independently observed arithmetic evaluator.
The uniform allowance pays the actual chart width and two square residuals.
These chart cells require a separate comparison to canonical affine cells.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds (Data)

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Geometry.Rational
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation
open Purelib.Approximation.Gaussian
open Purelib.Riemann.RootContinuation
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel LocalObservation)
open Purelib.Polynomial.Ascending
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate (DensePrimitive)
open Purelib.Polynomial.Bounds (Horner)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveReading)
open Purelib.Riemann.Normalization

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}
variable {targetRadicand : Pair.Polynomial.Coefficients}

open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)

variable {radicand : CoefficientPolynomial}

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive}
variable {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
variable {differential : OddPowerDifferential radicand}

/-- The original scalar chart-cell allowance pays its retained width and two actual residual requests. -/
@[expose] def allowance (data : Data site parameter differential)
    (span : Interval.Bounds) (accuracy : AccuracyRequest) : Fraction.Rational :=
  Bounds.signedChartSlope data * (span.upper - span.lower) ^ 2 + 2 * Bounds.residualSlope data * accuracy.tolerance

/-- The computed original allowance is nonnegative by intrinsic regularity and the retained positive request. -/
theorem allowance_nonnegative (data : Data site parameter differential)
    (span : Interval.Bounds) (regular : parameter ≠ criticalValue site) (accuracy : AccuracyRequest) :
    0 ≤ allowance data span accuracy := by
  have slopes := Bounds.signed_slopes_nonnegative data regular
  exact Fraction.Order.add_nonnegative
    (Arithmetic.mul_nonneg_direct slopes.1 (Arithmetic.sq_nonneg_direct _))
    (Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide +kernel) slopes.2) accuracy.positive.le)

set_option genInjectivity false in
/-- One paid scalar chart cell on an identical actual requested-time source of the original prepared parallel quarter.

The differential budget, complete source query and accuracy request remain
indices. The cofactor observation belongs to that source's exact certificate.
Its original signed window and residual payment derive the uniform allowance
for every compatible actual candidate along the same chart span.
-/
structure Model (data : Data site parameter differential)
    (source : Transport.Reading actual span.lower inside) (accuracy : AccuracyRequest) where
  /-- The original fibre is regular at its labelled collision. -/
  regular : parameter ≠ criticalValue site
  /-- The actual paid original cofactor observation, retaining its selected state and index. -/
  sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy
  /-- The observation retains the same original global signed cofactor window. -/
  signed : (UnitRoot.box site).Contains sample.reading
  /-- The actual reading pays the original cofactor's residual admission. -/
  residual : Bounds.RootResidual site parameter quarter span.lower sample.reading
  /-- The original scalar differential coefficient computed once on that same actual reading. -/
  center : Canonical
  /-- The coefficient keeps the original differential, point, ordinate and oriented chart velocity. -/
  center_eq : center = reading site parameter quarter span.lower differential sample.reading
  /-- The computed local squared-error allowance. -/
  allowance : Fraction.Rational
  /-- Its chart-width and two-residual contributions use the same retained budget and request. -/
  allowance_eq : allowance = Bounds.signedChartSlope data * (span.upper - span.lower) ^ 2 +
    2 * Bounds.residualSlope data * accuracy.tolerance
  /-- The original local allowance is nonnegative. -/
  allowance_nonnegative : 0 ≤ allowance

constructive_injectivity Model

namespace Model

/-- Attach one supplied original paid observation without resampling its process or rebuilding its geometric source. -/
@[expose] def ofSample (data : Data site parameter differential)
    (source : Transport.Reading actual span.lower inside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest)
    (sample : CertifiedSquareRoot.Sampling.ResidualObservation source.lift.unitRoot accuracy) :
    Model data source accuracy := by
  let center := reading site parameter quarter span.lower differential sample.reading
  let allowance := Cells.allowance data span accuracy
  exact
    { regular := regular
      sample := sample
      signed := source.signed.contains
        (sample.reading_in_initial_box source.lift.unitOwner source.lift.unitRoot_eq)
      residual := (sample.reading_residual_lt_target source.lift.unitOwner source.lift.unitRoot_eq).le
      center := center
      center_eq := rfl
      allowance := allowance
      allowance_eq := rfl
      allowance_nonnegative := Cells.allowance_nonnegative data span regular accuracy }

/-- Sample the same cached geometric cofactor certificate once and attach its computed original chart cell. -/
@[expose] def build (data : Data site parameter differential)
    (source : Transport.Reading actual span.lower inside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest) : Model data source accuracy :=
  let sample := CertifiedSquareRoot.Sampling.request source.lift.unitRoot accuracy
  ofSample data source regular accuracy sample

variable {data : Data site parameter differential}
variable {source : Transport.Reading actual span.lower inside} {accuracy : AccuracyRequest}

/-- Read this scalar cell's actual retained cofactor sample as a reading of its same original full-cubic channel.

The original conic ordinate and retained cofactor state produce the exact
same product possibility. Only the finite Reading container caches the
already computed root product and its actual original state radius.
-/
def rootReading (model : Model data source accuracy) :
    Equivalence.Observation.Reading source.lift.value :=
  Equivalence.Observation.Reading.retain source.lift.value (source.productState model.sample)
    (source.productReading model.sample) (source.productReading_possible model.sample)

/-- The full-root reading retains the scalar cell's same observation, ordinate and original state. -/
theorem rootReading_value (model : Model data source accuracy) :
    model.rootReading.value = model.sample.reading *
      (point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate := (rfl)

/-- The same actual full-root state radius decays with this scalar cell's retained residual-accuracy request.

The square-sensitivity request is paid by the SAME original observation.
The exact ordinate scales its radius, while no root or coefficient channel
is replaced or independently sampled.
-/
theorem rootReading_radius_le (model : Model data source accuracy) :
    model.rootReading.radius ≤ 4 * accuracy.tolerance *
      Norm.Basic.normSq (point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate := by
  have retained := source.productState_radius model.sample
  change model.rootReading.radius = _ at retained
  exact retained.trans_le (Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct model.sample.radius_lt_accuracy.le (by decide +kernel))
    (Norm.Basic.normSq_nonneg _))

/-- Every actual scalar-cell root radius obeys the same original quarter-wide half-gap sensitivity.

The retained residual request controls the actual cofactor state. The
original ellipse bound pays its exact conic factor uniformly over time,
without a new observation or a supplied successful radius payment.
-/
theorem rootReading_radius_uniform (model : Model data source accuracy) :
    model.rootReading.radius ≤ ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * accuracy.tolerance := by
  have ordinate := point_ordinate_normSq_le site parameter 2 (Waist.direction quarter span.lower)
    positive (by decide +kernel) (by decide +kernel)
  have factorNonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 4) accuracy.positive.le
  have scalar : (4 : Fraction.Rational) * (25 / 16) = 25 / 4 := by decide +kernel
  calc
    _ ≤ 4 * accuracy.tolerance * Norm.Basic.normSq
        (point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate :=
      model.rootReading_radius_le
    _ ≤ 4 * accuracy.tolerance * ((25 / 16) * Norm.Basic.normSq (halfGap site parameter)) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct ordinate factorNonnegative
    _ = (4 * (25 / 16)) * Norm.Basic.normSq (halfGap site parameter) * accuracy.tolerance := by ring1
    _ = _ := congrArg (fun coefficient => coefficient * Norm.Basic.normSq (halfGap site parameter) *
      accuracy.tolerance) scalar

/-- The actual scalar cell's original full-root reading pays its source's intrinsic positive trace floor. -/
theorem rootReading_lower (model : Model data source accuracy) :
    source.traceFloor ≤ normSq model.rootReading.value := by
  rewrite [model.rootReading_value]
  exact parallel_product_lower site parameter quarter span.lower model.signed

/-- Every original odd-power chart coefficient reads its retained full-root reciprocal and oriented tangent.

The same actual scalar center and cofactor observation remain inputs.
Intrinsic regularity makes the original ordinate nonzero. The existing
exact-factor cancellation removes one ordinate factor, retaining the full
original odd denominator exponent without identifying root samples.
-/
theorem center_fullRoot (model : Model data source accuracy) :
    model.center = (differential.scale * differential.numerator.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
        model.rootReading.value⁻¹ ^ differential.denominatorExponent *
          Tangent.baseVelocity site parameter 2 quarter span.lower := by
  have ordinateNonzero := parallel_ordinate_ne_zero site parameter (Waist.direction quarter span.lower) model.regular
  have cancelled := OddPowerDifferential.scalar_factor_cancellation
    (differential.scale * differential.numerator.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base)
    (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate
    (Stereographic.Tangent.logarithmicVelocity span.lower) differential.denominatorPairs ordinateNonzero
  rewrite [model.center_eq, reading, model.rootReading_value,
    Algebra.Field.Inverse.inverse_product model.sample.reading_nonzero ordinateNonzero,
    Tangent.baseVelocity_eq_ordinate_mul site parameter 2 quarter positive span.lower, Power.mul_pow]
  calc
    _ = ((differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
        Stereographic.Tangent.logarithmicVelocity span.lower *
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate⁻¹ ^
          (2 * differential.denominatorPairs)) * model.sample.reading⁻¹ ^ differential.denominatorExponent := rfl
    _ = (((differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate⁻¹ ^
          (2 * differential.denominatorPairs + 1)) *
        ((Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).ordinate *
          Stereographic.Tangent.logarithmicVelocity span.lower)) *
            model.sample.reading⁻¹ ^ differential.denominatorExponent :=
      congrArg (fun value : Canonical => value * model.sample.reading⁻¹ ^ differential.denominatorExponent)
        cancelled.symm
    _ = _ := by unfold OddPowerDifferential.denominatorExponent; ring1

/-- Change the differential while consuming the identical sampled cofactor observation and original source query. -/
@[expose] def reweight (model : Model data source accuracy) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Data site parameter nextDifferential) : Model nextData source accuracy :=
  ofSample nextData source model.regular accuracy model.sample

/-- Reweighting a retained scalar Model by its identical original differential budget preserves the whole Model.

The same actual observation is forwarded. The existing center and allowance
certificates determine the two computed scalar fields; all remaining proof
fields retain their original propositions. No new sample is acquired.
-/
theorem reweight_self (model : Model data source accuracy) : model.reweight data = model := by
  cases model with
  | mk regular sample signed residual center center_eq allowance allowance_eq nonnegative =>
      cases center_eq
      cases allowance_eq
      rfl

/-- Reweighting uses the complete original paid observation cache and performs no second root sample. -/
theorem reweight_sample (model : Model data source accuracy) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Data site parameter nextDifferential) :
    (model.reweight nextData).sample = model.sample := rfl

/-- Reweighting retains the complete original full-root observation and its actual state/radius caches. -/
theorem rootReading_reweight (model : Model data source accuracy)
    {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Data site parameter nextDifferential) :
    (model.reweight nextData).rootReading = model.rootReading := (rfl)

/-- Reweighting one acquired scalar model gives the complete original factory result for the other differential. -/
theorem reweight_build (data : Data site parameter differential)
    (source : Transport.Reading actual span.lower inside) (regular : parameter ≠ criticalValue site)
    (accuracy : AccuracyRequest) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Data site parameter nextDifferential) :
    (build data source regular accuracy).reweight nextData = build nextData source regular accuracy := (rfl)

/-- Any signed and paid cofactor reading on this original curved span meets the retained scalar cell allowance. -/
theorem candidate_error_le (model : Model data source accuracy) {time : Fraction.Rational}
    (within : span.Contains time) {root : Canonical} (signed : (UnitRoot.box site).Contains root)
    (residual : Bounds.RootResidual site parameter quarter time root)
    (paid : normSq (root * root - cofactor site parameter 2 quarter (by decide +kernel) time) ≤ accuracy.tolerance) :
    normSq (reading site parameter quarter time differential root - model.center) ≤ model.allowance := by
  have parameterBound := Interval.Radius.sub_sq_le_sampleRadiusSq span (sample := span.lower) within
  rewrite [Interval.Radius.sampleRadiusSq_lower_eq_widthSq] at parameterBound
  have comparison := Bounds.signed_reading_distance_le data quarter model.regular actual.data.bound time span.lower
    signed model.signed residual model.residual paid model.sample.reading_residual_lt.le
  rewrite [model.center_eq, model.allowance_eq]
  have slopes := Bounds.signed_slopes_nonnegative data model.regular
  exact comparison.trans
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct parameterBound slopes.1)
      ((show Bounds.residualSlope data * (accuracy.tolerance + accuracy.tolerance) =
        2 * Bounds.residualSlope data * accuracy.tolerance by ring1).le))

/-- The initial constant observation retains the original cached scalar coefficient with zero polynomial error. -/
@[expose] def centerObservation (model : Model data source accuracy) :
    LocalObservation (Gaussian.Basic.constant model.center) model.allowance :=
  { parameter := 0
    integrandReading := model.center
    error := 0
    decomposition := by
      rewrite [Gaussian.Evaluation.eval_constant]
      exact Basic.sub_self _
    error_le := by
      rewrite [← Norm.Basic.normSq_eq_canonical, Norm.Basic.normSq_zero]
      exact model.allowance_nonnegative }

/-- The original numerical container uses chart-time endpoints and the same cached scalar coefficient and allowance. -/
@[expose] def cell (model : Model data source accuracy) : CellModel where
  start := ⟨span.lower, 0⟩
  finish := ⟨span.upper, 0⟩
  polynomial := Gaussian.Basic.constant model.center
  localAllowance := model.allowance
  localAllowance_nonneg := model.allowance_nonnegative
  observations := [model.centerObservation]

/-- The retained cell integral sample is the exact original chart width times its identical coefficient cache. -/
theorem integralSample (model : Model data source accuracy) :
    model.cell.integralSample = (⟨span.upper - span.lower, 0⟩ : Canonical) * model.center := by
  have displacement : model.cell.finish - model.cell.start = (⟨span.upper - span.lower, 0⟩ : Canonical) := by
    apply Basic.ext
    · rfl
    · change (0 : Fraction.Rational) - 0 = 0
      ring1
  exact (CellModel.integralSample_constant model.cell model.center rfl).trans
    (congrArg (fun value => value * model.center) displacement)

/-- The actual coefficient residual compares a spatial polynomial with this cell's identical cached chart reading.

It uses the original base point and oriented radial velocity at the retained
source time. The scalar center remains the one computed from this Model's
actual cofactor observation; no new root query or numerical channel is built.
-/
@[expose] def primitiveResidual (model : Model data source accuracy) (polynomial : CoefficientPolynomial) :
    Fraction.Rational :=
  normSq (polynomial.eval (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base *
    Tangent.baseVelocity site parameter 2 quarter span.lower - model.center)

/-- A paid same-sheet root comparison bounds the actual scalar coefficient residual at every original odd power.

The same retained inverse-model error and root comparison determine an
uniform original inverse-magnitude ceiling. Finite power sensitivity then
bounds the actual odd-power coefficient, preserving the literal former
zero-pair bound without any additional caller magnitude premise.
-/
theorem primitiveResidual_le (model : Model data source accuracy)
    {polynomial : Pair.Polynomial.Coefficients} {count : Nat}
    {patch : ContinuedNeighborhood polynomial count}
    {point : ContinuedNeighborhood.Point patch
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base}
    {depth : Nat} {inverse : InverseRootPolynomial.Model polynomial patch.base.box}
    {powers : Dense.Power.OddPowers inverse.value}
    (shared : PrimitiveReading
      point depth inverse powers)
    (inside : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base)
    {target : Fraction.Rational}
    (comparison : Equivalence.Observation.Comparison model.rootReading shared.rootReading target)
    (floor : Fraction.Rational) (floorPositive : 0 < floor)
    (firstLower : floor ≤ normSq model.rootReading.value) (lastLower : floor ≤ normSq shared.root)
    (coefficient : CoefficientPolynomial)
    (coefficient_eq : coefficient.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base =
        (differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
            (match differential.denominatorPairs with
            | 0 => shared.inverse
            | remaining + 1 => shared.inverse ^ (2 * (remaining + 1) + 1))) :
    let error := 2 * (Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale depth +
      (floor⁻¹ * floor⁻¹) * comparison.bound)
    let upper := 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) + floor⁻¹
    model.primitiveResidual coefficient ≤
      normSq ((differential.scale * differential.numerator.eval
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
          Tangent.baseVelocity site parameter 2 quarter span.lower) *
        (match differential.denominatorPairs with
        | 0 => error
        | remaining + 1 => Norm.Power.differenceFactor upper (2 * (remaining + 1) + 1) * error) := by
  let error := 2 * (Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale depth +
    (floor⁻¹ * floor⁻¹) * comparison.bound)
  let upper := 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) + floor⁻¹
  change model.primitiveResidual coefficient ≤ _ *
    (match differential.denominatorPairs with
    | 0 => error
    | remaining + 1 => Norm.Power.differenceFactor upper (2 * (remaining + 1) + 1) * error)
  have rootDistance := comparison.residual_le
  rewrite [comparison.residual_eq, shared.rootReading_value] at rootDistance
  have reciprocal := (Norm.Reciprocal.difference_normSq_le floorPositive firstLower lastLower).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct rootDistance
      (Arithmetic.mul_nonneg_direct
        (Fraction.Order.Field.inv_pos_direct floorPositive).le (Fraction.Order.Field.inv_pos_direct floorPositive).le))
  rewrite [Norm.Bounds.normSq_sub_symm] at reciprocal
  have inverseDistance : normSq (shared.inverse - model.rootReading.value⁻¹) ≤ error :=
    (Norm.Bounds.normSq_sub_le_via shared.inverse shared.root⁻¹ model.rootReading.value⁻¹).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct (shared.inverse_error_le inside) reciprocal)
        (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
  have floorInversePositive := (Fraction.Order.Field.inv_pos_direct floorPositive).le
  have rootInverseBound := Norm.Reciprocal.normSq_le floorPositive firstLower
  have modelInverseBound := shared.inverse_norm_le inside
  have firstUpper : normSq shared.inverse ≤ upper := by
    calc
      _ ≤ 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) := modelInverseBound
      _ = 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) + 0 := by ring1
      _ ≤ upper := Arithmetic.add_le_add_direct
        (Fraction.Order.Basic.le_refl _) floorInversePositive
  have lastUpper : normSq model.rootReading.value⁻¹ ≤ upper := by
    calc
      _ ≤ floor⁻¹ := rootInverseBound
      _ = 0 + floor⁻¹ := by ring1
      _ ≤ upper := Arithmetic.add_le_add_direct
        ((Norm.Basic.normSq_nonneg shared.inverse).trans modelInverseBound) (Fraction.Order.Basic.le_refl _)
  have powered : normSq
      ((match differential.denominatorPairs with
        | 0 => shared.inverse
        | remaining + 1 => shared.inverse ^ (2 * (remaining + 1) + 1)) -
          model.rootReading.value⁻¹ ^ differential.denominatorExponent) ≤
      (match differential.denominatorPairs with
      | 0 => error
      | remaining + 1 => Norm.Power.differenceFactor upper (2 * (remaining + 1) + 1) * error) := by
    cases number : differential.denominatorPairs with
    | zero =>
        rewrite [OddPowerDifferential.denominatorExponent, number]
        simp only [Nat.mul_zero, Nat.zero_add, pow_one]
        exact inverseDistance
    | succ remaining =>
        rewrite [OddPowerDifferential.denominatorExponent, number]
        exact (Norm.Power.difference_normSq_le firstUpper lastUpper (2 * (remaining + 1) + 1)).trans
          (Arithmetic.mul_le_mul_of_nonneg_left_direct inverseDistance
            (Norm.Power.differenceFactor_nonnegative
              ((Norm.Basic.normSq_nonneg shared.inverse).trans firstUpper) _))
  unfold primitiveResidual
  rewrite [coefficient_eq, model.center_fullRoot]
  rewrite [show (differential.scale * differential.numerator.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
        (match differential.denominatorPairs with
        | 0 => shared.inverse
        | remaining + 1 => shared.inverse ^ (2 * (remaining + 1) + 1)) *
          Tangent.baseVelocity site parameter 2 quarter span.lower -
      (differential.scale * differential.numerator.eval
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
        model.rootReading.value⁻¹ ^ differential.denominatorExponent *
          Tangent.baseVelocity site parameter 2 quarter span.lower =
      ((differential.scale * differential.numerator.eval
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
          Tangent.baseVelocity site parameter 2 quarter span.lower) *
        ((match differential.denominatorPairs with
        | 0 => shared.inverse
        | remaining + 1 => shared.inverse ^ (2 * (remaining + 1) + 1)) -
          model.rootReading.value⁻¹ ^ differential.denominatorExponent) by ring1, Norm.Basic.normSq_mul]
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct powered (Norm.Basic.normSq_nonneg _)

section PrimitiveRequest

open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Polynomial.Dense.Power (OddPowers)

variable {polynomial : Pair.Polynomial.Coefficients} {count : Nat}
variable {patch : ContinuedNeighborhood polynomial count}
variable {sample : ContinuedNeighborhood.Point patch
  (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base}
variable {stage : Nat} {inverse : InverseRootPolynomial.Model polynomial patch.base.box}
variable {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
variable {powers : OddPowers inverse.value}

/-- The computed common floor of this original scalar source and the supplied original primitive patch. -/
@[expose] def comparisonFloor {time : Fraction.Rational} {timeInside : FixedRootBoxPath.Inside time}
    (source : Transport.Reading actual time timeInside)
    (patch : ContinuedNeighborhood polynomial count) : Fraction.Rational :=
  if source.traceFloor ≤ patch.rootLower then source.traceFloor else patch.rootLower

/-- The original regular scalar source and retained primitive patch pay both computed denominator floors. -/
theorem comparisonFloor_paid {time : Fraction.Rational} {timeInside : FixedRootBoxPath.Inside time}
    (source : Transport.Reading actual time timeInside) (patch : ContinuedNeighborhood polynomial count)
    (regular : parameter ≠ criticalValue site) :
    0 < comparisonFloor source patch ∧ comparisonFloor source patch ≤ source.traceFloor ∧
      comparisonFloor source patch ≤ patch.rootLower := by
  unfold comparisonFloor
  split
  · rename_i ordered
    exact ⟨(source.traceFloors_positive regular).1, Fraction.Order.Basic.le_refl _, ordered⟩
  · rename_i ordered
    exact ⟨patch.rootLower_positive, (lt_of_not_ge ordered).le, Fraction.Order.Basic.le_refl _⟩

/-- Compare this actual scalar cell with the same retained signed primitive Point and its shared root reading.

The supplied signed relation concerns the two original numerical channels.
The existing finite comparison consumes that relation and both actual
observations, computing its requested tails and radius payment internally.
-/
@[expose] def comparePrimitive (model : Model data source accuracy)
    (related : Equivalence.NamedEquivalent source.lift.value.name sample.certificate.value.name)
    (shared : PrimitiveReading sample stage inverse powers) (target : Fraction.Rational) (positive : 0 < target) :
    Equivalence.Observation.Comparison model.rootReading shared.rootReading target :=
  Equivalence.Observation.Comparison.build model.rootReading shared.rootReading related target positive

/-- The actual compiled numerator and odd-power primitive are controlled by the same retained root comparison.

The supplied primitive retains its original numerator, pair index and
coefficient cache. Exact scaled-numerator and pair-index equations link
those original indices to this scalar differential. The common source/patch
floor pays both actual roots; no numerical samples are identified.
-/
theorem primitiveComparison_le (model : Model data source accuracy)
    (pairs : differential.denominatorPairs = pairCount)
    (scale : ∀ point, numerator.eval point = differential.scale * differential.numerator.eval point)
    (shared : PrimitiveReading sample stage inverse powers)
    (common : PrimitiveModel patch stage numerator pairCount)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base)
    {target : Fraction.Rational}
    (comparison : Equivalence.Observation.Comparison model.rootReading shared.rootReading target) :
    let floor := comparisonFloor source patch
    let error := 2 * (Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale stage +
      (floor⁻¹ * floor⁻¹) * comparison.bound)
    let upper := 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) + floor⁻¹
    model.primitiveResidual common.coefficient ≤
      normSq ((differential.scale * differential.numerator.eval
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
          Tangent.baseVelocity site parameter 2 quarter span.lower) *
        ((fun count : Nat => match count with
        | 0 => error
        | remaining + 1 => Norm.Power.differenceFactor upper (2 * (remaining + 1) + 1) * error) pairCount) := by
  have paid := comparisonFloor_paid source patch model.regular
  have leftLower := paid.2.1.trans model.rootReading_lower
  have rightLower := paid.2.2.trans (sample.candidate_lower _ shared.possible)
  rewrite [← Norm.Basic.normSq_eq_canonical] at rightLower
  have compiled : common.coefficient.eval
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base =
        (differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
            (match differential.denominatorPairs with
            | 0 => shared.inverse
            | remaining + 1 => shared.inverse ^ (2 * (remaining + 1) + 1)) := by
    have sameInverse := shared.inverse_eq.trans
      (congrArg (fun retained : InverseRootPolynomial.Model polynomial patch.base.box =>
        retained.value.eval (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base)
          shared.model_eq)
    rewrite [common.coefficient_eq, scale _, pairs, ← sameInverse]
    cases pairCount <;> rfl
  have bound := model.primitiveResidual_le shared contained comparison (comparisonFloor source patch)
    paid.1 leftLower rightLower common.coefficient compiled
  rewrite [pairs] at bound
  exact bound

/-- The actual scalar request's paid comparison allowance keeps its original root sensitivity and accuracy. -/
@[expose] def comparisonAllowance (_model : Model data source accuracy) : Fraction.Rational :=
  (16 * (((25 / 4) * normSq (halfGap site parameter)) + 1) + 4) * accuracy.tolerance

/-- Both original observed radii and the same root request pay the computed scalar-cell comparison allowance. -/
theorem comparison_bound_le (model : Model data source accuracy)
    (sameModel : inverse = patch.base.refine stage)
    (root : ContinuedNeighborhood.Point.PrimitiveRoot sample stage accuracy.tolerance)
    (comparison : Equivalence.Observation.Comparison model.rootReading
      (root.readModel inverse sameModel powers).rootReading accuracy.tolerance) :
    comparison.bound ≤ model.comparisonAllowance := by
  have firstRadius := model.rootReading_radius_uniform
  have lastRadius := root.readModel_radius_lt inverse sameModel powers
  rewrite [comparison.bound_eq]
  exact (Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct firstRadius lastRadius.le)
      (by decide +kernel : (0 : Fraction.Rational) ≤ 16))
    (Fraction.Order.Basic.le_refl _)).trans_eq (by unfold comparisonAllowance; ring1)

/-- The exact original root, shared reading and comparison Sigma of a paid scalar coefficient request.

This ordinary named type retains the complete original indices, numerical
caches, factory equations and both payment guarantees. It adds no record or
alternative result; the name keeps dependent source-parent applications
compact until a client reads an actual retained component.
-/
@[expose] def CoefficientRequest (model : Model data source accuracy)
    (sameModel : inverse = patch.base.refine stage)
    (common : PrimitiveModel patch stage numerator pairCount) : Type 1 :=
  Σ root : {actual : ContinuedNeighborhood.Point.PrimitiveRoot sample stage accuracy.tolerance //
      actual = ContinuedNeighborhood.Point.selectPrimitiveRoot sample stage accuracy.tolerance accuracy.positive},
    Σ shared : {actual : PrimitiveReading sample stage inverse powers //
      actual = root.val.readModel inverse sameModel powers},
    {actual : Equivalence.Observation.Comparison model.rootReading shared.val.rootReading accuracy.tolerance //
      actual.bound ≤ model.comparisonAllowance ∧
      let floor := comparisonFloor source patch
      let error := 2 * (Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale stage +
        (floor⁻¹ * floor⁻¹) * model.comparisonAllowance)
      let upper := 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) + floor⁻¹
      model.primitiveResidual common.coefficient ≤
        normSq ((differential.scale * differential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) *
            Tangent.baseVelocity site parameter 2 quarter span.lower) *
          ((fun count : Nat => match count with
          | 0 => error
          | remaining + 1 => Norm.Power.differenceFactor upper (2 * (remaining + 1) + 1) * error) pairCount)}

namespace CoefficientRequest

/-- Attach the actual retained root, model reading and complete comparison to the original coefficient request.

The supplied root and shared reading carry their original factory equations.
The original comparison bound and odd-power residual proof pay the new
coefficient using those same observations; no root, model or comparison is
acquired again.
-/
@[expose] def ofReadings (model : Model data source accuracy)
    (pairs : differential.denominatorPairs = pairCount)
    (scale : ∀ point, numerator.eval point = differential.scale * differential.numerator.eval point)
    (sameModel : inverse = patch.base.refine stage)
    (common : PrimitiveModel patch stage numerator pairCount)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base)
    (root : {actual : ContinuedNeighborhood.Point.PrimitiveRoot sample stage accuracy.tolerance //
      actual = ContinuedNeighborhood.Point.selectPrimitiveRoot sample stage accuracy.tolerance accuracy.positive})
    (shared : {actual : PrimitiveReading sample stage inverse powers //
      actual = root.val.readModel inverse sameModel powers})
    (comparison : Equivalence.Observation.Comparison model.rootReading shared.val.rootReading accuracy.tolerance) :
    CoefficientRequest (sample := sample) (powers := powers) model sameModel common := by
  have comparisonPaid : comparison.bound ≤ model.comparisonAllowance := by
    obtain ⟨retained, sameShared⟩ := shared
    cases sameShared
    exact model.comparison_bound_le sameModel root.val comparison
  have inverseNonnegative :=
    (Fraction.Order.Field.inv_pos_direct (comparisonFloor_paid source patch model.regular).1).le
  have transferred := Arithmetic.mul_le_mul_of_nonneg_left_direct comparisonPaid
    (Arithmetic.mul_nonneg_direct inverseNonnegative inverseNonnegative)
  have errorPaid := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl
      (Rational.Geometric.Basic.quarterRadius patch.inverseErrorScale stage)) transferred)
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  have inverseSumNonnegative : 0 ≤ patch.inverseErrorScale + patch.rootLower⁻¹ := by
    calc
      0 = 0 + 0 := by decide +kernel
      _ ≤ _ := Arithmetic.add_le_add_direct patch.inverseErrorScale_positive.le
        (Fraction.Order.Field.inv_pos_direct patch.rootLower_positive).le
  have upperNonnegative : 0 ≤ 2 * (patch.inverseErrorScale + patch.rootLower⁻¹) +
      (comparisonFloor source patch)⁻¹ := by
    calc
      0 = 0 + 0 := by decide +kernel
      _ ≤ _ := Arithmetic.add_le_add_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Fraction.Rational) ≤ 2) inverseSumNonnegative)
        inverseNonnegative
  have coefficientPaid := model.primitiveComparison_le pairs scale shared.val common contained comparison
  refine ⟨root, shared, ⟨comparison, comparisonPaid, ?_⟩⟩
  apply coefficientPaid.trans
  apply Arithmetic.mul_le_mul_of_nonneg_left_direct _ (Norm.Basic.normSq_nonneg _)
  cases pairCount with
  | zero => exact errorPaid
  | succ remaining =>
      exact Arithmetic.mul_le_mul_of_nonneg_left_direct errorPaid
        (Norm.Power.differenceFactor_nonnegative upperNonnegative _)

/-- Reweight an actual original coefficient request while forwarding its same root, shared reading and comparison.

Only the differential coefficient and its original primitive change. The
complete left Reading equality transports the retained comparison index;
its actual owners, relation procedure, tail, samples and payment stay the
same data.
-/
@[expose] def reweight (model : Model data source accuracy)
    (sameModel : inverse = patch.base.refine stage)
    (common : PrimitiveModel patch stage numerator pairCount)
    (request : CoefficientRequest (sample := sample) (powers := powers) model sameModel common)
    {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : Data site parameter nextDifferential)
    {nextNumerator : Pair.Polynomial.Coefficients} {nextPairs : Nat}
    (pairs : nextDifferential.denominatorPairs = nextPairs)
    (scale : ∀ point, nextNumerator.eval point = nextDifferential.scale * nextDifferential.numerator.eval point)
    (nextCommon : PrimitiveModel patch stage nextNumerator nextPairs)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) :
    CoefficientRequest (sample := sample) (powers := powers) (Model.reweight model nextData) sameModel nextCommon :=
  let comparison := Eq.mpr
    (congrArg (fun retained => Equivalence.Observation.Comparison retained request.2.1.val.rootReading
      accuracy.tolerance) (model.rootReading_reweight nextData)) request.2.2.val
  ofReadings (Model.reweight model nextData) pairs scale sameModel nextCommon contained request.1 request.2.1 comparison

end CoefficientRequest

/-- Retain one actual requested root, shared reading and paid coefficient comparison on this original scalar cell.

The actual original Point and signed relation remain supplied mathematical
inputs. One original root request and readModel consume its retained inverse
and power caches; the domain is the same patch's actual containment. Both
original radii pay the same comparison and coefficient target internally.
-/
@[expose] def coefficientRequest (model : Model data source accuracy)
    (related : Equivalence.NamedEquivalent source.lift.value.name sample.certificate.value.name)
    (pairs : differential.denominatorPairs = pairCount)
    (scale : ∀ point, numerator.eval point = differential.scale * differential.numerator.eval point)
    (sameModel : inverse = patch.base.refine stage)
    (common : PrimitiveModel patch stage numerator pairCount)
    (contained : patch.box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base) :
    CoefficientRequest (sample := sample) (powers := powers) model sameModel common := by
  let root : ContinuedNeighborhood.Point.PrimitiveRoot sample stage accuracy.tolerance :=
    ContinuedNeighborhood.Point.selectPrimitiveRoot sample stage accuracy.tolerance accuracy.positive
  let shared : PrimitiveReading sample stage inverse powers := root.readModel inverse sameModel powers
  let comparison : Equivalence.Observation.Comparison model.rootReading shared.rootReading accuracy.tolerance :=
    model.comparePrimitive related shared accuracy.tolerance accuracy.positive
  exact CoefficientRequest.ofReadings model pairs scale sameModel common contained
    ⟨root, rfl⟩ ⟨shared, rfl⟩ comparison

end PrimitiveRequest

/-- The actual curved-cell primitive error has separate geometric Taylor and sampled-coefficient contributions.

The original radial geometry supplies both endpoint containment and movement
bounds. The supplied whole Horner cache belongs to the same polynomial and
actual box; its value component pays the tangent remainder. Supplied
endpoint containment concerns that same primitive domain. The final term
retains the actual coefficient residual without assuming it is small.
-/
theorem primitive_boundary_error_le (model : Model data source accuracy) {polynomial : CoefficientPolynomial}
    {box : Box} (primitive : DensePrimitive polynomial box) (bounds : Horner)
    (bounds_eq : bounds = Dense.Gaussian.Bounds.Box.denseHornerNormBounds polynomial box)
    (firstInside : box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base)
    (lastInside : box.Contains
      (Radial.point site parameter 2 (Waist.direction quarter span.upper) positive).base) :
    normSq (primitive.value.eval
        (Radial.point site parameter 2 (Waist.direction quarter span.upper) positive).base -
      primitive.value.eval (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base -
      model.cell.integralSample) ≤
        4 * (primitive.remainderBound * ((25 / 4) * normSq (halfGap site parameter)) ^ 2 +
          bounds.value * ((25 / 4) * normSq (halfGap site parameter))) * (span.upper - span.lower) ^ 4 +
            2 * model.primitiveResidual polynomial * (span.upper - span.lower) ^ 2 := by
  let first := (Radial.point site parameter 2 (Waist.direction quarter span.lower) positive).base
  let last := (Radial.point site parameter 2 (Waist.direction quarter span.upper) positive).base
  let velocity := Tangent.baseVelocity site parameter 2 quarter span.lower
  let step : Canonical := ⟨span.upper - span.lower, 0⟩
  let movement := (25 / 4) * normSq (halfGap site parameter)
  have movementNonnegative : 0 ≤ movement :=
    Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)
  have moved := quarter_base_distance_le site parameter 2 quarter positive actual.data.lower actual.data.upper
    span.upper span.lower
  have tangent := Tangent.base_remainder_normSq_le site parameter 2 quarter positive actual.data.lower
    actual.data.upper span.lower (span.upper - span.lower)
  rewrite [show span.lower + (span.upper - span.lower) = span.upper by ring1] at tangent
  have estimated := primitive.increment_bound_with_tangent
    (step := step) (direction := velocity) firstInside lastInside moved tangent
  have coefficient : normSq (polynomial.eval first) ≤ bounds.value := by
    have original := Dense.Gaussian.Bounds.Box.normSq_eval_le_denseEvalNormBound polynomial firstInside
    rewrite [bounds_eq]
    exact original
  have geometric : normSq (primitive.value.eval last - primitive.value.eval first -
      step * (polynomial.eval first * velocity)) ≤
        2 * (primitive.remainderBound * (movement * (span.upper - span.lower) ^ 2) ^ 2 +
          bounds.value * (movement * (span.upper - span.lower) ^ 4)) :=
    estimated.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _)
        (Arithmetic.mul_le_mul_of_nonneg_right_direct coefficient
          (Arithmetic.mul_nonneg_direct movementNonnegative (Arithmetic.pow_nonneg_direct
            (Arithmetic.sub_nonneg_direct span.valid) 4)))) (by decide +kernel))
  have stepNorm : normSq step = (span.upper - span.lower) ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    change (span.upper - span.lower) * (span.upper - span.lower) + 0 * 0 = _
    ring1
  have decomposition : primitive.value.eval last - primitive.value.eval first - step * model.center =
      (primitive.value.eval last - primitive.value.eval first - step * (polynomial.eval first * velocity)) +
        step * (polynomial.eval first * velocity - model.center) := by ring1
  rewrite [model.integralSample]
  change normSq (primitive.value.eval last - primitive.value.eval first - step * model.center) ≤ _
  rewrite [decomposition]
  apply (Norm.Bounds.normSq_add_le_two _ _).trans
  have retained := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct geometric
      (show normSq (step * (polynomial.eval first * velocity - model.center)) ≤
        (span.upper - span.lower) ^ 2 * model.primitiveResidual polynomial by
          rewrite [Norm.Basic.normSq_mul, stepNorm]
          exact Fraction.Order.Basic.le_refl _)) (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
  exact retained.trans (by apply Eq.le; ring1)

end Model

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
