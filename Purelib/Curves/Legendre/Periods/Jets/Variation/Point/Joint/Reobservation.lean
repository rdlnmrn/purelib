module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Joint
public import Purelib.Curves.Legendre.Periods.Jets.Variation.Arithmetic.Reobservation
public import Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation.Cache.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Jointly shrinking evaluator and root payments on the same actual Taylor bank

New arithmetic observations consume the existing Joint core and its unchanged
primary root data. Their free accuracy is the minimum of a spatial request and
the primary parameter-fourth request. The independent additional root spread
and the newly paid evaluator request give explicit jointly shrinking errors.
The same new readings also carry their direct parameter Taylor certificates.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

open Purelib
open Purelib.Approximation
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Observation
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

attribute [local irreducible] CertifiedSquareRoot.rawRoot

variable {parameter increment point : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {source : ContinuedNeighborhood.Point patch point} {step : Step source increment} {nonzero : increment ≠ 0}
    {sourceAdditional targetAdditional spatial : AccuracyRequest}

/-- The retained joint core uses the original source seed-box floor at every independently selected request stage. -/
theorem core_sourceFloor (retained : Joint step nonzero sourceAdditional targetAdditional) :
    retained.core.clearance.sourceFloor = patch.rootLower := by
  rewrite [retained.core_eq, sample, Sampling.ofObservations_clearance]
  rewrite [CertifiedSquareRoot.Sampling.Clearance.castParameters_sourceFloor]
  exact step.clearance_sourceFloor _ _

/-- The target core candidates retain that same original seed-box floor after the actual owner continuation. -/
theorem core_targetFloor (retained : Joint step nonzero sourceAdditional targetAdditional) :
    retained.core.clearance.targetFloor = patch.rootLower := by
  rewrite [retained.core_eq, sample, Sampling.ofObservations_clearance]
  rewrite [CertifiedSquareRoot.Sampling.Clearance.castParameters_targetFloor]
  exact step.clearance_targetFloor _ _

/-- The joint core sum margin retains its original fourfold seed-box floor, independently of the paid root requests. -/
theorem core_sumFloor (retained : Joint step nonzero sourceAdditional targetAdditional) :
    retained.core.clearance.sumFloor = 4 * patch.rootLower := by
  rewrite [retained.core_eq, sample, Sampling.ofObservations_clearance]
  rewrite [CertifiedSquareRoot.Sampling.Clearance.castParameters_sumFloor]
  exact step.clearance_sumFloor _ _

/-- Reobserve all ten retained evaluators without another root or scalar inverse/cubic cache construction. -/
def reobserve (retained : Joint step nonzero sourceAdditional targetAdditional) (spatial : AccuracyRequest) :
    Arithmetic.Reobservations retained.arithmetic spatial := Arithmetic.Reobservations.build retained.arithmetic spatial

/-- Construct both root payments and the genuinely independently paid arithmetic bank, retaining every actual cache.

The original Joint factory executes once. The new bank requests each old
exact evaluator once at the spatial/parameter minimum and keeps both old
and new readings with their honest existing operational comparison.
-/
def buildSpatial (step : Step source increment) (nonzero : increment ≠ 0) (spatial : AccuracyRequest) :
    (retained : Joint step nonzero spatial spatial) × Arithmetic.Reobservations retained.arithmetic spatial :=
  let retained := build step nonzero spatial spatial
  let paid := retained.reobserve spatial
  ⟨retained, paid⟩

/-- The first component of the original spatial factory is its original Joint factory. -/
theorem buildSpatial_joint (step : Step source increment) (nonzero : increment ≠ 0)
    (spatial : AccuracyRequest) :
    (buildSpatial step nonzero spatial).1 = build step nonzero spatial spatial := by
  unfold buildSpatial
  rfl

/-- The second component is the original evaluator factory on that same stored Joint. -/
theorem buildSpatial_paid (step : Step source increment) (nonzero : increment ≠ 0)
    (spatial : AccuracyRequest) :
    (buildSpatial step nonzero spatial).2 = (buildSpatial step nonzero spatial).1.reobserve spatial := by
  unfold buildSpatial
  rfl

attribute [local irreducible] Joint in
set_option genInjectivity false in
/-- A retained spatial bank stores the whole original Joint/evaluator result and its factory identity.

The original Step and requests remain indices. The existing dependent pair
is kept intact, including all root, inverse, evaluator and observation
caches; its second component belongs to its exact first Joint component.
-/
structure Spatial (step : Step source increment) (nonzero : increment ≠ 0) (spatial : AccuracyRequest) where
  /-- The complete original Joint/evaluator pair, with its exact dependent arithmetic owner. -/
  val : (retained : Joint step nonzero spatial spatial) ×
    Arithmetic.Reobservations retained.arithmetic spatial
  /-- The whole stored pair is the original spatial factory result on the same Step and request. -/
  property : val = buildSpatial step nonzero spatial

constructive_injectivity Spatial

namespace Spatial

/-- Execute and retain the original spatial bank factory once. -/
def build (step : Step source increment) (nonzero : increment ≠ 0) (spatial : AccuracyRequest) :
    Spatial step nonzero spatial :=
  let bank := buildSpatial step nonzero spatial
  ⟨bank, rfl⟩

variable (retained : Spatial step nonzero spatial)

/-- Read the whole original Joint from the stored spatial bank. -/
@[expose] def joint : Joint step nonzero spatial spatial := retained.val.1

/-- Read the whole paid evaluator bank on the same stored Joint. -/
@[expose] def paid : Arithmetic.Reobservations retained.joint.arithmetic spatial := retained.val.2

/-- The complete retained dependent pair is the original spatial factory result. -/
theorem cache_eq : retained.val = buildSpatial step nonzero spatial := retained.property

/-- The retained Joint is exactly the original Joint factory on the supplied Step and requests. -/
theorem joint_eq : retained.joint = Joint.build step nonzero spatial spatial := by
  have same := congrArg
    (fun bank : (joint : Joint step nonzero spatial spatial) ×
      Arithmetic.Reobservations joint.arithmetic spatial => bank.1) retained.property
  exact same.trans (buildSpatial_joint step nonzero spatial)

/-- The retained evaluator bank is exactly the original reobservation factory on the stored Joint. -/
theorem paid_eq : retained.paid = retained.joint.reobserve spatial := by
  change retained.val.2 = retained.val.1.reobserve spatial
  have same := congrArg
    (fun bank : (joint : Joint step nonzero spatial spatial) ×
      Arithmetic.Reobservations joint.arithmetic spatial => bank.2 = bank.1.reobserve spatial)
    retained.property
  exact Eq.mpr same (buildSpatial_paid step nonzero spatial)

end Spatial

/-- The original arithmetic sensitivity coefficient and original fourfold root spread give the exact factor sixteen. -/
private theorem spread_budget (accuracy sensitivity radius : Fraction.Rational) :
    accuracy + 4 * sensitivity * (4 * radius) = accuracy + 16 * sensitivity * radius := by ring1

/-- A common actual spatial tolerance has an explicit linear error factor on the fixed original evaluator and root. -/
private theorem common_budget (accuracy sensitivity denominator : Fraction.Rational) :
    accuracy + 16 * sensitivity * (accuracy / denominator) =
      (1 + 16 * sensitivity / denominator) * accuracy := by
  rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct]
  ring1

/-- The new sourceValue reading pays independent evaluator and root tolerances on its identical scalar core. -/
theorem sourceValue_spatial_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point retained.core.sourceSample.reading) ≤
      spatial.tolerance + 16 * Cache.sensitivity (Specification.valueSpecification parameter coordinate)
        point patch.rootLower *
          (CertifiedSquareRoot.Sampling.radiusRequest source.certificate sourceAdditional).tolerance := by
  have bound := paid.sourceValue_spatial_le coordinate retained.core_source_spread.le
  have same := congrArg (fun floor : Fraction.Rational =>
    spatial.tolerance + 4 * Cache.sensitivity (Specification.valueSpecification parameter coordinate)
      point floor * (4 * (CertifiedSquareRoot.Sampling.radiusRequest source.certificate sourceAdditional).tolerance))
    retained.core_sourceFloor
  exact bound.trans_eq (same.trans (spread_budget _ _ _))

/-- A common spatial request gives a fixed linear error factor for the same new sourceValue reading. -/
theorem sourceValue_common_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point retained.core.sourceSample.reading) ≤
      (1 + 16 * Cache.sensitivity (Specification.valueSpecification parameter coordinate) point
        patch.rootLower /
        CertifiedSquareRoot.Sampling.radiusDenominator source.certificate) * spatial.tolerance :=
  (retained.sourceValue_spatial_le paid coordinate).trans_eq (common_budget _ _ _)

/-- The new targetValue reading pays independent evaluator and root tolerances on its identical scalar core. -/
theorem targetValue_spatial_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.targetValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point retained.core.targetSample.reading) ≤
      spatial.tolerance + 16 * Cache.sensitivity (Specification.valueSpecification (parameter + increment) coordinate)
        point patch.rootLower * (CertifiedSquareRoot.Sampling.radiusRequest step.root targetAdditional).tolerance := by
  have bound := paid.targetValue_spatial_le coordinate retained.core_target_spread.le
  have same := congrArg (fun floor : Fraction.Rational =>
    spatial.tolerance + 4 * Cache.sensitivity (Specification.valueSpecification (parameter + increment) coordinate)
      point floor * (4 * (CertifiedSquareRoot.Sampling.radiusRequest step.root targetAdditional).tolerance))
    retained.core_targetFloor
  exact bound.trans_eq (same.trans (spread_budget _ _ _))

/-- A common spatial request gives a fixed linear error factor for the same new targetValue reading. -/
theorem targetValue_common_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.targetValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point retained.core.targetSample.reading) ≤
      (1 + 16 * Cache.sensitivity (Specification.valueSpecification (parameter + increment) coordinate) point
        patch.rootLower /
        CertifiedSquareRoot.Sampling.radiusDenominator step.root) * spatial.tolerance :=
  (retained.targetValue_spatial_le paid coordinate).trans_eq (common_budget _ _ _)

/-- The new sourceFirst reading pays independent evaluator and root tolerances on its identical scalar core. -/
theorem sourceFirst_spatial_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point retained.core.sourceSample.reading) ≤
      spatial.tolerance + 16 * Cache.sensitivity (Specification.firstDerivativeSpecification parameter coordinate)
        point patch.rootLower *
          (CertifiedSquareRoot.Sampling.radiusRequest source.certificate sourceAdditional).tolerance := by
  have bound := paid.sourceFirst_spatial_le coordinate retained.core_source_spread.le
  have same := congrArg (fun floor : Fraction.Rational =>
    spatial.tolerance + 4 * Cache.sensitivity (Specification.firstDerivativeSpecification parameter coordinate)
      point floor * (4 * (CertifiedSquareRoot.Sampling.radiusRequest source.certificate sourceAdditional).tolerance))
    retained.core_sourceFloor
  exact bound.trans_eq (same.trans (spread_budget _ _ _))

/-- A common spatial request gives a fixed linear error factor for the same new sourceFirst reading. -/
theorem sourceFirst_common_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point retained.core.sourceSample.reading) ≤
      (1 + 16 * Cache.sensitivity (Specification.firstDerivativeSpecification parameter coordinate) point
        patch.rootLower /
        CertifiedSquareRoot.Sampling.radiusDenominator source.certificate) * spatial.tolerance :=
  (retained.sourceFirst_spatial_le paid coordinate).trans_eq (common_budget _ _ _)

/-- The new targetFirst reading pays independent evaluator and root tolerances on its identical scalar core. -/
theorem targetFirst_spatial_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.targetFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point retained.core.targetSample.reading) ≤
      spatial.tolerance + 16 * Cache.sensitivity (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate)
        point patch.rootLower * (CertifiedSquareRoot.Sampling.radiusRequest step.root targetAdditional).tolerance := by
  have bound := paid.targetFirst_spatial_le coordinate retained.core_target_spread.le
  have same := congrArg (fun floor : Fraction.Rational =>
    spatial.tolerance + 4 * Cache.sensitivity
      (Specification.firstDerivativeSpecification (parameter + increment) coordinate) point floor *
        (4 * (CertifiedSquareRoot.Sampling.radiusRequest step.root targetAdditional).tolerance))
    retained.core_targetFloor
  exact bound.trans_eq (same.trans (spread_budget _ _ _))

/-- A common spatial request gives a fixed linear error factor for the same new targetFirst reading. -/
theorem targetFirst_common_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.targetFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point retained.core.targetSample.reading) ≤
      (1 + 16 * Cache.sensitivity (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate) point
        patch.rootLower /
        CertifiedSquareRoot.Sampling.radiusDenominator step.root) * spatial.tolerance :=
  (retained.targetFirst_spatial_le paid coordinate).trans_eq (common_budget _ _ _)

/-- The new sourceSecond reading pays independent evaluator and root tolerances on its identical scalar core. -/
theorem sourceSecond_spatial_le (retained : Joint step nonzero sourceAdditional targetAdditional)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceSecond.get coordinate).requested.reading -
      Variation.secondReading coordinate point retained.core.sourceSample.reading) ≤
      spatial.tolerance + 16 * Cache.sensitivity (Specification.secondDerivativeSpecification parameter coordinate)
        point patch.rootLower *
          (CertifiedSquareRoot.Sampling.radiusRequest source.certificate sourceAdditional).tolerance := by
  have bound := paid.sourceSecond_spatial_le coordinate retained.core_source_spread.le
  have same := congrArg (fun floor : Fraction.Rational =>
    spatial.tolerance + 4 * Cache.sensitivity (Specification.secondDerivativeSpecification parameter coordinate)
      point floor * (4 * (CertifiedSquareRoot.Sampling.radiusRequest source.certificate sourceAdditional).tolerance))
    retained.core_sourceFloor
  exact bound.trans_eq (same.trans (spread_budget _ _ _))

/-- A common spatial request gives a fixed linear error factor for the same new sourceSecond reading. -/
theorem sourceSecond_common_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2) :
    Norm.Basic.normSq ((paid.sourceSecond.get coordinate).requested.reading -
      Variation.secondReading coordinate point retained.core.sourceSample.reading) ≤
      (1 + 16 * Cache.sensitivity (Specification.secondDerivativeSpecification parameter coordinate) point
        patch.rootLower /
        CertifiedSquareRoot.Sampling.radiusDenominator source.certificate) * spatial.tolerance :=
  (retained.sourceSecond_spatial_le paid coordinate).trans_eq (common_budget _ _ _)

/-- The fixed physical box and original seed floor give a uniform spatial ceiling for the new sourceValue reading.

The original finite polynomial fold bounds the numerator at this admitted
physical point. The whole-seed-box candidate floor and the existing
arithmetic allowance theorem remove all request-stage and root-radius
constants from the ceiling.
-/
theorem sourceValue_uniform_spatial_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    {box : Geometry.Rational.Box} (inside : box.Contains point) :
    Norm.Basic.normSq ((paid.sourceValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point retained.core.sourceSample.reading) ≤
      Cache.allowanceCeiling (Specification.valueSpecification parameter coordinate) box
        patch.rootLower *
        spatial.tolerance := by
  have bound := retained.sourceValue_common_le paid coordinate
  change Norm.Basic.normSq ((paid.sourceValue.get coordinate).requested.reading -
    Variation.valueReading coordinate point retained.core.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.valueSpecification parameter coordinate) point
        source.certificate patch.rootLower *
        spatial.tolerance at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Cache.allowanceFactor_le_ceiling (Specification.valueSpecification parameter coordinate)
      source.certificate
      inside patch.rootLower_positive) spatial.positive.le)

/-- The fixed physical box and original seed floor give a uniform spatial ceiling for the new targetValue reading.

The original finite polynomial fold bounds the numerator at this admitted
physical point. The whole-seed-box candidate floor and the existing
arithmetic allowance theorem remove all request-stage and root-radius
constants from the ceiling.
-/
theorem targetValue_uniform_spatial_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    {box : Geometry.Rational.Box} (inside : box.Contains point) :
    Norm.Basic.normSq ((paid.targetValue.get coordinate).requested.reading -
      Variation.valueReading coordinate point retained.core.targetSample.reading) ≤
      Cache.allowanceCeiling (Specification.valueSpecification (parameter + increment) coordinate) box
        patch.rootLower *
        spatial.tolerance := by
  have bound := retained.targetValue_common_le paid coordinate
  change Norm.Basic.normSq ((paid.targetValue.get coordinate).requested.reading -
    Variation.valueReading coordinate point retained.core.targetSample.reading) ≤
      Cache.allowanceFactor (Specification.valueSpecification (parameter + increment) coordinate) point
        step.root patch.rootLower *
        spatial.tolerance at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Cache.allowanceFactor_le_ceiling (Specification.valueSpecification (parameter + increment) coordinate)
      step.root
      inside patch.rootLower_positive) spatial.positive.le)

/-- The fixed physical box and original seed floor give a uniform spatial ceiling for the new sourceFirst reading.

The original finite polynomial fold bounds the numerator at this admitted
physical point. The whole-seed-box candidate floor and the existing
arithmetic allowance theorem remove all request-stage and root-radius
constants from the ceiling.
-/
theorem sourceFirst_uniform_spatial_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    {box : Geometry.Rational.Box} (inside : box.Contains point) :
    Norm.Basic.normSq ((paid.sourceFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point retained.core.sourceSample.reading) ≤
      Cache.allowanceCeiling (Specification.firstDerivativeSpecification parameter coordinate) box
        patch.rootLower *
        spatial.tolerance := by
  have bound := retained.sourceFirst_common_le paid coordinate
  change Norm.Basic.normSq ((paid.sourceFirst.get coordinate).requested.reading -
    Variation.firstReading coordinate point retained.core.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.firstDerivativeSpecification parameter coordinate) point
        source.certificate patch.rootLower *
        spatial.tolerance at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Cache.allowanceFactor_le_ceiling (Specification.firstDerivativeSpecification parameter coordinate)
      source.certificate
      inside patch.rootLower_positive) spatial.positive.le)

/-- The fixed physical box and original seed floor give a uniform spatial ceiling for the new targetFirst reading.

The original finite polynomial fold bounds the numerator at this admitted
physical point. The whole-seed-box candidate floor and the existing
arithmetic allowance theorem remove all request-stage and root-radius
constants from the ceiling.
-/
theorem targetFirst_uniform_spatial_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    {box : Geometry.Rational.Box} (inside : box.Contains point) :
    Norm.Basic.normSq ((paid.targetFirst.get coordinate).requested.reading -
      Variation.firstReading coordinate point retained.core.targetSample.reading) ≤
      Cache.allowanceCeiling (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate) box
        patch.rootLower *
        spatial.tolerance := by
  have bound := retained.targetFirst_common_le paid coordinate
  change Norm.Basic.normSq ((paid.targetFirst.get coordinate).requested.reading -
    Variation.firstReading coordinate point retained.core.targetSample.reading) ≤
      Cache.allowanceFactor (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate) point
        step.root patch.rootLower *
        spatial.tolerance at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Cache.allowanceFactor_le_ceiling (Specification.firstDerivativeSpecification (parameter + increment)
        coordinate)
      step.root
      inside patch.rootLower_positive) spatial.positive.le)

/-- The fixed physical box and original seed floor give a uniform spatial ceiling for the new sourceSecond reading.

The original finite polynomial fold bounds the numerator at this admitted
physical point. The whole-seed-box candidate floor and the existing
arithmetic allowance theorem remove all request-stage and root-radius
constants from the ceiling.
-/
theorem sourceSecond_uniform_spatial_le (retained : Joint step nonzero spatial spatial)
    (paid : Arithmetic.Reobservations retained.arithmetic spatial) (coordinate : Fin 2)
    {box : Geometry.Rational.Box} (inside : box.Contains point) :
    Norm.Basic.normSq ((paid.sourceSecond.get coordinate).requested.reading -
      Variation.secondReading coordinate point retained.core.sourceSample.reading) ≤
      Cache.allowanceCeiling (Specification.secondDerivativeSpecification parameter coordinate) box
        patch.rootLower *
        spatial.tolerance := by
  have bound := retained.sourceSecond_common_le paid coordinate
  change Norm.Basic.normSq ((paid.sourceSecond.get coordinate).requested.reading -
    Variation.secondReading coordinate point retained.core.sourceSample.reading) ≤
      Cache.allowanceFactor (Specification.secondDerivativeSpecification parameter coordinate) point
        source.certificate patch.rootLower *
        spatial.tolerance at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Cache.allowanceFactor_le_ceiling (Specification.secondDerivativeSpecification parameter coordinate)
      source.certificate
      inside patch.rootLower_positive) spatial.positive.le)

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Joint

end
