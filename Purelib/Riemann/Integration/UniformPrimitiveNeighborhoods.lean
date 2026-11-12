module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Riemann.Normalization.AlignedInverseRootSeed
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Readings.PreparedObservationNeighborhoods
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Monotonicity
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Subdivision
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.RootIsolation.Newton.Restart.Separated.Track
import Purelib.RootIsolation.Track.Newton.Build

public import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
public import Purelib.Approximation.Budget.SquaredVariationRadius
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.RootIsolation.Track.Basic
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Integration.PreparedNumeratorVariation
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Mathlib.Order.Basic
import Mathlib.Order.MinMax
import Purelib.Tactic.Ring

open Purelib.Geometry.Rational.Box.Square.Centered

open Purelib.Data.Rat.Fraction.Order

@[expose] public section

/-!
# Uniform primitive neighborhoods along a clear segment

The segment's finite clearance and Horner calculations determine one positive
coordinate radius before a point or a root occurrence is selected.  Uniform
square-root reconditioning retains the occurrence while avoiding arbitrarily
small owner-dependent continuation clearances.
-/

namespace Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods

open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.AlignedInverseRootSeed (AlignedSeed)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (Seed SeededNeighborhood seed_residual_le_relative
  seed_small_on_box)
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (variationRadius variationRadius_positive
  variationRadius_le_one centeredBox_center centeredBox_refines ObservationNeighborhood)
open Purelib.Riemann.Normalization.OwnerSeededInverseRoot (Owner OwnerSample)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Readings.PreparedObservationPoints
open Purelib.Approximation.Budget.SquaredVariationRadius
open Purelib.Riemann.Normalization.InverseRootPolynomial

open Purelib.Data.Rat in
/-- The exact rational carrier for uniform retained neighborhood bounds. -/
abbrev Coordinate := Fraction.Rational
open Purelib.Data.Gaussian in
/-- The canonical Gaussian rational carrier for original points and root seeds. -/
abbrev Gaussian := Basic.Canonical
open Purelib.Polynomial.Dense.Gaussian in
/-- The original dense Gaussian polynomial carrier. -/
abbrev Polynomial := Basic.CanonicalCoefficients.CoefficientPolynomial
/-- The original rational Gaussian box carrier with retained coordinate bounds. -/
abbrev Box := Geometry.Rational.Box

variable {mode : Purelib.Polynomial.Geometry.ClearPath.ClearSegment.Mode}
variable {polynomial : Polynomial} {ambient : Normalization.InverseRootPolynomial.Box} {start finish :
  Gaussian}

open Purelib.Data.Rat in
/-- Decreasing the target and increasing the nonnegative variation scale cannot increase the retained variation radius.

The unchanged minimum selects the same unit cap and scaled target quotient.
Positive denominator comparison bounds that quotient using the supplied targets and scales. -/
theorem variationRadius_le_of_bounds {smallTarget largeTarget smallScale largeScale : Coordinate}
    (targetNonnegative : 0 ≤ smallTarget) (targetBound : smallTarget ≤ largeTarget)
    (scaleNonnegative : 0 ≤ smallScale) (scaleBound : smallScale ≤ largeScale) :
    variationRadius smallTarget largeScale ≤ variationRadius largeTarget smallScale := by
  apply Basic.le_min (Basic.min_le_left _ _)
  apply (Basic.min_le_right _ _).trans
  apply Arithmetic.mul_le_mul_of_nonneg_right_direct _
    (Field.inv_pos_direct (by decide : (0 : Coordinate) < 4)).le
  change smallTarget / (8 * (largeScale + 1)) ≤ largeTarget / (8 * (smallScale + 1))
  have denominatorPositive : 0 < 8 * (smallScale + 1) :=
    Arithmetic.mul_pos_direct (by decide)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct scaleNonnegative (by decide))
  exact (Field.div_le_div_of_nonneg_left_direct
    targetNonnegative denominatorPositive
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (add_le_add scaleBound le_rfl) (by decide))).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct targetBound
      (Field.inv_pos_direct denominatorPositive).le)

namespace Bounds

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Riemann.RootContinuation

/-- A certified larger point radius for the same actual original cleared segment.

The lower bound preserves the original unit observation ambients. Choosing
one ambient-dependent radius for several genuine segments allows their
numerical polynomial bounds to be retained without changing their endpoints.
-/
def PointRadius (segment : ClearSegment polynomial ambient start finish mode) : Type :=
  {radius : Coordinate // UniformSquareRootPreparation.segmentPointRadius segment + 1 ≤ radius}

namespace PointRadius

/-- Use a supplied certified radius or the original exact segment-dependent default. -/
def value (segment : ClearSegment polynomial ambient start finish mode)
    (requested : Option (PointRadius segment)) : Coordinate :=
  match requested with
  | none => UniformSquareRootPreparation.segmentPointRadius segment + 1
  | some retained => retained.val

/-- Every selected point radius includes the entire original observation ambient. -/
theorem lower (segment : ClearSegment polynomial ambient start finish mode)
    (requested : Option (PointRadius segment)) :
    UniformSquareRootPreparation.segmentPointRadius segment + 1 ≤ value segment requested := by
  cases requested with
  | none => exact Basic.le_refl _
  | some retained => exact retained.property

/-- A shared endpoint quadrance ceiling bounds the original unit-observation point radius. -/
theorem bound_of_normSq_le {first last : Gaussian} {ceiling : Coordinate}
    (firstBound : Norm.Basic.normSq first ≤ ceiling) (lastBound : Norm.Basic.normSq last ≤ ceiling) :
    2 * (Norm.Basic.normSq (last - first) + Norm.Basic.normSq first) + 1 + 1 ≤ 10 * ceiling + 2 := by
  have distance : Norm.Basic.normSq (last - first) ≤ 4 * ceiling :=
    (Norm.Bounds.normSq_sub_le_two last first).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct lastBound firstBound) (by decide +kernel)).trans_eq (by ring1))
  exact (Arithmetic.add_le_add_direct
    (Arithmetic.add_le_add_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct distance firstBound) (by decide +kernel)) (Basic.le_refl _))
      (Basic.le_refl _)).trans_eq (by ring1)

/-- The actual original segment ambient computes a common certified point radius.

Both actual endpoints lie in the retained ambient. Its squared-norm ceiling
bounds the source and displacement quadrances, so this radius can be reused
for every original segment contained in that same ambient.
-/
def ofAmbient (segment : ClearSegment polynomial ambient start finish mode)
    (within : segment.WithinAmbient) : PointRadius segment := by
  have firstInside : ambient.Contains start := by
    have retained : ambient.Contains (segment.pointAt 0) := segment.pointAt_contains within 0 (by decide +kernel)
    exact Eq.mp (congrArg ambient.Contains segment.pointAt_zero) retained
  have lastInside : ambient.Contains finish := by
    have retained : ambient.Contains (segment.pointAt 1) := segment.pointAt_contains within 1 (by decide +kernel)
    exact Eq.mp (congrArg ambient.Contains segment.pointAt_one) retained
  refine ⟨10 * ambient.normSqBound + 2, ?_⟩
  exact bound_of_normSq_le (Box.normSq_le_normSqBound firstInside) (Box.normSq_le_normSqBound lastInside)

/-- The ambient point-radius request retains its exact original scalar computation. -/
theorem ofAmbient_value (segment : ClearSegment polynomial ambient start finish mode)
    (within : segment.WithinAmbient) :
    (ofAmbient segment within).val = 10 * ambient.normSqBound + 2 := rfl

end PointRadius

end Bounds

open Purelib in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- Uniform cached point, root, seed and continuation bounds for an original cleared polynomial segment.

Exact equations retain the enlarged point ambient box, polynomial Lipschitz majorant, prepared root ambient and
diameter, predicted clearance and a positive common observation radius. -/
structure Bounds (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish mode)
    (requested : optParam (Option (Bounds.PointRadius segment)) none) where
  /-- The retained positive radius of the enlarged point ambient box. -/ pointRadius : Coordinate
  /-- The point radius is the supplied certified enlargement or the exact original default. -/
    pointRadius_eq : pointRadius = Bounds.PointRadius.value segment requested
  /-- The retained point ambient radius is strictly positive. -/ pointRadius_positive : 0 < pointRadius
  /-- The retained symmetric point ambient box. -/ pointAmbient : Box
  /-- The point ambient is exactly the symmetric box with the retained radius. -/ pointAmbient_eq : pointAmbient =
    Box.symmetric pointRadius pointRadius_positive.le
  /-- The cached positive polynomial Lipschitz majorant on the point ambient box. -/ slope : Coordinate
  /-- The slope equals the exact original dense polynomial box Lipschitz bound. -/ slope_eq : slope =
    Bounds.Box.denseLipschitzBound polynomial pointAmbient
  /-- The retained polynomial slope majorant is strictly positive. -/ slope_positive : 0 < slope
  /-- The retained uniform ambient box for the original segment's prepared roots. -/ rootAmbient : Box
  /-- The box is exactly the original uniform root ambient construction. -/ rootAmbient_eq : rootAmbient =
    UniformSquareRootPreparation.rootAmbient segment
  /-- The cached squared-norm bound of the retained root ambient box. -/ rootNorm : Coordinate
  /-- The cache equals that original root box's exact squared-norm bound. -/ rootNorm_eq : rootNorm =
    rootAmbient.normSqBound
  /-- The retained root norm majorant is nonnegative. -/ rootNorm_nonnegative : 0 ≤ rootNorm
  /-- The cached uniform squared-norm majorant for prepared inverse seeds. -/ seedNorm : Coordinate
  /-- The seed norm majorant is the retained root norm divided by the original segment clearance. -/ seedNorm_eq :
    seedNorm = rootNorm / segment.clearanceBound
  /-- The retained seed norm majorant is nonnegative. -/ seedNorm_nonnegative : 0 ≤ seedNorm
  /-- The positive retained squared-diameter request for uniform root preparation. -/ rootDiameter : Coordinate
  /-- The requested diameter is one one-thousand-twenty-fourth divided by the retained seed majorant plus one. -/
    rootDiameter_eq : rootDiameter = (1 / 1024) / (seedNorm + 1)
  /-- The retained root-diameter request is strictly positive. -/ rootDiameter_positive : 0 < rootDiameter
  /-- The retained common predicted root-continuation clearance. -/ clearance : Coordinate
  /-- The clearance equals the original uniform preparation prediction at the retained root diameter. -/ clearance_eq :
    clearance = UniformSquareRootPreparation.predictedClearance segment rootDiameter
  /-- The retained predicted continuation clearance is strictly positive. -/ clearance_positive : 0 < clearance
  /-- The retained positive common radius for observations, seed error and continuation movement. -/ radius : Coordinate
  /-- The radius equals the exact minimum of the three retained observation and squared-variation radii. -/ radius_eq :
    radius = min (variationRadius segment.clearanceBound slope)
    (min (squaredVariationRadius (1 / 64) (slope * seedNorm ^ 2))
      (squaredVariationRadius clearance slope))
  /-- The retained common neighborhood radius is strictly positive. -/ radius_positive : 0 < radius

constructive_injectivity Bounds

namespace Bounds

variable {segment : ClearSegment polynomial ambient start finish mode}
variable {requested : Option (PointRadius segment)}

section

open Purelib
open Purelib.Data.Rat
open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian
open Purelib.Riemann.RootContinuation

/-- Cache uniform primitive-neighborhood bounds from the original cleared segment.

The exact point and root ambient boxes determine the derivative and seed majorants. A prepared root diameter and
predicted clearance determine the positive minimum radius paying observation, seed and continuation errors. -/
def build (segment : Geometry.ClearPath.ClearSegment polynomial ambient start finish mode)
    (requested : Option (PointRadius segment) := none) : Bounds segment requested := by
  let pointRadius := PointRadius.value segment requested
  have pointPositive : 0 < pointRadius := (Arithmetic.add_pos_of_pos_of_nonneg_direct
    (UniformSquareRootPreparation.segmentPointRadius_positive segment) (by decide)).trans_le
      (PointRadius.lower segment requested)
  let pointAmbient := Box.symmetric pointRadius pointPositive.le
  let slope := Bounds.Box.denseLipschitzBound polynomial pointAmbient
  have slopePositive : 0 < slope := Bounds.Box.denseLipschitzBound_pos _ _
  let rootAmbient := UniformSquareRootPreparation.rootAmbient segment
  let rootNorm := rootAmbient.normSqBound
  have rootNonnegative : 0 ≤ rootNorm := rootAmbient.normSqBound_nonneg
  let seedNorm := rootNorm / segment.clearanceBound
  have seedNonnegative : 0 ≤ seedNorm := Field.div_nonneg_direct
    rootNonnegative segment.clearanceBound_positive.le
  let rootDiameter : Coordinate := (1 / 1024) / (seedNorm + 1)
  have diameterPositive : 0 < rootDiameter := Field.div_pos_direct
    (by decide +kernel) (Arithmetic.add_pos_of_nonneg_of_pos_direct seedNonnegative (by decide))
  let clearance := UniformSquareRootPreparation.predictedClearance segment rootDiameter
  have clearancePositive : 0 < clearance := UniformSquareRootPreparation.predictedClearance_positive
    segment rootDiameter diameterPositive
  let radius := min (variationRadius segment.clearanceBound slope)
    (min (squaredVariationRadius (1 / 64) (slope * seedNorm ^ 2))
      (squaredVariationRadius clearance slope))
  have radiusPositive : 0 < radius := Basic.lt_min
    (variationRadius_positive segment.clearanceBound_positive slopePositive.le)
    (Basic.lt_min (squaredVariationRadius_positive _ _)
      (squaredVariationRadius_positive _ _))
  exact
    { pointRadius := pointRadius
      pointRadius_eq := rfl
      pointRadius_positive := pointPositive
      pointAmbient := pointAmbient
      pointAmbient_eq := rfl
      slope := slope
      slope_eq := rfl
      slope_positive := slopePositive
      rootAmbient := rootAmbient
      rootAmbient_eq := rfl
      rootNorm := rootNorm
      rootNorm_eq := rfl
      rootNorm_nonnegative := rootNonnegative
      seedNorm := seedNorm
      seedNorm_eq := rfl
      seedNorm_nonnegative := seedNonnegative
      rootDiameter := rootDiameter
      rootDiameter_eq := rfl
      rootDiameter_positive := diameterPositive
      clearance := clearance
      clearance_eq := rfl
      clearance_positive := clearancePositive
      radius := radius
      radius_eq := rfl
      radius_positive := radiusPositive }

/-- Omitting the enlargement preserves the complete original uniform-bound construction.

Every original numerical field and its specification certificate agree with
the former factory expression, including the chosen radius and preparation
floor. The original axis branch is the same specialization of this equality.
-/
theorem build_default (segment : ClearSegment polynomial ambient start finish mode) :
    build segment = (by
      let pointRadius := UniformSquareRootPreparation.segmentPointRadius segment + 1
      have pointPositive : 0 < pointRadius := Arithmetic.add_pos_of_pos_of_nonneg_direct
        (UniformSquareRootPreparation.segmentPointRadius_positive segment) (by decide)
      let pointAmbient := Box.symmetric pointRadius pointPositive.le
      let slope := Bounds.Box.denseLipschitzBound polynomial pointAmbient
      have slopePositive : 0 < slope := Bounds.Box.denseLipschitzBound_pos _ _
      let rootAmbient := UniformSquareRootPreparation.rootAmbient segment
      let rootNorm := rootAmbient.normSqBound
      have rootNonnegative : 0 ≤ rootNorm := rootAmbient.normSqBound_nonneg
      let seedNorm := rootNorm / segment.clearanceBound
      have seedNonnegative : 0 ≤ seedNorm := Field.div_nonneg_direct
        rootNonnegative segment.clearanceBound_positive.le
      let rootDiameter : Coordinate := (1 / 1024) / (seedNorm + 1)
      have diameterPositive : 0 < rootDiameter := Field.div_pos_direct
        (by decide +kernel) (Arithmetic.add_pos_of_nonneg_of_pos_direct seedNonnegative (by decide))
      let clearance := UniformSquareRootPreparation.predictedClearance segment rootDiameter
      have clearancePositive : 0 < clearance := UniformSquareRootPreparation.predictedClearance_positive
        segment rootDiameter diameterPositive
      let radius := min (variationRadius segment.clearanceBound slope)
        (min (squaredVariationRadius (1 / 64) (slope * seedNorm ^ 2))
          (squaredVariationRadius clearance slope))
      have radiusPositive : 0 < radius := Basic.lt_min
        (variationRadius_positive segment.clearanceBound_positive slopePositive.le)
        (Basic.lt_min (squaredVariationRadius_positive _ _)
          (squaredVariationRadius_positive _ _))
      exact
        { pointRadius := pointRadius
          pointRadius_eq := rfl
          pointRadius_positive := pointPositive
          pointAmbient := pointAmbient
          pointAmbient_eq := rfl
          slope := slope
          slope_eq := rfl
          slope_positive := slopePositive
          rootAmbient := rootAmbient
          rootAmbient_eq := rfl
          rootNorm := rootNorm
          rootNorm_eq := rfl
          rootNorm_nonnegative := rootNonnegative
          seedNorm := seedNorm
          seedNorm_eq := rfl
          seedNorm_nonnegative := seedNonnegative
          rootDiameter := rootDiameter
          rootDiameter_eq := rfl
          rootDiameter_positive := diameterPositive
          clearance := clearance
          clearance_eq := rfl
          clearance_positive := clearancePositive
          radius := radius
          radius_eq := rfl
          radius_positive := radiusPositive }
      : Bounds segment) := rfl

/-- Retarget the same numerical bounds to another actual segment with the identical retained frame quantities.

The scalar point radius, whole point and root ambient boxes, slope, seed
bound, diameter, preparation floor and final radius are consumed literally.
Only the original target-segment readback proofs change; no polynomial fold,
root preparation or numerical sampling is performed by this operation.
-/
def retarget (bounds : Bounds segment requested) {targetStart targetFinish : Gaussian}
    {targetMode : ClearSegment.Mode}
    (target : ClearSegment polynomial ambient targetStart targetFinish targetMode)
    (targetRequest : Option (PointRadius target))
    (samePointRadius : PointRadius.value target targetRequest = bounds.pointRadius)
    (sameRootAmbient : UniformSquareRootPreparation.rootAmbient target = bounds.rootAmbient)
    (sameFloor : target.clearanceBound = segment.clearanceBound)
    (sameClearance : UniformSquareRootPreparation.predictedClearance target bounds.rootDiameter = bounds.clearance) :
    Bounds target targetRequest :=
  { bounds with
    pointRadius_eq := samePointRadius.symm
    rootAmbient_eq := sameRootAmbient.symm
    seedNorm_eq := by rewrite [sameFloor]; exact bounds.seedNorm_eq
    clearance_eq := sameClearance.symm
    radius_eq := by rewrite [sameFloor]; exact bounds.radius_eq }

/-- Retargeting preserves the entire original radius used by every neighborhood construction. -/
theorem retarget_radius (bounds : Bounds segment requested) {targetStart targetFinish : Gaussian}
    {targetMode : ClearSegment.Mode}
    (target : ClearSegment polynomial ambient targetStart targetFinish targetMode)
    (targetRequest : Option (PointRadius target))
    (samePointRadius : PointRadius.value target targetRequest = bounds.pointRadius)
    (sameRootAmbient : UniformSquareRootPreparation.rootAmbient target = bounds.rootAmbient)
    (sameFloor : target.clearanceBound = segment.clearanceBound)
    (sameClearance : UniformSquareRootPreparation.predictedClearance target bounds.rootDiameter = bounds.clearance) :
    (bounds.retarget target targetRequest samePointRadius sameRootAmbient sameFloor sameClearance).radius =
      bounds.radius := rfl

end

open Purelib.Data.Rat in
/-- The retained uniform radius is bounded by the original observation variation radius.

The original three-radius minimum includes the observation variation radius.
Its retained cache equation gives this same scalar inclusion. -/
theorem radius_le_observation (bounds : Bounds segment requested) :
    bounds.radius ≤ variationRadius segment.clearanceBound bounds.slope := by
  rw [bounds.radius_eq]
  exact Basic.min_le_left _ _

/-- The retained uniform neighborhood radius is at most one. -/
theorem radius_le_one (bounds : Bounds segment requested) : bounds.radius ≤ 1 :=
  bounds.radius_le_observation.trans (variationRadius_le_one _ _)

section
open Purelib
open Purelib.Data.Rat
/-- The retained radius pays the uniform seed variation error within one sixty-fourth.

The original common minimum lies below the retained seed-variation radius.
Its same nonnegative slope and squared seed norm pay the displayed residual bound. -/
theorem seed_error (bounds : Bounds segment requested) :
    (bounds.slope * bounds.seedNorm ^ 2) * (8 * bounds.radius ^ 2) ≤ 1 / 64 := by
  apply (squaredVariation_error_lt (by decide +kernel)
    (Arithmetic.mul_nonneg_direct bounds.slope_positive.le
      (Arithmetic.sq_nonneg_direct _)) bounds.radius_positive.le ?_).le
  rw [bounds.radius_eq]
  exact (Basic.min_le_right _ _).trans (Basic.min_le_left _ _)

/-- Polynomial movement at the retained uniform radius is strictly below the cached continuation clearance.

The original common minimum lies below the retained movement-variation radius.
Its same positive polynomial slope pays the displayed continuation allowance. -/
theorem movement_error (bounds : Bounds segment requested) :
    bounds.slope * (8 * bounds.radius ^ 2) < bounds.clearance := by
  apply squaredVariation_error_lt bounds.clearance_positive
    bounds.slope_positive.le bounds.radius_positive.le
  rw [bounds.radius_eq]
  exact (Basic.min_le_right _ _).trans (Basic.min_le_right _ _)

end

open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- The unit observation box at every original segment parameter refines the retained enlarged point ambient box. -/
theorem observationAmbient_refines (bounds : Bounds segment requested) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (BoxTransport.centeredBox (segment.pointAt parameter) 1 (by decide)).Refines bounds.pointAmbient
      := by
  have pointInside := UniformSquareRootPreparation.segmentPointAmbient_contains segment parameter inside
  rw [bounds.pointAmbient_eq]
  change
    -bounds.pointRadius ≤ (segment.pointAt parameter).re - 1 ∧
      (segment.pointAt parameter).re + 1 ≤ bounds.pointRadius ∧
      -bounds.pointRadius ≤ (segment.pointAt parameter).im - 1 ∧
      (segment.pointAt parameter).im + 1 ≤ bounds.pointRadius
  have lower : UniformSquareRootPreparation.segmentPointRadius segment + 1 ≤ bounds.pointRadius := by
    rewrite [bounds.pointRadius_eq]
    exact PointRadius.lower segment requested
  have negative : -(UniformSquareRootPreparation.segmentPointRadius segment + 1) =
      -UniformSquareRootPreparation.segmentPointRadius segment - 1 := by ring1
  have negativeLower := Arithmetic.neg_le_neg_direct lower
  rewrite [negative] at negativeLower
  exact ⟨negativeLower.trans (Arithmetic.sub_le_sub_right_direct pointInside.1 1),
    (add_le_add pointInside.2.1 (Basic.le_refl (1 : Coordinate))).trans lower,
    negativeLower.trans (Arithmetic.sub_le_sub_right_direct pointInside.2.2.1 1),
    (add_le_add pointInside.2.2.2 (Basic.le_refl (1 : Coordinate))).trans lower⟩

open Purelib.Polynomial.Dense.Gaussian in
/-- Every original segment observation neighborhood has denominator slope bounded by the retained uniform Lipschitz
majorant. -/
theorem observationSlope_le (bounds : Bounds segment requested) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) (count : Nat) :
    (ObservationNeighborhood.ofPoint polynomial count (segment.pointAt parameter)
      (segment.pointAt_eval_ne_zero parameter inside)).denominatorSlope ≤ bounds.slope := by
  rw [bounds.slope_eq]
  exact Bounds.Box.Monotonicity.denseLipschitzBound_le_of_refines polynomial
    (bounds.observationAmbient_refines parameter inside)

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial.Dense.Gaussian in
/-- Polynomial movement within the retained uniform centered box is strictly below the cached continuation clearance. -/
theorem radius_movement (bounds : Bounds segment requested) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1) {point : Gaussian}
    (pointInside : (BoxTransport.centeredBox (segment.pointAt parameter) bounds.radius
      bounds.radius_positive.le).Contains point) :
    normSq (polynomial.eval (segment.pointAt parameter) - polynomial.eval point) < bounds.clearance := by
  have centerInside := centeredBox_center (segment.pointAt parameter) bounds.radius_positive.le
  have refines := (centeredBox_refines (segment.pointAt parameter) bounds.radius_positive.le
    (by decide) bounds.radius_le_one).trans (bounds.observationAmbient_refines parameter inside)
  have variation := Bounds.Box.normSq_eval_sub_eval_le_denseLipschitzBound polynomial
    (refines.contains centerInside) (refines.contains pointInside)
  rw [← bounds.slope_eq] at variation
  have distance := Box.normSq_sub_le_diagonalSq centerInside pointInside
  rw [BoxTransport.centeredBox_diagonalSq] at distance
  simpa only [Norm.Basic.normSq_eq_canonical] using (variation.trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
    distance bounds.slope_positive.le)).trans_lt bounds.movement_error

open Purelib.Riemann.RootContinuation in
/-- The original uniformly prepared root owner's initial box refines the retained root ambient box. -/
theorem prepared_refines (bounds : Bounds segment requested) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter))) :
    (UniformSquareRootPreparation.prepared segment parameter inside owner bounds.rootDiameter
      bounds.rootDiameter_positive).track.initial.box.Refines bounds.rootAmbient := by
  rw [UniformSquareRootPreparation.prepared_initial_box, bounds.rootAmbient_eq]
  exact (UniformSquareRootPreparation.restartInput segment parameter inside owner
    bounds.rootDiameter bounds.rootDiameter_positive).centeredBox_refines

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Riemann.RootContinuation in
/-- A sample in the original prepared root box gives an inverse seed with squared norm bounded by the retained uniform
seed majorant. -/
theorem seed_norm_le (bounds : Bounds segment requested) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter))) {sample : Gaussian}
    (sampleInside : (UniformSquareRootPreparation.prepared segment parameter inside owner
      bounds.rootDiameter bounds.rootDiameter_positive).track.initial.box.Contains sample) :
    normSq (sample * inv (polynomial.eval (segment.pointAt parameter))) ≤ bounds.seedNorm := by
  have inverseNorm := normSq_inv _ (segment.pointAt_eval_ne_zero parameter inside)
  have inverse_eq : (polynomial.eval (segment.pointAt parameter))⁻¹ = inv (polynomial.eval
    (segment.pointAt parameter)) := by
    with_unfolding_all exact rfl
  rw [inverse_eq] at inverseNorm
  rw [normSq_mul, inverseNorm, bounds.seedNorm_eq]
  have sampleBound : normSq sample ≤ bounds.rootNorm := by
    rw [bounds.rootNorm_eq]
    simpa only [Norm.Basic.normSq_eq_canonical] using Box.normSq_le_normSqBound
      ((bounds.prepared_refines parameter inside owner).contains sampleInside)
  have parameterLower := segment.clearanceBound_le_eval_normSq
    (segment.pointAt_onCertifiedLine parameter inside)
  simp only [Norm.Basic.normSq_eq_canonical] at parameterLower
  have parameterPositive := Norm.Basic.normSq_pos (segment.pointAt_eval_ne_zero parameter inside)
  rw [Norm.Basic.normSq_eq_canonical] at parameterPositive
  exact (Arithmetic.mul_le_mul_of_nonneg_right_direct sampleBound
    (Field.inv_pos_direct parameterPositive).le).trans
    (Field.div_le_div_of_nonneg_left_direct
      bounds.rootNorm_nonnegative segment.clearanceBound_positive parameterLower)

open Purelib.Riemann.RootContinuation in
set_option genInjectivity false in
/-- An aligned seed of the exact uniformly prepared original owner with a retained uniform seed-norm bound.

The explicit owner equation preserves the original prepared construction rather than merely comparing its root reading.
-/
structure PreparedSeed (bounds : Bounds segment requested) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter))) where
  /-- The original aligned seed indexed by the exact uniformly prepared owner. -/ aligned : AlignedSeed
    (UniformSquareRootPreparation.prepared segment parameter inside owner
    bounds.rootDiameter bounds.rootDiameter_positive)
  /-- The seed owner is exactly the original uniform preparation at the retained diameter. -/ owner_eq :
    aligned.seed.owner = UniformSquareRootPreparation.prepared segment parameter inside owner
    bounds.rootDiameter bounds.rootDiameter_positive
  /-- The retained seed value satisfies the original uniform squared-norm majorant. -/ norm_le : normSq
    aligned.seed.value ≤ bounds.seedNorm

constructive_injectivity PreparedSeed

namespace PreparedSeed

variable {bounds : Bounds segment requested} {parameter : Coordinate}
  {inside : 0 ≤ parameter ∧ parameter ≤ 1}
  {owner : Owner (polynomial.eval (segment.pointAt parameter))}

open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation
/-- Build a uniformly bounded aligned seed from a sample of the exact prepared owner at the retained relative residual
request.

The original prepared diameter and seed-norm majorant pay the seed-box mismatch bound, and the resulting seed retains
exactly that prepared owner. -/
def ofSample (sample : OwnerSample
    (UniformSquareRootPreparation.prepared segment parameter inside owner
      bounds.rootDiameter bounds.rootDiameter_positive)
    ((1 / 1024) * normSq (polynomial.eval (segment.pointAt parameter)))) :
    PreparedSeed bounds parameter inside owner := by
  let prepared := UniformSquareRootPreparation.prepared segment parameter inside owner
    bounds.rootDiameter bounds.rootDiameter_positive
  have sampleCoarse : normSq (sample.value * sample.value - polynomial.eval (segment.pointAt parameter)) ≤
      normSq (polynomial.eval (segment.pointAt parameter)) / 64 := by
    calc
      _ ≤ (1 / 1024 : Coordinate) * normSq (polynomial.eval (segment.pointAt parameter)) := sample.residualBound
      _ ≤ (1 / 64 : Coordinate) * normSq (polynomial.eval (segment.pointAt parameter)) :=
        Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) (normSq_nonneg
          _)
      _ = _ := by
        simp only [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.one_mul]
        ring1
  let seed := Seed.ofSample prepared sample.value sample.inside sampleCoarse
  have seedNorm : normSq seed.value ≤ bounds.seedNorm :=
    bounds.seed_norm_le parameter inside owner sample.inside
  have boxSmall : seed.owner.track.initial.box.diagonalSq * normSq seed.value ≤ 1 / 1024 := by
    calc
      _ ≤ bounds.rootDiameter * bounds.seedNorm := Arithmetic.mul_le_mul_direct
        (UniformSquareRootPreparation.prepared_diagonal_lt segment parameter inside owner
          bounds.rootDiameter_positive).le seedNorm (normSq_nonneg _) bounds.rootDiameter_positive.le
      _ ≤ bounds.rootDiameter * (bounds.seedNorm + 1) :=
        Arithmetic.mul_le_mul_of_nonneg_left_direct
          (le_add_of_nonneg_right (by decide)) bounds.rootDiameter_positive.le
      _ = 1 / 1024 := by
        rw [bounds.rootDiameter_eq]
        exact Fraction.Field.div_mul_cancel_of_ne _ _
          (Arithmetic.add_pos_of_nonneg_of_pos_direct bounds.seedNorm_nonnegative (by decide)).ne'
  exact
    { aligned := AlignedSeed.ofSeed seed prepared.track.initial.box.refines_refl
        (seed_residual_le_relative prepared.parameterNonzero sample.residualBound) boxSmall
      owner_eq := rfl
      norm_le := seedNorm }

/-- Acquire the retained relative-accuracy sample from the exact uniformly prepared owner and construct its aligned
bounded seed. -/
def acquire (bounds : Bounds segment requested) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter))) :
    PreparedSeed bounds parameter inside owner :=
  ofSample (OwnerSample.acquire
    (UniformSquareRootPreparation.prepared segment parameter inside owner
      bounds.rootDiameter bounds.rootDiameter_positive)
    ((1 / 1024) * normSq (polynomial.eval (segment.pointAt parameter)))
    (Arithmetic.mul_pos_direct (by decide +kernel)
      (by
          simpa only [Norm.Basic.normSq_eq_canonical]
            using (Norm.Basic.normSq_pos (segment.pointAt_eval_ne_zero parameter inside)))))

end PreparedSeed

open Purelib.Riemann.RootContinuation in
open Purelib.RootIsolation in
/-- All four ambient-side clearances of the exact uniformly prepared root state equal its retained contour-clearance
bound. -/
private theorem prepared_ambient_clearances (bounds : Bounds segment requested) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    (owner : Owner (polynomial.eval (segment.pointAt parameter))) :
    let initial := (UniformSquareRootPreparation.prepared segment parameter inside owner
      bounds.rootDiameter bounds.rootDiameter_positive).track.initial
    initial.ambientLeftClearance.bound = initial.clearance.bound ∧
      initial.ambientRightClearance.bound = initial.clearance.bound ∧
      initial.ambientBottomClearance.bound = initial.clearance.bound ∧
      initial.ambientTopClearance.bound = initial.clearance.bound := by
  unfold UniformSquareRootPreparation.prepared UniformSquareRootPreparation.track
    Newton.Restart.Separated.Basic.SeparatedRestartInput.centeredTrackWithMajorant Track.Newton.Build.ofInitial
  exact ⟨rfl, rfl, rfl, rfl⟩

namespace PreparedSeed

variable {bounds : Bounds segment requested} {parameter : Coordinate}
  {inside : 0 ≤ parameter ∧ parameter ≤ 1}
  {owner : Owner (polynomial.eval (segment.pointAt parameter))}

open Purelib.Data.Gaussian in
open Purelib.Data.Rat in
open Purelib.Geometry.Rational in
open Purelib.Polynomial in
open Purelib.Riemann.Readings in
/-- Construct a seeded observation neighborhood whose radius includes the retained uniform radius.

The exact original seed and observation site are preserved. Taking the larger of the uniform and previous radii reuses
the corresponding retained residual certificate on each branch. -/
def seededNeighborhood (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    SeededNeighborhood polynomial count := by
  let site := ObservationNeighborhood.ofPoint polynomial count (segment.pointAt parameter)
    (segment.pointAt_eval_ne_zero parameter inside)
  have slopeBound : site.denominatorSlope ≤ bounds.slope := bounds.observationSlope_le parameter inside count
  have valueBound : segment.clearanceBound ≤ site.denominatorValue := by
    rw [site.denominatorValue_eq]
    have center : site.center = segment.pointAt parameter := rfl
    rw [center]
    simpa only [Norm.Basic.normSq_eq_canonical] using segment.clearanceBound_le_eval_normSq
      (segment.pointAt_onCertifiedLine parameter inside)
  have siteRadius : bounds.radius ≤ site.radius := by
    rw [site.radius_eq]
    exact bounds.radius_le_observation.trans (variationRadius_le_of_bounds
      segment.clearanceBound_positive.le valueBound site.denominatorSlope_positive.le slopeBound)
  have scaleBound : site.denominatorSlope * normSq seed.aligned.seed.value ^ 2 ≤
      bounds.slope * bounds.seedNorm ^ 2 := Arithmetic.mul_le_mul_direct
    slopeBound (Arithmetic.pow_le_pow_direct (normSq_nonneg _) seed.norm_le 2)
    (Arithmetic.sq_nonneg_direct _) bounds.slope_positive.le
  have seedError : (site.denominatorSlope * normSq seed.aligned.seed.value ^ 2) * (8 * bounds.radius ^ 2) ≤ 1 / 64 :=
    (Arithmetic.mul_le_mul_of_nonneg_right_direct scaleBound
      (Arithmetic.mul_nonneg_direct (by decide)
        (Arithmetic.sq_nonneg_direct _))).trans bounds.seed_error
  let previous := SeededNeighborhood.ofSeed site seed.aligned.seed
  let radius := max bounds.radius previous.radius
  have positive : 0 < radius := bounds.radius_positive.trans_le (Basic.le_max_left _ _)
  exact SeededNeighborhood.ofRadius site seed.aligned.seed radius positive
    (Basic.max_le siteRadius previous.radius_le_site) (fun point pointInside => by
      if larger : bounds.radius ≤ previous.radius then
        have retained : previous.box.Contains point := by
          rw [previous.box_eq]
          change (BoxTransport.centeredBox site.center previous.radius
            previous.radius_positive.le).Contains point
          simpa only [radius, Basic.max_eq_right larger] using pointInside
        have residual := previous.model.residualBound point retained
        rw [previous.model.residual_eq, previous.model_value_eq,
          Dense.Basic.DensePolynomial.eval_constant] at residual
        exact residual.trans previous.model.bound_small
      else
        have retained : (BoxTransport.centeredBox site.center bounds.radius
          bounds.radius_positive.le).Contains point := by
          simpa only [radius, Basic.max_eq_left (le_of_not_ge larger)] using pointInside
        exact seed_small_on_box site seed.aligned.seed bounds.radius_positive.le
          bounds.radius_le_one seedError retained)

/-- Construct the original continued neighborhood from the retained enlarged seeded neighborhood and exact seed
alignment.

The exact enlarged seeded box and aligned original seed determine this
continued neighborhood; the original source owner and alignment evidence are reused. -/
def defaultNeighborhood (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    ContinuedNeighborhood polynomial count :=
  ContinuedNeighborhood.ofSeeded (seed.seededNeighborhood count) _ seed.aligned.refines seed.aligned.aligned

open Purelib.Riemann.RootContinuation in
/-- The original default continued neighborhood's minimum contour-and-ambient allowance equals the retained uniform
clearance.

All four ambient-side clearances of the exact uniformly prepared state
are its same contour clearance. Their unchanged nested minimum equals that retained bound. -/
theorem defaultNeighborhood_allowance (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (seed.defaultNeighborhood count).continuationAllowance = bounds.clearance := by
  change min seed.aligned.seed.owner.track.initial.clearance.bound
    (min seed.aligned.seed.owner.track.initial.ambientLeftClearance.bound
      (min seed.aligned.seed.owner.track.initial.ambientRightClearance.bound
        (min seed.aligned.seed.owner.track.initial.ambientBottomClearance.bound
          seed.aligned.seed.owner.track.initial.ambientTopClearance.bound))) = _
  rw [seed.owner_eq]
  have clearances := prepared_ambient_clearances bounds parameter inside owner
  rw [clearances.1, clearances.2.1, clearances.2.2.1, clearances.2.2.2,
    min_self, min_self, min_self, min_self,
    UniformSquareRootPreparation.prepared_clearance_bound, bounds.clearance_eq]

open Purelib.Data.Rat in
/-- Enlarge the original continued neighborhood to include the retained uniform radius while preserving its seed owner
and allowance.

The larger-radius branch uses the cached uniform movement bound; the other branch reuses the original neighborhood's
exact movement certificate. -/
def neighborhood (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    ContinuedNeighborhood polynomial count :=
  let patch := seed.defaultNeighborhood count
  let radius := max bounds.radius patch.radius
  have positive : 0 < radius := bounds.radius_positive.trans_le (Basic.le_max_left _ _)
  patch.withRadius radius positive (Basic.max_le (Basic.le_max_left _ _)
    patch.radius_le_base)
    (fun point pointInside => by
      if larger : bounds.radius ≤ patch.radius then
        apply patch.movement_small point
        rw [patch.box_eq]
        simpa only [radius, Basic.max_eq_right larger] using pointInside
      else
        rw [seed.defaultNeighborhood_allowance]
        apply bounds.radius_movement parameter inside
        have center : patch.base.site.center = segment.pointAt parameter := rfl
        rw [center] at pointInside
        simpa only [radius, Basic.max_eq_left (le_of_not_ge larger)] using pointInside)

/-- The retained continued neighborhood is centered at the exact original segment parameter point. -/
theorem neighborhood_center (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (seed.neighborhood count).base.site.center = segment.pointAt parameter := rfl

/-- The continued neighborhood retains the identical original aligned seed owner at every refinement index.

The radius enlargement changes only its region and movement certificates.
The complete original owner, ambient box, track and preparation cache remain
the same stored value.
-/
theorem neighborhood_owner (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (seed.neighborhood count).base.seed.owner = seed.aligned.seed.owner := rfl

section
open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation

/-- The continued neighborhood retains the identical complete original inverse-root seed.

The original owner, root sample, inverse value and their certificates remain
one stored seed when the observation and continuation radii are enlarged.
-/
theorem neighborhood_seed (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (seed.neighborhood count).base.seed = seed.aligned.seed := rfl

/-- The actual retained seed box has diameter at most its same neighborhood root floor divided by 256.

The original prepared diameter and seed-norm cache determine this bound.
It concerns the seed's actual reboxed owner, with no containment claim about
the independently retained source owner's original box.
-/
theorem neighborhood_diameter (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (seed.neighborhood count).base.seed.owner.track.initial.box.diagonalSq ≤
      (seed.neighborhood count).rootLower / 256 := by
  have preparedBound : seed.aligned.seed.owner.track.initial.box.diagonalSq ≤ bounds.rootDiameter := by
    rewrite [seed.owner_eq]
    exact (UniformSquareRootPreparation.prepared_diagonal_lt segment parameter inside owner
      bounds.rootDiameter_positive).le
  rewrite [seed.neighborhood_owner]
  apply preparedBound.trans
  rewrite [bounds.rootDiameter_eq, (seed.neighborhood count).rootLower_eq, seed.neighborhood_seed]
  have denominatorPositive : 0 < normSq seed.aligned.seed.value + 1 :=
    Arithmetic.add_pos_of_nonneg_of_pos_direct (normSq_nonneg _) (by decide +kernel)
  calc
    _ ≤ (1 / 1024) / (normSq seed.aligned.seed.value + 1) :=
      Field.div_le_div_of_nonneg_left_direct (by decide +kernel) denominatorPositive
        (Arithmetic.add_le_add_direct seed.norm_le (Basic.le_refl _))
    _ = _ := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      calc
        _ = ((1 / 4 : Coordinate) * (256 : Coordinate)⁻¹) *
            (normSq seed.aligned.seed.value + 1)⁻¹ :=
          congrArg (fun coefficient : Coordinate => coefficient * (normSq seed.aligned.seed.value + 1)⁻¹)
            (by decide +kernel : (1 : Coordinate) * 1024⁻¹ = (1 / 4) * 256⁻¹)
        _ = _ := by
          simp only [Fraction.Field.div_eq_mul_inv_direct]
          ring1

end

/-- The retained continued neighborhood keeps exactly the cached uniform continuation allowance. -/
theorem neighborhood_allowance (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (seed.neighborhood count).continuationAllowance = bounds.clearance :=
  seed.defaultNeighborhood_allowance count

section MovementBounds

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann.Readings.PreparedObservationNeighborhoods (variation_error_le_quarter)

/-- The exact default continuation radius leaves a strict uniform movement margin below its retained allowance.

The original minimum radius pays one quarter of its own retained allowance.
Its original positivity supplies the strict remaining margin.
-/
theorem defaultNeighborhood_movement_error (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (seed.defaultNeighborhood count).base.site.denominatorSlope *
      (8 * (seed.defaultNeighborhood count).radius ^ 2) <
        (seed.defaultNeighborhood count).continuationAllowance := by
  let patch := seed.defaultNeighborhood count
  have radiusBound : patch.radius ≤ variationRadius patch.continuationAllowance patch.base.site.denominatorSlope :=
    ContinuedNeighborhood.ofSeeded_radius_le_variation (seed.seededNeighborhood count) _
      seed.aligned.refines seed.aligned.aligned
  have paid := variation_error_le_quarter patch.base.site.denominatorSlope_positive.le
    patch.radius_positive.le radiusBound
  exact paid.trans_lt (Rat.Bounds.Quarter.quarter_lt_self patch.continuationAllowance_positive)

/-- The actual enlarged seed neighborhood retains a strict whole-box movement ceiling on its original radius.

The maximum selects either the original default continuation radius or the
original uniform segment radius. Their own retained slope and clearance
payments bound the same scalar ceiling in both cases.
-/
theorem neighborhood_movement_error (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (seed.neighborhood count).base.site.denominatorSlope *
      (8 * (seed.neighborhood count).radius ^ 2) <
        (seed.neighborhood count).continuationAllowance := by
  let patch := seed.defaultNeighborhood count
  change patch.base.site.denominatorSlope * (8 * (max bounds.radius patch.radius) ^ 2) <
    patch.continuationAllowance
  if larger : bounds.radius ≤ patch.radius then
    rewrite [Basic.max_eq_right larger]
    exact seed.defaultNeighborhood_movement_error count
  else
    have radiusBound : patch.radius ≤ bounds.radius :=
      Arithmetic.le_of_lt_direct (Arithmetic.lt_of_not_ge_direct larger)
    rewrite [Basic.max_eq_left radiusBound, seed.defaultNeighborhood_allowance count]
    have slopeBound : patch.base.site.denominatorSlope ≤ bounds.slope :=
      bounds.observationSlope_le parameter inside count
    exact (Arithmetic.mul_le_mul_of_nonneg_right_direct slopeBound
      (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 : Coordinate) ≤ 8)
        (Arithmetic.sq_nonneg_direct bounds.radius))).trans_lt bounds.movement_error

end MovementBounds

open Purelib.Data.Rat in
/-- The retained uniform radius is no larger than the constructed continued-neighborhood radius.

The neighborhood radius retains the original maximum of the uniform
and prior continued radii; its unchanged value includes the same uniform radius. -/
theorem radius_lower (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    bounds.radius ≤ (seed.neighborhood count).radius := Basic.le_max_left _ _

open Purelib.Geometry.Rational in
/-- The exact uniform centered box refines the retained continued-neighborhood box at the same original segment point.
-/
theorem uniformBox_refines (seed : PreparedSeed bounds parameter inside owner) (count : Nat) :
    (BoxTransport.centeredBox (segment.pointAt parameter) bounds.radius
      bounds.radius_positive.le).Refines (seed.neighborhood count).box := by
  rw [(seed.neighborhood count).box_eq, seed.neighborhood_center]
  exact centeredBox_refines _ bounds.radius_positive.le
    (seed.neighborhood count).radius_positive.le (seed.radius_lower count)

open Purelib.Approximation.Gaussian in
open Purelib.Riemann.RootContinuation in
/-- Compare the original root owner's certificate with the retained seed owner's certificate after exact uniform
preparation.

The seed's owner equation identifies the original prepared owner, preserving the source parameter and the retained
positive diameter request. -/
def rootEquivalent (seed : PreparedSeed bounds parameter inside owner) :
    Equivalence.NamedEquivalent
      (owner.certificate (segment.pointAt_eval_ne_zero parameter inside)).value.name
      (seed.aligned.seed.owner.certificate
        (segment.pointAt_eval_ne_zero parameter inside)).value.name := by
  rw [seed.owner_eq]
  exact SquareRootTrackEquivalence.rootEquivalent_uniformPrepare
    segment parameter inside owner bounds.rootDiameter_positive

end PreparedSeed

end Bounds

end Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
