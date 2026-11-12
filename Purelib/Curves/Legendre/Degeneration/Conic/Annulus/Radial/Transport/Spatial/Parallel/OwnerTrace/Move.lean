module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Riemann.RootContinuation.UniformSquareRootPreparation
import Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Geometry.Rational.Box.Hull
import Purelib.Geometry.Rational.Box.Point
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathParentCaches
public import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Programs
import Purelib.Geometry.Path.Gaussian.Lifted.Basic
import Purelib.Riemann.Paths.PreparedPathParentContainment
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Primitive
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive
import Purelib.Riemann.Normalization.ContinuedInverseRoot.Primitive.Request
import Purelib.Polynomial.Dense.Power
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Power
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.List.Membership
import Purelib.Data.List.DependentProduct
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.RootIsolation.SquareRoot.Owner.Transport
import Purelib.Tactic.Ring

/-! # Paid owner moves and their retained primitive comparisons

One common numerical preparation frame and one original finite search pay
every actual affine chart chord. Original one-time preparations, actual
paid targets, signed residual comparisons and all-future OwnerLinks remain
cached beside the same original Reading, Geometry, Edge and Chain banks.
Each move retains the original owner continuation and its actual primitive comparisons.

This construction concerns the computed affine-chord path. Comparing it to
the independently prepared spatial L-route Blocks, cyclic seams, geometric
twist assembly and period transport remain separate mathematical operations.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Approximation.Rational
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods.Bounds (PointRadius)

open Purelib.Data.Rat.Fraction.Order
open Purelib.Data.Rat.Fraction.Cast.Order (natCast_pos_direct natCast_le_direct)

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic.Canonical (normSq)
open Purelib.Data.Rat
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.Paths
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerTail OwnerJoin ownerApproximation)
open Purelib.Riemann.Branches.PreparedSheetContinuation (StepRequest CachedSource)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Polynomial.Clearance.Box.Region (RegionClearance)
open Purelib.Approximation
open Purelib.RootIsolation.SquareRoot.Owner
open Purelib.Integration.Path.Dyadic
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells (Model)

variable {site : Fin 2} {parameter : Canonical} {quarter : UnitCircuitQuarter}

namespace OwnerBudget

/-- The positive root-box diameter used before each actual parallel-chart move. -/
@[expose] def diameter (site : Fin 2) (parameter : Canonical) : Fraction.Rational :=
  Radial.Clearance.rootFloor site parameter / 1024

/-- Regularity makes the common actual source-preparation diameter positive. -/
theorem diameter_positive (regular : parameter ≠ criticalValue site) : 0 < diameter site parameter :=
  Fraction.Order.Field.div_pos_direct (Radial.Clearance.rootFloor_positive site parameter regular)
    (natCast_pos_direct (n := 1024) (by decide +kernel))

/-- The actual original preparation request uses the genuine target endpoint and common root-box diameter. -/
@[expose] def request (regular : parameter ≠ criticalValue site) : StepRequest :=
  ⟨Riemann.Branches.ClearSheetContinuation.Subdivision.Endpoint.last,
    diameter site parameter, diameter_positive regular⟩

/-- The original move request retains the exact common source-diameter allowance. -/
theorem request_diameter (regular : parameter ≠ criticalValue site) :
    (request regular).rootDiameter = Radial.Clearance.rootFloor site parameter / 1024 := rfl

/-- The retained original source region-clearance cache at the genuine start of this Leg. -/
@[expose] def SourceClearance (leg : Leg site parameter quarter) : Type :=
  {retained : RegionClearance (Paths.polynomial parameter)
      (box site parameter quarter 0 leg.regular) //
    retained = Radial.Clearance.clearance site parameter (Waist.direction quarter 0)
      leg.regular leg.actual.data.bound}

/-- A stationary genuine source chord fixes only the common numerical preparation frame.

The endpoints are the original Leg's actual source coordinate. Its complete
region clearance and original whole ambient Horner cache are supplied and
retained by the original affine constructor. No root owner is created here.
-/
@[expose] def frame (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (clearance : SourceClearance leg) :
    ClearSegment (Paths.polynomial parameter) (spatialBox site)
      (coordinate site parameter 2 quarter (by decide +kernel) 0)
      (coordinate site parameter 2 quarter (by decide +kernel) 0) .region :=
  let within := point_inside site parameter 2 (Waist.direction quarter 0) (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper leg.actual.data.bound
  .affine _ _ (box site parameter quarter 0 leg.regular) ⟨within, within⟩ clearance.val
    (source_inside leg.regular) (source_inside leg.regular) coarse.bounds coarse.bounds_eq

/-- The cached numerical frame floor remains linked to the exact original preparation operation. -/
@[expose] def Floor (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (clearance : SourceClearance leg) : Type :=
  {retained : Fraction.Rational // retained = UniformSquareRootPreparation.predictedClearance
    (frame leg coarse clearance) (diameter site parameter)}

/-- The retained actual frame floor is positive by the original uniform preparation theorem. -/
theorem floor_positive {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
    {clearance : SourceClearance leg} (floor : Floor leg coarse clearance) : 0 < floor.val := by
  rewrite [floor.property]
  exact UniformSquareRootPreparation.predictedClearance_positive _ _ (diameter_positive leg.regular)

section

open Purelib.Riemann.Integration
open Purelib.Geometry.Rational (Box)

/-- Original uniform primitive bounds in the same retained source frame with one whole-ambient point radius.

The exact original Bounds owner stores the common point and root ambients,
polynomial slope, seed ceiling and preparation radius. It is a numerical
cache over the actual Leg and whole original Horner record, not a new root
owner or a certificate of target agreement.
-/
@[expose] def PrimitiveBounds (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (clearance : SourceClearance leg) : Type :=
  UniformPrimitiveNeighborhoods.Bounds (frame leg coarse clearance)
    (some (PointRadius.ofAmbient (frame leg coarse clearance) True.intro))

/-- Compute the original whole-ambient primitive cache once on the actual retained Leg frame. -/
@[expose] def primitiveBounds (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (clearance : SourceClearance leg) : PrimitiveBounds leg coarse clearance :=
  UniformPrimitiveNeighborhoods.Bounds.build (frame leg coarse clearance)
    (some (PointRadius.ofAmbient (frame leg coarse clearance) True.intro))

namespace PrimitiveBounds

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg} {clearance : SourceClearance leg}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}

/-- Consume the same complete numerical primitive cache on an actual retained chord of this original Leg.

Both genuine region segments carry the same original ambient Horner record
and the proved intrinsic clearance floor. Their ambient point-radius choice
is identical, so every numerical bound and the final positive radius are
retained while the segment-specific readback proofs are transported.
-/
@[expose] def chord (cached : PrimitiveBounds leg coarse clearance)
    (geometry : Geometry reading targetReading leg.regular payment) :
    UniformPrimitiveNeighborhoods.Bounds (geometry.chord coarse.bounds coarse.bounds_eq)
      (some (PointRadius.ofAmbient
        (geometry.chord coarse.bounds coarse.bounds_eq) True.intro)) := by
  apply cached.retarget (geometry.chord coarse.bounds coarse.bounds_eq)
    (some (PointRadius.ofAmbient
      (geometry.chord coarse.bounds coarse.bounds_eq) True.intro))
  · exact (PointRadius.ofAmbient_value
      (geometry.chord coarse.bounds coarse.bounds_eq) True.intro).trans
        (cached.pointRadius_eq.trans
          (PointRadius.ofAmbient_value (frame leg coarse clearance)
            True.intro)).symm
  · rewrite [cached.rootAmbient_eq]
    unfold Geometry.chord frame UniformSquareRootPreparation.rootAmbient
      UniformSquareRootPreparation.rootAmbientRadius UniformSquareRootPreparation.rootSampleCoordinateRadius
      UniformSquareRootPreparation.radicandNormBound
    rfl
  · unfold Geometry.chord frame
    change geometry.clearance.bound = clearance.val.bound
    rewrite [geometry.clearance_eq, clearance.property]
    rfl
  · rewrite [cached.clearance_eq]
    unfold Geometry.chord frame
    apply UniformSquareRootPreparation.predictedClearance_affine_eq
    rewrite [geometry.clearance_eq, clearance.property]
    rfl

/-- Every actual chord consumes exactly the radius cached once on the original source frame. -/
theorem chord_radius (cached : PrimitiveBounds leg coarse clearance)
    (geometry : Geometry reading targetReading leg.regular payment) :
    (cached.chord geometry).radius = cached.radius := by
  dsimp only [chord, UniformPrimitiveNeighborhoods.Bounds.retarget]

/-- The positive squared common primitive radius as an original numerical accuracy request. -/
@[expose] def radiusRequest (cached : PrimitiveBounds leg coarse clearance) : AccuracyRequest :=
  ⟨cached.radius ^ 2, Arithmetic.pow_pos_direct cached.radius_positive 2⟩

/-- A computed chart-time allowance putting intrinsic base movement within the same cached primitive radius.

The exact original residual/time request is applied to the squared radius and
the intrinsic quarter movement scale. Its positive finite tolerance depends
only on the retained Leg and numerical cache, before any root or edge is
selected.
-/
@[expose] def timeRequest (cached : PrimitiveBounds leg coarse clearance) : AccuracyRequest :=
  leg.source.residualTimeRequest cached.radiusRequest
    ((25 / 4) * Norm.Basic.normSq (halfGap site parameter))
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _))

/-- A stronger original Leg request paying the computed common-domain time allowance. -/
@[expose] def accuracy (cached : PrimitiveBounds leg coarse clearance) : Leg.TraceAccuracy leg :=
  ⟨⟨min (leg.source.traceRequest leg.regular).tolerance cached.timeRequest.tolerance,
    Fraction.Order.Basic.lt_min (leg.source.traceRequest leg.regular).positive cached.timeRequest.positive⟩,
    Fraction.Order.Basic.min_le_left _ _⟩

/-- Select an actual original finite Leg budget consuming the same whole coarse Horner cache and common-domain request.

The original bounded geometric search retains every ceiling, stage and
payment. This operation constructs a refinement request; it does not replace
a previously supplied OwnerTrace or assert equality of distinct path integrals.
-/
@[expose] def traceBudget (cached : PrimitiveBounds leg coarse clearance) : Leg.TraceBudget leg cached.accuracy :=
  Leg.TraceBudget.ofBounds leg coarse.bounds coarse.bounds_eq cached.accuracy

/-- The computed common-domain budget retains the identical original whole Horner value. -/
theorem traceBudget_bounds (cached : PrimitiveBounds leg coarse clearance) :
    cached.traceBudget.bounds = coarse.bounds := by
  dsimp only [traceBudget, Leg.TraceBudget.ofBounds, Leg.TraceBudget.bounds]

/-- Every actually selected stronger edge fits the intrinsic base-movement radius.

The original finite Selection pays the nested residual/time request. Direct
positive denominator bounds weaken that payment to the stored common-domain
request, whose original payment law gives the displayed squared-distance scale.
-/
theorem base_paid (cached : PrimitiveBounds leg coarse clearance)
    (refined : Leg.TraceBudget leg cached.accuracy)
    (edge : Fin (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1).length) :
    ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) *
      (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
        DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 <
      cached.radius ^ 2 := by
  have movementNonnegative := leg.traceMovement_nonnegative refined.bounds refined.bounds_eq
  have requestBound := leg.source.residualTimeRequest_le cached.accuracy.val
    (leg.traceMovement refined.bounds) movementNonnegative
  have paid := ((refined.edge_paid_lt edge).trans_le requestBound).trans_le
    (show cached.accuracy.val.tolerance ≤ cached.timeRequest.tolerance from
      Fraction.Order.Basic.min_le_right _ _)
  exact leg.source.residualTimeRequest_pays_lt cached.radiusRequest
    ((25 / 4) * Norm.Basic.normSq (halfGap site parameter))
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)) _ paid

/-- Every curved-quarter point of a selected stronger interval lies in the actual common centered primitive domain.

The original quarter coordinate estimate and interval ordering derive the
squared displacement bound internally from the actual finite Selection.
No successful model-coverage or root-comparison premise is supplied.
-/
theorem curve_inside (cached : PrimitiveBounds leg coarse clearance)
    (refined : Leg.TraceBudget leg cached.accuracy)
    (edge : Fin (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1).length)
    (time : Fraction.Rational)
    (between :
      DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc ≤ time ∧
      time ≤ DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.succ) :
    (Box.Square.Centered.BoxTransport.centeredBox
      (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc))
      cached.radius cached.radius_positive.le).Contains
        (coordinate site parameter 2 quarter (by decide +kernel) time) := by
  apply Box.Square.Centered.centeredBox_contains_of_normSq_sub_le cached.radius_positive.le
  have distance := quarter_base_distance_le site parameter 2 quarter (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper time
    (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc)
  have width := Arithmetic.pow_le_pow_direct
    (Arithmetic.sub_nonneg_direct between.1)
    (Arithmetic.sub_le_sub_right_direct between.2 _) 2
  have bounded := distance.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct width
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)))
  have signedWidth :
      (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.succ -
        DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc) ^ 2 =
      (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
        DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 := by
    ring1
  rewrite [signedWidth] at bounded
  exact bounded.trans (cached.base_paid refined edge).le

/-- Every point of the actual stronger edge's endpoint rectangle lies in the same common primitive domain.

The actual endpoint point boxes and their retained hull give the displacement
bound, including degenerate edges. Original spatial-route confinement can
therefore consume this certificate without replacing either endpoint.
-/
theorem hull_inside (cached : PrimitiveBounds leg coarse clearance)
    (refined : Leg.TraceBudget leg cached.accuracy)
    (edge : Fin (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1).length)
    (value : Canonical)
    (inside : (Box.Hull.hull
      (Box.Point.pointBox (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc)))
      (Box.Point.pointBox (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1)
          edge.succ)))).Contains value) :
    (Box.Square.Centered.BoxTransport.centeredBox
      (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc))
      cached.radius cached.radius_positive.le).Contains value := by
  apply Box.Square.Centered.centeredBox_contains_of_normSq_sub_le cached.radius_positive.le
  have displacement := Box.normSq_sub_le_diagonalSq inside
    (Box.Hull.hull_contains_left (Box.Point.pointBox_contains
      (coordinate site parameter 2 quarter (by decide +kernel)
        (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc))))
  rewrite [Box.Hull.pointBoxes_diagonalSq] at displacement
  have distance := quarter_base_distance_le site parameter 2 quarter (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper
    (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.succ)
    (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc)
  have signedWidth :
      (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.succ -
        DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc) ^ 2 =
      (DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.castSucc -
        DyadicTrace.indexed 0 (DyadicTrace.tail refined.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 := by
    ring1
  rewrite [signedWidth] at distance
  exact (displacement.trans distance).trans (cached.base_paid refined edge).le

end PrimitiveBounds

end

/-- One exact residual request pays the original edge, root margin, actual owner preparation and signed alignment.

The preparation floor is retained executable data. It bounds each actual
cached prepared source through the same original prediction law; it is not
an assumption about an inherited owner or a future successful trace.
-/
@[expose] def accuracy (leg : Leg site parameter quarter) {coarse : Leg.TraceBudget leg}
    {clearance : SourceClearance leg} (floor : Floor leg coarse clearance)
    (limit : Option AccuracyRequest := none) : Leg.TraceAccuracy leg :=
  let retained : Leg.TraceAccuracy leg :=
    let lower := Radial.Clearance.rootFloor site parameter
    let pair := (lower / 64) * leg.source.traceSumFloor / 16
    have lowerPositive := Radial.Clearance.rootFloor_positive site parameter leg.regular
    have pairPositive : 0 < pair := Fraction.Order.Field.div_pos_direct
      (Arithmetic.mul_pos_direct
        (Fraction.Order.Field.div_pos_direct lowerPositive (by decide +kernel))
        (leg.source.traceFloors_positive leg.regular).2) (by decide +kernel)
    ⟨⟨min (leg.source.traceRequest leg.regular).tolerance
        (min (lower ^ 2 / 1024) (min floor.val pair)),
      Fraction.Order.Basic.lt_min (leg.source.traceRequest leg.regular).positive
        (Fraction.Order.Basic.lt_min
          (Fraction.Order.Field.div_pos_direct (Arithmetic.pow_pos_direct lowerPositive 2)
            (by decide +kernel))
          (Fraction.Order.Basic.lt_min (floor_positive floor) pairPositive))⟩,
      Fraction.Order.Basic.min_le_left _ _⟩
  match limit with
  | none => retained
  | some request =>
      ⟨⟨min retained.val.tolerance request.tolerance,
        Fraction.Order.Basic.lt_min retained.val.positive request.positive⟩,
        (Fraction.Order.Basic.min_le_left _ _).trans retained.property⟩

/-- The omitted cap retains the complete original owner-preparation and signed-selection request. -/
theorem accuracy_default (leg : Leg site parameter quarter) {coarse : Leg.TraceBudget leg}
    {clearance : SourceClearance leg} (floor : Floor leg coarse clearance) :
    accuracy leg floor none = (
    let lower := Radial.Clearance.rootFloor site parameter
    let pair := (lower / 64) * leg.source.traceSumFloor / 16
    have lowerPositive := Radial.Clearance.rootFloor_positive site parameter leg.regular
    have pairPositive : 0 < pair := Fraction.Order.Field.div_pos_direct
      (Arithmetic.mul_pos_direct
        (Fraction.Order.Field.div_pos_direct lowerPositive (by decide +kernel))
        (leg.source.traceFloors_positive leg.regular).2) (by decide +kernel)
    ⟨⟨min (leg.source.traceRequest leg.regular).tolerance
        (min (lower ^ 2 / 1024) (min floor.val pair)),
      Fraction.Order.Basic.lt_min (leg.source.traceRequest leg.regular).positive
        (Fraction.Order.Basic.lt_min
          (Fraction.Order.Field.div_pos_direct (Arithmetic.pow_pos_direct lowerPositive 2)
            (by decide +kernel))
          (Fraction.Order.Basic.lt_min (floor_positive floor) pairPositive))⟩,
      Fraction.Order.Basic.min_le_left _ _⟩
      : Leg.TraceAccuracy leg) := rfl

/-- Every capped request retains all bounds of the complete original owner request. -/
theorem accuracy_le_default (leg : Leg site parameter quarter) {coarse : Leg.TraceBudget leg}
    {clearance : SourceClearance leg} (floor : Floor leg coarse clearance) (limit : Option AccuracyRequest) :
    (accuracy leg floor limit).val.tolerance ≤ (accuracy leg floor none).val.tolerance := by
  cases limit with
  | none => exact Fraction.Order.Basic.le_refl _
  | some request => exact Fraction.Order.Basic.min_le_left _ _

/-- A supplied positive cap bounds the same actual original owner request. -/
theorem accuracy_le_limit (leg : Leg site parameter quarter) {coarse : Leg.TraceBudget leg}
    {clearance : SourceClearance leg} (floor : Floor leg coarse clearance) (request : AccuracyRequest) :
    (accuracy leg floor (some request)).val.tolerance ≤ request.tolerance :=
  Fraction.Order.Basic.min_le_right _ _

end OwnerBudget

variable {limit : Option AccuracyRequest}

/-- The original refined TraceBudget with its actual source clearance and numerical preparation floor retained once.

The coarse budget's entire original Horner cache is consumed unchanged. Its
old numerical selection is not used for owner moves. No coarse interior
Reading or sample table is constructed. The finer table is materialized only
after this bounded selection, retaining the original Leg's endpoint Readings.
-/
@[expose] def OwnerBudget (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (limit : optParam (Option AccuracyRequest) none) : Type :=
  Σ clearance : OwnerBudget.SourceClearance leg,
  Σ floor : OwnerBudget.Floor leg coarse clearance,
    {retained : Leg.TraceBudget leg (OwnerBudget.accuracy leg floor limit) //
      retained = Leg.TraceBudget.ofBounds leg coarse.bounds coarse.bounds_eq (OwnerBudget.accuracy leg floor limit)}

namespace OwnerBudget

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}

/-- Compute the genuine source clearance, common preparation floor and one refined finite selection. -/
@[expose] def build (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg)
    (limit : Option AccuracyRequest := none) : OwnerBudget leg coarse limit :=
  let clearance : SourceClearance leg := ⟨Radial.Clearance.clearance site parameter (Waist.direction quarter 0)
    leg.regular leg.actual.data.bound, rfl⟩
  let floor : Floor leg coarse clearance :=
    ⟨UniformSquareRootPreparation.predictedClearance (frame leg coarse clearance) (diameter site parameter), rfl⟩
  let fine := Leg.TraceBudget.ofBounds leg coarse.bounds coarse.bounds_eq (accuracy leg floor limit)
  ⟨clearance, floor, ⟨fine, rfl⟩⟩

/-- The omitted cap retains the complete original budget factory, numerical caches and bounded search. -/
theorem build_default (leg : Leg site parameter quarter) (coarse : Leg.TraceBudget leg) :
    build leg coarse none = (
    let clearance : SourceClearance leg := ⟨Radial.Clearance.clearance site parameter (Waist.direction quarter 0)
      leg.regular leg.actual.data.bound, rfl⟩
    let floor : Floor leg coarse clearance :=
      ⟨UniformSquareRootPreparation.predictedClearance (frame leg coarse clearance) (diameter site parameter), rfl⟩
    let fine := Leg.TraceBudget.ofBounds leg coarse.bounds coarse.bounds_eq (accuracy leg floor)
    ⟨clearance, floor, ⟨fine, rfl⟩⟩
      : OwnerBudget leg coarse) := rfl

/-- Read the exact original source-region clearance stored by this actual budget. -/
@[expose] def clearance (budget : OwnerBudget leg coarse limit) : SourceClearance leg := budget.1

/-- Read the actual original numerical preparation floor without recomputing it for a chord. -/
@[expose] def floor (budget : OwnerBudget leg coarse limit) : Floor leg coarse budget.clearance := budget.2.1

/-- Read the same actual refined original budget and its retained bounded search. -/
@[expose] def fine (budget : OwnerBudget leg coarse limit) : Leg.TraceBudget leg (accuracy leg budget.floor limit) :=
  budget.2.2.val

/-- The complete refined budget is the original factory consuming the identical retained coarse Horner cache. -/
theorem fine_eq (budget : OwnerBudget leg coarse limit) : budget.fine =
    Leg.TraceBudget.ofBounds leg coarse.bounds coarse.bounds_eq (accuracy leg budget.floor limit) := budget.2.2.property

/-- Every chord consumes the identical whole Horner cache rather than recomputing the original fold. -/
theorem fine_bounds (budget : OwnerBudget leg coarse limit) : budget.fine.bounds = coarse.bounds := by
  exact (congrArg Leg.TraceBudget.bounds budget.fine_eq).trans
    (Leg.TraceBudget.ofBounds_bounds leg coarse.bounds coarse.bounds_eq (accuracy leg budget.floor limit))

/-- The actual selected depth has the original finite fuel bound at the stronger computed request. -/
theorem depth_le (budget : OwnerBudget leg coarse limit) :
    budget.fine.selection.stage ≤ 7 + budget.fine.selection.fuel := budget.fine.depth_le

/-- The actual residual tolerance is below the retained preparation floor. -/
theorem tolerance_le_floor (budget : OwnerBudget leg coarse limit) :
    (accuracy leg budget.floor limit).val.tolerance ≤ budget.floor.val :=
  (accuracy_le_default leg budget.floor limit).trans
    ((Fraction.Order.Basic.min_le_right _ _).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _)))

/-- The actual residual tolerance pays the common owner-reading squared margin. -/
theorem tolerance_le_root (budget : OwnerBudget leg coarse limit) :
    (accuracy leg budget.floor limit).val.tolerance ≤ Radial.Clearance.rootFloor site parameter ^ 2 / 1024 :=
  (accuracy_le_default leg budget.floor limit).trans
    ((Fraction.Order.Basic.min_le_right _ _).trans (Fraction.Order.Basic.min_le_left _ _))

/-- Every bounded actual fine-mesh movement strictly fits the common actual-preparation floor. -/
theorem edge_movement_lt (budget : OwnerBudget leg coarse limit)
    (edge : Fin (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :
    leg.traceMovement coarse.bounds *
      (DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage 0 1) edge.castSucc -
        DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 <
      budget.floor.val := by
  have retained := (budget.fine.movement_paid_lt edge).trans_le budget.tolerance_le_floor
  have same := congrArg (fun bounds => leg.traceMovement bounds *
    (DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage 0 1) edge.castSucc -
      DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage 0 1) edge.succ) ^ 2)
    budget.fine_bounds
  exact same.symm.le.trans_lt retained

/-- Every bounded actual fine-mesh movement pays the common owner-link margin. -/
theorem edge_movement_root (budget : OwnerBudget leg coarse limit)
    (edge : Fin (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1).length) :
    leg.traceMovement coarse.bounds *
      (DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage 0 1) edge.castSucc -
        DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage (0 : Fraction.Rational) 1) edge.succ) ^ 2 ≤
      Radial.Clearance.rootFloor site parameter ^ 2 / 1024 := by
  have retained := (budget.fine.movement_paid_lt edge).le.trans budget.tolerance_le_root
  have same := congrArg (fun bounds => leg.traceMovement bounds *
    (DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage 0 1) edge.castSucc -
      DyadicTrace.indexed 0 (DyadicTrace.tail budget.fine.selection.stage 0 1) edge.succ) ^ 2)
    budget.fine_bounds
  exact same.symm.le.trans retained

/-- Every actual affine chart chord has the identical retained numerical preparation floor.

The whole original Horner cache is shared and both actual region clearances
carry the same proved full-cubic lower bound. Only the scalar preparation
formula is equated; the actual region boxes and root owners stay distinct.
-/
theorem chord_floor (budget : OwnerBudget leg coarse limit)
    {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
    {lastInside : FixedRootBoxPath.Inside last}
    {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
    {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (geometry : Geometry reading targetReading leg.regular payment) :
    UniformSquareRootPreparation.predictedClearance (geometry.chord coarse.bounds coarse.bounds_eq)
      (diameter site parameter) = budget.floor.val := by
  rewrite [budget.floor.property]
  unfold Geometry.chord frame
  apply UniformSquareRootPreparation.predictedClearance_affine_eq
  rewrite [geometry.clearance_eq, budget.clearance.property]
  rfl

/-- The retained common floor bounds the clearance of this very cached prepared source owner.

The inherited owner's original box may be arbitrarily small. This bound is
for the actual one-time preparation cache, before creating the target owner,
using the original prepared-clearance theorem and the shared numerical frame.
-/
theorem floor_le_prepared (budget : OwnerBudget leg coarse limit)
    {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
    {lastInside : FixedRootBoxPath.Inside last}
    {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
    {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (geometry : Geometry reading targetReading leg.regular payment)
    (source : Owner ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first)))
    (cached : Riemann.Branches.PreparedSheetContinuation.CachedSource.Start
      (geometry.chord coarse.bounds coarse.bounds_eq) source (request leg.regular)) :
    budget.floor.val ≤ (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached).track.initial.clearance.bound :=
  (budget.chord_floor geometry).symm.le.trans (CachedSource.startPrepared_clearance
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached)

end OwnerBudget

namespace OwnerBudget

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}

/-- The actual complete original source cache on one retained affine chart chord. -/
@[expose] def StartCache (_budget : OwnerBudget leg coarse limit)
    (geometry : Geometry reading targetReading leg.regular payment)
    (source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))) :
    Type :=
  CachedSource.Start (geometry.chord coarse.bounds coarse.bounds_eq) source (request leg.regular)

/-- The original region-clearance certificate proves nonvanishing at the actual target before the move. -/
theorem target_nonzero (geometry : Geometry reading targetReading leg.regular payment) :
    (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) last) ≠ 0 :=
  geometry.clearance.eval_ne_zero (target_inside leg.regular payment)

/-- A computed strong time payment fits this actual prepared source's unchanged original clearance. -/
theorem move_small (budget : OwnerBudget leg coarse limit)
    (geometry : Geometry reading targetReading leg.regular payment)
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))}
    (cached : StartCache budget geometry source)
    (paid : leg.traceMovement coarse.bounds * (first - last) ^ 2 < (accuracy leg budget.floor limit).val.tolerance) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first) -
      (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) last)) <
      (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached).track.initial.clearance.bound := by
  have movement := coarse.movement_endpoints first last
  change Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first) -
    (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) last)) ≤
      leg.traceMovement coarse.bounds * (first - last) ^ 2 at movement
  exact (movement.trans_lt (paid.trans_le budget.tolerance_le_floor)).trans_le
    (budget.floor_le_prepared geometry source cached)

/-- The actual prepared-source sample margin pays the source diameter used by an original OwnerLink. -/
theorem prepared_link_diameter (budget : OwnerBudget leg coarse limit)
    (geometry : Geometry reading targetReading leg.regular payment)
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))}
    (cached : StartCache budget geometry source) :
    (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached).track.initial.box.diagonalSq ≤
      Radial.Clearance.rootFloor site parameter / 1024 :=
  (CachedSource.startPrepared_diagonal
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached).le

/-- The same prepared source has the signed-selection diameter for every actual owner in its retained spatial square.

The original source cache supplies its diameter, and the full-cubic region
floor bounds the supplied owner's own apartness. The owner may lie at any
contained point; it is not reconstructed from the region certificate.
-/
theorem prepared_small_on_box (budget : OwnerBudget leg coarse limit)
    (geometry : Geometry reading targetReading leg.regular payment)
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))}
    (cached : StartCache budget geometry source) {point : Canonical}
    (inside : (box site parameter quarter first leg.regular).Contains point)
    (target : Owner ((Paths.polynomial parameter).eval point)) :
    (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached).track.initial.box.diagonalSq ≤
      (target.certificate target.parameterNonzero).apart.certificate.lowerSq / 16 := by
  have targetLower := Radial.Clearance.rootFloor_le_owner site parameter (Waist.direction quarter first)
    leg.regular leg.actual.data.bound inside target
  exact (budget.prepared_link_diameter geometry cached).trans
    ((Fraction.Order.Field.div_le_div_of_nonneg_left_direct
      (Radial.Clearance.rootFloor_positive site parameter leg.regular).le
      (natCast_pos_direct (n := 16) (by decide +kernel))
      (natCast_le_direct (m := 16) (n := 1024) (by decide +kernel))).trans
      (Fraction.Order.Field.divide_mono targetLower (by decide +kernel)))

/-- The same actual source preparation is small enough for every actual target certificate's signed selection scale. -/
theorem prepared_small (budget : OwnerBudget leg coarse limit)
    (geometry : Geometry reading targetReading leg.regular payment)
    {source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))}
    (cached : StartCache budget geometry source)
    (target : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) last))) :
    (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached).track.initial.box.diagonalSq ≤
      (target.certificate target.parameterNonzero).apart.certificate.lowerSq / 16 :=
  budget.prepared_small_on_box geometry cached (target_inside leg.regular payment) target

/-- The computed strong request pays signed comparison with any actual owner in the retained source square. -/
theorem tolerance_le_pair_on_box (budget : OwnerBudget leg coarse limit)
    (_geometry : Geometry reading targetReading leg.regular payment)
    {point : Canonical} (inside : (box site parameter quarter first leg.regular).Contains point)
    (target : Owner ((Paths.polynomial parameter).eval point)) :
    (accuracy leg budget.floor limit).val.tolerance ≤
      (reading.pairRequest leg.regular (Reading.ownerDistance target)).tolerance := by
  have targetLower := Radial.Clearance.rootFloor_le_owner site parameter (Waist.direction quarter first)
    leg.regular leg.actual.data.bound inside target
  have selected : (accuracy leg budget.floor limit).val.tolerance ≤
      (Radial.Clearance.rootFloor site parameter / 64) * reading.traceSumFloor / 16 :=
    (accuracy_le_default leg budget.floor limit).trans
      ((Fraction.Order.Basic.min_le_right _ _).trans ((Fraction.Order.Basic.min_le_right _ _).trans
        (Fraction.Order.Basic.min_le_right _ _)))
  exact selected.trans (Fraction.Order.Field.divide_mono
    (Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Fraction.Order.Field.divide_mono targetLower (by decide +kernel))
      (reading.traceFloors_positive leg.regular).2.le) (by decide +kernel))

/-- The computed strong residual request pays signed comparison with this actual target owner. -/
theorem tolerance_le_pair (budget : OwnerBudget leg coarse limit)
    (_geometry : Geometry reading targetReading leg.regular payment)
    (target : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) last))) :
    (accuracy leg budget.floor limit).val.tolerance ≤
      (reading.pairRequest leg.regular (Reading.ownerDistance target)).tolerance :=
  budget.tolerance_le_pair_on_box _geometry (target_inside leg.regular payment) target

/-- The actual finite chart-time payment is also valid for the computed signed owner-selection request. -/
theorem pair_paid (budget : OwnerBudget leg coarse limit)
    (geometry : Geometry reading targetReading leg.regular payment)
    (target : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) last)))
    (paid : (first - last) ^ 2 < (leg.source.residualTimeRequest (accuracy leg budget.floor limit).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance) :
    (first - last) ^ 2 ≤ (reading.residualTimeRequest
      (reading.pairRequest leg.regular (Reading.ownerDistance target)) (leg.traceMovement coarse.bounds)
      (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance :=
  paid.le.trans (reading.residualTimeRequest_mono _ _ (budget.tolerance_le_pair geometry target)
    (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq))

end OwnerBudget

namespace OwnerMove

/-- The exact original source preparation cache with its complete production identity. -/
@[expose] def Preparation {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
    (budget : OwnerBudget leg coarse limit)
    {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
    {lastInside : FixedRootBoxPath.Inside last}
    {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
    {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (geometry : Geometry reading targetReading leg.regular payment)
    (source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))) : Type :=
  {retained : OwnerBudget.StartCache budget geometry source //
    retained = CachedSource.atStart
      (geometry.chord coarse.bounds coarse.bounds_eq) source (OwnerBudget.request leg.regular)}

/-- The original complete same-point join cache with its production identity. -/
@[expose] def Join {parameter : Canonical} (left right : Owner parameter)
    (agreement : NamedEquivalent
      (left.certificate left.parameterNonzero).value.name
      (right.certificate right.parameterNonzero).value.name) : Type :=
  {retained : OwnerJoin left right // retained = OwnerJoin.acquire left right agreement}

/-- The actual original paid target owner with its exact movement equation. -/
@[expose] def Target {sourceParameter targetParameter : Canonical} (source : Owner sourceParameter)
    (nonzero : targetParameter ≠ 0)
    (small : Norm.Basic.normSq (sourceParameter - targetParameter) <
      source.track.initial.clearance.bound) : Type :=
  {retained : Owner targetParameter // retained = source.advance
    (source := sourceParameter) (target := targetParameter) nonzero small}

namespace Target

/-- The exact original paid target refines the same supplied source's original box. -/
theorem refines {sourceParameter targetParameter : Canonical} {source : Owner sourceParameter}
    {nonzero : targetParameter ≠ 0}
    {small : Norm.Basic.normSq (sourceParameter - targetParameter) <
      source.track.initial.clearance.bound}
    (target : Target source nonzero small) : target.val.track.initial.box.Refines source.track.initial.box := by
  have equal := congrArg (fun retained : Owner targetParameter => retained.track.initial.box) target.property
  have completed := source.advance_initial_box_refines
    (source := sourceParameter) (target := targetParameter) nonzero small
  exact equal.symm ▸ completed

end Target

/-- The whole original acquired owner tail with its exact acquisition equation. -/
@[expose] def Tail {parameter : Canonical} (owner : Owner parameter) : Type :=
  {retained : OwnerTail owner // retained = OwnerTail.acquire owner}

/-- The two original square-residual comparisons at their actual supplied starts. -/
@[expose] def Residuals {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site) (distance : AccuracyRequest) (firstStart lastStart : Nat) : Type :=
  {retained : Reading.PairResiduals firstReading lastReading regular distance firstStart lastStart //
    retained = Reading.PairResiduals.build firstReading lastReading regular distance firstStart lastStart}

/-- The exact original signed comparison cache with its complete production equation. -/
@[expose] def Compared {positive : (0 : Fraction.Rational) < 2}
    {actual : Quarter site parameter 2 quarter positive} {first last : Fraction.Rational}
    {firstInside : FixedRootBoxPath.Inside first} {lastInside : FixedRootBoxPath.Inside last}
    (firstReading : Reading actual first firstInside) (lastReading : Reading actual last lastInside)
    (regular : parameter ≠ criticalValue site)
    (source : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base))
    (target : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter last) positive).base))
    (sourceAgreement : NamedEquivalent (source.certificate source.parameterNonzero).value.name
      firstReading.lift.value.name)
    (refines : target.track.initial.box.Refines source.track.initial.box)
    (small : source.track.initial.box.diagonalSq ≤
      (target.certificate target.parameterNonzero).apart.certificate.lowerSq / 16)
    (movementScale : Fraction.Rational) (nonnegative : 0 ≤ movementScale)
    (movement : Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) positive).base -
      (Paths.polynomial parameter).eval (point site parameter 2 (Waist.direction quarter last) positive).base) ≤
        movementScale * (first - last) ^ 2)
    (paid : (first - last) ^ 2 ≤ (firstReading.residualTimeRequest
      (firstReading.pairRequest regular (Reading.ownerDistance target)) movementScale nonnegative).tolerance)
    (firstStart lastStart : Nat)
    (residuals : Reading.PairResiduals firstReading lastReading regular
      (Reading.ownerDistance target) firstStart lastStart) :
    Type :=
  {retained : Reading.OwnerAgreement firstReading lastReading regular source target sourceAgreement residuals //
    retained = firstReading.ownerAgreementOfResiduals lastReading regular source target sourceAgreement refines small
      movementScale nonnegative movement paid firstStart lastStart residuals}

/-- The unchanged original moving link with its original tails, bounds and complete production equation. -/
@[expose] def Link {polynomial : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial}
    {baseStart baseFinish oldFirst oldLast : Canonical}
    {left : Owner (polynomial.eval baseStart)} {right : Owner (polynomial.eval baseFinish)}
    (data : SquareRootTrace.EdgeData polynomial oldFirst oldLast baseStart baseFinish)
    (leftTail : OwnerTail left) (rightTail : OwnerTail right)
    (lower : Fraction.Rational) (positive : 0 < lower)
    (lowerBound : ∀ index : Nat,
      lower ≤ Norm.Basic.normSq ((OwnerTraceReadings.ownerApproximation left).sample index))
    (refines : right.track.initial.box.Refines left.track.initial.box)
    (diameter : left.track.initial.box.diagonalSq ≤ lower / 1024)
    (movement : data.movementBound ≤ lower ^ 2 / 1024) : Type :=
  {retained : OwnerLink polynomial baseStart baseFinish left right //
    retained = OwnerLink.ofRefiningBox (left := left) (right := right) data leftTail rightTail
      lower positive lowerBound refines diameter movement}

end OwnerMove

/-- The actual preparation, paid move, signed comparison and OwnerLink caches for one retained chart edge.

This is an exact Sigma/subtype view of the original operation values, not a
second continuation or comparison family. The genuine inherited source is
prepared once. That fixed prepared owner is used to create the actual target
before any residual comparison or later preparation. Every original factory
identity remains attached to its whole retained value.
-/
@[expose] def OwnerMove {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
    (budget : OwnerBudget leg coarse limit)
    {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
    {lastInside : FixedRootBoxPath.Inside last}
    {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
    {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
    (geometry : Geometry reading targetReading leg.regular payment)
    {oldFirst oldLast : Canonical}
    (data : SquareRootTrace.EdgeData (Paths.polynomial parameter) oldFirst oldLast
      (coordinate site parameter 2 quarter (by decide +kernel) first)
      (coordinate site parameter 2 quarter (by decide +kernel) last))
    (paid : (first - last) ^ 2 < (leg.source.residualTimeRequest (OwnerBudget.accuracy leg budget.floor limit).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance)
    (dataPaid : data.movementBound ≤ Radial.Clearance.rootFloor site parameter ^ 2 / 1024)
    (source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first)))
    (sourceAgreement : NamedEquivalent
      (source.certificate source.parameterNonzero).value.name reading.lift.value.name) : Type :=
  have movementPaid : leg.traceMovement coarse.bounds * (first - last) ^ 2 <
      (OwnerBudget.accuracy leg budget.floor limit).val.tolerance :=
    leg.source.residualTimeRequest_pays_lt (OwnerBudget.accuracy leg budget.floor limit).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
      (first - last) paid
  Σ cached : OwnerMove.Preparation budget geometry source,
  Σ joined : OwnerMove.Join source (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) (CachedSource.startAgreement
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val),
  Σ target : OwnerMove.Target
      (sourceParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first))
      (targetParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) last))
      (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) (OwnerBudget.target_nonzero geometry)
      (budget.move_small (source := source) geometry cached.val movementPaid),
  Σ targetTail : OwnerMove.Tail target.val,
  Σ residuals : OwnerMove.Residuals reading targetReading leg.regular (Reading.ownerDistance target.val) 0 0,
  Σ _compared : OwnerMove.Compared reading targetReading leg.regular
      (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) target.val
      ((CachedSource.startAgreement
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val).symm.trans sourceAgreement)
      (OwnerMove.Target.refines
      (sourceParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first))
      (targetParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) last))
      (nonzero := OwnerBudget.target_nonzero geometry)
      (small := budget.move_small (source := source) geometry cached.val movementPaid)
      (source := (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val)) target)
      (budget.prepared_small (source := source) geometry cached.val target.val)
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
      (coarse.movement_endpoints first last) (budget.pair_paid geometry target.val paid) 0 0 residuals.val,
    OwnerMove.Link
        (left := CachedSource.startPrepared
          (start := coordinate site parameter 2 quarter (by decide +kernel) first)
          (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
          (mode := .region) (request := OwnerBudget.request leg.regular)
          (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source) cached.val)
        (right := target.val) data joined.val.rightTail targetTail.val
        (Radial.Clearance.rootFloor site parameter)
        (Radial.Clearance.rootFloor_positive site parameter leg.regular)
        (Radial.Clearance.rootFloor_le_sample site parameter (Waist.direction quarter first)
          leg.regular leg.actual.data.bound (source_inside leg.regular) (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val))
        (OwnerMove.Target.refines
      (sourceParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first))
      (targetParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) last))
      (nonzero := OwnerBudget.target_nonzero geometry)
      (small := budget.move_small (source := source) geometry cached.val movementPaid)
      (source := (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val)) target)
        (budget.prepared_link_diameter (source := source) geometry cached.val) dataPaid

namespace OwnerMove

section

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg} {budget : OwnerBudget leg coarse limit}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometry : Geometry reading targetReading leg.regular payment}
variable {oldFirst oldLast : Canonical}
variable {data : SquareRootTrace.EdgeData (Paths.polynomial parameter) oldFirst oldLast
  (coordinate site parameter 2 quarter (by decide +kernel) first)
  (coordinate site parameter 2 quarter (by decide +kernel) last)}
variable {paid : (first - last) ^ 2 < (leg.source.residualTimeRequest (OwnerBudget.accuracy leg budget.floor limit).val
  (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance}
variable {dataPaid : data.movementBound ≤ Radial.Clearance.rootFloor site parameter ^ 2 / 1024}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent
  (source.certificate source.parameterNonzero).value.name reading.lift.value.name}

/-- Prepare and move the inherited owner once, retaining the actual target before constructing its signed comparison. -/
@[expose] def build (budget : OwnerBudget leg coarse limit)
    (geometry : Geometry reading targetReading leg.regular payment)
    (data : SquareRootTrace.EdgeData (Paths.polynomial parameter) oldFirst oldLast
      (coordinate site parameter 2 quarter (by decide +kernel) first)
      (coordinate site parameter 2 quarter (by decide +kernel) last))
    (paid : (first - last) ^ 2 < (leg.source.residualTimeRequest (OwnerBudget.accuracy leg budget.floor limit).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance)
    (dataPaid : data.movementBound ≤ Radial.Clearance.rootFloor site parameter ^ 2 / 1024)
    (source : Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first)))
    (sourceAgreement : NamedEquivalent
      (source.certificate source.parameterNonzero).value.name reading.lift.value.name) :
    OwnerMove budget geometry data paid dataPaid source sourceAgreement :=
  have movementPaid : leg.traceMovement coarse.bounds * (first - last) ^ 2 <
      (OwnerBudget.accuracy leg budget.floor limit).val.tolerance :=
    leg.source.residualTimeRequest_pays_lt (OwnerBudget.accuracy leg budget.floor limit).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
      (first - last) paid
  (fun cached : OwnerMove.Preparation budget geometry source =>
(fun joined : OwnerMove.Join source (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) (CachedSource.startAgreement
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) =>
(fun target : OwnerMove.Target
      (sourceParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first))
      (targetParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) last))
      (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) (OwnerBudget.target_nonzero geometry)
      (budget.move_small (source := source) geometry cached.val movementPaid) =>
(fun targetTail : OwnerMove.Tail target.val =>
(fun residuals : OwnerMove.Residuals reading targetReading leg.regular (Reading.ownerDistance target.val) 0 0 =>
(fun compared : OwnerMove.Compared reading targetReading leg.regular
      (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) target.val
      ((CachedSource.startAgreement
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val).symm.trans sourceAgreement)
      (OwnerMove.Target.refines
      (sourceParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first))
      (targetParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) last))
      (nonzero := OwnerBudget.target_nonzero geometry)
      (small := budget.move_small (source := source) geometry cached.val movementPaid)
      (source := (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val)) target)
      (budget.prepared_small (source := source) geometry cached.val target.val)
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
      (coarse.movement_endpoints first last) (budget.pair_paid geometry target.val paid) 0 0 residuals.val =>
(fun linked : OwnerMove.Link
        (left := CachedSource.startPrepared
          (start := coordinate site parameter 2 quarter (by decide +kernel) first)
          (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
          (mode := .region) (request := OwnerBudget.request leg.regular)
          (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source) cached.val)
        (right := target.val) data joined.val.rightTail targetTail.val
        (Radial.Clearance.rootFloor site parameter)
        (Radial.Clearance.rootFloor_positive site parameter leg.regular)
        (Radial.Clearance.rootFloor_le_sample site parameter (Waist.direction quarter first)
          leg.regular leg.actual.data.bound (source_inside leg.regular) (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val))
        (OwnerMove.Target.refines
      (sourceParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first))
      (targetParameter := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) last))
      (nonzero := OwnerBudget.target_nonzero geometry)
      (small := budget.move_small (source := source) geometry cached.val movementPaid)
      (source := (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val)) target)
        (budget.prepared_link_diameter (source := source) geometry cached.val) dataPaid =>
(show OwnerMove budget geometry data paid dataPaid source sourceAgreement from
  ⟨cached, joined, target, targetTail, residuals, compared, linked⟩))
  ⟨OwnerLink.ofRefiningBox
        (left := CachedSource.startPrepared
          (start := coordinate site parameter 2 quarter (by decide +kernel) first)
          (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
          (mode := .region) (request := OwnerBudget.request leg.regular)
          (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source) cached.val)
        (right := target.val) data joined.val.rightTail targetTail.val (Radial.Clearance.rootFloor site parameter)
    (Radial.Clearance.rootFloor_positive site parameter leg.regular)
    (Radial.Clearance.rootFloor_le_sample site parameter (Waist.direction quarter first)
      leg.regular leg.actual.data.bound (source_inside leg.regular) (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val)) (OwnerMove.Target.refines
    (sourceParameter := (Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))
    (targetParameter := (Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) last))
    (source := (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val)) (nonzero := OwnerBudget.target_nonzero geometry)
    (small := budget.move_small (source := source) geometry cached.val movementPaid) target)
    (budget.prepared_link_diameter (source := source) geometry cached.val) dataPaid, rfl⟩)
  ⟨reading.ownerAgreementOfResiduals targetReading leg.regular (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) target.val
    ((CachedSource.startAgreement
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val).symm.trans sourceAgreement) (OwnerMove.Target.refines
    (sourceParameter := (Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))
    (targetParameter := (Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) last))
    (source := (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val)) (nonzero := OwnerBudget.target_nonzero geometry)
    (small := budget.move_small (source := source) geometry cached.val movementPaid) target)
    (budget.prepared_small (source := source) geometry cached.val target.val)
    (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
    (coarse.movement_endpoints first last) (budget.pair_paid geometry target.val paid) 0 0 residuals.val, rfl⟩)
  ⟨Reading.PairResiduals.build reading targetReading leg.regular (Reading.ownerDistance target.val) 0 0, rfl⟩)
  ⟨OwnerTail.acquire target.val, rfl⟩)
  ⟨(CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val).advance
      (source := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first))
      (target := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) last))
      (OwnerBudget.target_nonzero geometry)
      (budget.move_small (source := source) geometry cached.val movementPaid), rfl⟩)
  ⟨OwnerJoin.acquire source (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val) (CachedSource.startAgreement
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      cached.val), rfl⟩)
  ⟨CachedSource.atStart (geometry.chord coarse.bounds coarse.bounds_eq) source
    (OwnerBudget.request leg.regular), rfl⟩

/-- Read the actual complete original source preparation without running its producer again. -/
@[expose] def cached (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    OwnerBudget.StartCache budget geometry source := move.1.val

/-- Read the same cached prepared source at its original geometric point without preparing another owner.

Only the exact starting-point equality transports the complete original
prepared owner. Its track, observations and numerical channel stay attached
to the existing source cache.
-/
@[expose] def prepared (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first)) :=
  CachedSource.startPrepared
    (start := coordinate site parameter 2 quarter (by decide +kernel) first)
    (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
    (mode := .region) (request := OwnerBudget.request leg.regular)
    (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source) move.cached

/-- The displayed prepared source is the entire same retained cache with only its radicand index transported. -/
theorem prepared_heq (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    HEq move.prepared move.cached.preparedOwner := CachedSource.startPrepared_heq _

/-- Read the actual complete original same-point join retaining both inherited and prepared source owners. -/
@[expose] def joined (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    OwnerJoin source (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      move.cached) := move.2.1.val

/-- Read the very target created by the original paid move, preserving its actual track and fixed source box. -/
@[expose] def target (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    Owner ((Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) last)) := move.2.2.1.val

/-- The complete target owner is the original advance on this retained cache and actual computed payment. -/
theorem target_eq (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    move.target = (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      move.cached).advance
      (source := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first))
      (target := (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) last))
      (OwnerBudget.target_nonzero geometry)
      (budget.move_small (source := source) geometry move.cached
        (leg.source.residualTimeRequest_pays_lt (OwnerBudget.accuracy leg budget.floor limit).val
          (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
          (first - last) paid)) :=
  move.2.2.1.property

/-- Read the same target tail acquired once on the actual moved owner. -/
@[expose] def targetTail (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    OwnerTail move.target := move.2.2.2.1.val

/-- Read both actual square-residual comparison caches attached to their original requested starts. -/
@[expose] def residuals (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    Reading.PairResiduals reading targetReading leg.regular (Reading.ownerDistance move.target) 0 0 :=
  move.2.2.2.2.1.val

/-- The actual moved owner agrees with the retained target product through the computed signed comparison. -/
@[expose] def agrees (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    NamedEquivalent (move.target.certificate move.target.parameterNonzero).value.name
      targetReading.lift.value.name :=
  Reading.OwnerAgreement.agrees reading targetReading leg.regular (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source) move.cached) move.target
    ((CachedSource.startAgreement
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source) move.cached).symm.trans
      sourceAgreement) move.residuals move.2.2.2.2.2.1.val

/-- Read the original moving link consuming the identical source/target tails and retained EdgeData. -/
@[expose] def link (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    OwnerLink (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) first)
      (coordinate site parameter 2 quarter (by decide +kernel) last) (CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source)
      move.cached) move.target :=
  move.2.2.2.2.2.2.val

/-- The actual inherited source, preparation join and paid moving link assemble the original OwnerPath. -/
@[expose] def path (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) first) source
      (coordinate site parameter 2 quarter (by decide +kernel) last) move.target :=
  .cons (OwnerLink.stationary _ _ move.joined) (.cons move.link (.nil _ move.target))

/-- Compare the spatial cover finish with the same affine target through its original prepared-source join.

Both paths consume the same geometry and inherited source. The stored Leg
budget pays every spatial vertex internally; its original endpoint bound
pays the actual affine link. The comparison reuses the existing prepared
source join, not a new source attachment or a presumed target agreement.
-/
@[expose] def spatialAgreement (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement)
    (covered : Covered geometry source) :
    Gaussian.Equivalence.Equivalent (ownerApproximation covered.finishOwner) (ownerApproximation move.target) := by
  have movementPaid : leg.traceMovement coarse.bounds * (first - last) ^ 2 ≤
      Radial.Clearance.rootFloor site parameter ^ 2 / 1024 :=
    (leg.source.residualTimeRequest_pays_lt (OwnerBudget.accuracy leg budget.floor limit).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
      (first - last) paid).le.trans budget.tolerance_le_root
  apply OwnerPath.approximationEquivalent covered.trace
    (.cons move.link (.nil _ move.target)) move.joined
    (Radial.Clearance.rootFloor site parameter) (Radial.Clearance.rootFloor_positive site parameter leg.regular)
  · intro index
    have bound := Radial.Clearance.rootFloor_le_sample site parameter (Waist.direction quarter first)
      leg.regular leg.actual.data.bound (source_inside leg.regular) source index
    rewrite [Norm.Basic.normSq_eq_canonical] at bound
    exact bound
  · intro value member
    have bound := covered.trace_movement leg coarse value member
    rewrite [Norm.Basic.normSq_eq_canonical] at bound
    have reverse : normSq
        ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first) -
          (Paths.polynomial parameter).eval value) = normSq
        ((Paths.polynomial parameter).eval value -
          (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first)) := by
      rewrite [show (Paths.polynomial parameter).eval
          (coordinate site parameter 2 quarter (by decide +kernel) first) - (Paths.polynomial parameter).eval value =
        -((Paths.polynomial parameter).eval value - (Paths.polynomial parameter).eval
          (coordinate site parameter 2 quarter (by decide +kernel) first)) by ring1,
        Basic.Canonical.normSq_neg]
      rfl
    rewrite [reverse]
    exact bound.trans movementPaid
  · intro value member
    change value ∈ [coordinate site parameter 2 quarter (by decide +kernel) last] at member
    cases member with
    | head =>
        have bound := coarse.movement_endpoints first last
        rewrite [Norm.Basic.normSq_eq_canonical] at bound
        exact bound.trans movementPaid
    | tail _ absent => cases absent

/-- Retain the actual spatial terminal tail and original affine target tail in their computed same-point owner join.

The spatial tail is projected from the original cached OwnerLinks, with the
same inherited tail in the empty branch. Both original owners and all paid
comparison indices remain in the original OwnerJoin; neither is replaced.
-/
@[expose] def spatialJoin (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement)
    (covered : Covered geometry source) : OwnerJoin covered.finishOwner move.target :=
  OwnerJoin.ofApproximationTails (covered.trace.terminalTail move.joined.leftTail) move.targetTail
    (move.spatialAgreement covered)

/-- Prepend the actual spatial block and internally computed same-point join to the retained affine-target tail.

The original covered preparation is built once on the inherited source.
Its real terminal owner is retained by the block, and the complete original
join transfers the tail to the very same affine target already stored in
the supplied OwnerMove. No successful join is a caller argument.
-/
@[expose] def prependSpatial (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement)
    {finish : Canonical} {target : Owner ((Paths.polynomial parameter).eval finish)}
    (tail : CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) last) move.target finish target) :
    CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) first) source finish target :=
  let covered := Covered.build geometry source
  let joined := move.spatialJoin covered
  .cons covered.block (.handoff ⟨move.target, joined⟩ tail)

/-- One internally compared spatial block contributes one geometric block with its separate retained join payment. -/
theorem prependSpatial_length (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement)
    {finish : Canonical} {target : Owner ((Paths.polynomial parameter).eval finish)}
    (tail : CoveredTracedPath.Blocks (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) last) move.target finish target) :
    (move.prependSpatial tail).length = tail.length + 1 := by
  unfold prependSpatial
  rewrite [CoveredTracedPath.Blocks.length_cons, CoveredTracedPath.Blocks.length_handoff]
  rfl

end

section Primitive

open Purelib.Riemann.Integration.UniformPrimitiveNeighborhoods (Bounds)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Branches
open Purelib.Geometry.Rational (Box)

variable {leg : Leg site parameter quarter} {coarse : Leg.TraceBudget leg}
variable {clearance : OwnerBudget.SourceClearance leg}
variable (bounds : OwnerBudget.PrimitiveBounds leg coarse clearance)
variable {budget : OwnerBudget leg coarse (some bounds.timeRequest)}
variable {first last : Fraction.Rational} {firstInside : FixedRootBoxPath.Inside first}
variable {lastInside : FixedRootBoxPath.Inside last}
variable {reading : Reading leg.actual first firstInside} {targetReading : Reading leg.actual last lastInside}
variable {payment : (last - first) ^ 2 ≤ Geometric.Basic.quarterRadius 1 7}
variable {geometry : Geometry reading targetReading leg.regular payment}
variable {oldFirst oldLast : Canonical}
variable {data : SquareRootTrace.EdgeData (Paths.polynomial parameter) oldFirst oldLast
  (coordinate site parameter 2 quarter (by decide +kernel) first)
  (coordinate site parameter 2 quarter (by decide +kernel) last)}
variable {paid : (first - last) ^ 2 < (leg.source.residualTimeRequest
  (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val
  (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance}
variable {dataPaid : data.movementBound ≤ Radial.Clearance.rootFloor site parameter ^ 2 / 1024}
variable {source : Owner ((Paths.polynomial parameter).eval
  (coordinate site parameter 2 quarter (by decide +kernel) first))}
variable {sourceAgreement : NamedEquivalent
  (source.certificate source.parameterNonzero).value.name reading.lift.value.name}

/-- The original uniform primitive seed on this same move's retained fixed prepared source.

The whole source CachedSource and actual target remain in the supplied
OwnerMove. This exact type view changes no root parent or index; the shared
numerical bounds are retargeted to its actual original chord.
-/
@[expose] def PrimitiveSeed
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) : Type :=
  Bounds.PreparedSeed (bounds.chord geometry) 0 (by decide +kernel) move.cached.preparedOwner

/-- Acquire one original uniform seed from the same actual fixed prepared source after its target was created. -/
@[expose] def primitiveSeed
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) : PrimitiveSeed bounds move :=
  Bounds.PreparedSeed.acquire (bounds.chord geometry) 0 (by decide +kernel) move.cached.preparedOwner

/-- The actual moved target refines that very same retained source cache before primitive reconditioning. -/
theorem primitiveTarget_refines
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    move.target.track.initial.box.Refines move.cached.preparedOwner.track.initial.box := by
  have movementPaid : leg.traceMovement coarse.bounds * (first - last) ^ 2 <
      (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val.tolerance :=
    leg.source.residualTimeRequest_pays_lt
      (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq) _ paid
  have retained := Target.refines
    (sourceParameter := (Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) first))
    (targetParameter := (Paths.polynomial parameter).eval
      (coordinate site parameter 2 quarter (by decide +kernel) last))
    (source := CachedSource.startPrepared
      (start := coordinate site parameter 2 quarter (by decide +kernel) first)
      (finish := coordinate site parameter 2 quarter (by decide +kernel) last)
      (mode := .region) (request := OwnerBudget.request leg.regular)
      (segment := geometry.chord coarse.bounds coarse.bounds_eq) (owner := source) move.cached)
    (nonzero := OwnerBudget.target_nonzero geometry)
    (small := budget.move_small (source := source) geometry move.cached movementPaid) move.2.2.1
  simpa only [target, CachedSource.startPrepared, Transport.castOwnerParameter_initial_box] using retained

/-- The same original paid movement fits the retained source cache used by the shared primitive seed. -/
theorem primitiveTarget_small
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval
        ((geometry.chord coarse.bounds coarse.bounds_eq).pointAt 0) -
      (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) last)) <
      move.cached.preparedOwner.track.initial.clearance.bound := by
  have movementPaid : leg.traceMovement coarse.bounds * (first - last) ^ 2 <
      (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val.tolerance :=
    leg.source.residualTimeRequest_pays_lt
      (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq) _ paid
  have retained := budget.move_small (source := source) geometry move.cached movementPaid
  rewrite [CachedSource.startPrepared, Transport.castOwnerParameter_clearance_bound] at retained
  exact Eq.mpr (congrArg (fun start : Canonical =>
    Norm.Basic.normSq ((Paths.polynomial parameter).eval start -
      (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) last)) <
        move.cached.preparedOwner.track.initial.clearance.bound)
    (geometry.chord coarse.bounds coarse.bounds_eq).pointAt_zero) retained

/-- The retained cap pays the actual intrinsic quarter displacement scale on this move. -/
theorem primitiveBase_paid
    (_move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) :
    ((25 / 4) * Norm.Basic.normSq (halfGap site parameter)) * (first - last) ^ 2 < bounds.radius ^ 2 := by
  have requestBound := leg.source.residualTimeRequest_le
    (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val
    (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
  have paidCap := paid.trans_le
    (requestBound.trans (OwnerBudget.accuracy_le_limit leg budget.floor bounds.timeRequest))
  exact leg.source.residualTimeRequest_pays_lt bounds.radiusRequest
    ((25 / 4) * Norm.Basic.normSq (halfGap site parameter))
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)) _ paidCap

/-- Every paid intrinsic quarter displacement lies in the same retained seed neighborhood.

The supplied scalar inequality bounds only the actual time displacement.
The same cap, quarter coordinate bound and uniform-box refinement construct
the domain certificate without another preparation or owner selection.
-/
theorem primitivePoint_inside
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement)
    (seed : PrimitiveSeed bounds move) (count : Nat) (time : Fraction.Rational)
    (within : (time - first) ^ 2 ≤ (first - last) ^ 2) :
    (seed.neighborhood count).box.Contains (coordinate site parameter 2 quarter (by decide +kernel) time) := by
  have distance := quarter_base_distance_le site parameter 2 quarter (by decide +kernel)
    leg.actual.data.lower leg.actual.data.upper time first
  have inRadius : Norm.Basic.normSq
      (coordinate site parameter 2 quarter (by decide +kernel) time -
        (geometry.chord coarse.bounds coarse.bounds_eq).pointAt 0) ≤
      (bounds.chord geometry).radius ^ 2 := by
    rewrite [(geometry.chord coarse.bounds coarse.bounds_eq).pointAt_zero, bounds.chord_radius geometry]
    exact (distance.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct within
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Norm.Basic.normSq_nonneg _)))).trans
      (primitiveBase_paid bounds move).le
  exact (seed.uniformBox_refines count).contains
    (Box.Square.Centered.centeredBox_contains_of_normSq_sub_le
      (bounds.chord geometry).radius_positive.le inRadius)

/-- The cap and stored payment put the actual target in the same retained seed neighborhood. -/
theorem primitiveTarget_inside
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement)
    (seed : PrimitiveSeed bounds move) (count : Nat) :
    (seed.neighborhood count).box.Contains (coordinate site parameter 2 quarter (by decide +kernel) last) := by
  apply primitivePoint_inside bounds move seed count last
  have same : (last - first) ^ 2 = (first - last) ^ 2 := by ring1
  exact same.le

/-- Compare the actual stored target with a retained point of the same shared primitive seed on its signed sheet.

The original common-source comparison consumes the actual target refinement
and stored movement. Its neighborhood containment is derived from the same
positive cap rather than supplied as a successful comparison or coverage.
-/
@[expose] def primitiveTarget_equivalent
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement)
    (seed : PrimitiveSeed bounds move) (count : Nat)
    (sample : ContinuedNeighborhood.Point (seed.neighborhood count)
      (coordinate site parameter 2 quarter (by decide +kernel) last)) :
    NamedEquivalent (move.target.certificate move.target.parameterNonzero).value.name
      sample.certificate.value.name := by
  have small := primitiveTarget_small bounds move
  rewrite [Norm.Basic.normSq_eq_canonical] at small
  exact UniformPrimitiveSheetCompatibility.Bounds.PreparedSeed.pointEquivalent seed count
    (primitiveTarget_inside bounds move seed count) move.target
    (primitiveTarget_refines bounds move) small sample

/-- The retained actual move and its once-built original seed, neighborhood, target point and signed root link.

This exact Sigma view retains the complete supplied OwnerMove and original
cache values. Their full factory equations preserve source attachment and
numerical channel identity without introducing a second root or comparison
record family.
-/
@[expose] def PrimitiveTarget
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) : Type :=
  Σ retained : {actual : OwnerMove budget geometry data paid dataPaid source sourceAgreement // actual = move},
  Σ seed : {actual : PrimitiveSeed bounds retained.val // actual = primitiveSeed bounds retained.val},
  Σ patch : {actual : ContinuedNeighborhood (Paths.polynomial parameter) count //
      actual = seed.val.neighborhood count},
  Σ sample : ContinuedNeighborhood.Point patch.val
      (coordinate site parameter 2 quarter (by decide +kernel) last),
    NamedEquivalent
      (retained.val.target.certificate retained.val.target.parameterNonzero).value.name sample.certificate.value.name

/-- Build and retain each original shared primitive value once on the supplied actual paid move. -/
@[expose] def primitiveTarget
    (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    PrimitiveTarget bounds move count :=
  let segment := geometry.chord coarse.bounds coarse.bounds_eq
  let common := bounds.chord geometry
  let seed : PrimitiveSeed bounds move :=
    Bounds.PreparedSeed.acquire (segment := segment) common 0 (by decide +kernel) move.cached.preparedOwner
  let patch : ContinuedNeighborhood (Paths.polynomial parameter) count :=
    Bounds.PreparedSeed.neighborhood (segment := segment) (bounds := common) seed count
  let sample : ContinuedNeighborhood.Point patch
      (coordinate site parameter 2 quarter (by decide +kernel) last) :=
    ContinuedNeighborhood.Point.acquire patch _ (primitiveTarget_inside bounds move seed count)
  let equivalent := primitiveTarget_equivalent bounds move seed count sample
  ⟨⟨move, rfl⟩, ⟨seed, rfl⟩, ⟨patch, rfl⟩, sample, equivalent⟩

namespace PrimitiveTarget

variable {original : OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}

/-- Read the complete original paid move retained with its actual shared primitive values. -/
@[expose] def move (cached : PrimitiveTarget bounds original count) :
    OwnerMove budget geometry data paid dataPaid source sourceAgreement := cached.1.val

/-- The retained move is the entire supplied original value, including its target and source caches. -/
theorem move_eq (cached : PrimitiveTarget bounds original count) : cached.move = original := cached.1.property

/-- Read the original prepared primitive seed on the actual stored move's fixed source cache. -/
@[expose] def seed (cached : PrimitiveTarget bounds original count) : PrimitiveSeed bounds cached.move :=
  cached.2.1.val

/-- The stored seed is the complete original seed factory result on this same actual move. -/
theorem seed_eq (cached : PrimitiveTarget bounds original count) :
    cached.seed = primitiveSeed bounds cached.move := cached.2.1.property

/-- Read the original continued neighborhood stored once beside its same seed. -/
@[expose] def patch (cached : PrimitiveTarget bounds original count) :
    ContinuedNeighborhood (Paths.polynomial parameter) count := cached.2.2.1.val

/-- The whole retained neighborhood is the original same-seed neighborhood at this refinement index. -/
theorem patch_eq (cached : PrimitiveTarget bounds original count) :
    cached.patch = cached.seed.neighborhood count := cached.2.2.1.property

/-- Read the actual stored target Point without acquiring another owner or observation. -/
@[expose] def sample (cached : PrimitiveTarget bounds original count) :
    ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) last) := cached.2.2.2.1

/-- Read the same retained signed relation from the original moved target to the original patch Point. -/
@[expose] def equivalent (cached : PrimitiveTarget bounds original count) :
    NamedEquivalent
      (cached.move.target.certificate cached.move.target.parameterNonzero).value.name
      cached.sample.certificate.value.name := cached.2.2.2.2

/-- Link the supplied original scalar target Reading to the same stored primitive Point and actual target move.

Both computed relations are read from the actual retained cache. The target
owner, scalar Reading, primitive sample and their numerical names stay
unchanged when this relation is requested at a later accuracy.
-/
@[expose] def readingEquivalent (cached : PrimitiveTarget bounds original count) :
    NamedEquivalent targetReading.lift.value.name cached.sample.certificate.value.name :=
  cached.move.agrees.symm.trans cached.equivalent

/-- The actual original quarter source belongs to the same stored primitive patch.

Only the retained whole patch equality and the original exact center law are
used. This coverage proof does not enlarge the inverse-root model's domain.
-/
theorem source_inside (cached : PrimitiveTarget bounds original count) :
    cached.patch.box.Contains (coordinate site parameter 2 quarter (by decide +kernel) first) := by
  have retained := (cached.seed.neighborhood count).center_inside
  have centered := (cached.seed.neighborhood_center count).trans
    (geometry.chord coarse.bounds coarse.bounds_eq).pointAt_zero
  have covered := Eq.mp (congrArg (fun center : Canonical =>
    (cached.seed.neighborhood count).box.Contains center) centered) retained
  exact Eq.mpr (congrArg (fun patch : ContinuedNeighborhood (Paths.polynomial parameter) count =>
    patch.box.Contains (coordinate site parameter 2 quarter (by decide +kernel) first)) cached.patch_eq) covered

/-- The same stored primitive patch contains the actual paid target from the original capped move. -/
theorem target_inside (cached : PrimitiveTarget bounds original count) :
    cached.patch.box.Contains (coordinate site parameter 2 quarter (by decide +kernel) last) :=
  Eq.mpr (congrArg (fun patch : ContinuedNeighborhood (Paths.polynomial parameter) count =>
    patch.box.Contains (coordinate site parameter 2 quarter (by decide +kernel) last)) cached.patch_eq)
    (primitiveTarget_inside bounds cached.move cached.seed count)

/-- The actual original spatial route lies in the same stored common primitive patch as the paid curve interval.

The cap puts both original endpoints in this retained box. Its coordinate
hull then contains the complete computed spatial route, including stationary
branches; no successful overlap or enlarged approximation domain is assumed.
-/
theorem spatial_path_inside (cached : PrimitiveTarget bounds original count) :
    Polynomial.Geometry.ClearPath.InBox cached.patch.box geometry.route.path := by
  have firstRefines : (Box.Point.pointBox
      (coordinate site parameter 2 quarter (by decide +kernel) first)).Refines cached.patch.box :=
    cached.source_inside
  have lastRefines : (Box.Point.pointBox
      (coordinate site parameter 2 quarter (by decide +kernel) last)).Refines cached.patch.box :=
    cached.target_inside
  exact Polynomial.Geometry.ClearPath.InBox.mono (Box.Hull.refines firstRefines lastRefines) geometry.route_inBox

/-- The squared displacement of an interior chart time fits the actual retained endpoint payment. -/
theorem curve_width (_cached : PrimitiveTarget bounds original count) (time : Fraction.Rational)
    (between : first ≤ time ∧ time ≤ last) : (time - first) ^ 2 ≤ (first - last) ^ 2 := by
  have retained := Arithmetic.pow_le_pow_direct
    (Arithmetic.sub_nonneg_direct between.1)
    (Arithmetic.sub_le_sub_right_direct between.2 first) 2
  have signedWidth : (last - first) ^ 2 = (first - last) ^ 2 := by ring1
  exact retained.trans_eq signedWidth

/-- Every actual intermediate quarter point belongs to the identical retained common primitive patch.

The interval endpoints are those of the stored move. Its original positive
cap supplies containment through the same seed and full patch equality;
no independently successful coverage is an input.
-/
theorem curve_inside (cached : PrimitiveTarget bounds original count) (time : Fraction.Rational)
    (between : first ≤ time ∧ time ≤ last) :
    cached.patch.box.Contains (coordinate site parameter 2 quarter (by decide +kernel) time) :=
  Eq.mpr (congrArg (fun patch : ContinuedNeighborhood (Paths.polynomial parameter) count =>
    patch.box.Contains (coordinate site parameter 2 quarter (by decide +kernel) time)) cached.patch_eq)
    (primitivePoint_inside bounds cached.move cached.seed count time (curve_width bounds cached time between))

/-- The actual retained region-clearance certifies nonvanishing at the given intermediate quarter coordinate. -/
theorem curve_nonzero (_cached : PrimitiveTarget bounds original count) (time : Fraction.Rational)
    (between : first ≤ time ∧ time ≤ last) :
    (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) time) ≠ 0 :=
  geometry.clearance.eval_ne_zero (interval_inside leg.regular payment time between)

/-- The actual intermediate time consumes no more of the retained residual request than the original moved endpoint. -/
theorem curve_paid (cached : PrimitiveTarget bounds original count) (time : Fraction.Rational)
    (between : first ≤ time ∧ time ≤ last) :
    (first - time) ^ 2 < (leg.source.residualTimeRequest
      (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val
      (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance := by
  have signedWidth : (first - time) ^ 2 = (time - first) ^ 2 := by ring1
  rewrite [signedWidth]
  exact (curve_width bounds cached time between).trans_lt paid

/-- Retain the original seed owner as the source Point of the same stored primitive neighborhood.

Only the exact neighborhood and spatial-point equalities transport the
original Point. Its owner is the existing aligned seed owner; no advance,
root acquisition or neighborhood factory is called again.
-/
@[expose] def sourceSample (cached : PrimitiveTarget bounds original count) :
    ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) first) :=
  let sample : ContinuedNeighborhood.Point (cached.seed.neighborhood count)
      ((geometry.chord coarse.bounds coarse.bounds_eq).pointAt 0) :=
    ContinuedNeighborhood.Point.ofOwner cached.seed.aligned.seed.owner (by
      rewrite [cached.seed.neighborhood_owner count]
      exact Box.refines_refl _)
  ContinuedNeighborhood.Point.castPoint
    (geometry.chord coarse.bounds coarse.bounds_eq).pointAt_zero.symm
    (ContinuedNeighborhood.Point.castPatch cached.patch_eq sample)

/-- Compare the actual original scalar source with a supplied Point of that same retained primitive patch.

The original stored OwnerJoin supplies the all-accuracy inherited-to-prepared
link. The existing sheet procedure compares the literal prepared owner with
the actual Point, using zero base movement and the stored patch equality.
Neither original source preparation nor the seed preparation is reconstructed.
-/
@[expose] def sourceEquivalent (cached : PrimitiveTarget bounds original count)
    (sample : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) first)) :
    NamedEquivalent reading.lift.value.name sample.certificate.value.name := by
  have refines : cached.move.prepared.track.initial.box.Refines cached.move.cached.preparedOwner.track.initial.box := by
    simpa only [OwnerMove.prepared, CachedSource.startPrepared, Transport.castOwnerParameter_initial_box] using
      (Box.refines_refl cached.move.cached.preparedOwner.track.initial.box)
  have inside : (cached.seed.neighborhood count).box.Contains
      (coordinate site parameter 2 quarter (by decide +kernel) first) := by
    exact Eq.mp (congrArg (fun patch : ContinuedNeighborhood (Paths.polynomial parameter) count =>
      patch.box.Contains (coordinate site parameter 2 quarter (by decide +kernel) first)) cached.patch_eq)
      cached.source_inside
  have small : normSq ((Paths.polynomial parameter).eval
      ((geometry.chord coarse.bounds coarse.bounds_eq).pointAt 0) -
      (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first)) <
      cached.move.cached.preparedOwner.track.initial.clearance.bound := by
    have zero : (Paths.polynomial parameter).eval
        ((geometry.chord coarse.bounds coarse.bounds_eq).pointAt 0) -
        (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first) = 0 := by
      rewrite [(geometry.chord coarse.bounds coarse.bounds_eq).pointAt_zero]
      ring1
    rewrite [zero, Basic.Canonical.normSq_zero]
    exact cached.move.cached.preparedOwner.track.initial.clearance.positive
  let viewed := ContinuedNeighborhood.Point.castPatch cached.patch_eq.symm sample
  let compared := UniformPrimitiveSheetCompatibility.Bounds.PreparedSeed.pointEquivalent cached.seed count
    inside cached.move.prepared refines small viewed
  let sourceLink : NamedEquivalent reading.lift.value.name
      (cached.move.prepared.certificate cached.move.prepared.parameterNonzero).value.name :=
    sourceAgreement.symm.trans cached.move.joined.equivalent
  exact sourceLink.trans (NamedEquivalent.transport rfl
    (ContinuedNeighborhood.Point.castPatch_name cached.patch_eq.symm sample) compared)

/-- Build the source Point once and retain its computed original scalar-sheet relation beside it.

The supplied primitive target cache remains the parent of the same patch
and seed. Both actual endpoint Points therefore belong to one original
inverse-root neighborhood, with independently retained original scalar links.
-/
@[expose] def sourcePoint (cached : PrimitiveTarget bounds original count) :
    Σ sample : ContinuedNeighborhood.Point cached.patch
        (coordinate site parameter 2 quarter (by decide +kernel) first),
      NamedEquivalent reading.lift.value.name sample.certificate.value.name :=
  let sample := sourceSample bounds cached
  let related := sourceEquivalent bounds cached sample
  ⟨sample, related⟩

/-- The original source Point and its retained scalar-sheet relation on this same primitive patch. -/
@[expose] def SourcePoint (cached : PrimitiveTarget bounds original count) : Type :=
  Σ sample : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) first),
    NamedEquivalent reading.lift.value.name sample.certificate.value.name

/-- The actual raw source-to-seed comparison at the same retained source reading's relative target. -/
@[expose] def SourceComparison (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached) (reference : OwnerTail.Reading cached.move.joined.leftTail) : Type :=
  Gaussian.Equivalence.Comparison (ownerApproximation source) (ownerApproximation sourcePoint.1.owner)
    cached.move.joined.comparison.leftIndex 0 (reference.norm / 1024)

/-- Compare the actual supplied source Point with its original source owner using the stored signed relation.

Both original owners and the source Point remain inputs. The existing
raw-name conversion consumes the retained scalar-sheet relation; it does
not rebuild a source preparation, common seed, Point or isolation owner.
-/
@[expose] def sourceComparison (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached) (reference : OwnerTail.Reading cached.move.joined.leftTail) :
    SourceComparison bounds cached sourcePoint reference := by
  let related := sourceAgreement.trans sourcePoint.2
  let raw := SquareRootTrackEquivalence.approximationEquivalent_of_rootEquivalent
    source.parameterNonzero source.track sourcePoint.1.owner.track related
  exact raw.compare cached.move.joined.comparison.leftIndex 0 (reference.norm / 1024)
    (Fraction.Order.Field.div_pos_direct
      (cached.move.joined.leftTail.lower_positive.trans_le reference.lower) (by decide +kernel))

section SourceScalarCell

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Polynomial.Dense.Power (OddPowers)

namespace SourcePoint

/-- The exact retained source Point reindexed at an equal original chart time.

The subtype keeps the complete original Point.castPoint equation. Its
actual Point is the same original owner/cache, not an independently chosen
root at a matching coordinate.
-/
@[expose] def At (cached : PrimitiveTarget bounds original count) (sourcePoint : SourcePoint bounds cached)
    (time : Fraction.Rational) (sameTime : time = first) : Type :=
  {actual : ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) time) //
    actual = ContinuedNeighborhood.Point.castPoint (patch := cached.patch)
      (congrArg (fun time => coordinate site parameter 2 quarter (by decide +kernel) time) sameTime) sourcePoint.1}

/-- Reindex the same whole cached source Point once, retaining its exact original factory equation. -/
def atTime (cached : PrimitiveTarget bounds original count) (sourcePoint : SourcePoint bounds cached)
    (time : Fraction.Rational) (sameTime : time = first) : At bounds cached sourcePoint time sameTime :=
  ⟨ContinuedNeighborhood.Point.castPoint (patch := cached.patch)
    (congrArg (fun time => coordinate site parameter 2 quarter (by decide +kernel) time) sameTime) sourcePoint.1, rfl⟩

/-- Exact source-time reindexing retains the entire original Point, including its nominal owner and cached norm. -/
theorem atTime_heq (cached : PrimitiveTarget bounds original count) (sourcePoint : SourcePoint bounds cached)
    (time : Fraction.Rational) (sameTime : time = first) :
    HEq (atTime bounds cached sourcePoint time sameTime).val sourcePoint.1 := by
  cases sameTime
  rfl

end SourcePoint

/-- The original operational name relation from an actual scalar Reading to this exact retained source Point.

This ordinary type is exactly the existing NamedEquivalent object on the
supplied original owners. It compacts the source-parent projection type;
no Point, name, preparation or independent comparison is constructed.
-/
private def SourceReadingAgreement (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached) {time : Fraction.Rational}
    {scalarInside : FixedRootBoxPath.Inside time} (scalarReading : Reading leg.actual time scalarInside) : Type :=
  NamedEquivalent scalarReading.lift.value.name sourcePoint.1.certificate.value.name

/-- Link another actual scalar reading of the same source time to the identical retained source Point.

The original prepared-quarter query equations identify the exact complete
numerical channel at that time. Only exact time equality reindexes the
original Point; its cached owner and already retained signed relation stay
unchanged, without any root comparison or source preparation.
-/
private def sourceReadingEquivalent (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached) {span : Interval.Bounds}
    {scalarInside : FixedRootBoxPath.Inside span.lower}
    (scalarReading : Reading leg.actual span.lower scalarInside) (sameTime : span.lower = first) :
    SourceReadingAgreement bounds cached sourcePoint scalarReading := by
  cases sameTime
  have sameChannel := congrArg (fun channel : Gaussian.Name.Coherent.CoherentNamed => channel.name)
    (scalarReading.value_eq_other reading)
  exact NamedEquivalent.transport sameChannel.symm rfl sourcePoint.2

/-- Request the actual scalar coefficient on this retained primitive parent's genuine source endpoint.

The supplied source Point and scalar cell are completed original caches.
The original same-time query equations derive their signed link internally;
original source containment supplies the actual common-model domain. The
shared cell procedure requests and retains the same root/readModel/comparison
as its interior consumer, without rebuilding any source or primitive model.
-/
def sourceCoefficientRequest (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached)
    {cellRadicand : Purelib.Algebra.Quadratic.Pair.Polynomial.Coefficients}
    {cellDifferential : OddPowerDifferential cellRadicand}
    {cellData : WaistBounds site parameter cellDifferential}
    {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
    {scalarReading : Reading leg.actual span.lower scalarInside} {cellAccuracy : AccuracyRequest}
    (sameTime : span.lower = first)
    (retained : SourcePoint.At bounds cached sourcePoint span.lower sameTime)
    (cell : Model cellData scalarReading cellAccuracy)
    {numerator : InverseRootPolynomial.Polynomial} {pairCount : Nat}
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location)
    {stage : Nat} {inverse : InverseRootPolynomial.Model (Paths.polynomial parameter) cached.patch.base.box}
    (powers : OddPowers inverse.value) (sameModel : inverse = cached.patch.base.refine stage)
    (common : PrimitiveModel cached.patch stage numerator pairCount) :
    Model.CoefficientRequest
      (polynomial := Paths.polynomial parameter) (patch := cached.patch) (sample := retained.val)
      (powers := powers) cell sameModel common :=
  let sourceLink : SourceReadingAgreement bounds cached sourcePoint scalarReading :=
    sourceReadingEquivalent (span := span) (scalarInside := scalarInside)
      bounds cached sourcePoint scalarReading sameTime
  have sameName : retained.val.certificate.value.name = sourcePoint.1.certificate.value.name :=
    (congrArg (fun sample : ContinuedNeighborhood.Point cached.patch
        (coordinate site parameter 2 quarter (by decide +kernel) span.lower) => sample.certificate.value.name)
      retained.property).trans (ContinuedNeighborhood.Point.castPoint_name (patch := cached.patch) _ sourcePoint.1)
  let related : NamedEquivalent scalarReading.lift.value.name
      retained.val.certificate.value.name :=
    NamedEquivalent.transport rfl sameName.symm sourceLink
  Model.coefficientRequest
    (patch := cached.patch) (sample := retained.val) (powers := powers)
    cell related pairs scale sameModel common (by
      rewrite [sameTime]
      exact source_inside bounds cached)

end SourceScalarCell

/-- The original source reading, actual paid source-to-seed comparison and its exact retained anchor.

This exact Sigma view binds the complete original factory results. One
reference is shared by all Points and parent-prefix comparisons on the
same supplied primitive patch, with no alternative root or cache record.
-/
@[expose] def Reference (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached) : Type :=
  Σ retained : {actual : OwnerTail.Reading cached.move.joined.leftTail //
      actual = cached.move.joined.leftReading},
  Σ compared : {actual : SourceComparison bounds cached sourcePoint retained.val //
      actual = sourceComparison bounds cached sourcePoint retained.val},
    {anchor : Canonical // anchor = (ownerApproximation sourcePoint.1.owner).sample compared.val.rightIndex}

/-- Cache one actual source reading and computed seed alignment for the whole supplied primitive patch. -/
@[expose] def reference (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached) : Reference bounds cached sourcePoint :=
  let retained := cached.move.joined.leftReading
  let compared := sourceComparison bounds cached sourcePoint retained
  let anchor := (ownerApproximation sourcePoint.1.owner).sample compared.rightIndex
  ⟨⟨retained, rfl⟩, ⟨compared, rfl⟩, ⟨anchor, rfl⟩⟩

/-- One original primitive target together with its once-computed signed source Point and fixed source reference.

The exact Sigma retains complete original factory values and equations on
the supplied actual move. Both endpoint/root owners, the common seed and
neighborhood, source comparison, sampled anchor and all paid indices remain
in their original owners; no alternate root or comparison family is added.
-/
@[expose] def Anchored (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement)
    (count : Nat) : Type :=
  Σ target : {actual : PrimitiveTarget bounds move count // actual = primitiveTarget bounds move count},
  Σ first : {actual : SourcePoint bounds target.val // actual = sourcePoint bounds target.val},
    {actual : Reference bounds target.val first.val // actual = reference bounds target.val first.val}

/-- Prepare one original shared primitive target, signed source Point and actual source reference on the same paid move.

Each original factory runs once. The reference consumes the very same
retained target and source Point; all three complete cached values and
factory equations are returned for source/interior and spatial-parent reuse.
-/
def anchor (move : OwnerMove budget geometry data paid dataPaid source sourceAgreement) (count : Nat) :
    Anchored bounds move count :=
  let target := primitiveTarget bounds move count
  let first := sourcePoint bounds target
  let retained := reference bounds target first
  ⟨⟨target, rfl⟩, ⟨first, rfl⟩, ⟨retained, rfl⟩⟩

namespace Anchored

variable {move : OwnerMove budget geometry data paid dataPaid source sourceAgreement} {count : Nat}

/-- Read the complete original target/seed/neighborhood/Point cache retained on the same actual move. -/
@[expose] def target (value : Anchored bounds move count) : PrimitiveTarget bounds move count := value.1.val

/-- The retained target cache is the entire original primitive factory result on the same actual move. -/
theorem target_eq (value : Anchored bounds move count) :
    value.target = primitiveTarget bounds move count := value.1.property

/-- Read the same complete original signed source Point retained on the stored primitive target. -/
@[expose] def sourcePoint (value : Anchored bounds move count) : SourcePoint bounds value.target := value.2.1.val

/-- The signed source Point is the whole original source factory result on the same retained target. -/
theorem sourcePoint_eq (value : Anchored bounds move count) :
    value.sourcePoint = PrimitiveTarget.sourcePoint bounds value.target := value.2.1.property

/-- Read the same actual fixed source reading, paid alignment comparison and sampled anchor. -/
@[expose] def reference (value : Anchored bounds move count) : Reference bounds value.target value.sourcePoint :=
  value.2.2.val

/-- The source reference is the entire original factory result consuming the same retained target and source Point. -/
theorem reference_eq (value : Anchored bounds move count) :
    value.reference = PrimitiveTarget.reference bounds value.target value.sourcePoint := value.2.2.property

end Anchored

/-- The actual stored patch's seed box satisfies its own retained root-floor diameter bound. -/
theorem patch_diameter (cached : PrimitiveTarget bounds original count) :
    cached.patch.base.seed.owner.track.initial.box.diagonalSq ≤ cached.patch.rootLower / 256 :=
  Eq.mpr (congrArg (fun patch : ContinuedNeighborhood (Paths.polynomial parameter) count =>
    patch.base.seed.owner.track.initial.box.diagonalSq ≤ patch.rootLower / 256) cached.patch_eq)
    (cached.seed.neighborhood_diameter count)

namespace Reference

variable {cached : PrimitiveTarget bounds original count} {sourcePoint : SourcePoint bounds cached}

/-- Read the same cached original source reading without another approximation request. -/
@[expose] def sourceReading (value : Reference bounds cached sourcePoint) :
    OwnerTail.Reading cached.move.joined.leftTail := value.1.val

/-- The retained source reading is the complete original join-reading factory result. -/
theorem sourceReading_eq (value : Reference bounds cached sourcePoint) :
    value.sourceReading = cached.move.joined.leftReading := value.1.property

/-- Read the actual retained source-to-seed comparison with its original requested start and target. -/
@[expose] def comparison (value : Reference bounds cached sourcePoint) :
    SourceComparison bounds cached sourcePoint value.sourceReading := value.2.1.val

/-- The retained comparison is the complete original computed procedure result. -/
theorem comparison_eq (value : Reference bounds cached sourcePoint) :
    value.comparison = sourceComparison bounds cached sourcePoint value.sourceReading := value.2.1.property

/-- Read the original seed-owner sample cached at the actual selected comparison index. -/
@[expose] def anchor (value : Reference bounds cached sourcePoint) : Canonical := value.2.2.val

/-- The retained anchor is the exact selected raw sample of that same original source Point owner. -/
theorem anchor_eq (value : Reference bounds cached sourcePoint) :
    value.anchor = (ownerApproximation sourcePoint.1.owner).sample value.comparison.rightIndex := value.2.2.property

/-- The actual retained reference reading has positive squared norm. -/
theorem positive (value : Reference bounds cached sourcePoint) : 0 < value.sourceReading.norm :=
  cached.move.joined.leftTail.lower_positive.trans_le value.sourceReading.lower

/-- The actual selected seed anchor stays in this same original patch's retained seed box. -/
theorem anchor_inside (value : Reference bounds cached sourcePoint) :
    cached.patch.base.seed.owner.track.initial.box.Contains value.anchor := by
  rewrite [value.anchor_eq]
  exact sourcePoint.1.approximation_inside value.comparison.rightIndex

/-- The computed source-to-seed payment places its actual cached anchor near the same fixed source reading.

The source join already pays its sharper 256th-norm tail. Its retained
alignment pays the additional 1024th-norm distance, using the actual
selected indices rather than a successful-comparison premise.
-/
theorem near (value : Reference bounds cached sourcePoint) :
    normSq (value.anchor - value.sourceReading.value) ≤ value.sourceReading.norm / 64 := by
  have sourceNear := cached.move.joined.sample_near_leftReading value.comparison.leftIndex value.comparison.left_ge
  rewrite [← value.sourceReading_eq] at sourceNear
  have aligned := value.comparison.close (Nat.le_refl value.comparison.leftIndex)
    (Nat.le_refl value.comparison.rightIndex)
  rewrite [Norm.Basic.normSq_eq_canonical, ← value.anchor_eq] at aligned
  have reverse : normSq (value.anchor - (ownerApproximation source).sample value.comparison.leftIndex) =
      normSq ((ownerApproximation source).sample value.comparison.leftIndex - value.anchor) := by
    rewrite [show value.anchor - (ownerApproximation source).sample value.comparison.leftIndex =
      -((ownerApproximation source).sample value.comparison.leftIndex - value.anchor) by ring1,
      Basic.Canonical.normSq_neg]
    rfl
  have triangle := Norm.Bounds.normSq_sub_le_via value.anchor
    ((ownerApproximation source).sample value.comparison.leftIndex) value.sourceReading.value
  simp only [Norm.Basic.normSq_eq_canonical] at triangle
  rewrite [reverse] at triangle
  calc
    _ ≤ 2 * (normSq ((ownerApproximation source).sample value.comparison.leftIndex - value.anchor) +
        normSq ((ownerApproximation source).sample value.comparison.leftIndex - value.sourceReading.value)) := triangle
    _ ≤ 2 * (value.sourceReading.norm / 1024 + value.sourceReading.norm / 256) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Arithmetic.add_le_add_direct aligned.le sourceNear) (by decide +kernel)
    _ = (2 * ((1024 : Fraction.Rational)⁻¹ + (256 : Fraction.Rational)⁻¹)) * value.sourceReading.norm := by
      simp only [Fraction.Field.div_eq_mul_inv_direct]
      ring1
    _ ≤ (64 : Fraction.Rational)⁻¹ * value.sourceReading.norm :=
      Arithmetic.mul_le_mul_of_nonneg_right_direct (by decide +kernel) value.positive.le
    _ = value.sourceReading.norm / 64 := by
      rewrite [Fraction.Field.div_eq_mul_inv_direct]
      ring1

/-- Every actual Point sample on this same patch stays near the identical cached source reference. -/
theorem point_near (value : Reference bounds cached sourcePoint) {point : Canonical}
    (sample : ContinuedNeighborhood.Point cached.patch point) (index : Nat) :
    normSq ((ownerApproximation sample.owner).sample index - value.sourceReading.value) ≤
      value.sourceReading.norm / 16 :=
  sample.approximation_near_reference value.anchor value.sourceReading.value
    value.sourceReading.norm value.sourceReading.norm_eq
    value.positive.le value.anchor_inside value.near cached.patch_diameter index

/-- The same raw source samples stay near the unchanged original cached reading beyond their paid join floor. -/
theorem source_near (value : Reference bounds cached sourcePoint) (index : Nat)
    (later : cached.move.joined.comparison.leftIndex ≤ index) :
    normSq ((ownerApproximation source).sample index - value.sourceReading.value) ≤ value.sourceReading.norm / 16 := by
  have retained := cached.move.joined.sample_near_leftReading index later
  rewrite [← value.sourceReading_eq] at retained
  exact retained.trans (by
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    exact Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) value.positive.le)

/-- Compare an actual retained spatial-prefix owner with its same-point common primitive owner on the signed sheet.

The supplied original path and common Point remain unchanged. The original
path realization fixes the first tail, the retained seed alignment fixes
the second, and the shared numerical worker pays both actual root residuals.
-/
@[expose] def pathEquivalent (value : Reference bounds cached sourcePoint) {point : Canonical}
    {target : Owner ((Paths.polynomial parameter).eval point)}
    (path : OwnerPath (Paths.polynomial parameter)
      (coordinate site parameter 2 quarter (by decide +kernel) first) source point target)
    (movement : ∀ vertex ∈ path.vertices,
      normSq ((Paths.polynomial parameter).eval
          (coordinate site parameter 2 quarter (by decide +kernel) first) -
        (Paths.polynomial parameter).eval vertex) ≤ value.sourceReading.norm ^ 2 / 1024)
    (sample : ContinuedNeighborhood.Point cached.patch point) :
    Gaussian.Equivalence.Equivalent (ownerApproximation target) (ownerApproximation sample.owner) := by
  exact SquareRootTrackEquivalence.approximationEquivalent_of_near_reference
    (parameter := (Paths.polynomial parameter).eval point) target.track sample.owner.track
    value.sourceReading.value value.sourceReading.norm value.sourceReading.norm_eq value.positive
    (by
      unfold SquareRootTrackEquivalence.NearReference
      intro leftStart rightStart comparison index leftLater rightLater
      exact path.sample_near_reference value.sourceReading cached.move.joined.comparison.leftIndex
        (source_near bounds value) movement comparison index leftLater rightLater)
    (by
      unfold SquareRootTrackEquivalence.NearReference
      intro leftStart rightStart comparison index _ _
      exact (point_near bounds value sample index).trans (by
        simp only [Fraction.Field.div_eq_mul_inv_direct]
        exact Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) value.positive.le))

end Reference

/-- The identical original prepared source retained at the scalar Reading's exact radicand presentation.

This subtype stores the same complete owner and its whole equality to the
parent's fixed prepared source. It is a cache view, not another root owner
or an independently prepared continuation. Constructors can consume its
actual owner variable without opening the parent's source transport.
-/
@[expose] def CurveSource (cached : PrimitiveTarget bounds original count) : Type :=
  {retained : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) //
    retained = cached.move.prepared}

/-- Read the original fixed prepared owner once for all data of an interior continuation. -/
@[expose] def curveSource (cached : PrimitiveTarget bounds original count) : CurveSource bounds cached :=
  ⟨cached.move.prepared, rfl⟩

/-- The retained scalar source view has exactly the original preparation cache's root box. -/
theorem curveSource_box (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached) :
    prepared.val.track.initial.box = cached.move.cached.preparedOwner.track.initial.box := by
  rewrite [prepared.property]
  simp only [OwnerMove.prepared, CachedSource.startPrepared, Transport.castOwnerParameter_initial_box,
    -eq_self, -iff_self]
  rfl

/-- The retained scalar source view has exactly the original preparation cache's clearance payment. -/
theorem curveSource_clearance (cached : PrimitiveTarget bounds original count)
    (prepared : CurveSource bounds cached) :
    prepared.val.track.initial.clearance.bound = cached.move.cached.preparedOwner.track.initial.clearance.bound := by
  rewrite [prepared.property]
  simp only [OwnerMove.prepared, CachedSource.startPrepared, Transport.castOwnerParameter_clearance_bound,
    -eq_self, -iff_self]
  rfl

/-- The actual original source Reading agrees with the same retained source view through its stored original join. -/
@[expose] def curveSourceEquivalent (cached : PrimitiveTarget bounds original count)
    (prepared : CurveSource bounds cached) :
    NamedEquivalent reading.lift.value.name
      (prepared.val.certificate prepared.val.parameterNonzero).value.name := by
  let related := sourceAgreement.symm.trans (OwnerJoin.equivalent
    (parameter := (Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) cached.move.joined)
  have equal := congrArg (fun retained : Owner ((Paths.polynomial parameter).eval
    (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base) =>
      (retained.certificate retained.parameterNonzero).value.name) prepared.property
  exact NamedEquivalent.transport rfl equal.symm related

/-- The original movement payment fits the identical fixed prepared source at every actual interior coordinate. -/
theorem curve_small (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) (between : first ≤ time ∧ time ≤ last) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base -
      (Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) <
      prepared.val.track.initial.clearance.bound := by
  have movementPaid := leg.source.residualTimeRequest_pays_lt
    (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val
    (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq) _
    (curve_paid bounds cached time between)
  have retained := (coarse.movement_endpoints first time).trans_lt movementPaid
  have lower := budget.floor_le_prepared geometry source cached.move.cached
  rewrite [CachedSource.startPrepared, Transport.castOwnerParameter_clearance_bound] at lower
  rewrite [curveSource_clearance bounds cached prepared]
  exact (retained.trans_le budget.tolerance_le_floor).trans_le lower

/-- The same retained fixed-source diameter pays signed selection for every actual intermediate owner. -/
theorem curve_prepared_small (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) (between : first ≤ time ∧ time ≤ last)
    (target : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base)) :
    prepared.val.track.initial.box.diagonalSq ≤
      (target.certificate target.parameterNonzero).apart.certificate.lowerSq / 16 := by
  have retained := budget.prepared_small_on_box (source := source) geometry cached.move.cached
    (interval_inside leg.regular payment time between) target
  rewrite [CachedSource.startPrepared, Transport.castOwnerParameter_initial_box] at retained
  rewrite [curveSource_box bounds cached prepared]
  exact retained

/-- The original time payment pays the source Reading's signed residual request at every actual intermediate owner. -/
theorem curve_pair_paid (cached : PrimitiveTarget bounds original count) (time : Fraction.Rational)
    (between : first ≤ time ∧ time ≤ last)
    (target : Owner ((Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base)) :
    (first - time) ^ 2 ≤ (reading.residualTimeRequest
      (reading.pairRequest leg.regular (Reading.ownerDistance target)) (leg.traceMovement coarse.bounds)
      (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)).tolerance :=
  (curve_paid bounds cached time between).le.trans (reading.residualTimeRequest_mono _ _
    (budget.tolerance_le_pair_on_box geometry (interval_inside leg.regular payment time between) target)
    (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq))

/-- The original actual move from the retained fixed source to one contained intermediate quarter point. -/
@[expose] def CurveTarget (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) (between : first ≤ time ∧ time ≤ last) : Type :=
  Target (targetParameter := (Paths.polynomial parameter).eval
    (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base)
    prepared.val (curve_nonzero bounds cached time between) (curve_small bounds cached prepared time between)

/-- Move the same fixed prepared source once to the actual intermediate coordinate.

Nonvanishing and movement are derived from the retained quarter data and
payment. The original paid endpoint target is unchanged; this is a distinct
actual occurrence strictly inside that endpoint interval.
-/
@[expose] def curveTarget (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) (between : first ≤ time ∧ time ≤ last) :
    CurveTarget bounds cached prepared time between :=
  ⟨prepared.val.advance
    (source := (Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base)
    (target := (Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base)
    (curve_nonzero bounds cached time between) (curve_small bounds cached prepared time between), rfl⟩

/-- The actual intermediate continuation refines the identical fixed prepared source of its retained parent. -/
theorem curve_refines (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) (between : first ≤ time ∧ time ≤ last)
    (target : CurveTarget bounds cached prepared time between) :
    target.val.track.initial.box.Refines prepared.val.track.initial.box :=
  Target.refines
    (sourceParameter := (Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter first) (by decide +kernel)).base)
    (targetParameter := (Paths.polynomial parameter).eval
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base)
    (source := prepared.val) (nonzero := curve_nonzero bounds cached time between)
    (small := curve_small bounds cached prepared time between) target

/-- The exact original signed comparison cache on a supplied interior Reading and the actual retained continuation. -/
@[expose] def CurveCompared (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) {timeInside : FixedRootBoxPath.Inside time}
    (pointReading : Reading leg.actual time timeInside) (between : first ≤ time ∧ time ≤ last)
    (target : CurveTarget bounds cached prepared time between)
    (residuals : Reading.PairResiduals reading pointReading leg.regular
      (Reading.ownerDistance target.val) 0 0) : Type :=
  Compared reading pointReading leg.regular prepared.val target.val
    (curveSourceEquivalent bounds cached prepared).symm (curve_refines bounds cached prepared time between target)
    (curve_prepared_small bounds cached prepared time between target.val)
    (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
    (coarse.movement_endpoints first time) (curve_pair_paid bounds cached time between target.val) 0 0 residuals

/-- Compare the actual intermediate continuation with its original scalar Reading using the same residual cache. -/
@[expose] def curveCompared (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) {timeInside : FixedRootBoxPath.Inside time}
    (pointReading : Reading leg.actual time timeInside) (between : first ≤ time ∧ time ≤ last)
    (target : CurveTarget bounds cached prepared time between)
    (residuals : Reading.PairResiduals reading pointReading leg.regular (Reading.ownerDistance target.val) 0 0) :
    CurveCompared bounds cached prepared time pointReading between target residuals :=
  ⟨reading.ownerAgreementOfResiduals pointReading leg.regular prepared.val target.val
    (curveSourceEquivalent bounds cached prepared).symm (curve_refines bounds cached prepared time between target)
    (curve_prepared_small bounds cached prepared time between target.val)
    (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
    (coarse.movement_endpoints first time) (curve_pair_paid bounds cached time between target.val) 0 0 residuals, rfl⟩

namespace CurveCompared

/-- Read the original target-to-scalar relation from an actual retained interior comparison. -/
@[expose] def agrees (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) {timeInside : FixedRootBoxPath.Inside time}
    (pointReading : Reading leg.actual time timeInside) (between : first ≤ time ∧ time ≤ last)
    (target : CurveTarget bounds cached prepared time between)
    (residuals : Reading.PairResiduals reading pointReading leg.regular (Reading.ownerDistance target.val) 0 0)
    (value : CurveCompared bounds cached prepared time pointReading between target residuals) :
    NamedEquivalent (target.val.certificate target.val.parameterNonzero).value.name
      pointReading.lift.value.name :=
  Reading.OwnerAgreement.agrees reading pointReading leg.regular prepared.val target.val
    (curveSourceEquivalent bounds cached prepared).symm residuals value.val

end CurveCompared

/-- The actual intermediate continuation agrees with the original Point on the same retained primitive patch. -/
@[expose] def curveTargetEquivalent (cached : PrimitiveTarget bounds original count)
    (prepared : CurveSource bounds cached) (time : Fraction.Rational) (between : first ≤ time ∧ time ≤ last)
    (target : CurveTarget bounds cached prepared time between)
    (sample : ContinuedNeighborhood.Point cached.patch
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) :
    NamedEquivalent (target.val.certificate target.val.parameterNonzero).value.name
      sample.certificate.value.name := by
  have refines := curve_refines bounds cached prepared time between target
  rewrite [curveSource_box bounds cached prepared] at refines
  have small := curve_small bounds cached prepared time between
  rewrite [curveSource_clearance bounds cached prepared, Norm.Basic.normSq_eq_canonical] at small
  have moved : normSq ((Paths.polynomial parameter).eval
      ((geometry.chord coarse.bounds coarse.bounds_eq).pointAt 0) -
      (Paths.polynomial parameter).eval
        (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) <
      cached.move.cached.preparedOwner.track.initial.clearance.bound := by
    exact Eq.mpr (congrArg (fun start : Canonical =>
      normSq ((Paths.polynomial parameter).eval start -
        (Paths.polynomial parameter).eval
          (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base) <
            cached.move.cached.preparedOwner.track.initial.clearance.bound)
      (geometry.chord coarse.bounds coarse.bounds_eq).pointAt_zero) small
  have inside : (cached.seed.neighborhood count).box.Contains
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base :=
    Eq.mp (congrArg (fun patch : ContinuedNeighborhood (Paths.polynomial parameter) count =>
      patch.box.Contains (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base)
      cached.patch_eq)
      (curve_inside bounds cached time between)
  let viewed := ContinuedNeighborhood.Point.castPatch cached.patch_eq.symm sample
  let compared := UniformPrimitiveSheetCompatibility.Bounds.PreparedSeed.pointEquivalent cached.seed count
    inside target.val refines moved viewed
  exact NamedEquivalent.transport rfl
    (ContinuedNeighborhood.Point.castPatch_name cached.patch_eq.symm sample) compared

/-- The original parent and fixed source, scalar Reading, actual interior move and same-patch Point retained together.

Only existing exact Sigma and subtype views store these original values.
The whole factory equations bind the actual cached work. The supplied parent
retains its unchanged endpoint target and original source attachment.
-/
@[expose] def CurvePoint (cached : PrimitiveTarget bounds original count) (time : Fraction.Rational)
    {timeInside : FixedRootBoxPath.Inside time} (pointReading : Reading leg.actual time timeInside)
    (interior : first < time ∧ time < last) : Type 1 :=
  Σ parent : {actual : PrimitiveTarget bounds original count // actual = cached},
  Σ prepared : CurveSource bounds parent.val,
  Σ retainedReading : {actual : Reading leg.actual time timeInside // actual = pointReading},
  Σ target : CurveTarget bounds parent.val prepared time ⟨interior.1.le, interior.2.le⟩,
  Σ residuals : Residuals reading retainedReading.val leg.regular (Reading.ownerDistance target.val) 0 0,
  Σ _compared : CurveCompared bounds parent.val prepared time retainedReading.val ⟨interior.1.le, interior.2.le⟩
      target residuals.val,
  Σ sample : ContinuedNeighborhood.Point parent.val.patch
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base,
    NamedEquivalent (target.val.certificate target.val.parameterNonzero).value.name
      sample.certificate.value.name

section CoefficientBudget

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Approximation.Rational.Geometric

variable {cellRadicand : Purelib.Algebra.Quadratic.Pair.Polynomial.Coefficients}
variable {cellDifferential : OddPowerDifferential cellRadicand}
variable {cellData : WaistBounds site parameter cellDifferential}
variable {span : Interval.Bounds} {cellInside : FixedRootBoxPath.Inside span.lower}
variable {cellReading : Reading leg.actual span.lower cellInside} {cellAccuracy : AccuracyRequest}

/-- The actual numerator ceiling multiplied by the original finite odd-power sensitivity.

The zero-pair branch is the literal original tangent-numerator ceiling.
Higher pairs use the same uniform inverse-model and root-comparison floors;
no scalar observation, future root or polynomial model is constructed.
-/
@[expose] def coefficientWeight (cached : PrimitiveTarget bounds original count)
    (data : WaistBounds site parameter cellDifferential) (pairCount : Nat) : Fraction.Rational :=
  let weight := Radial.Differential.Bounds.tangentNumeratorBound data
  match pairCount with
  | 0 => weight
  | remaining + 1 =>
      let upper := 2 * (cached.patch.inverseErrorScale + cached.patch.rootLower⁻¹) +
        (Model.comparisonFloor reading cached.patch)⁻¹
      weight * Norm.Power.differenceFactor upper (2 * (remaining + 1) + 1)

/-- The same original numerator and denominator payments make every computed coefficient weight nonnegative. -/
private theorem coefficientWeight_nonnegative (cached : PrimitiveTarget bounds original count)
    (data : WaistBounds site parameter cellDifferential) (pairCount : Nat) :
    0 ≤ coefficientWeight bounds cached data pairCount := by
  have weight := Radial.Differential.Bounds.tangentNumeratorBound_nonnegative data
  cases pairCount with
  | zero => exact weight
  | succ remaining =>
      have upperNonnegative : 0 ≤ 2 * (cached.patch.inverseErrorScale + cached.patch.rootLower⁻¹) +
          (Model.comparisonFloor reading cached.patch)⁻¹ :=
        Fraction.Order.add_nonnegative
          (Arithmetic.mul_nonneg_direct (by decide +kernel)
            (Fraction.Order.add_nonnegative cached.patch.inverseErrorScale_positive.le
              (Fraction.Order.Field.inv_pos_direct cached.patch.rootLower_positive).le))
          (Fraction.Order.Field.inv_pos_direct (Model.comparisonFloor_paid reading cached.patch leg.regular).1).le
      exact Arithmetic.mul_nonneg_direct weight
        (Norm.Power.differenceFactor_nonnegative upperNonnegative _)

/-- The uniform original coefficient scale for the common inverse model's geometric error. -/
@[expose] def modelErrorScale (cached : PrimitiveTarget bounds original count)
    (data : WaistBounds site parameter cellDifferential) (pairCount : optParam Nat 0) :
    Fraction.Rational :=
  2 * coefficientWeight bounds cached data pairCount * cached.patch.inverseErrorScale

/-- The original coefficient's uniform model-error scale is nonnegative. -/
private theorem modelErrorScale_nonnegative (cached : PrimitiveTarget bounds original count)
    (data : WaistBounds site parameter cellDifferential) (pairCount : Nat) :
    0 ≤ modelErrorScale bounds cached data pairCount :=
  Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (coefficientWeight_nonnegative bounds cached data pairCount)) cached.patch.inverseErrorScale_positive.le

/-- The uniform original coefficient scale for actual scalar-cell accuracy at a retained initial tolerance. -/
@[expose] def samplingErrorScale (cached : PrimitiveTarget bounds original count)
    (data : WaistBounds site parameter cellDifferential) (initialAccuracy : AccuracyRequest)
    (pairCount : optParam Nat 0) : Fraction.Rational :=
  2 * coefficientWeight bounds cached data pairCount *
    ((Model.comparisonFloor reading cached.patch)⁻¹ *
      (Model.comparisonFloor reading cached.patch)⁻¹) *
      (16 * (((25 / 4) * data.gapNorm) + 1) + 4) * initialAccuracy.tolerance

/-- The original coefficient's uniform sampling-error scale is nonnegative. -/
private theorem samplingErrorScale_nonnegative (cached : PrimitiveTarget bounds original count)
    (data : WaistBounds site parameter cellDifferential) (initialAccuracy : AccuracyRequest)
    (pairCount : Nat) : 0 ≤ samplingErrorScale bounds cached data initialAccuracy pairCount := by
  have inverseNonnegative :=
    (Fraction.Order.Field.inv_pos_direct (Model.comparisonFloor_paid reading cached.patch leg.regular).1).le
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel)
          (coefficientWeight_nonnegative bounds cached data pairCount))
        (Arithmetic.mul_nonneg_direct inverseNonnegative inverseNonnegative))
      (Fraction.Order.add_nonnegative
        (Arithmetic.mul_nonneg_direct (by decide +kernel)
          (Fraction.Order.add_nonnegative
            (Arithmetic.mul_nonneg_direct (by decide +kernel) data.gapNorm_nonnegative)
            (by decide +kernel))) (by decide +kernel))) initialAccuracy.positive.le

/-- Compute and retain the actual finite model and scalar stages paying the same requested coefficient target.

One retained numerator ceiling and one common inverse floor feed both
original bounded quarter-radius searches. The target is divided once;
actual scale, quotient, fuel, stage and allowance caches remain in the two
original Selection objects. No future cell or root is acquired to select.
-/
def coefficientSelections (cached : PrimitiveTarget bounds original count)
    (data : WaistBounds site parameter cellDifferential) (initialAccuracy : AccuracyRequest)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (pairCount : optParam Nat 0) :
    Search.Selection (modelErrorScale bounds cached data pairCount) modelFloor (target / 2) ×
      Search.Selection (samplingErrorScale bounds cached data initialAccuracy pairCount) scalarFloor (target / 2) := by
  let weight := coefficientWeight bounds cached data pairCount
  let inverseFloor := (Model.comparisonFloor reading cached.patch)⁻¹
  let modelScale := 2 * weight * cached.patch.inverseErrorScale
  let sampleScale := 2 * weight * (inverseFloor * inverseFloor) *
    (16 * (((25 / 4) * data.gapNorm) + 1) + 4) * initialAccuracy.tolerance
  let halfTarget := target / 2
  have halfPositive : 0 < halfTarget := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have modelNonnegative : 0 ≤ modelScale := modelErrorScale_nonnegative bounds cached data pairCount
  have sampleNonnegative : 0 ≤ sampleScale :=
    samplingErrorScale_nonnegative bounds cached data initialAccuracy pairCount
  exact ⟨Search.Selection.build modelScale modelNonnegative modelFloor halfTarget halfPositive,
    Search.Selection.build sampleScale sampleNonnegative scalarFloor halfTarget halfPositive⟩

/-- The omitted pair index retains the complete original two-search factory and all of its finite payment caches.

Only proofs of the original two scalar-scale signs are parameters of this
readback. The original numerator, inverse floor, target split, ordered
searches and starting floors remain unchanged as complete Selection values.
-/
theorem coefficientSelections_zero_eq (cached : PrimitiveTarget bounds original count)
    (data : WaistBounds site parameter cellDifferential) (initialAccuracy : AccuracyRequest)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (modelNonnegative : 0 ≤ modelErrorScale bounds cached data)
    (sampleNonnegative : 0 ≤ samplingErrorScale bounds cached data initialAccuracy) :
    coefficientSelections bounds cached data initialAccuracy modelFloor scalarFloor target positive =
      (let weight := Radial.Differential.Bounds.tangentNumeratorBound data
       let inverseFloor := (Model.comparisonFloor reading cached.patch)⁻¹
       let modelScale := 2 * weight * cached.patch.inverseErrorScale
       let sampleScale := 2 * weight * (inverseFloor * inverseFloor) *
         (16 * (((25 / 4) * data.gapNorm) + 1) + 4) * initialAccuracy.tolerance
       let halfTarget := target / 2
       have halfPositive : 0 < halfTarget := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
       (Search.Selection.build modelScale modelNonnegative modelFloor halfTarget halfPositive,
         Search.Selection.build sampleScale sampleNonnegative scalarFloor halfTarget halfPositive)) := (rfl)

/-- The same actual paid coefficient request obeys separate uniform model-stage and scalar-depth geometric bounds.

The original scalar accuracy equation is an exact Layer readback. The
retained numerator/Horner and half-gap caches give a uniform sensitivity,
while the actual root request supplies both radius payments. Neither
coefficient decay nor a desired comparison inequality is an input.
-/
theorem coefficient_error_le (cached : PrimitiveTarget bounds original count)
    (cell : Model cellData cellReading cellAccuracy)
    {stage : Nat} {inverse : InverseRootPolynomial.Model (Paths.polynomial parameter) cached.patch.base.box}
    {powers : OddPowers inverse.value}
    {sample : ContinuedNeighborhood.Point cached.patch
      (point site parameter 2 (Waist.direction quarter span.lower) (by decide +kernel)).base}
    (sameModel : inverse = cached.patch.base.refine stage)
    {numerator : InverseRootPolynomial.Polynomial} {pairCount : Nat}
    (common : PrimitiveModel cached.patch stage numerator pairCount)
    (request : Model.CoefficientRequest (sample := sample) (powers := powers)
      cell sameModel common)
    (initialAccuracy : AccuracyRequest) (depth : Nat)
    (accuracy_eq : cellAccuracy.tolerance = Geometric.Basic.quarterRadius initialAccuracy.tolerance depth) :
    cell.primitiveResidual common.coefficient ≤
      Geometric.Basic.quarterRadius (modelErrorScale bounds cached cellData pairCount) stage +
        Geometric.Basic.quarterRadius (samplingErrorScale bounds cached cellData initialAccuracy pairCount) depth := by
  have attained := request.2.2.property.2
  have allowanceNonnegative : 0 ≤ cell.comparisonAllowance :=
    (Norm.Basic.normSq_nonneg request.2.2.val.residual).trans
      (request.2.2.val.residual_le.trans request.2.2.property.1)
  have inverseNonnegative :=
    (Fraction.Order.Field.inv_pos_direct (Model.comparisonFloor_paid reading cached.patch leg.regular).1).le
  have errorNonnegative := Arithmetic.mul_nonneg_direct
    (by decide +kernel : (0 : Fraction.Rational) ≤ 2)
    (Fraction.Order.add_nonnegative
      (Geometric.Basic.quarterRadius_nonneg cached.patch.inverseErrorScale_positive.le stage)
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct inverseNonnegative inverseNonnegative) allowanceNonnegative))
  have weightBound := Radial.Differential.Bounds.tangentNumerator_normSq_le
    cellData quarter leg.actual.data.bound span.lower
  have upperNonnegative : 0 ≤ 2 * (cached.patch.inverseErrorScale + cached.patch.rootLower⁻¹) +
      (Model.comparisonFloor cellReading cached.patch)⁻¹ :=
    Fraction.Order.add_nonnegative
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Fraction.Order.add_nonnegative cached.patch.inverseErrorScale_positive.le
          (Fraction.Order.Field.inv_pos_direct cached.patch.rootLower_positive).le)) inverseNonnegative
  have weightedErrorNonnegative : 0 ≤
      ((fun count : Nat => match count with
      | 0 => 2 * (Geometric.Basic.quarterRadius cached.patch.inverseErrorScale stage +
          ((Model.comparisonFloor cellReading cached.patch)⁻¹ *
            (Model.comparisonFloor cellReading cached.patch)⁻¹) * cell.comparisonAllowance)
      | remaining + 1 => Norm.Power.differenceFactor
          (2 * (cached.patch.inverseErrorScale + cached.patch.rootLower⁻¹) +
            (Model.comparisonFloor cellReading cached.patch)⁻¹) (2 * (remaining + 1) + 1) *
          (2 * (Geometric.Basic.quarterRadius cached.patch.inverseErrorScale stage +
            ((Model.comparisonFloor cellReading cached.patch)⁻¹ *
              (Model.comparisonFloor cellReading cached.patch)⁻¹) * cell.comparisonAllowance))) pairCount) := by
    cases pairCount with
    | zero => exact errorNonnegative
    | succ remaining =>
        exact Arithmetic.mul_nonneg_direct
          (Norm.Power.differenceFactor_nonnegative upperNonnegative _) errorNonnegative
  have uniform := attained.trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct weightBound weightedErrorNonnegative)
  have sameFloor : Model.comparisonFloor cellReading cached.patch =
      Model.comparisonFloor reading cached.patch := (rfl)
  rewrite [sameFloor] at uniform
  exact uniform.trans_eq (by
    unfold modelErrorScale samplingErrorScale coefficientWeight Model.comparisonAllowance
    rewrite [accuracy_eq, ← cellData.gapNorm_eq]
    cases pairCount <;> simp only [Geometric.Basic.quarterRadius_eq_mul_pow] <;> ring1)

/-- The computed two finite stages strictly pay the original coefficient request on the actual scalar cell and model.

The stages are selected by the original bounded searches, and the accuracy
equation is the scalar Layer's exact cached readback. Actual later stages
preserve both payments. No successful root search or residual-decay premise
is substituted for the original retained numerical observations.
-/
theorem coefficient_error_lt (cached : PrimitiveTarget bounds original count)
    (cell : Model cellData cellReading cellAccuracy)
    {stage : Nat} {inverse : InverseRootPolynomial.Model (Paths.polynomial parameter) cached.patch.base.box}
    {powers : OddPowers inverse.value}
    {sample : ContinuedNeighborhood.Point cached.patch
      (point site parameter 2 (Waist.direction quarter span.lower) (by decide +kernel)).base}
    (sameModel : inverse = cached.patch.base.refine stage)
    {numerator : InverseRootPolynomial.Polynomial} {pairCount : Nat}
    (common : PrimitiveModel cached.patch stage numerator pairCount)
    (request : Model.CoefficientRequest (sample := sample) (powers := powers)
      cell sameModel common)
    (initialAccuracy : AccuracyRequest) (depth modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (accuracy_eq : cellAccuracy.tolerance = Geometric.Basic.quarterRadius initialAccuracy.tolerance depth)
    (modelAfter : (coefficientSelections bounds cached cellData initialAccuracy
      modelFloor scalarFloor target positive pairCount).1.stage ≤ stage)
    (scalarAfter : (coefficientSelections bounds cached cellData initialAccuracy
      modelFloor scalarFloor target positive pairCount).2.stage ≤ depth) :
    cell.primitiveResidual common.coefficient < target := by
  have bound := coefficient_error_le bounds cached cell sameModel common request initialAccuracy depth accuracy_eq
  have first := (coefficientSelections bounds cached cellData initialAccuracy
    modelFloor scalarFloor target positive pairCount).1.later_accurate modelAfter
  have last := (coefficientSelections bounds cached cellData initialAccuracy
    modelFloor scalarFloor target positive pairCount).2.later_accurate scalarAfter
  have grouped : target / 2 + target / 2 = target := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct]
    have half : (2 : Fraction.Rational)⁻¹ + (2 : Fraction.Rational)⁻¹ = 1 := by decide +kernel
    calc
      _ = target * ((2 : Fraction.Rational)⁻¹ + (2 : Fraction.Rational)⁻¹) := by ring1
      _ = target := by rewrite [half, Fraction.Field.mul_one_direct]; rfl
  exact bound.trans_lt ((Arithmetic.add_lt_add_direct first last).trans_eq grouped)

end CoefficientBudget

namespace CurvePoint

/-- Assemble the original interior cache from its actual supplied values without replaying any producer. -/
@[expose] def ofData (cached : PrimitiveTarget bounds original count) (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) {timeInside : FixedRootBoxPath.Inside time}
    (pointReading : Reading leg.actual time timeInside) (interior : first < time ∧ time < last)
    (target : CurveTarget bounds cached prepared time ⟨interior.1.le, interior.2.le⟩)
    (residuals : Residuals reading pointReading leg.regular (Reading.ownerDistance target.val) 0 0)
    (compared : CurveCompared bounds cached prepared time pointReading ⟨interior.1.le, interior.2.le⟩
      target residuals.val)
    (sample : ContinuedNeighborhood.Point cached.patch
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base)
    (equivalent : NamedEquivalent
      (target.val.certificate target.val.parameterNonzero).value.name sample.certificate.value.name) :
    CurvePoint bounds cached time pointReading interior :=
  ⟨⟨cached, rfl⟩, prepared, ⟨pointReading, rfl⟩, target, residuals, compared, sample, equivalent⟩

variable {cached : PrimitiveTarget bounds original count} {time : Fraction.Rational}
variable {timeInside : FixedRootBoxPath.Inside time} {pointReading : Reading leg.actual time timeInside}
variable {interior : first < time ∧ time < last}

/-- Read the whole original primitive parent, including its unchanged paid endpoint and fixed source caches. -/
@[expose] def parent (value : CurvePoint bounds cached time pointReading interior) :
    PrimitiveTarget bounds original count := value.1.val

/-- The interior cache retains the entire supplied original primitive parent. -/
theorem parent_eq (value : CurvePoint bounds cached time pointReading interior) : value.parent = cached :=
  value.1.property

/-- Read the original fixed prepared source actually consumed by this interior continuation. -/
@[expose] def prepared (value : CurvePoint bounds cached time pointReading interior) :
    CurveSource bounds value.parent := value.2.1

/-- Read the original interior scalar Reading with its unchanged cofactor and lift caches. -/
@[expose] def scalarReading (value : CurvePoint bounds cached time pointReading interior) :
    Reading leg.actual time timeInside := value.2.2.1.val

/-- The retained scalar Reading is the entire supplied original value. -/
theorem scalarReading_eq (value : CurvePoint bounds cached time pointReading interior) :
    value.scalarReading = pointReading := value.2.2.1.property

/-- Read the actual intermediate continuation and its full original advance equation. -/
@[expose] def target (value : CurvePoint bounds cached time pointReading interior) :
    CurveTarget bounds value.parent value.prepared time ⟨interior.1.le, interior.2.le⟩ := value.2.2.2.1

/-- Read both actual original pair-residual comparisons at their unchanged zero starts. -/
@[expose] def residuals (value : CurvePoint bounds cached time pointReading interior) :
    Residuals reading value.scalarReading leg.regular (Reading.ownerDistance value.target.val) 0 0 := value.2.2.2.2.1

/-- Read the actual signed owner comparison with its complete original producer equation. -/
@[expose] def compared (value : CurvePoint bounds cached time pointReading interior) :
    CurveCompared bounds value.parent value.prepared time value.scalarReading ⟨interior.1.le, interior.2.le⟩
      value.target value.residuals.val := value.2.2.2.2.2.1

/-- Read the actual Point stored once on its retained parent's primitive neighborhood. -/
@[expose] def storedSample (value : CurvePoint bounds cached time pointReading interior) :
    ContinuedNeighborhood.Point value.parent.patch
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base := value.2.2.2.2.2.2.1

/-- Read the same Point on the supplied original primitive parent through its whole retained equality.

The original exact neighborhood transport preserves the complete Point and
its numerical channel. This view lets the original supplied primitive bank
consume that same Point without rebuilding a model or acquiring an owner.
-/
@[expose] def sample (value : CurvePoint bounds cached time pointReading interior) :
    ContinuedNeighborhood.Point cached.patch
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base :=
  ContinuedNeighborhood.Point.castPatch
    (congrArg (fun retained : PrimitiveTarget bounds original count => retained.patch) value.parent_eq).symm
    value.storedSample

/-- Reindexing to the original parent's patch retains the entire original Point heterogeneously. -/
theorem sample_heq (value : CurvePoint bounds cached time pointReading interior) :
    HEq value.sample value.storedSample :=
  ContinuedNeighborhood.Point.castPatch_heq _ _

/-- The exact original Point name is unchanged by its whole-parent patch view. -/
theorem sample_name (value : CurvePoint bounds cached time pointReading interior) :
    value.sample.certificate.value.name = value.storedSample.certificate.value.name :=
  ContinuedNeighborhood.Point.castPatch_name _ _

/-- Read the signed relation between the actual intermediate continuation and the identical original primitive Point. -/
@[expose] def equivalent (value : CurvePoint bounds cached time pointReading interior) :
    NamedEquivalent (value.target.val.certificate value.target.val.parameterNonzero).value.name
      value.sample.certificate.value.name :=
  NamedEquivalent.transport rfl value.sample_name.symm value.2.2.2.2.2.2.2

/-- The retained original scalar Reading has exactly its supplied input's numerical name. -/
theorem scalarReading_name (value : CurvePoint bounds cached time pointReading interior) :
    value.scalarReading.lift.value.name = pointReading.lift.value.name :=
  congrArg (fun retained : Reading leg.actual time timeInside => retained.lift.value.name) value.scalarReading_eq

/-- Read the original target-to-scalar relation without reducing the complete cached comparison record. -/
@[expose] def ownerAgreement (value : CurvePoint bounds cached time pointReading interior) :
    NamedEquivalent (value.target.val.certificate value.target.val.parameterNonzero).value.name
      value.scalarReading.lift.value.name :=
  CurveCompared.agrees bounds value.parent value.prepared time value.scalarReading
    ⟨interior.1.le, interior.2.le⟩ value.target value.residuals.val value.compared

/-- The retained scalar Reading agrees with the actual Point on the same stored parent before index transport. -/
@[expose] def storedReadingEquivalent (value : CurvePoint bounds cached time pointReading interior) :
    NamedEquivalent value.scalarReading.lift.value.name
      value.storedSample.certificate.value.name :=
  value.ownerAgreement.symm.trans value.2.2.2.2.2.2.2

/-- The original scalar Reading lies on the signed sheet of the same retained primitive Point.

Both computed relations consume their stored original owner and residual
caches. Whole Reading and parent equalities preserve the actual supplied
inputs and original Point; no scalar query or root is constructed again.
-/
@[expose] def readingEquivalent (value : CurvePoint bounds cached time pointReading interior) :
    NamedEquivalent pointReading.lift.value.name value.sample.certificate.value.name :=
  NamedEquivalent.transport value.scalarReading_name value.sample_name.symm
    value.storedReadingEquivalent

section ScalarCell

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point (PrimitiveReading)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Normalization
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Approximation.Gaussian

variable {cellRadicand : Purelib.Algebra.Quadratic.Pair.Polynomial.Coefficients}
variable {cellDifferential : OddPowerDifferential cellRadicand}
variable {cellData : WaistBounds site parameter cellDifferential}
variable {span : Interval.Bounds} {cellInside : FixedRootBoxPath.Inside span.lower}
variable {cellReading : Reading leg.actual span.lower cellInside}
variable {cellInterior : first < span.lower ∧ span.lower < last} {cellAccuracy : AccuracyRequest}
variable {stage : Nat} {inverse : InverseRootPolynomial.Model (Paths.polynomial parameter) cached.patch.base.box}
variable {powers : OddPowers inverse.value}

/-- Compare an actual scalar cell with the shared actual primitive-root reading on this same retained interior Point.

The signed relation is derived from the original cached continuation and
Point. Both existing Reading objects retain their real states and values;
the original finite comparison computes its own paid tails and radius bound.
No successful comparison, sheet identification or sample inequality is an input.
-/
def compareCell (value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (cell : Model cellData cellReading cellAccuracy)
    (shared : PrimitiveReading value.sample stage inverse powers)
    (target : Fraction.Rational) (positive : 0 < target) :
    Equivalence.Observation.Comparison cell.rootReading shared.rootReading target :=
  cell.comparePrimitive value.readingEquivalent shared target positive

/-- The real zero-pair scalar coefficient is controlled by the same retained primitive and paid root comparison.

Original curve containment derives the inverse-model domain internally.
The computed minimum of the actual source and patch floors pays reciprocal
sensitivity on both original readings. The numerator, scale and common
primitive coefficient retain their actual complete original presentations.
-/
theorem cell_primitiveResidual_le (value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (cell : Model cellData cellReading cellAccuracy)
    (pairs : cellDifferential.denominatorPairs = 0) (scale : cellDifferential.scale = 1)
    (shared : PrimitiveReading value.sample stage inverse powers)
    (common : PrimitiveModel cached.patch stage cellDifferential.numerator)
    {target : Fraction.Rational}
    (comparison : Equivalence.Observation.Comparison cell.rootReading shared.rootReading target) :
    cell.primitiveResidual common.coefficient ≤
      Norm.Basic.normSq ((cellDifferential.scale * cellDifferential.numerator.eval
        (Radial.point site parameter 2 (Waist.direction quarter span.lower) (by decide +kernel)).base) *
          Tangent.baseVelocity site parameter 2 quarter span.lower) *
        (2 * (Geometric.Basic.quarterRadius cached.patch.inverseErrorScale stage +
          ((Model.comparisonFloor cellReading cached.patch)⁻¹ *
            (Model.comparisonFloor cellReading cached.patch)⁻¹) * comparison.bound)) := by
  exact cell.primitiveComparison_le pairs (fun location => ((congrArg (fun factor : Canonical =>
      factor * cellDifferential.numerator.eval location) scale).trans (Basic.one_mul _)).symm) shared common
    (curve_inside bounds cached span.lower ⟨cellInterior.1.le, cellInterior.2.le⟩) comparison

/-- Compute and retain the actual comparison whose paid residual controls the same original scalar coefficient.

This combines the original comparison producer with its internally derived
coefficient estimate. It retains the comparison itself as the existing
nominal owner; the additional coefficient guarantee is erased proof data.
-/
def coefficientComparison (value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (cell : Model cellData cellReading cellAccuracy)
    (pairs : cellDifferential.denominatorPairs = 0) (scale : cellDifferential.scale = 1)
    (shared : PrimitiveReading value.sample stage inverse powers)
    (common : PrimitiveModel cached.patch stage cellDifferential.numerator)
    (target : Fraction.Rational) (positive : 0 < target) :
    {actual : Equivalence.Observation.Comparison cell.rootReading shared.rootReading target //
      cell.primitiveResidual common.coefficient ≤
        Norm.Basic.normSq ((cellDifferential.scale * cellDifferential.numerator.eval
          (Radial.point site parameter 2 (Waist.direction quarter span.lower) (by decide +kernel)).base) *
            Tangent.baseVelocity site parameter 2 quarter span.lower) *
          (2 * (Geometric.Basic.quarterRadius cached.patch.inverseErrorScale stage +
            ((Model.comparisonFloor cellReading cached.patch)⁻¹ *
              (Model.comparisonFloor cellReading cached.patch)⁻¹) * actual.bound))} := by
  let comparison : Equivalence.Observation.Comparison cell.rootReading shared.rootReading target :=
    compareCell bounds value cell shared target positive
  exact ⟨comparison, cell_primitiveResidual_le bounds value cell pairs scale shared common comparison⟩

/-- The computed root-comparison allowance combines the actual scalar-cell sensitivity and two paid requests. -/
@[expose] def comparisonAllowance (_value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (_cell : Model cellData cellReading cellAccuracy) : Fraction.Rational :=
  _cell.comparisonAllowance

/-- Actual paid root refinement and the same scalar cell pay the retained root-comparison allowance. -/
theorem comparison_bound_le (value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (cell : Model cellData cellReading cellAccuracy)
    (sameModel : inverse = cached.patch.base.refine stage)
    (root : ContinuedNeighborhood.Point.PrimitiveRoot value.sample stage cellAccuracy.tolerance)
    (comparison : Equivalence.Observation.Comparison cell.rootReading
      (root.readModel inverse sameModel powers).rootReading cellAccuracy.tolerance) :
    comparison.bound ≤ comparisonAllowance bounds value cell :=
  cell.comparison_bound_le sameModel root comparison

/-- Retain the actual root request, shared primitive reading and paid comparison of this same scalar coefficient.

One original root request consumes the same retained interior Point. One
readModel consumes the supplied original inverse model and power cache.
The actual scalar observation and signed Point relation feed one original
comparison; its two actual radii and requested target pay the explicit
coefficient bound, without a supplied radius or coefficient payment.
-/
def coefficientRequest (value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (cell : Model cellData cellReading cellAccuracy)
    {numerator : InverseRootPolynomial.Polynomial} {pairCount : Nat}
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location)
    (sameModel : inverse = cached.patch.base.refine stage)
    (common : PrimitiveModel cached.patch stage numerator pairCount) :
    Model.CoefficientRequest (sample := value.sample) (powers := powers) cell sameModel common :=
  cell.coefficientRequest (powers := powers) (numerator := numerator)
      (pairCount := pairCount) value.readingEquivalent pairs scale sameModel common
    (curve_inside bounds cached span.lower ⟨cellInterior.1.le, cellInterior.2.le⟩)

open Purelib.Approximation.Rational.Geometric

/-- The complete retained interior comparison is the original observation procedure on the same actual inputs. -/
theorem compareCell_eq (value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (cell : Model cellData cellReading cellAccuracy)
    (shared : PrimitiveReading value.sample stage inverse powers)
    (target : Fraction.Rational) (positive : 0 < target) :
    compareCell bounds value cell shared target positive =
      Equivalence.Observation.Comparison.build cell.rootReading shared.rootReading
        value.readingEquivalent target positive := (rfl)

/-- The entire original interior request is the shared cell operation on its same retained signed Point and domain. -/
theorem coefficientRequest_cell (value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (cell : Model cellData cellReading cellAccuracy)
    {numerator : InverseRootPolynomial.Polynomial} {pairCount : Nat}
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location)
    (sameModel : inverse = cached.patch.base.refine stage)
    (common : PrimitiveModel cached.patch stage numerator pairCount) :
    coefficientRequest (powers := powers) bounds value cell pairs scale sameModel common =
      cell.coefficientRequest (powers := powers) (numerator := numerator)
      (pairCount := pairCount) value.readingEquivalent pairs scale sameModel common
        (curve_inside bounds cached span.lower ⟨cellInterior.1.le, cellInterior.2.le⟩) := (rfl)

/-- The original interior request retains its complete comparison on the same actual shared reading. -/
theorem coefficientRequest_comparison (value : CurvePoint bounds cached span.lower cellReading cellInterior)
    (cell : Model cellData cellReading cellAccuracy)
    {numerator : InverseRootPolynomial.Polynomial} {pairCount : Nat}
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location)
    (sameModel : inverse = cached.patch.base.refine stage)
    (common : PrimitiveModel cached.patch stage numerator pairCount) :
    (coefficientRequest (powers := powers) bounds value cell pairs scale sameModel common).2.2.val =
      compareCell bounds value cell
        (coefficientRequest (powers := powers) bounds value cell pairs scale sameModel common).2.1.val
        cellAccuracy.tolerance cellAccuracy.positive := (rfl)

end ScalarCell

end CurvePoint

/-- Construct an interior link using the actual supplied fixed source view of the same retained parent.

An entire interior bank can retain this source view outside its entry
producer. The genuine continuation, pair residuals, comparison and Point
are each computed once from this same source and original supplied Reading.
-/
@[expose] def curvePointFromSource (cached : PrimitiveTarget bounds original count)
    (prepared : CurveSource bounds cached)
    (time : Fraction.Rational) {timeInside : FixedRootBoxPath.Inside time}
    (pointReading : Reading leg.actual time timeInside) (interior : first < time ∧ time < last) :
    CurvePoint bounds cached time pointReading interior :=
  let target : CurveTarget bounds cached prepared time ⟨interior.1.le, interior.2.le⟩ :=
    curveTarget bounds cached prepared time ⟨interior.1.le, interior.2.le⟩
  let residuals : Residuals reading pointReading leg.regular (Reading.ownerDistance target.val) 0 0 :=
    ⟨Reading.PairResiduals.build reading pointReading leg.regular (Reading.ownerDistance target.val) 0 0, rfl⟩
  let compared : CurveCompared bounds cached prepared time pointReading ⟨interior.1.le, interior.2.le⟩
      target residuals.val :=
    curveCompared bounds cached prepared time pointReading ⟨interior.1.le, interior.2.le⟩ target residuals.val
  let sample : ContinuedNeighborhood.Point cached.patch
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base :=
    ContinuedNeighborhood.Point.acquire cached.patch _ (curve_inside bounds cached time ⟨interior.1.le, interior.2.le⟩)
  let equivalent := curveTargetEquivalent bounds cached prepared time ⟨interior.1.le, interior.2.le⟩ target sample
  CurvePoint.ofData bounds cached prepared time pointReading interior target residuals compared sample equivalent

/-- Construct the actual interior scalar-to-primitive link from the same original retained move and supplied Reading.

The time must be strictly inside the paid interval. The original source
view is read once and consumed by the cache-aware constructor. Existing
source and endpoint Points, targets and preparation caches remain unchanged.
-/
@[expose] def curvePoint (cached : PrimitiveTarget bounds original count) (time : Fraction.Rational)
    {timeInside : FixedRootBoxPath.Inside time} (pointReading : Reading leg.actual time timeInside)
    (interior : first < time ∧ time < last) : CurvePoint bounds cached time pointReading interior :=
  curvePointFromSource bounds cached (curveSource bounds cached) time pointReading interior

/-- The default interior producer is the complete cache-aware procedure on the same actual retained source view. -/
theorem curvePoint_default (cached : PrimitiveTarget bounds original count) (time : Fraction.Rational)
    {timeInside : FixedRootBoxPath.Inside time} (pointReading : Reading leg.actual time timeInside)
    (interior : first < time ∧ time < last) :
    curvePoint bounds cached time pointReading interior =
      curvePointFromSource bounds cached (curveSource bounds cached) time pointReading interior := rfl

section ScalarPoints

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)

/-- The computed source or strict-interior view of an actual scalar occurrence on its original primitive parent.

The existing sum and dependent pairs retain either the identical source
Point with its exact time transport, or the original whole CurvePoint with
its actual continuation and signed comparison. No root, request or nominal
Point family replaces either original branch.
-/
@[expose] def ScalarPoint (cached : PrimitiveTarget bounds original count)
    (sourcePoint : SourcePoint bounds cached) {span : Interval.Bounds}
    {scalarInside : FixedRootBoxPath.Inside span.lower} (scalarReading : Reading leg.actual span.lower scalarInside) :
    Type 1 :=
  (PSigma fun sameTime : span.lower = first => SourcePoint.At bounds cached sourcePoint span.lower sameTime) ⊕
    (PSigma fun interior : first < span.lower ∧ span.lower < last =>
      CurvePoint bounds cached span.lower scalarReading interior)

/-- Construct the actual source or interior scalar link from retained original caches and intrinsic interval bounds.

Exact time equality retains the same original source Point. Otherwise the
strict interior follows from the retained lower/upper bounds, and the
original interior factory consumes the supplied fixed source view. Neither
branch accepts a successful comparison, domain or replacement owner.
-/
def scalarPoint (cached : PrimitiveTarget bounds original count) (sourcePoint : SourcePoint bounds cached)
    (prepared : CurveSource bounds cached) {span : Interval.Bounds}
    {scalarInside : FixedRootBoxPath.Inside span.lower} (scalarReading : Reading leg.actual span.lower scalarInside)
    (within : first ≤ span.lower ∧ span.lower < last) : ScalarPoint bounds cached sourcePoint scalarReading :=
  if sameTime : span.lower = first then
    .inl ⟨sameTime, SourcePoint.atTime bounds cached sourcePoint span.lower sameTime⟩
  else
    have later : first < span.lower :=
      ⟨within.1, fun reverse => sameTime (Fraction.Order.Basic.le_antisymm _ _ reverse within.1)⟩
    .inr ⟨⟨later, within.2⟩,
      curvePointFromSource bounds cached prepared span.lower scalarReading ⟨later, within.2⟩⟩

namespace ScalarPoint

variable {cached : PrimitiveTarget bounds original count} {sourcePoint : SourcePoint bounds cached}
variable {span : Interval.Bounds} {scalarInside : FixedRootBoxPath.Inside span.lower}
variable {scalarReading : Reading leg.actual span.lower scalarInside}

/-- Read the same original source or interior Point without a query or acquisition. -/
@[expose] def sample (value : ScalarPoint bounds cached sourcePoint scalarReading) :
    ContinuedNeighborhood.Point cached.patch
      (coordinate site parameter 2 quarter (by decide +kernel) span.lower) :=
  match value with
  | .inl retained => retained.snd.val
  | .inr retained => retained.snd.sample

/-- Request the actual scalar coefficient through its retained original source or strict-interior producer.

Both branches return the EXISTING CoefficientRequest on their same stored
Point and original scalar observation. The original inverse/power/common
model caches feed one original root request, shared reading and numerical
comparison; no separate branch algorithm or successful payment is supplied.
-/
def coefficientRequest (value : ScalarPoint bounds cached sourcePoint scalarReading)
    {cellRadicand : Purelib.Algebra.Quadratic.Pair.Polynomial.Coefficients}
    {cellDifferential : OddPowerDifferential cellRadicand}
    {cellData : WaistBounds site parameter cellDifferential} {cellAccuracy : AccuracyRequest}
    (cell : Model cellData scalarReading cellAccuracy)
    {numerator : InverseRootPolynomial.Polynomial} {pairCount : Nat}
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location)
    {stage : Nat} {inverse : InverseRootPolynomial.Model (Paths.polynomial parameter) cached.patch.base.box}
    (powers : OddPowers inverse.value) (sameModel : inverse = cached.patch.base.refine stage)
    (common : PrimitiveModel cached.patch stage numerator pairCount) :
    Model.CoefficientRequest (sample := value.sample) (powers := powers) cell sameModel common :=
  match value with
  | .inl retained => sourceCoefficientRequest bounds cached sourcePoint retained.fst retained.snd cell
      pairs scale powers sameModel common
  | .inr retained => CurvePoint.coefficientRequest (powers := powers) bounds retained.snd cell
      pairs scale sameModel common

end ScalarPoint

/-- Retain the computed original scalar branch and its complete paid coefficient request on the same cached primitive.

The target, source Point and fixed source view are supplied completed work.
One source/interior construction and one original coefficient request retain
their actual factory result, Point, root, reading, comparison and payments.
Intrinsic dyadic containment supplies the interval bounds at production
clients; no requested residual estimate is an input.
-/
def scalarCoefficientRequest (retained : Anchored bounds original count)
    (prepared : CurveSource bounds retained.target) {span : Interval.Bounds}
    {scalarInside : FixedRootBoxPath.Inside span.lower} {scalarReading : Reading leg.actual span.lower scalarInside}
    {cellRadicand : Purelib.Algebra.Quadratic.Pair.Polynomial.Coefficients}
    {cellDifferential : OddPowerDifferential cellRadicand}
    {cellData : WaistBounds site parameter cellDifferential} {cellAccuracy : AccuracyRequest}
    (cell : Model cellData scalarReading cellAccuracy) (within : first ≤ span.lower ∧ span.lower < last)
    {numerator : InverseRootPolynomial.Polynomial} {pairCount : Nat}
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location)
    {stage : Nat}
    {inverse : InverseRootPolynomial.Model (Paths.polynomial parameter) retained.target.patch.base.box}
    (powers : OddPowers inverse.value) (sameModel : inverse = retained.target.patch.base.refine stage)
    (common : PrimitiveModel retained.target.patch stage numerator pairCount) :
    Σ point : {actual : ScalarPoint bounds retained.target retained.sourcePoint scalarReading //
        actual = scalarPoint bounds retained.target retained.sourcePoint prepared scalarReading within},
      Model.CoefficientRequest (sample := point.val.sample) (powers := powers) cell sameModel common :=
  let point := scalarPoint bounds retained.target retained.sourcePoint prepared scalarReading within
  let request := ScalarPoint.coefficientRequest bounds point cell pairs scale powers sameModel common
  ⟨⟨point, rfl⟩, request⟩

end ScalarPoints

section ScalarModels

open Purelib.Riemann.Normalization
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Polynomial.Dense.Power (OddPowers)
open Purelib.Polynomial.Bounds (Horner)
open Purelib.Algebra.Quadratic (Pair)
open Radial.Differential.Refinement (Piece Layer)

/-- The once-retained original inverse model, its complete odd powers and common primitive on one actual patch.

The exact dependent pairs retain all three original factory results. Their
same patch, refinement index and displayed numerator remain indices; no
root, primitive record or polynomial presentation is reconstructed.
-/
@[expose] def ScalarModels (cached : PrimitiveTarget bounds original count) (index : Nat)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : optParam Nat 0)
    (supplied : Option (PrimitiveModel cached.patch index numerator pairCount) := none) : Type :=
  Σ inverse : {actual : InverseRootPolynomial.Model (Paths.polynomial parameter) cached.patch.base.box //
      actual = cached.patch.base.refine index},
  Σ powers : {actual : OddPowers inverse.val.value // actual = OddPowers.build inverse.val.value},
    {actual : PrimitiveModel cached.patch index numerator pairCount //
      actual = match supplied with
        | none => PrimitiveModel.ofPowers cached.patch index numerator inverse.val
            (congrArg (fun model => model.value) inverse.property) powers.val pairCount
        | some retained => retained}

namespace ScalarModels

variable {cached : PrimitiveTarget bounds original count} {index : Nat}
variable {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
variable {supplied : Option (PrimitiveModel cached.patch index numerator pairCount)}

/-- The exact retained inverse and complete original odd powers at one indexed primitive parent.

Both whole factory equations retain the original cached objects. This
existing dependent pair is supplied work; reading it computes no model or
power polynomial.
-/
@[expose] def Factors (cached : PrimitiveTarget bounds original count) (index : Nat) : Type :=
  Σ inverse : {actual : InverseRootPolynomial.Model (Paths.polynomial parameter) cached.patch.base.box //
      actual = cached.patch.base.refine index},
    {actual : OddPowers inverse.val.value // actual = OddPowers.build inverse.val.value}

/-- Assemble the original three-cache model view from its actual factors and certified common primitive.

The complete input objects are forwarded literally. The supplied common
certificate carries the same existing default-or-retained factory equation;
this constructor performs no numerical operation or polynomial scaling.
-/
@[expose] def ofCached (cached : PrimitiveTarget bounds original count) (index : Nat)
    (numerator : Pair.Polynomial.Coefficients) (factors : Factors bounds cached index) (pairCount : Nat)
    (supplied : Option (PrimitiveModel cached.patch index numerator pairCount))
    (common : {actual : PrimitiveModel cached.patch index numerator pairCount //
      actual = match supplied with
        | none => PrimitiveModel.ofPowers cached.patch index numerator factors.1.val
            (congrArg (fun model => model.value) factors.1.property) factors.2.val pairCount
        | some retained => retained}) : ScalarModels bounds cached index numerator pairCount supplied :=
  ⟨factors.1, factors.2, common⟩

/-- Attach the actual retained factors and common primitive to the original three-cache model view.

An actual supplied primitive is forwarded literally. Without one, the
original power-aware constructor consumes the same retained factors; its
zero-pair branch is the complete former derivative-bound construction.
-/
@[expose] def ofFactors (cached : PrimitiveTarget bounds original count) (index : Nat)
    (numerator : Pair.Polynomial.Coefficients) (factors : Factors bounds cached index)
    (pairCount : optParam Nat 0)
    (supplied : Option (PrimitiveModel cached.patch index numerator pairCount) := none) :
    ScalarModels bounds cached index numerator pairCount supplied :=
  let common := match supplied with
    | none => PrimitiveModel.ofPowers cached.patch index numerator factors.1.val
        (congrArg (fun model => model.value) factors.1.property) factors.2.val pairCount
    | some retained => retained
  ofCached bounds cached index numerator factors pairCount supplied ⟨common, rfl⟩

end ScalarModels

/-- Compute or consume the same original inverse, powers and common primitive once outside scalar cell entries.

The omitted inputs retain the complete old inverse/powers/ofModel factory.
Supplied actual factors and primitive remain whole original cached objects;
no model, power, coefficient or primitive is recomputed for that branch.
-/
def scalarModels (cached : PrimitiveTarget bounds original count) (index : Nat)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : optParam Nat 0)
    (supplied : Option (PrimitiveModel cached.patch index numerator pairCount) := none)
    (factors : Option (ScalarModels.Factors bounds cached index) := none) :
    ScalarModels bounds cached index numerator pairCount supplied :=
  let actual := match factors with
    | some retained => retained
    | none =>
        let inverse := cached.patch.base.refine index
        let powers := OddPowers.build inverse.value
        ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩⟩
  ScalarModels.ofFactors bounds cached index numerator actual pairCount supplied

/-- Omitting the odd-power and supplied-cache inputs retains the entire original three-cache factory result. -/
theorem scalarModels_default (cached : PrimitiveTarget bounds original count) (index : Nat)
    (numerator : Pair.Polynomial.Coefficients) :
    scalarModels bounds cached index numerator =
      (let inverse := cached.patch.base.refine index
       let powers := OddPowers.build inverse.value
       let common := PrimitiveModel.ofModel cached.patch index numerator inverse rfl
       ⟨⟨inverse, rfl⟩, ⟨powers, rfl⟩, ⟨common, rfl⟩⟩) := (rfl)

/-- Supplying retained original factors forwards the complete factor/common construction without a second factory. -/
theorem scalarModels_ofFactors (cached : PrimitiveTarget bounds original count) (index : Nat)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : Nat)
    (supplied : Option (PrimitiveModel cached.patch index numerator pairCount))
    (factors : ScalarModels.Factors bounds cached index) :
    scalarModels bounds cached index numerator pairCount supplied (some factors) =
      ScalarModels.ofFactors bounds cached index numerator factors pairCount supplied := (rfl)

namespace ScalarModels

variable {cached : PrimitiveTarget bounds original count} {index : Nat}
variable {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
variable {supplied : Option (PrimitiveModel cached.patch index numerator pairCount)}

/-- Read the complete original inverse model retained at this same actual refinement index. -/
@[expose] def inverse (models : ScalarModels bounds cached index numerator pairCount supplied) :
    InverseRootPolynomial.Model (Paths.polynomial parameter) cached.patch.base.box := models.1.val

/-- The retained whole inverse model is exactly the original refinement result. -/
theorem inverse_eq (models : ScalarModels bounds cached index numerator pairCount supplied) :
    models.inverse = cached.patch.base.refine index := models.1.property

/-- Read the same complete odd-power cache computed on this actual retained inverse polynomial. -/
@[expose] def powers (models : ScalarModels bounds cached index numerator pairCount supplied) :
    OddPowers models.inverse.value :=
  models.2.1.val

/-- The retained odd powers are the entire original factory result on this same inverse polynomial. -/
theorem powers_eq (models : ScalarModels bounds cached index numerator pairCount supplied) :
    models.powers = OddPowers.build models.inverse.value := models.2.1.property

/-- Read the original common primitive retained on this same patch, numerator and model stage. -/
@[expose] def common (models : ScalarModels bounds cached index numerator pairCount supplied) :
    PrimitiveModel cached.patch index numerator pairCount := models.2.2.val

/-- The common primitive is the whole original factory result consuming the actual retained inverse model. -/
theorem common_eq (models : ScalarModels bounds cached index numerator pairCount supplied) :
    models.common = match supplied with
      | none => PrimitiveModel.ofPowers cached.patch index numerator models.inverse
          (congrArg (fun model => model.value) models.inverse_eq) models.powers pairCount
      | some retained => retained := by
  cases supplied with
  | none => exact models.2.2.property
  | some retained => exact models.2.2.property

section Requests

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation.Rational.Geometric

variable {cellRadicand : Pair.Polynomial.Coefficients}
variable {cellDifferential : OddPowerDifferential cellRadicand}
variable {cellData : WaistBounds site parameter cellDifferential}
variable {span : Interval.Bounds} {cellInside : FixedRootBoxPath.Inside span.lower}
variable {cellReading : Reading leg.actual span.lower cellInside} {cellAccuracy : AccuracyRequest}

/-- One actual original scalar Point and whole coefficient request consuming the same retained model cache.

The Point keeps its entire original factory equality for every proof of the
same time interval. The original request retains its selected root, shared
reading, comparison and payments. The final scalar bound concerns those
actual retained observations rather than a newly sampled coefficient.
-/
@[expose] def CellRequest (retained : Anchored bounds original count)
    (prepared : CurveSource bounds retained.target)
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel retained.target.patch index numerator pairCount)}
    (models : ScalarModels bounds retained.target index numerator pairCount retainedCommon)
    (cell : Model cellData cellReading cellAccuracy) (target : Fraction.Rational) : Type 1 :=
  Σ linked : {actual : ScalarPoint bounds retained.target retained.sourcePoint cellReading //
      ∀ within : first ≤ span.lower ∧ span.lower < last,
        actual = scalarPoint bounds retained.target retained.sourcePoint prepared cellReading within},
    {_actual : Model.CoefficientRequest (sample := linked.val.sample) (powers := models.powers)
        cell models.inverse_eq models.common // cell.primitiveResidual models.common.coefficient < target}

/-- Consume one actual supplied scalar cell with the retained inverse, powers and common primitive.

Original finite selections and the exact scalar accuracy equation pay the
computed residual bound. The Point and complete original request are built
once by the original combined producer; proof transport changes no cache,
source, signed owner or numerical channel.
-/
def request (retained : Anchored bounds original count) (prepared : CurveSource bounds retained.target)
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel retained.target.patch index numerator pairCount)}
    (models : ScalarModels bounds retained.target index numerator pairCount retainedCommon)
    (cell : Model cellData cellReading cellAccuracy) (within : first ≤ span.lower ∧ span.lower < last)
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location)
    (initialAccuracy : AccuracyRequest) (depth modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (accuracy_eq : cellAccuracy.tolerance = Geometric.Basic.quarterRadius initialAccuracy.tolerance depth)
    (modelAfter : (coefficientSelections bounds retained.target cellData initialAccuracy
      modelFloor scalarFloor target positive pairCount).1.stage ≤ index)
    (scalarAfter : (coefficientSelections bounds retained.target cellData initialAccuracy
      modelFloor scalarFloor target positive pairCount).2.stage ≤ depth) :
    CellRequest bounds retained prepared models cell target := by
  let original := scalarCoefficientRequest bounds retained prepared cell within pairs scale
    models.powers models.inverse_eq models.common
  have attained := coefficient_error_lt bounds retained.target cell models.inverse_eq models.common original.2
    initialAccuracy depth modelFloor scalarFloor target positive accuracy_eq modelAfter scalarAfter
  exact ⟨⟨original.1.val, fun _ => original.1.property⟩, ⟨original.2, attained⟩⟩

/-- The original ordered dependent bank of actual scalar Points and coefficient requests on one retained parent.

The supplied scalar layer and its exact bounded occurrences remain the
indices. Every request consumes the same stored inverse, powers, common
primitive and fixed prepared source; the bank adds no nominal owner family.
-/
@[expose] def LayerRequests (retained : Anchored bounds original count)
    (prepared : CurveSource bounds retained.target)
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel retained.target.patch index numerator pairCount)}
    (models : ScalarModels bounds retained.target index numerator pairCount retainedCommon)
    {initialAccuracy : AccuracyRequest} {initial : Piece cellData leg.actual initialAccuracy} {depth : Nat}
    (layer : Layer initial depth) (target : Fraction.Rational) : Type 1 :=
  DependentProduct layer.pieces (fun ordinal =>
    CellRequest bounds retained prepared models (layer.pieces[ordinal.val]'ordinal.isLt).cell target)

/-- Construct the actual ordered source/interior requests from the same supplied scalar factory layer.

Exact original spans derive every interval bound and positive child width.
The producer consumes the original paid cells; it does not rebuild the layer,
repeat its readings, prepare a source or compute models inside the entries.
The actual upper endpoint remains excluded from source/interior selection.
-/
def layerRequests (retained : Anchored bounds original count) (prepared : CurveSource bounds retained.target)
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel retained.target.patch index numerator pairCount)}
    (models : ScalarModels bounds retained.target index numerator pairCount retainedCommon)
    {initialAccuracy : AccuracyRequest} (initial : Piece cellData leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    {depth : Nat} (layer : Layer initial depth)
    (spans : layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts depth initial.span)
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location)
    (modelFloor scalarFloor : Nat) (target : Fraction.Rational) (positive : 0 < target)
    (modelAfter : (coefficientSelections bounds retained.target cellData initialAccuracy
      modelFloor scalarFloor target positive pairCount).1.stage ≤ index)
    (scalarAfter : (coefficientSelections bounds retained.target cellData initialAccuracy
      modelFloor scalarFloor target positive pairCount).2.stage ≤ depth) :
    LayerRequests bounds retained prepared models layer target := by
  refine DependentProduct.ofFn layer.pieces (fun ordinal => ?_)
  let piece := layer.pieces[ordinal.val]'ordinal.isLt
  have member : piece ∈ layer.pieces := List.getElem_mem ordinal.isLt
  have initialProper : initial.span.lower < initial.span.upper := by
    rewrite [span_eq.1, span_eq.2]
    exact proper
  have within : first ≤ piece.span.lower ∧ piece.span.lower < last := by
    have original := layer.lower_within spans initialProper piece member
    rewrite [span_eq.1, span_eq.2] at original
    exact original
  exact request bounds retained prepared models piece.cell within pairs scale initialAccuracy depth
    modelFloor scalarFloor target positive layer.accuracy_eq modelAfter scalarAfter

namespace LayerRequests

/-- Read the actual retained Point, whole coefficient request and payment at the original scalar occurrence. -/
@[expose] def get {retained : Anchored bounds original count} {prepared : CurveSource bounds retained.target}
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel retained.target.patch index numerator pairCount)}
    {models : ScalarModels bounds retained.target index numerator pairCount retainedCommon}
    {initialAccuracy : AccuracyRequest} {initial : Piece cellData leg.actual initialAccuracy} {depth : Nat}
    {layer : Layer initial depth} {target : Fraction.Rational}
    (requests : LayerRequests bounds retained prepared models layer target) (ordinal : Fin layer.pieces.length) :
    CellRequest bounds retained prepared models (layer.pieces[ordinal.val]'ordinal.isLt).cell target :=
  DependentProduct.get layer.pieces requests ordinal

/-- The finite maximum of actual same-layer coefficient residuals is bounded by the computed request target.

The proof consumes the actual stored request at each original bounded
occurrence. The existing nonnegative finite maximum supplies the zero and
list cases; neither residual decay nor a desired sample inequality is a
caller premise of the request producer.
-/
theorem residual_le {retained : Anchored bounds original count} {prepared : CurveSource bounds retained.target}
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel retained.target.patch index numerator pairCount)}
    {models : ScalarModels bounds retained.target index numerator pairCount retainedCommon}
    {initialAccuracy : AccuracyRequest} {initial : Piece cellData leg.actual initialAccuracy} {depth : Nat}
    {layer : Layer initial depth} {target : Fraction.Rational}
    (requests : LayerRequests bounds retained prepared models layer target) (positive : 0 < target) :
    layer.primitiveResidual models.common.coefficient ≤ target := by
  apply Data.Rat.List.Maximum.nonnegativeMaximum_le _ positive.le
  intro residual member
  rcases Data.List.Map.mem_map.mp member with ⟨piece, pieceMember, equal⟩
  rcases List.getElem_of_mem pieceMember with ⟨ordinal, bound, samePiece⟩
  have attained := (requests.get bounds ⟨ordinal, bound⟩).2.property.le
  rewrite [samePiece] at attained
  exact equal ▸ attained

end LayerRequests

end Requests

end ScalarModels

/-- An actual scalar factory layer on this original move has its finite primitive bound on the same retained patch.

The interval endpoint equations express the same original chart occurrence.
The actual paid move derives all curved-domain containment internally. The
original finite telescope consumes the supplied model, Horner cache and
actual cell residuals. An optional upper ceiling consumes a proved request
bank bound; the literal default remains its actual original residual
maximum. No inverse-root domain extension is performed.
-/
theorem scalarLayer_error_le (cached : PrimitiveTarget bounds original count)
    {cellRadicand : Pair.Polynomial.Coefficients}
    {cellDifferential : Hyperelliptic.Differentials.OddPower.Basic.OddPowerDifferential cellRadicand}
    {cellData : WaistBounds site parameter cellDifferential}
    {initialAccuracy : AccuracyRequest} (initial : Piece cellData leg.actual initialAccuracy)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last)
    {depth index : Nat} (layer : Layer initial depth)
    (spans : layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts depth initial.span)
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel cached.patch index numerator pairCount)}
    (models : ScalarModels bounds cached index numerator pairCount retainedCommon) (horner : Horner)
    (horner_eq : horner = Purelib.Polynomial.Dense.Gaussian.Bounds.Box.denseHornerNormBounds
      models.common.coefficient cached.patch.box)
    (ceiling : {upper : Fraction.Rational // layer.primitiveResidual models.common.coefficient ≤ upper} :=
      ⟨layer.primitiveResidual models.common.coefficient, Fraction.Order.Basic.le_refl _⟩) :
    Norm.Basic.normSq (models.common.primitive.value.eval
        (coordinate site parameter 2 quarter (by decide +kernel) last) -
      models.common.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) first) -
      layer.model.integralSample) ≤
        4 * (models.common.primitive.remainderBound * ((25 / 4) * normSq (halfGap site parameter)) ^ 2 +
          horner.value * ((25 / 4) * normSq (halfGap site parameter))) * initial.span.width ^ 2 *
            Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth +
              2 * ceiling.val * initial.span.width ^ 2 := by
  have domain : ∀ time, initial.span.Contains time → cached.patch.box.Contains
      (point site parameter 2 (Waist.direction quarter time) (by decide +kernel)).base := by
    intro time contained
    apply curve_inside bounds cached time
    exact ⟨span_eq.1 ▸ contained.1, span_eq.2 ▸ contained.2⟩
  have estimated := layer.spatialPrimitive_error_le spans models.common.primitive horner horner_eq domain
  rewrite [span_eq.1, span_eq.2] at estimated
  simp only [Norm.Basic.normSq_eq_canonical] at estimated ⊢
  have residual := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct ceiling.property
      (by decide +kernel : (0 : Fraction.Rational) ≤ 2))
    (Arithmetic.sq_nonneg_direct initial.span.width)
  exact estimated.trans
    (Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) residual)

namespace ScalarModels

open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Approximation.Rational.Geometric
open Purelib.Polynomial.Dense.Gaussian.Bounds

variable {cellRadicand : Pair.Polynomial.Coefficients}
variable {cellDifferential : OddPowerDifferential cellRadicand}
variable {cellData : WaistBounds site parameter cellDifferential}
variable {initialAccuracy : AccuracyRequest}

/-- The coefficient target whose actual squared-width weighted contribution pays half the final integral request. -/
@[expose] def coefficientTarget (initial : Piece cellData leg.actual initialAccuracy)
    (target : Fraction.Rational) : Fraction.Rational :=
  Budget.Weighted.allowance (target / 2) (2 * initial.span.width ^ 2)

/-- The original weighted coefficient allowance is positive at every positive integral target. -/
theorem coefficientTarget_positive (initial : Piece cellData leg.actual initialAccuracy)
    {target : Fraction.Rational} (positive : 0 < target) : 0 < coefficientTarget initial target :=
  Budget.Weighted.allowance_positive
    (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
    (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.sq_nonneg_direct _))

/-- The original finite Taylor scale of this actual common primitive on the supplied original scalar interval.

The retained gap quadrance and actual Horner cache are used once. This scale
is chosen after the inverse polynomial, so no uniform Taylor bound over
changing inverse-model degrees or coefficients is presumed.
-/
@[expose] def taylorScale {cached : PrimitiveTarget bounds original count} {index : Nat}
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel cached.patch index numerator pairCount)}
    (models : ScalarModels bounds cached index numerator pairCount retainedCommon)
    (initial : Piece cellData leg.actual initialAccuracy) (horner : Horner) : Fraction.Rational :=
  4 * (models.common.primitive.remainderBound * ((25 / 4) * cellData.gapNorm) ^ 2 +
    horner.value * ((25 / 4) * cellData.gapNorm)) * initial.span.width ^ 2 * initial.span.width ^ 2

/-- The actual retained primitive and original box Horner cache have a nonnegative finite Taylor scale. -/
theorem taylorScale_nonnegative {cached : PrimitiveTarget bounds original count} {index : Nat}
    {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
    {retainedCommon : Option (PrimitiveModel cached.patch index numerator pairCount)}
    (models : ScalarModels bounds cached index numerator pairCount retainedCommon)
    (initial : Piece cellData leg.actual initialAccuracy) (horner : Horner)
    (horner_eq : horner = Box.denseHornerNormBounds models.common.coefficient cached.patch.box) :
    0 ≤ taylorScale bounds models initial horner := by
  have hornerNonnegative : 0 ≤ horner.value := by
    rewrite [horner_eq]
    exact (Box.denseHornerNormBounds_nonneg models.common.coefficient cached.patch.box).1
  exact Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct (by decide +kernel)
        (Fraction.Order.add_nonnegative
          (Arithmetic.mul_nonneg_direct models.common.primitive.remainderBound_nonnegative
            (Arithmetic.sq_nonneg_direct _))
          (Arithmetic.mul_nonneg_direct hornerNonnegative
            (Arithmetic.mul_nonneg_direct (by decide +kernel) cellData.gapNorm_nonnegative))))
      (Arithmetic.sq_nonneg_direct _))
    (Arithmetic.sq_nonneg_direct _)

namespace Precision

/-- The exact whole original coefficient-selection pair and its complete factory equation at the integral allowance. -/
@[expose] def Selections (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) (pairCount : Nat) : Type :=
  let error := coefficientTarget initial target
  {actual : Search.Selection (modelErrorScale bounds cached cellData pairCount) modelFloor (error / 2) ×
      Search.Selection (samplingErrorScale bounds cached cellData initialAccuracy pairCount)
          scalarFloor (error / 2) //
    actual = coefficientSelections bounds cached cellData initialAccuracy modelFloor scalarFloor error
      (coefficientTarget_positive initial positive) pairCount}

/-- An actual original three-cache model view at a retained sufficient model stage.

The optional common primitive remains its whole original input. The proof
compares only the original finite model Selection stage to this actual
retained index; it is not a residual bound or successful comparison premise.
-/
@[expose] def Retained (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : Nat) : Type :=
  {actual : Σ index : Nat,
    Σ common : Option (PrimitiveModel cached.patch index numerator pairCount),
      ScalarModels bounds cached index numerator pairCount common //
    (coefficientSelections bounds cached cellData initialAccuracy modelFloor scalarFloor
      (coefficientTarget initial target) (coefficientTarget_positive initial positive) pairCount).1.stage ≤
        actual.1}

variable {cached : PrimitiveTarget bounds original count}
variable {initial : Piece cellData leg.actual initialAccuracy} {modelFloor scalarFloor : Nat}
variable {target : Fraction.Rational} {positive : 0 < target}

/-- Read the actual retained model index and common-primitive input, or the literal computed default stage. -/
@[expose] def parameters (cached : PrimitiveTarget bounds original count)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : Nat) (selected : Nat)
    (suppliedModels : Option
      (Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount)) :
    Σ index : Nat, Option (PrimitiveModel cached.patch index numerator pairCount) :=
  match suppliedModels with
  | none => ⟨selected, none⟩
  | some retained => ⟨retained.val.1, retained.val.2.1⟩

/-- Consume the same supplied whole model view, or compute its original default once outside cell entries. -/
private def modelsAt (cached : PrimitiveTarget bounds original count)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : Nat) (selected : Nat)
    (suppliedModels : Option
      (Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount)) :
    let actual := parameters bounds cached numerator pairCount selected suppliedModels
    ScalarModels bounds cached actual.1 numerator pairCount actual.2 := by
  cases suppliedModels with
  | none => exact scalarModels bounds cached selected numerator pairCount
  | some retained => exact retained.val.2.2

end Precision

/-- The original finite coefficient choices, actual model/Horner caches and subsequent Taylor selection.

The omitted numerator, pair and retained-model inputs are the complete old
zero-pair constructor. A supplied original view retains its actual later
model index and selected-floor proof; both the Taylor scale and subsequent
requests consume that same stored polynomial and common primitive.
-/
@[expose] def Precision (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (numerator : Pair.Polynomial.Coefficients := cellDifferential.numerator) (pairCount : optParam Nat 0)
    (suppliedModels : Option
      (Precision.Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount) := none) :
    Type :=
  let error := coefficientTarget initial target
  Σ selected : {actual :
      Search.Selection (modelErrorScale bounds cached cellData pairCount) modelFloor (error / 2) ×
        Search.Selection (samplingErrorScale bounds cached cellData initialAccuracy pairCount)
          scalarFloor (error / 2) //
    actual = coefficientSelections bounds cached cellData initialAccuracy modelFloor scalarFloor error
      (coefficientTarget_positive initial positive) pairCount},
  let actual := Precision.parameters bounds cached numerator pairCount selected.val.1.stage suppliedModels
  Σ models : ScalarModels bounds cached actual.1 numerator pairCount actual.2,
  Σ horner : {actual : Horner // actual = Box.denseHornerNormBounds models.common.coefficient cached.patch.box},
  Σ scale : {actual : Fraction.Rational // actual = taylorScale bounds models initial horner.val},
    Search.Selection scale.val selected.val.2.stage (target / 2)

namespace Precision

/-- Compute the original Horner and Taylor caches on supplied whole coefficient Selections and scalar models.

The original finite precision result retains both supplied inputs. Its
model stage and common primitive remain indexed by the same parameters;
no model, power, primitive or coefficient-stage factory is evaluated.
-/
def ofModels (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : Nat)
    (suppliedModels : Option
      (Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount))
    (selections : Selections bounds cached initial modelFloor scalarFloor target positive pairCount)
    (models : let actual := parameters bounds cached numerator pairCount selections.val.1.stage suppliedModels
      ScalarModels bounds cached actual.1 numerator pairCount actual.2) :
    ScalarModels.Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels := by
  let selected := selections.val
  let horner := Box.denseHornerNormBounds models.common.coefficient cached.patch.box
  let scale := taylorScale bounds models initial horner
  let taylor := Search.Selection.build scale (taylorScale_nonnegative bounds models initial horner rfl)
    selected.2.stage (target / 2) (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
  exact ⟨selections, models, ⟨horner, rfl⟩, ⟨scale, rfl⟩, taylor⟩

/-- The finite assembly retains both complete original input caches with their exact dependent indices. -/
theorem ofModels_caches (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : Nat)
    (suppliedModels : Option
      (Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount))
    (selections : Selections bounds cached initial modelFloor scalarFloor target positive pairCount)
    (models : let actual := parameters bounds cached numerator pairCount selections.val.1.stage suppliedModels
      ScalarModels bounds cached actual.1 numerator pairCount actual.2) :
    let actual := ofModels bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels selections models
    actual.1 = selections ∧ HEq actual.2.1 models := by
  exact ⟨rfl, HEq.rfl⟩

end Precision

/-- Choose coefficient stages before one actual model cache, then pay its finite Taylor scale at a later scalar stage.

A supplied original model view is forwarded literally with its actual
index, inverse, powers and primitive. The default retains the complete old
factory sequence. No Point, source, scalar layer or numerical observation
is acquired by this finite selection procedure.
-/
def precision (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (numerator : Pair.Polynomial.Coefficients := cellDifferential.numerator) (pairCount : optParam Nat 0)
    (suppliedModels : Option
      (Precision.Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount) := none)
    (retainedSelections : Option
      (Precision.Selections bounds cached initial modelFloor scalarFloor target positive pairCount) := none) :
    Precision bounds cached initial modelFloor scalarFloor target positive numerator pairCount suppliedModels := by
  let error := coefficientTarget initial target
  have errorPositive : 0 < error := coefficientTarget_positive initial positive
  let selections : Precision.Selections bounds cached initial modelFloor scalarFloor target positive pairCount :=
    match retainedSelections with
    | some retained => retained
    | none => ⟨coefficientSelections bounds cached cellData initialAccuracy
        modelFloor scalarFloor error errorPositive pairCount, rfl⟩
  let selected := selections.val
  let models := Precision.modelsAt bounds cached numerator pairCount selected.1.stage suppliedModels
  exact Precision.ofModels bounds cached initial modelFloor scalarFloor target positive
    numerator pairCount suppliedModels selections models

/-- Omitting the retained-model and odd-power inputs preserves the whole original finite precision construction. -/
theorem precision_default (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    precision bounds cached initial modelFloor scalarFloor target positive =
      (let error := coefficientTarget initial target
       let errorPositive := coefficientTarget_positive initial positive
       let selected := coefficientSelections bounds cached cellData initialAccuracy
         modelFloor scalarFloor error errorPositive
       let models := scalarModels bounds cached selected.1.stage cellDifferential.numerator
       let horner := Box.denseHornerNormBounds models.common.coefficient cached.patch.box
       let scale := taylorScale bounds models initial horner
       let taylor := Search.Selection.build scale (taylorScale_nonnegative bounds models initial horner rfl)
         selected.2.stage (target / 2) (Fraction.Order.Field.div_pos_direct positive (by decide +kernel))
       ⟨⟨selected, rfl⟩, models, ⟨horner, rfl⟩, ⟨scale, rfl⟩, taylor⟩) := (rfl)

namespace Precision

variable {cached : PrimitiveTarget bounds original count}
variable {initial : Piece cellData leg.actual initialAccuracy} {modelFloor scalarFloor : Nat}
variable {target : Fraction.Rational} {positive : 0 < target}
variable {numerator : Pair.Polynomial.Coefficients} {pairCount : Nat}
variable {suppliedModels : Option
  (Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount)}

/-- Read both whole original coefficient Selections retained before the actual model view was consumed. -/
@[expose] def coefficients
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :=
  value.1.val

/-- The actual retained coefficient pair is the original finite search on the same numerator and odd index. -/
theorem coefficients_eq
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    value.coefficients = coefficientSelections bounds cached cellData initialAccuracy modelFloor scalarFloor
      (coefficientTarget initial target) (coefficientTarget_positive initial positive) pairCount := value.1.property

/-- Read the original model's actual retained stage or the exact default coefficient stage. -/
@[expose] def modelStage
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    Nat := (parameters bounds cached numerator pairCount value.coefficients.1.stage suppliedModels).1

/-- The actual original model stage pays the same retained coefficient Selection floor. -/
theorem modelStage_ge
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    value.coefficients.1.stage ≤ value.modelStage := by
  cases suppliedModels with
  | none => exact Nat.le_refl _
  | some retained =>
      exact (congrArg (fun pair => pair.1.stage) value.coefficients_eq).le.trans retained.property

/-- Read the same original inverse, complete powers and common primitive at their actual retained stage. -/
@[expose] def models
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    ScalarModels bounds cached value.modelStage numerator pairCount
      (parameters bounds cached numerator pairCount value.coefficients.1.stage suppliedModels).2 := value.2.1

/-- Read the whole original coefficient/box Horner fold retained once after the common primitive. -/
@[expose] def horner
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    Horner := value.2.2.1.val

/-- The original stored Horner fold belongs to the same actual common coefficient and primitive box. -/
theorem horner_eq
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    value.horner = Box.denseHornerNormBounds value.models.common.coefficient cached.patch.box := value.2.2.1.property

/-- Read the actual finite Taylor scale computed on this same primitive and retained Horner fold. -/
@[expose] def scale
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    Fraction.Rational := value.2.2.2.1.val

/-- The retained Taylor scale uses this original span, actual common model and retained Horner value. -/
theorem scale_eq
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    value.scale = taylorScale bounds value.models initial value.horner := value.2.2.2.1.property

/-- Read the complete scalar-stage selection, retaining its original floor, finite fuel and actual allowance. -/
@[expose] def taylor
    (value : Precision bounds cached initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels) :
    Search.Selection value.scale value.coefficients.2.stage (target / 2) := value.2.2.2.2

/-- The original finite precision producer forwards the complete supplied inverse, powers and primitive view. -/
theorem precision_models (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : Nat)
    (retained : Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount)
    (selections : Option (Selections bounds cached initial modelFloor scalarFloor target positive pairCount)) :
    (precision bounds cached initial modelFloor scalarFloor target positive numerator pairCount
      (some retained) selections).models = retained.val.2.2 := (rfl)

/-- The original finite precision producer retains the complete supplied pair of coefficient Selections. -/
theorem precision_coefficients (cached : PrimitiveTarget bounds original count)
    (initial : Piece cellData leg.actual initialAccuracy) (modelFloor scalarFloor : Nat)
    (target : Fraction.Rational) (positive : 0 < target)
    (numerator : Pair.Polynomial.Coefficients) (pairCount : Nat)
    (supplied : Option (Retained bounds cached initial modelFloor scalarFloor target positive numerator pairCount))
    (selections : Selections bounds cached initial modelFloor scalarFloor target positive pairCount) :
    (precision bounds cached initial modelFloor scalarFloor target positive numerator pairCount
      supplied (some selections)).coefficients = selections.val := (rfl)

/-- Construct the ordered actual requests at the computed or a later scalar stage on this same original model.

Both model and scalar floors follow from the retained Selections and actual
supplied stage proof. The scaled numerator equation and pair identity
refer to this same original common primitive; no coefficient bound is a
caller premise.
-/
def requests (retained : Anchored bounds original count)
    {suppliedModels : Option
      (Retained bounds retained.target initial modelFloor scalarFloor target positive numerator pairCount)}
    (value : Precision bounds retained.target initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels)
    (prepared : CurveSource bounds retained.target)
    (stage : {later : Nat // value.taylor.stage ≤ later} := ⟨value.taylor.stage, Nat.le_refl _⟩)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last) (proper : first < last)
    (layer : Layer initial stage.val)
    (spans : layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts stage.val initial.span)
    (pairs : cellDifferential.denominatorPairs = pairCount)
    (scale : ∀ location, numerator.eval location = cellDifferential.scale * cellDifferential.numerator.eval location) :
    LayerRequests bounds retained prepared value.models layer (coefficientTarget initial target) := by
  have errorPositive : 0 < coefficientTarget initial target := coefficientTarget_positive initial positive
  have modelStage := congrArg (fun pair => pair.1.stage) value.coefficients_eq
  have scalarStage := congrArg (fun pair => pair.2.stage) value.coefficients_eq
  exact layerRequests bounds retained prepared value.models initial span_eq proper layer spans pairs scale
    modelFloor scalarFloor (coefficientTarget initial target) errorPositive
    (modelStage.symm.le.trans value.modelStage_ge)
    (scalarStage.symm.le.trans (value.taylor.lower.trans stage.property))

/-- The actual paid scalar layer approximates its same primitive boundary at every requested target.

The original finite telescope consumes the stored request bank. The same
weighted coefficient allowance and later Taylor Selection pay the bound;
no final sample inequality or successful sheet comparison is assumed.
-/
theorem accurate (retained : Anchored bounds original count)
    {suppliedModels : Option
      (Retained bounds retained.target initial modelFloor scalarFloor target positive numerator pairCount)}
    (value : Precision bounds retained.target initial modelFloor scalarFloor target positive
      numerator pairCount suppliedModels)
    {prepared : CurveSource bounds retained.target}
    (stage : {later : Nat // value.taylor.stage ≤ later} := ⟨value.taylor.stage, Nat.le_refl _⟩)
    (span_eq : initial.span.lower = first ∧ initial.span.upper = last)
    (layer : Layer initial stage.val)
    (spans : layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts stage.val initial.span)
    (requests : LayerRequests bounds retained prepared value.models layer (coefficientTarget initial target)) :
    Norm.Basic.normSq (value.models.common.primitive.value.eval
        (coordinate site parameter 2 quarter (by decide +kernel) last) -
      value.models.common.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) first) -
      layer.model.integralSample) < target := by
  have halfPositive : 0 < target / 2 := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  have weightNonnegative : 0 ≤ 2 * initial.span.width ^ 2 :=
    Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.sq_nonneg_direct _)
  have errorPositive : 0 < coefficientTarget initial target := coefficientTarget_positive initial positive
  have bound := scalarLayer_error_le bounds retained.target initial span_eq layer spans value.models
    value.horner value.horner_eq ⟨coefficientTarget initial target, requests.residual_le bounds errorPositive⟩
  have gapEqual := cellData.gapNorm_eq
  simp only [Norm.Basic.normSq_eq_canonical] at gapEqual bound ⊢
  have sameTaylor :
      4 * (value.models.common.primitive.remainderBound * ((25 / 4) * normSq (halfGap site parameter)) ^ 2 +
        value.horner.value * ((25 / 4) * normSq (halfGap site parameter))) * initial.span.width ^ 2 *
          Geometric.Basic.quarterRadius (initial.span.width ^ 2) stage.val =
        Geometric.Basic.quarterRadius value.scale stage.val := by
    have transported := congrArg (fun amount : Fraction.Rational =>
      Geometric.Basic.quarterRadius amount stage.val) value.scale_eq
    apply Eq.trans ?_ transported.symm
    unfold taylorScale
    rewrite [← gapEqual]
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1
  rewrite [sameTaylor] at bound
  have errorPaid : 2 * coefficientTarget initial target * initial.span.width ^ 2 ≤ target / 2 := by
    calc
      _ = (2 * initial.span.width ^ 2) * coefficientTarget initial target := by ring1
      _ ≤ target / 2 := Budget.Weighted.mul_allowance_le halfPositive.le weightNonnegative
  have taylorPaid := value.taylor.later_accurate stage.property
  have total : Geometric.Basic.quarterRadius value.scale stage.val +
      2 * coefficientTarget initial target * initial.span.width ^ 2 < target := by
    calc
      _ ≤ Geometric.Basic.quarterRadius value.scale stage.val + target / 2 :=
        Arithmetic.add_le_add_direct (Fraction.Order.Basic.le_refl _) errorPaid
      _ < target / 2 + target / 2 := Arithmetic.add_lt_add_right_direct taylorPaid (target / 2)
      _ = target := Fraction.half_add_half target
  exact bound.trans_lt total

end Precision

end ScalarModels

end ScalarModels

/-- The original ordered interior Reading occurrences paired with their actual same-parent primitive Points.

The existing dependent product preserves every bounded time occurrence and
its original Reading index. Each entry contains the same original primitive
parent and its actual internally computed continuation/comparison caches.
-/
@[expose] def CurvePoints (cached : PrimitiveTarget bounds original count) (times : List Fraction.Rational)
    (inside : Inside times) (readings : Readings leg.actual times inside)
    (interior : ∀ index : Fin times.length,
      first < times[index.val]'index.isLt ∧ times[index.val]'index.isLt < last) : Type 1 :=
  DependentProduct times (fun index => CurvePoint bounds cached (times[index.val]'index.isLt)
    (Readings.get readings index) (interior index))

/-- Materialize the actual interior links once, sharing the same retained source outside the entry producer.

Only the original supplied Reading bank is read. Its original cofactor and
lift queries are not repeated, and the exact prepared source view is captured
once by the producer of all ordered dependent entries.
-/
@[expose] def curvePoints (cached : PrimitiveTarget bounds original count) (times : List Fraction.Rational)
    (inside : Inside times) (readings : Readings leg.actual times inside)
    (interior : ∀ index : Fin times.length,
      first < times[index.val]'index.isLt ∧ times[index.val]'index.isLt < last) :
    CurvePoints bounds cached times inside readings interior :=
  let prepared : CurveSource bounds cached := curveSource bounds cached
  DependentProduct.ofFn times (fun index => curvePointFromSource bounds cached prepared (times[index.val]'index.isLt)
    (Readings.get readings index) (interior index))

namespace CurvePoints

/-- Read one complete retained interior cache at its original bounded occurrence without invoking its producer. -/
@[expose] def get {cached : PrimitiveTarget bounds original count} {times : List Fraction.Rational}
    {inside : Inside times} {readings : Readings leg.actual times inside}
    {interior : ∀ index : Fin times.length,
      first < times[index.val]'index.isLt ∧ times[index.val]'index.isLt < last}
    (values : CurvePoints bounds cached times inside readings interior) (index : Fin times.length) :
    CurvePoint bounds cached (times[index.val]'index.isLt) (Readings.get readings index) (interior index) :=
  DependentProduct.get times values index

end CurvePoints

/-- An actual bank entry is the complete original cache-aware result on that same stored source and original Reading. -/
theorem curvePoints_get (cached : PrimitiveTarget bounds original count) (times : List Fraction.Rational)
    (inside : Inside times) (readings : Readings leg.actual times inside)
    (interior : ∀ index : Fin times.length,
      first < times[index.val]'index.isLt ∧ times[index.val]'index.isLt < last) (index : Fin times.length) :
    CurvePoints.get bounds (curvePoints bounds cached times inside readings interior) index =
      curvePointFromSource bounds cached (curveSource bounds cached) (times[index.val]'index.isLt)
        (Readings.get readings index) (interior index) := by
  unfold curvePoints CurvePoints.get
  exact DependentProduct.get_ofFn times _ index

section Parents

open Purelib.Curves.Legendre.Periods
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)

variable {differential : Differential 1} {sheet : Fin 2}

/-- The original cached parents lie in this same actual primitive patch by their original spatial-route containment.

The exact ParentCache and original occurrence membership transport the
retained route hull. Both endpoint domains follow from the paid move's
intrinsic cap, without successful overlap evidence or domain enlargement.
-/
theorem parent_endpoints_inside (cached : PrimitiveTarget bounds original count)
    (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge (Fibre.frameCurve frame) differential)
    (member : parent ∈ cache.parents) :
    cached.patch.box.Contains (parent.edge.point 0) ∧ cached.patch.box.Contains (parent.edge.point 1) :=
  PreparedPathParentContainment.ParentCache.endpoints_inBox cache cached.spatial_path_inside parent member

/-- Every original parent-prefix vertex obeys the retained intrinsic Leg/Horner movement bound.

The original complete spatial cover derives its route containment. Parent
provenance identifies its exact source owner and literal original prefix;
this mathematical readback does not acquire a numerical parent or path.
-/
theorem parent_prefix_movement (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (index : Fin cache.parents.length) (point : Canonical)
    (member : point ∈ OwnerPath.vertices
      (cache.ownerPrefixFromTrace geometry.route.within covered.block_eq covered.block.traced.trace.get rfl index)) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval point -
      (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first)) ≤
      leg.traceMovement coarse.bounds * (first - last) ^ 2 := by
  have whole := cache.ownerPrefixFromTrace_member geometry.route.within covered.block_eq
    covered.block.traced.trace.get rfl index point member
  exact covered.trace_movement leg coarse point whole

/-- The same retained move payment bounds every original prefix vertex in the actual shared reference units. -/
private theorem parent_prefix_paid (cached : PrimitiveTarget bounds original count)
    {sourcePoint : SourcePoint bounds cached} (value : Reference bounds cached sourcePoint)
    (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (index : Fin cache.parents.length) (vertex : Canonical)
    (member : vertex ∈ OwnerPath.vertices
      (cache.ownerPrefixFromTrace geometry.route.within covered.block_eq covered.block.traced.trace.get rfl index)) :
    Norm.Basic.normSq ((Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first) -
      (Paths.polynomial parameter).eval vertex) ≤ value.sourceReading.norm ^ 2 / 1024 := by
  have rootLower : Radial.Clearance.rootFloor site parameter ≤ value.sourceReading.norm := by
    rewrite [value.sourceReading.norm_eq, value.sourceReading.value_eq]
    have retained := Radial.Clearance.rootFloor_le_sample site parameter (Waist.direction quarter first)
      leg.regular leg.actual.data.bound (Parallel.source_inside leg.regular) source value.sourceReading.index
    rewrite [Norm.Basic.normSq_eq_canonical] at retained
    exact retained
  have movementPaid := (leg.source.residualTimeRequest_pays_lt
    (OwnerBudget.accuracy leg budget.floor (some bounds.timeRequest)).val
    (leg.traceMovement coarse.bounds) (leg.traceMovement_nonnegative coarse.bounds coarse.bounds_eq)
    (first - last) paid).le.trans budget.tolerance_le_root
  have retained := parent_prefix_movement (leg := leg) (coarse := coarse) frame covered cache index vertex member
  have reverse : Norm.Basic.normSq ((Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first) - (Paths.polynomial parameter).eval vertex) =
      Norm.Basic.normSq ((Paths.polynomial parameter).eval vertex - (Paths.polynomial parameter).eval
        (coordinate site parameter 2 quarter (by decide +kernel) first)) := by
    rewrite [show (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first) -
      (Paths.polynomial parameter).eval vertex = -((Paths.polynomial parameter).eval vertex -
        (Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first)) by ring1,
      Norm.Basic.normSq_neg]
    rfl
  rewrite [reverse]
  exact (retained.trans movementPaid).trans (Fraction.Order.Field.divide_mono
    (Arithmetic.pow_le_pow_direct
      (Radial.Clearance.rootFloor_positive site parameter leg.regular).le rootLower 2) (by decide +kernel))

/-- One actual parent's common Point, original raw comparison and original signed name relation.

The bounded original parent occurrence remains the source owner and exact
coordinate. This is a view of existing Point and comparison objects, not a
new owner or comparison family.
-/
@[expose] def ParentPoint (cached : PrimitiveTarget bounds original count) (frame : Paths.Frame parameter)
    (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (index : Fin cache.parents.length) : Type :=
  let parent := cache.parents[index.val]'index.isLt
  Σ sample : ContinuedNeighborhood.Point cached.patch (parent.edge.segment.pointAt parent.edge.left.parameter),
  Σ _raw : Gaussian.Equivalence.Equivalent (ownerApproximation parent.edge.owner) (ownerApproximation sample.owner),
    NamedEquivalent (parent.edge.owner.certificate parent.edge.owner.parameterNonzero).value.name
      sample.certificate.value.name

/-- Construct the actual parent's signed common Point from the retained reference and intrinsic original provenance.

The supplied original cover derives the domain and movement payment. Its
prefix and trace are used only in proofs; no prefix bank is materialized or
retained solely for sign. The actual Point and raw/name results are retained.
-/
def parentPoint (cached : PrimitiveTarget bounds original count) {sourcePoint : SourcePoint bounds cached}
    (value : Reference bounds cached sourcePoint) (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (index : Fin cache.parents.length) : ParentPoint bounds cached frame covered cache index := by
  let parent := cache.parents[index.val]'index.isLt
  have endpoints := parent_endpoints_inside bounds cached frame covered cache parent
    (_root_.List.getElem_mem index.isLt)
  have inside : cached.patch.box.Contains (parent.edge.segment.pointAt parent.edge.left.parameter) := by
    have first := endpoints.1
    rewrite [parent.edge.point_zero] at first
    exact first
  let sample := ContinuedNeighborhood.Point.acquire cached.patch
    (parent.edge.segment.pointAt parent.edge.left.parameter) inside
  let initialPath := cache.ownerPrefixFromTrace geometry.route.within covered.block_eq
    covered.block.traced.trace.get rfl index
  have movement : ∀ vertex ∈ initialPath.vertices,
      normSq ((Paths.polynomial parameter).eval (coordinate site parameter 2 quarter (by decide +kernel) first) -
        (Paths.polynomial parameter).eval vertex) ≤ value.sourceReading.norm ^ 2 / 1024 := by
    intro vertex member
    have retained := parent_prefix_paid bounds cached value frame covered cache index vertex member
    rewrite [Norm.Basic.normSq_eq_canonical] at retained
    exact retained
  let raw := Reference.pathEquivalent bounds value (target := parent.edge.owner) initialPath movement sample
  let related := SquareRootTrackEquivalence.rootEquivalent_of_approximationEquivalent
    parent.edge.owner.parameterNonzero parent.edge.owner.track sample.owner.track raw
  exact ⟨sample, raw, related⟩

/-- The once-retained original Reference and whole original bounded Point bank with exact factory equations.

Only actual comparison/Point results are retained. Prefix and trace
provenance belong to the sign proofs and are not additional runtime banks.
-/
@[expose] def ParentPoints (cached : PrimitiveTarget bounds original count) (sourcePoint : SourcePoint bounds cached)
    (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet) : Type :=
  Σ retained : {actual : Reference bounds cached sourcePoint // actual = reference bounds cached sourcePoint},
    {points : DependentProduct cache.parents (fun index => ParentPoint bounds cached frame covered cache index) //
      points = DependentProduct.ofFn cache.parents
        (fun index => parentPoint bounds cached retained.val frame covered cache index)}

/-- Build one actual signed parent-Point bank with its shared reference outside the entry producer.

The same original cached patch, source Point, cover, actual parent list and
bounded occurrences are consumed. A supplied whole Reference is reused;
the default retains the entire original factory result. No source
preparation or prefix bank is repeated to manufacture annotations.
-/
def parentPoints (cached : PrimitiveTarget bounds original count) (sourcePoint : SourcePoint bounds cached)
    (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (retained : {actual : Reference bounds cached sourcePoint //
      actual = reference bounds cached sourcePoint} := ⟨reference bounds cached sourcePoint, rfl⟩) :
    ParentPoints bounds cached sourcePoint frame covered cache :=
  let points := DependentProduct.ofFn cache.parents
    (fun index => parentPoint bounds cached retained.val frame covered cache index)
  ⟨retained, ⟨points, rfl⟩⟩

/-- The complete original parent-Point constructor consumes the same supplied Reference and exact ordered Point bank.

The default argument is the entire original reference factory result. Its
specialization therefore preserves the whole former constructor value,
while a supplied retained reference is passed literally to each original
Point producer, outside the finite entry traversal.
-/
theorem parentPoints_eq (cached : PrimitiveTarget bounds original count) (sourcePoint : SourcePoint bounds cached)
    (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (retained : {actual : Reference bounds cached sourcePoint //
      actual = reference bounds cached sourcePoint} := ⟨reference bounds cached sourcePoint, rfl⟩) :
    parentPoints bounds cached sourcePoint frame covered cache retained =
      ⟨retained, ⟨DependentProduct.ofFn cache.parents
        (fun index => parentPoint bounds cached retained.val frame covered cache index), rfl⟩⟩ := (rfl)

namespace ParentPoints

variable {cached : PrimitiveTarget bounds original count} {sourcePoint : SourcePoint bounds cached}
variable {frame : Paths.Frame parameter} {covered : Covered geometry source}
variable {cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet}

/-- Read the identical retained whole shared Reference. -/
@[expose] def reference (bank : ParentPoints bounds cached sourcePoint frame covered cache) :
    Reference bounds cached sourcePoint := bank.1.val

/-- The shared Reference is the whole original reference factory on these same actual inputs. -/
theorem reference_eq (bank : ParentPoints bounds cached sourcePoint frame covered cache) :
    bank.reference = PrimitiveTarget.reference bounds cached sourcePoint := bank.1.property

/-- Read the original stored bounded Point/raw/name bank without traversing a prefix or acquiring a root. -/
@[expose] def points (bank : ParentPoints bounds cached sourcePoint frame covered cache) :
    DependentProduct cache.parents (fun index => ParentPoint bounds cached frame covered cache index) := bank.2.val

/-- The entire stored Point bank is the original producer on the same shared reference and actual parent occurrences. -/
theorem points_eq (bank : ParentPoints bounds cached sourcePoint frame covered cache) :
    bank.points = DependentProduct.ofFn cache.parents
      (fun index => parentPoint bounds cached bank.reference frame covered cache index) := bank.2.property

/-- Every bounded lookup returns the complete original cache-aware Point/raw/name result. -/
theorem points_get (bank : ParentPoints bounds cached sourcePoint frame covered cache)
    (index : Fin cache.parents.length) :
    DependentProduct.get cache.parents bank.points index =
      parentPoint bounds cached bank.reference frame covered cache index := by
  rewrite [bank.points_eq]
  exact DependentProduct.get_ofFn cache.parents _ index

section SourceParents

open Purelib.Curves.Legendre.Periods
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.InverseModelEdgeTransition (EdgeTransition)

/-- Construct one original source/common model edge from this same bounded retained parent Point.

The original parent occurrence, stored Point and signed name comparison are
read directly. Its actual cover and intrinsic route containment derive both
common endpoint domains. The original prepared-source operation consumes
its own stored firstSample and model; no Point, reference, source request
or owner prefix is acquired by this construction.
-/
def sourceEdge (bank : ParentPoints bounds cached sourcePoint frame covered cache)
    (index : Fin cache.parents.length)
    {localCount localFloor : Nat}
    {patch : PreparedPatch (cache.parents[index.val]'index.isLt)}
    {localInside : (patch.neighborhood localCount).box.Contains
      ((cache.parents[index.val]'index.isLt).edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {path : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets path stage}
    (prepared : Jets.Source.Cell.PreparedParent (frame := frame) (basis := differential)
      patch localCount localFloor localInside targets)
    {commonFloor : Nat} {commonTarget : Fraction.Rational} {commonCache : Jets.Source.Cache cached.patch}
    (requested : Jets.Source.Request commonCache commonFloor commonTarget) :
    {edge : EdgeTransition ((patch.neighborhood localCount).base.refine
        prepared.preparation.attached.source.selection.stage)
      (cached.patch.base.refine requested.selection.stage)
      (Jets.Source.Cell.PreparedParent.startPoint (cache.parents[index.val]'index.isLt)).coordinate
      (Jets.Source.Cell.PreparedParent.finishPoint (cache.parents[index.val]'index.isLt)).coordinate //
      edge.sample.alignment.flip = false} := by
  let parent := cache.parents[index.val]'index.isLt
  let retained := DependentProduct.get cache.parents bank.points index
  have endpoints := parent_endpoints_inside bounds cached frame covered cache parent
    (_root_.List.getElem_mem index.isLt)
  have firstInside : cached.patch.box.Contains (Jets.Source.Cell.PreparedParent.startPoint parent).coordinate := by
    have selected := endpoints.1
    rewrite [parent.edge.point_zero] at selected
    exact selected
  have lastInside : cached.patch.box.Contains (Jets.Source.Cell.PreparedParent.finishPoint parent).coordinate := by
    have selected := endpoints.2
    rewrite [parent.edge.point_one] at selected
    exact selected
  exact Jets.Source.Cell.PreparedParent.commonEdge prepared requested retained.1 retained.2.2 firstInside lastInside

end SourceParents

end ParentPoints

section IntegralComparison

open Purelib.Riemann.Readings.UniformPreparedRequests (RequestedParents PrimitiveSumRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {localCount : Nat} {target : Fraction.Rational}

/-- Compute each original spatial parent's retained pair budget and finite selection from intrinsic common domains.

The same actual cover and parent cache derive all endpoint containments.
The supplied ordered request bank fixes the original local neighborhoods;
no caller successful overlap, signed relation or precision bound is needed.
-/
def parentPairSelections (cached : PrimitiveTarget bounds original count) (frame : Paths.Frame parameter)
    (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (requests : RequestedParents localCount target cache.parents)
    (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    RequestedParents.PairSelections requests cached.patch tolerance :=
  requests.pairSelections cached.patch tolerance positive (fun index => by
    have endpoints := parent_endpoints_inside bounds cached frame covered cache
      (cache.parents[index.val]'index.isLt) (_root_.List.getElem_mem index.isLt)
    have first := endpoints.1
    rewrite [(cache.parents[index.val]'index.isLt).edge.point_zero] at first
    exact ⟨first, endpoints.2⟩)

/-- The actual refined parent bank's sum meets its common primitive boundary at the chosen aggregate mismatch target.

All original endpoint domains, strict parent order, source ownership and
signed relations come from the same retained geometric and Point banks.
The original connected parent chain performs cancellation. This compares
primitive increments; it does not discard the separate integration error.
-/
theorem parent_boundary_mismatch_lt (cached : PrimitiveTarget bounds original count)
    {sourcePoint : SourcePoint bounds cached} (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (points : ParentPoints bounds cached sourcePoint frame covered cache)
    (requests : RequestedParents localCount target cache.parents) (positive : 0 < target)
    (mismatchTarget : Fraction.Rational) (mismatchPositive : 0 < mismatchTarget)
    (selections : RequestedParents.PairSelections requests cached.patch
      (Budget.Aggregate.perTerm mismatchTarget cache.parents.length))
    {modelIndex : Nat} (model : PrimitiveModel cached.patch modelIndex (differentialNumerator differential))
    (later : selections.stage ≤ modelIndex)
    (floor : {minimum : Nat // selections.stage ≤ minimum} := ⟨selections.stage, Nat.le_refl _⟩) :
    normSq (gaussianSum (requests.refine positive cache.proper floor.val).increments -
      (model.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) last) -
        model.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) first))) <
      mismatchTarget := by
  obtain ⟨chain⟩ := cache.chain
  have bound := selections.refined_boundary_le positive cache.proper
    (fun index => (DependentProduct.get cache.parents (ParentPoints.points bounds points) index).1)
    (fun index => (DependentProduct.get cache.parents (ParentPoints.points bounds points) index).2.2)
    model later chain.toDirectPathChain floor
  have paid := Budget.Aggregate.count_mul_perTerm_lt mismatchPositive cache.parents.length
  have units : (cache.parents.length : Fraction.Rational) ^ 2 *
      Budget.Aggregate.perTerm mismatchTarget cache.parents.length =
      (cache.parents.length : Fraction.Rational) * ((cache.parents.length : Fraction.Rational) *
        Budget.Aggregate.perTerm mismatchTarget cache.parents.length) := by ring1
  exact bound.trans_lt (units.trans_lt paid)

namespace ParentIntegralRequest

/-- The actual ordered pair-selection cache with its complete original factory identity.

This exact subtype view retains the supplied original PairSelections bank.
Its whole procedure equality connects the model floor and parent request
without executing either selection procedure again.
-/
@[expose] def Selections (cached : PrimitiveTarget bounds original count) (frame : Paths.Frame parameter)
    (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (mismatchTarget : Fraction.Rational) (mismatchPositive : 0 < mismatchTarget) : Type :=
  {actual : RequestedParents.PairSelections requests cached.patch
      (Budget.Aggregate.perTerm mismatchTarget cache.parents.length) //
    actual = parentPairSelections bounds cached frame covered cache requests
      (Budget.Aggregate.perTerm mismatchTarget cache.parents.length)
      (Budget.Aggregate.perTerm_positive mismatchPositive cache.parents.length)}

/-- One actual original common model with its complete factory equation and computed all-parent stage payment.

The existing dependent pair and subtype retain the actual model index and
whole supplied PrimitiveModel. The paid floor comes from this same original
ordered parent's computed pair selections; it is not a comparison or domain
success premise and creates no replacement request or root owner.
-/
@[expose] def Model (cached : PrimitiveTarget bounds original count) (frame : Paths.Frame parameter)
    (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (mismatchTarget : Fraction.Rational) (mismatchPositive : 0 < mismatchTarget) : Type :=
  Σ index : Nat,
    {actual : PrimitiveModel cached.patch index (differentialNumerator differential) //
      actual = PrimitiveModel.ofIndex cached.patch index (differentialNumerator differential) ∧
      (parentPairSelections bounds cached frame covered cache requests
        (Budget.Aggregate.perTerm mismatchTarget cache.parents.length)
        (Budget.Aggregate.perTerm_positive mismatchPositive cache.parents.length)).stage ≤ index}

/-- Select the actual supplied model index, or the same retained bank's original common stage.

The explicit natural result keeps the original request's dependent floor
small. The supplied-model branch reads only its stored index; the default
alone traverses the actual retained selection bank's finite maximum.
-/
@[expose] def floor (cached : PrimitiveTarget bounds original count) (frame : Paths.Frame parameter)
    (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (mismatchTarget : Fraction.Rational) (mismatchPositive : 0 < mismatchTarget)
    (selections : Selections bounds cached frame covered cache requests mismatchTarget mismatchPositive)
    (model : Option (Model bounds cached frame covered cache requests mismatchTarget mismatchPositive)) : Nat :=
  match model with
  | none => selections.val.stage
  | some retained => retained.1

end ParentIntegralRequest

/-- The actual all-parent finite selections, common model, boundary value and paid original aggregate request.

The exact Sigma view retains the original ordered bank refined to its
computed common floor, or a supplied later paid model, and its once-evaluated
boundary. Both mismatch and integration allowances remain explicit and
separate, with the full original request factory retained by equality.
-/
@[expose] def ParentIntegralRequest (cached : PrimitiveTarget bounds original count) (frame : Paths.Frame parameter)
    (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (positive : 0 < target) (mismatchTarget : Fraction.Rational)
    (mismatchPositive : 0 < mismatchTarget)
    (retainedModel : Option (ParentIntegralRequest.Model bounds cached frame covered cache requests
      mismatchTarget mismatchPositive) := none) : Type 2 :=
  Σ selections : ParentIntegralRequest.Selections bounds cached frame covered cache requests
      mismatchTarget mismatchPositive,
  Σ floor : {actual : Nat // actual = ParentIntegralRequest.floor bounds cached frame covered cache requests
    mismatchTarget mismatchPositive selections retainedModel},
  Σ refined : {actual : RequestedParents localCount
      (Budget.Aggregate.perTerm target cache.parents.length) cache.parents //
    actual = requests.refine (Budget.Aggregate.perTerm_positive positive cache.parents.length)
      cache.proper floor.val},
  Σ model : {actual : PrimitiveModel cached.patch floor.val (differentialNumerator differential) //
    actual = PrimitiveModel.ofIndex cached.patch floor.val (differentialNumerator differential)},
  Σ boundary : {actual : Canonical // actual =
    model.val.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) last) -
      model.val.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) first)},
  {result : PrimitiveSumRequest cache.parents localCount target //
    result = PrimitiveSumRequest.ofRequests cache.parents target positive refined.val ∧
    normSq (result.primitiveSum - boundary.val) < mismatchTarget ∧
    normSq (boundary.val - result.integralSample) < 2 * (mismatchTarget + target)}

/-- Compare the common boundary with the actual retained spatial parents and original integral caches.

One supplied or once-computed original pair/Selection bank fixes the common
floor. A supplied actual aggregate refines once and retains its adequate scalar caches; the
default uses the original bank/assembler. One common primitive and boundary
are built or retained outside entries. A supplied common model retains its
actual index and computed floor payment. The actual aggregate's PAID target remains
explicit, so the squared error is twice the sum of both allowances.
-/
def parentIntegralRequest (cached : PrimitiveTarget bounds original count)
    {sourcePoint : SourcePoint bounds cached} (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (points : ParentPoints bounds cached sourcePoint frame covered cache)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (positive : 0 < target) (mismatchTarget : Fraction.Rational)
    (mismatchPositive : 0 < mismatchTarget)
    (retained : Option {actual : PrimitiveSumRequest cache.parents localCount target //
      actual.requestsAtTarget = requests} := none)
    (retainedSelections : ParentIntegralRequest.Selections bounds cached frame covered cache requests
      mismatchTarget mismatchPositive :=
      ⟨parentPairSelections bounds cached frame covered cache requests
        (Budget.Aggregate.perTerm mismatchTarget cache.parents.length)
        (Budget.Aggregate.perTerm_positive mismatchPositive cache.parents.length), rfl⟩)
    (retainedModel : Option (ParentIntegralRequest.Model bounds cached frame covered cache requests
      mismatchTarget mismatchPositive) := none) :
    ParentIntegralRequest bounds cached frame covered cache requests positive mismatchTarget mismatchPositive
      retainedModel := by
  let selections := retainedSelections.val
  let floor := ParentIntegralRequest.floor bounds cached frame covered cache requests
    mismatchTarget mismatchPositive retainedSelections retainedModel
  have later : selections.stage ≤ floor := by
    cases retainedModel with
    | none => exact Nat.le_refl _
    | some kept =>
        exact (congrArg (fun actual : RequestedParents.PairSelections requests cached.patch
          (Budget.Aggregate.perTerm mismatchTarget cache.parents.length) => actual.stage)
          retainedSelections.property).le.trans kept.2.property.2
  have localPositive := Budget.Aggregate.perTerm_positive positive cache.parents.length
  let integral : Σ refined : {actual : RequestedParents localCount
        (Budget.Aggregate.perTerm target cache.parents.length) cache.parents //
      actual = requests.refine localPositive cache.proper floor},
      {result : PrimitiveSumRequest cache.parents localCount target //
        result = PrimitiveSumRequest.ofRequests cache.parents target positive refined.val} :=
    match retained with
    | none =>
        let refined := requests.refine localPositive cache.proper floor
        let result := PrimitiveSumRequest.ofRequests cache.parents target positive refined
        ⟨⟨refined, rfl⟩, ⟨result, rfl⟩⟩
    | some original =>
        let result := original.val.refine cache.proper floor
        let refined := result.requestsAtTarget
        have refinedEq : refined = requests.refine localPositive cache.proper floor := by
          exact (original.val.requestsAtTarget_refine cache.proper floor).trans
            (congrArg (fun actual => actual.refine localPositive cache.proper floor) original.property)
        ⟨⟨refined, refinedEq⟩, ⟨result, result.ofRequests_requestsAtTarget_eq.symm⟩⟩
  let model : PrimitiveModel cached.patch floor (differentialNumerator differential) := by
    cases retainedModel with
    | none => exact PrimitiveModel.ofIndex cached.patch floor (differentialNumerator differential)
    | some kept => exact kept.2.val
  have modelEq : model = PrimitiveModel.ofIndex cached.patch floor (differentialNumerator differential) := by
    cases retainedModel with
    | none => rfl
    | some kept => exact kept.2.property.1
  let boundary := model.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) last) -
    model.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) first)
  let result := integral.2.val
  have mismatch := parent_boundary_mismatch_lt bounds cached frame covered cache points requests localPositive
    mismatchTarget mismatchPositive selections model later ⟨floor, later⟩
  have resultSum : result.primitiveSum = gaussianSum (requests.refine localPositive cache.proper floor).increments := by
    have readback := congrArg (fun actual : PrimitiveSumRequest cache.parents localCount target =>
      actual.primitiveSum) integral.2.property
    exact readback.trans (congrArg (fun actual : RequestedParents localCount
      (Budget.Aggregate.perTerm target cache.parents.length) cache.parents =>
        gaussianSum actual.increments) integral.1.property)
  have resultMismatch : normSq (result.primitiveSum - boundary) < mismatchTarget := by
    rewrite [resultSum]
    exact mismatch
  have reverse := Norm.Bounds.normSq_sub_symm boundary result.primitiveSum
  simp only [Norm.Basic.normSq_eq_canonical] at reverse
  have firstBound : normSq (boundary - result.primitiveSum) < mismatchTarget := reverse.trans_lt resultMismatch
  have lastBound := result.accurate
  have combined := Norm.Bounds.normSq_sub_le_via boundary result.primitiveSum result.integralSample
  simp only [Norm.Basic.normSq_eq_canonical] at combined
  have attained := combined.trans_lt (Arithmetic.mul_lt_mul_of_pos_left_direct
    (by decide +kernel : (0 : Fraction.Rational) < 2)
    (Arithmetic.add_lt_add_direct firstBound lastBound))
  exact ⟨⟨selections, retainedSelections.property⟩, ⟨floor, rfl⟩, integral.1, ⟨model, modelEq⟩, ⟨boundary, rfl⟩,
    ⟨result, integral.2.property, resultMismatch, attained⟩⟩

namespace ParentIntegralRequest

variable {cached : PrimitiveTarget bounds original count} {frame : Paths.Frame parameter}
variable {covered : Covered geometry source}
variable {cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet}
variable {requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
  cache.parents} {positive : 0 < target} {mismatchTarget : Fraction.Rational}
variable {mismatchPositive : 0 < mismatchTarget}
variable {retainedModel : Option (Model bounds cached frame covered cache requests
  mismatchTarget mismatchPositive)}

/-- Read the actual common-model stage stored in the original parent request. -/
@[expose] def index
    (value : ParentIntegralRequest bounds cached frame covered cache requests positive
      mismatchTarget mismatchPositive retainedModel) : Nat := value.2.1.val

/-- Read the whole actual common primitive model stored before evaluating its boundary. -/
@[expose] def model
    (value : ParentIntegralRequest bounds cached frame covered cache requests positive
      mismatchTarget mismatchPositive retainedModel) :
    PrimitiveModel cached.patch value.index (differentialNumerator differential) := value.2.2.2.1.val

/-- Read the exact once-computed boundary of the retained common primitive. -/
@[expose] def boundary
    (value : ParentIntegralRequest bounds cached frame covered cache requests positive
      mismatchTarget mismatchPositive retainedModel) : Canonical :=
  value.2.2.2.2.1.val

/-- Read the complete original aggregate request and its actual child-block integral cache. -/
@[expose] def request
    (value : ParentIntegralRequest bounds cached frame covered cache requests positive
      mismatchTarget mismatchPositive retainedModel) :
    PrimitiveSumRequest cache.parents localCount target := value.2.2.2.2.2.val

/-- The stored original primitive sum meets its separately paid common-boundary mismatch target. -/
theorem mismatch (value : ParentIntegralRequest bounds cached frame covered cache requests positive
      mismatchTarget mismatchPositive retainedModel) :
    normSq (value.request.primitiveSum - value.boundary) < mismatchTarget := value.2.2.2.2.2.property.2.1

/-- The actual retained child-block integral meets the sum of its original and common-boundary allowances. -/
theorem accurate (value : ParentIntegralRequest bounds cached frame covered cache requests positive
      mismatchTarget mismatchPositive retainedModel) :
    normSq (value.boundary - value.request.integralSample) < 2 * (mismatchTarget + target) :=
  value.2.2.2.2.2.property.2.2

end ParentIntegralRequest

/-- The actual parent comparison refines a supplied aggregate once and reads its same whole result. -/
theorem parentIntegralRequest_request_retained (cached : PrimitiveTarget bounds original count)
    {sourcePoint : SourcePoint bounds cached} (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (points : ParentPoints bounds cached sourcePoint frame covered cache)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (positive : 0 < target) (mismatchTarget : Fraction.Rational)
    (mismatchPositive : 0 < mismatchTarget)
    (retained : {actual : PrimitiveSumRequest cache.parents localCount target // actual.requestsAtTarget = requests})
    (retainedSelections : ParentIntegralRequest.Selections bounds cached frame covered cache requests
      mismatchTarget mismatchPositive :=
      ⟨parentPairSelections bounds cached frame covered cache requests
        (Budget.Aggregate.perTerm mismatchTarget cache.parents.length)
        (Budget.Aggregate.perTerm_positive mismatchPositive cache.parents.length), rfl⟩)
    (retainedModel : Option (ParentIntegralRequest.Model bounds cached frame covered cache requests
      mismatchTarget mismatchPositive) := none) :
    (parentIntegralRequest bounds cached frame covered cache points requests positive mismatchTarget mismatchPositive
      (some retained) retainedSelections retainedModel).request = retained.val.refine cache.proper
      (ParentIntegralRequest.floor bounds cached frame covered cache requests mismatchTarget mismatchPositive
        retainedSelections retainedModel) := (rfl)

/-- The actual supplied-model branch reads the same whole retained primitive model.

The heterogeneous equality preserves its actual stored index together with
the original patch and numerator. It requires no reduction of the opaque
parent-request producer in an ordinary client.
-/
theorem parentIntegralRequest_model_retained (cached : PrimitiveTarget bounds original count)
    {sourcePoint : SourcePoint bounds cached} (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (points : ParentPoints bounds cached sourcePoint frame covered cache)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (positive : 0 < target) (mismatchTarget : Fraction.Rational)
    (mismatchPositive : 0 < mismatchTarget)
    (retained : Option {actual : PrimitiveSumRequest cache.parents localCount target //
      actual.requestsAtTarget = requests})
    (selections : ParentIntegralRequest.Selections bounds cached frame covered cache requests
      mismatchTarget mismatchPositive)
    (model : ParentIntegralRequest.Model bounds cached frame covered cache requests mismatchTarget mismatchPositive) :
    HEq (parentIntegralRequest bounds cached frame covered cache points requests positive
      mismatchTarget mismatchPositive
      retained selections (some model)).model model.2.val :=
  (HEq.rfl)

/-- The actual boundary cache evaluates the same supplied whole primitive at the original two chart endpoints. -/
theorem parentIntegralRequest_boundary_retained (cached : PrimitiveTarget bounds original count)
    {sourcePoint : SourcePoint bounds cached} (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (points : ParentPoints bounds cached sourcePoint frame covered cache)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (positive : 0 < target) (mismatchTarget : Fraction.Rational)
    (mismatchPositive : 0 < mismatchTarget)
    (retained : Option {actual : PrimitiveSumRequest cache.parents localCount target //
      actual.requestsAtTarget = requests})
    (selections : ParentIntegralRequest.Selections bounds cached frame covered cache requests
      mismatchTarget mismatchPositive)
    (model : ParentIntegralRequest.Model bounds cached frame covered cache requests mismatchTarget mismatchPositive) :
    (parentIntegralRequest bounds cached frame covered cache points requests positive mismatchTarget mismatchPositive
      retained selections (some model)).boundary =
      model.2.val.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) last) -
        model.2.val.primitive.value.eval (coordinate site parameter 2 quarter (by decide +kernel) first) := (rfl)

/-- An adequate supplied aggregate remains the same complete original value in the actual parent comparison. -/
theorem parentIntegralRequest_request_of_ge (cached : PrimitiveTarget bounds original count)
    {sourcePoint : SourcePoint bounds cached} (frame : Paths.Frame parameter) (covered : Covered geometry source)
    (cache : ParentCache (curve := Fibre.frameCurve frame) covered.block differential sheet)
    (points : ParentPoints bounds cached sourcePoint frame covered cache)
    (requests : RequestedParents localCount (Budget.Aggregate.perTerm target cache.parents.length)
      cache.parents) (positive : 0 < target) (mismatchTarget : Fraction.Rational)
    (mismatchPositive : 0 < mismatchTarget)
    (retained : {actual : PrimitiveSumRequest cache.parents localCount target // actual.requestsAtTarget = requests})
    (adequate : ∀ index : Fin cache.parents.length,
      (parentPairSelections bounds cached frame covered cache requests
        (Budget.Aggregate.perTerm mismatchTarget cache.parents.length)
        (Budget.Aggregate.perTerm_positive mismatchPositive cache.parents.length)).stage ≤
      (retained.val.requests.get index).request.index) :
    (parentIntegralRequest bounds cached frame covered cache points requests positive mismatchTarget mismatchPositive
      (some retained)).request = retained.val :=
  (parentIntegralRequest_request_retained bounds cached frame covered cache points requests positive
    mismatchTarget mismatchPositive retained).trans (retained.val.refine_of_ge cache.proper _ adequate)

end IntegralComparison

end Parents

end PrimitiveTarget

end Primitive

end OwnerMove

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
