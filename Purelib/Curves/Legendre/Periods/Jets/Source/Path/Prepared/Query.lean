module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
public import Purelib.Curves.Legendre.Periods.Jets.Source.Parameter
public import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.Query
import Purelib.Integration.Polynomial.Gaussian.Cell.Spatial.Observation
import Purelib.Polynomial.Geometry.ClearPath

/-! # The actual prepared source query at its original affine parent point

The original complete Cell factory equation retains its real patch, request
and spatial coordinate cache. Every already retained query sample is compared
to the original edge root at that exact physical fraction. Its box refinement
is transported as a scalar box identity; the original Point, owner, certificate
and six observation caches are not rebuilt or replaced.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Polynomial.Gaussian.Cell
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Normalization.ContinuedInverseRoot.ContinuedNeighborhood (UniformBounds)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}

/-- Compare the SAME original first Point with an already retained zero Query.

The original physical zero law and covering patch containment select the
actual cached endpoint. Only the existing common-seed comparison runs;
no Query, Point, source preparation or root Owner is acquired.
-/
def firstRetainedQueryEquivalent (prepared : PreparedParent patch count floor covered targets)
    (direct : PreparedEdge.Query parent.edge 0 parent.edge.baseInside) :
    NamedEquivalent (parent.edge.rootName 0 parent.edge.baseInside) prepared.firstSample.certificate.value.name :=
  patch.retainedQueryEquivalent count 0 parent.edge.baseInside direct parent.edge.point_zero
    (start_inside patch count) prepared.firstSample

/-- Compare the independent original last Point with the SAME retained unit Query.

The original physical unit law and stored covering endpoint admission
identify the cached sample's exact point and neighborhood. No LocalRequest
or six-channel model query is substituted for either original input.
-/
def lastRetainedQueryEquivalent (prepared : PreparedParent patch count floor covered targets)
    (direct : PreparedEdge.Query parent.edge 1 (of_decide_eq_true rfl)) :
    NamedEquivalent (parent.edge.rootName 1 (of_decide_eq_true rfl)) prepared.lastSample.certificate.value.name :=
  patch.retainedQueryEquivalent count 1 (of_decide_eq_true rfl) direct parent.edge.point_one
    (finish_inside patch count covered) prepared.lastSample

section Samples

include covered in
/-- The original covering patch contains every admitted fraction of its SAME parent.

The patch supplies its original starting admission, while covered retains
the actual finishing admission. Affinity propagates those two bounds; no
Point, Query, root transport or numerical request is acquired.
-/
theorem sample_inside {fraction : Rational} (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    (patch.neighborhood count).box.Contains (parent.edge.point fraction) := by
  have first := patch.start_inside count
  have last := covered
  change (patch.neighborhood count).box.Contains (parent.edge.localSegment.pointAt 0) at first
  change (patch.neighborhood count).box.Contains (parent.edge.localSegment.pointAt 1) at last
  rewrite [parent.edge.localSegment.pointAt_zero] at first
  rewrite [parent.edge.localSegment.pointAt_one] at last
  exact parent.edge.localSegment.pointAt_contains_of_endpoints first last fraction inside

variable (prepared : PreparedParent patch count floor covered targets)

/-- Retain an original endpoint Point or acquire one genuine physical-patch interior Point.

Only equality of the parent parameter selects an endpoint branch. Zero
reuses the whole firstSample and one reuses the distinct lastSample,
transporting their point indices. Every other fraction acquires one new
Point on the same covering patch; coordinate coincidences do not deduplicate
occurrences, infer root agreement or upgrade an old observation's accuracy.
-/
def sampleAt (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) :
    ContinuedNeighborhood.Point (patch.neighborhood count) (parent.edge.point fraction) :=
  if atZero : fraction = 0 then
    ContinuedNeighborhood.Point.castPoint
      ((congrArg parent.edge.point atZero).trans parent.edge.point_zero) prepared.firstSample
  else if atOne : fraction = 1 then
    ContinuedNeighborhood.Point.castPoint
      ((congrArg parent.edge.point atOne).trans parent.edge.point_one) prepared.lastSample
  else
    ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (parent.edge.point fraction)
      (sample_inside (frame := frame) (basis := basis) (parent := parent) (covered := covered) inside)

/-- The zero branch retains the entire original first Point under its exact coordinate transport. -/
private theorem packaged_sampleAt_zero (inside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1) :
    prepared.sampleAt 0 inside =
      ContinuedNeighborhood.Point.castPoint parent.edge.point_zero prepared.firstSample := by
  unfold sampleAt
  rewrite [dif_pos rfl]
  rfl

/-- Sampling parameter zero reuses the SAME complete physical first Point. -/
theorem sampleAt_zero (inside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1) :
    prepared.sampleAt 0 inside =
      ContinuedNeighborhood.Point.castPoint parent.edge.point_zero prepared.firstSample :=
  packaged_sampleAt_zero prepared inside

/-- The unit branch retains the entire independent last Point under its exact coordinate transport. -/
private theorem packaged_sampleAt_one (inside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1) :
    prepared.sampleAt 1 inside =
      ContinuedNeighborhood.Point.castPoint parent.edge.point_one prepared.lastSample := by
  unfold sampleAt
  rewrite [dif_neg (by decide +kernel : (1 : Rational) ≠ 0), dif_pos rfl]
  rfl

/-- Sampling parameter one reuses the SAME complete physical last Point. -/
theorem sampleAt_one (inside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1) :
    prepared.sampleAt 1 inside =
      ContinuedNeighborhood.Point.castPoint parent.edge.point_one prepared.lastSample :=
  packaged_sampleAt_one prepared inside

/-- A strict parameter branch is the exact original new Point acquisition on its derived covering admission. -/
private theorem packaged_sampleAt_strict {fraction : Rational} (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (notZero : fraction ≠ 0) (notOne : fraction ≠ 1) :
    prepared.sampleAt fraction inside =
      ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (parent.edge.point fraction)
        (sample_inside (frame := frame) (basis := basis) (parent := parent) (covered := covered) inside) := by
  unfold sampleAt
  rewrite [dif_neg notZero, dif_neg notOne]
  rfl

/-- Every nonendpoint parameter executes the SAME one-time Point factory, without a new clearance premise. -/
theorem sampleAt_strict {fraction : Rational} (inside : 0 ≤ fraction ∧ fraction ≤ 1)
    (notZero : fraction ≠ 0) (notOne : fraction ≠ 1) :
    prepared.sampleAt fraction inside =
      ContinuedNeighborhood.Point.acquire (patch.neighborhood count) (parent.edge.point fraction)
        (sample_inside (frame := frame) (basis := basis) (parent := parent) (covered := covered) inside) :=
  packaged_sampleAt_strict prepared inside notZero notOne

end Samples

/-- Transport one SAME complete parameter Range along equality of its original source Cell index. -/
private def transportRange {first last : Cell (parameter := parameter) (liftedCell parent)}
    (equal : first = last) (range : Variation.Point.Range last.patch) : Variation.Point.Range first.patch := by
  cases equal
  exact range

/-- Source-Cell index transport preserves every field and cache of the original parameter Range heterogeneously. -/
private theorem transportRange_heq {first last : Cell (parameter := parameter) (liftedCell parent)}
    (equal : first = last) (range : Variation.Point.Range last.patch) : HEq (transportRange equal range) range := by
  cases equal
  rfl

/-- The original parameter bound is unchanged by the SAME exact source-Cell index transport. -/
private theorem transportRange_bound {first last : Cell (parameter := parameter) (liftedCell parent)}
    (equal : first = last) (range : Variation.Point.Range last.patch) :
    (transportRange equal range).bound = range.bound := by
  cases equal
  rfl

/-- An arbitrary retained spatial coordinate on these SAME physical endpoints reads the original parent fraction. -/
theorem coordinate_point_eq
    (coordinate : Spatial.Coordinate (startPoint parent).coordinate (finishPoint parent).coordinate)
    (input : Rational) : coordinate.point input = parent.edge.point input := by
  unfold Spatial.Coordinate.point
  rewrite [coordinate.displacement_eq]
  rfl

/-- The actual source Cell's shared coordinate reads the original affine parent at the SAME fraction. -/
theorem queryPoint_eq (prepared : PreparedParent patch count floor covered targets) (input : Rational) :
    prepared.preparation.cell.models.coordinate.point input = parent.edge.point input :=
  coordinate_point_eq prepared.preparation.cell.models.coordinate input

/-- Compare a source Cell's actual sample through its complete original Cell factory identity. -/
def sampleEquivalent {sourceCache : Cache (patch.neighborhood count)} {sourceFloor : Nat}
    {sourceTarget allowance : Rational} (request : Request sourceCache sourceFloor sourceTarget)
    (models : CellModels request (startPoint parent).coordinate (finishPoint parent).coordinate allowance)
    (cell : Cell (parameter := parameter) (liftedCell parent))
    (cell_eq : cell = Cell.ofModels request (liftedCell parent) models
      (start_inside patch count) (finish_inside patch count covered))
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (sample : ContinuedNeighborhood.Point cell.patch (cell.models.coordinate.point input))
    (direct : PreparedEdge.Query parent.edge input inside) :
    NamedEquivalent (parent.edge.rootName input inside) sample.certificate.value.name := by
  cases cell_eq
  have point_eq := (coordinate_point_eq models.coordinate input).symm
  exact patch.retainedQueryEquivalent count input inside direct point_eq
    (models.coordinate.point_inside (start_inside patch count) (finish_inside patch count covered)
      inside.1 inside.2) sample

/-- Derive signed agreement with an already retained actual source query sample at the SAME original parent fraction.

The complete original Cell equality identifies its patch and model indices.
The sample is an input with its actual owner and certificate. The existing
PreparedPatch comparison consumes the SAME retained direct Query to construct
the root relation; no desired agreement, new acquisition or Query execution
is supplied or performed here.
-/
def querySampleEquivalent (prepared : PreparedParent patch count floor covered targets)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (sample : ContinuedNeighborhood.Point prepared.preparation.cell.patch
      (prepared.preparation.cell.models.coordinate.point input))
    (direct : PreparedEdge.Query parent.edge input inside) :
    NamedEquivalent (parent.edge.rootName input inside) sample.certificate.value.name :=
  sampleEquivalent (covered := covered) prepared.preparation.attached.source prepared.preparation.models
    prepared.preparation.cell
    prepared.preparation.cell_eq input inside sample direct

/-- The SAME actual Cell's original seed box is the retained covering patch's seed box. -/
theorem querySeedBox_eq (prepared : PreparedParent patch count floor covered targets) :
    prepared.preparation.cell.patch.base.seed.owner.track.initial.box =
      (patch.neighborhood count).base.seed.owner.track.initial.box := by
  have same := congrArg
    (fun cell : Cell (parameter := parameter) (liftedCell parent) => cell.patch.base.seed.owner.track.initial.box)
    prepared.preparation.cell_eq
  exact same

/-- The actual query sample refines the original covering seed, preserving its independent original Cell/count owner. -/
theorem querySample_refines (prepared : PreparedParent patch count floor covered targets)
    (input : Rational) (sample : ContinuedNeighborhood.Point prepared.preparation.cell.patch
      (prepared.preparation.cell.models.coordinate.point input)) :
    sample.owner.track.initial.box.Refines (patch.neighborhood count).base.seed.owner.track.initial.box :=
  Eq.mp (congrArg (fun box => sample.owner.track.initial.box.Refines box) prepared.querySeedBox_eq) sample.refines

/-- View the SAME retained physical-patch Range at the actual raw source Query's original Cell/count index.

Only the existing whole Cell factory equality transports the original
Range. Its seed, movement ceiling, contour/coefficient bounds and finite
payment remain unchanged; the original neighborhood is not grown again.
-/
def queryRange (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count)) :
    Variation.Point.Range prepared.preparation.cell.patch := transportRange prepared.preparation.cell_eq range

/-- The actual query Range view preserves the whole original retained parameter-range cache heterogeneously. -/
theorem queryRange_heq (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count)) : HEq (prepared.queryRange range) range :=
  transportRange_heq prepared.preparation.cell_eq range

/-- The actual raw-query Range retains the SAME original common parameter-increment bound. -/
theorem queryRange_bound (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count)) : (prepared.queryRange range).bound = range.bound :=
  transportRange_bound prepared.preparation.cell_eq range

/-- Execute one original raw Query answer and advance that SAME point owner using its already retained physical range.

The existing Query.advance produces both original caches once. Its Range
view changes only the exact Cell/count index. All source models, requests,
observations and Targets remain the original raw-query data; callers with
an already retained Step consume that Step directly instead.
-/
def advanceQuery (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count))
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)
    (increment : Canonical) (paid : Data.Gaussian.Norm.Basic.normSq increment ≤ range.bound) :=
  prepared.preparation.query.advance frame (prepared.queryRange range) input lower upper increment
    (Eq.mp (congrArg (fun bound => Data.Gaussian.Norm.Basic.normSq increment ≤ bound)
      (prepared.queryRange_bound range).symm) paid)

/-- The new raw-query continuation retains its complete actual original six-channel answer without substitution. -/
theorem advanceQuery_observation (prepared : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count))
    (input : Rational) (lower : 0 ≤ input) (upper : input ≤ 1)
    (increment : Canonical) (paid : Data.Gaussian.Norm.Basic.normSq increment ≤ range.bound) :
    (prepared.advanceQuery range input lower upper increment paid).1 =
      prepared.preparation.query.observe frame input lower upper := by
  unfold advanceQuery
  exact prepared.preparation.query.advance_observation frame (prepared.queryRange range)
    input lower upper increment _

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent

end
