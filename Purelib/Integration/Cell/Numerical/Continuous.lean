module
public import Purelib.Integration.Cell.Numerical
public import Purelib.Approximation.Rational.Uniform.Numerical
public import Purelib.Integration.Partition.Uniform.Grid
public import Purelib.Data.Rat.Interval.Bisection
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Integration from finite numerical point requests

The modulus supplies the mesh and each actual point process receives its own
positive width request. Cell ranges inflate the cached point intervals by
the local variation; both costs enter the finite integral width bound.
-/

public section

namespace Purelib.Integration.NumericalFrontier.Continuous

open Purelib.Approximation
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order
open Purelib.Integration.Partition

/-- Inflate a cached numerical point interval by a nonnegative variation budget. -/
@[expose] def readingRange {source : Fraction.Rational → BoundProcess}
    (variation : Fraction.Rational) (nonnegative : 0 ≤ variation) (tag : NumericalPoint source) :
    Purelib.Data.Rat.Interval where
  lower := tag.reading.lower - variation
  upper := tag.reading.upper + variation
  valid := by
    have signed := Arithmetic.neg_le_self_of_nonnegative nonnegative
    have combined := Arithmetic.add_le_add_direct tag.reading.valid signed
    have first : tag.reading.lower + -variation = tag.reading.lower - variation := by ring1
    rw [first] at combined
    exact combined

/-- The actual range width is the point-reading width plus twice the variation. -/
theorem readingRange_width {source : Fraction.Rational → BoundProcess}
    (variation : Fraction.Rational) (nonnegative : 0 ≤ variation) (tag : NumericalPoint source) :
    (readingRange variation nonnegative tag).width = tag.reading.width + (variation + variation) := by
  change (tag.reading.upper + variation) - (tag.reading.lower - variation) =
    (tag.reading.upper - tag.reading.lower) + (variation + variation)
  ring1

set_option genInjectivity false in
/-- A numerical integration request with its actual point and variation budgets and computed mesh.

The original point-process family and modulus remain the indexed owners.
The point-width request, local variation, mesh and normalized partition all
retain their exact computations from the original positive request. -/
structure Preparation {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source) where
  /-- The original positive integration request. -/ request : AccuracyRequest
  /-- The retained positive point-width request. -/ pointRequest : AccuracyRequest
  /-- The point-width request uses one quarter of the original tolerance. -/ pointRequest_eq :
    pointRequest.tolerance = request.tolerance / 4
  /-- The retained local source-variation budget. -/ variation : Fraction.Rational
  /-- The variation budget uses one quarter of the original tolerance. -/ variation_eq :
    variation = request.tolerance / 4
  /-- The computed positive mesh bound. -/ mesh : Fraction.Rational
  /-- The mesh is the original modulus response to the retained variation. -/ mesh_eq : mesh = modulus.radius variation
  /-- The exact normalized grid selected from the computed mesh. -/ partition : Unit.Normalized
  /-- The partition is the original finite grid construction. -/ partition_eq : partition = Uniform.Grid.forWidth mesh

constructive_injectivity Preparation

namespace Preparation

/-- Compute both quarter budgets, the original modulus response and the actual finite grid. -/
@[expose] def prepare {source : Fraction.Rational → BoundProcess}
    (modulus : Rational.Uniform.Numerical source) (request : AccuracyRequest) : Preparation modulus :=
  let quarter := request.tolerance / 4
  let pointRequest : AccuracyRequest := ⟨quarter, Bounds.Quarter.quarter_pos request.positive⟩
  let mesh := modulus.radius quarter
  { request := request
    pointRequest := pointRequest
    pointRequest_eq := rfl
    variation := quarter
    variation_eq := rfl
    mesh := mesh
    mesh_eq := rfl
    partition := Uniform.Grid.forWidth mesh
    partition_eq := rfl }

/-- The retained local source-variation budget is strictly positive. -/
theorem variationPositive {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus) : 0 < prepared.variation := by
  rw [prepared.variation_eq]
  exact Bounds.Quarter.quarter_pos prepared.request.positive

/-- The original modulus produces a positive computed mesh. -/
theorem meshPositive {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus) : 0 < prepared.mesh := by
  rw [prepared.mesh_eq]
  exact modulus.radius_pos prepared.variation prepared.variationPositive

/-- Every actual retained grid interval is shorter than the original computed mesh. -/
theorem intervalSmall {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals) :
    interval.signedLength < prepared.mesh := by
  have intervals := congrArg Unit.Normalized.intervals prepared.partition_eq
  have actual : interval ∈ (Uniform.Grid.forWidth prepared.mesh).intervals := intervals ▸ member
  exact Uniform.Grid.forWidth_interval_lt prepared.meshPositive interval actual

/-- The range from a selected start reading overlaps every finite state at each cell point. -/
theorem rangeOverlapSelected {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals)
    (selected : NumericalPoint.StartObservation source interval prepared.pointRequest)
    (point : Fraction.Rational) (lower : interval.start ≤ point) (upper : point ≤ interval.finish)
    (state : (source point).State) :
    (readingRange prepared.variation prepared.variationPositive.le selected.val).Overlaps
      ((source point).bound state) := by
  have valid := prepared.partition.valid interval member
  have difference : point - interval.start ≤ interval.signedLength :=
    Arithmetic.sub_le_sub_direct upper le_rfl
  have small : point - interval.start < modulus.radius prepared.variation := by
    have bound := prepared.intervalSmall interval member
    rw [prepared.mesh_eq] at bound
    exact difference.trans_lt bound
  let tag := selected.val
  let tagState : (source interval.start).State := selected.property.2.1 ▸ tag.state
  have reading_eq : tag.reading = (source interval.start).bound tagState :=
    NumericalPoint.transport_reading selected.property.2.1 tag.state tag.reading tag.reading_eq
  have variation := modulus.variation prepared.variation prepared.variationPositive interval.start point
    valid.1 lower (upper.trans valid.2.2) small tagState state
  change tag.reading.lower - prepared.variation ≤ ((source point).bound state).upper ∧
    ((source point).bound state).lower ≤ tag.reading.upper + prepared.variation
  rw [reading_eq]
  exact variation

/-- The range from the original fresh start reading overlaps every finite state at each cell point. -/
theorem rangeOverlap {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals)
    (point : Fraction.Rational) (lower : interval.start ≤ point) (upper : point ≤ interval.finish)
    (state : (source point).State) :
    (readingRange prepared.variation prepared.variationPositive.le
      (NumericalPoint.atStart source interval (prepared.partition.valid interval member)
        prepared.pointRequest)).Overlaps ((source point).bound state) :=
  prepared.rangeOverlapSelected interval member
    (NumericalFrontier.freshStart source prepared.partition prepared.pointRequest ⟨interval, member⟩)
    point lower upper state

/-- Select interval-start observations from the original saved numerical point bank. -/
@[expose] def cachedStart {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) (entry : {interval // interval ∈ prepared.partition.intervals}) :
    NumericalPoint.StartObservation source entry.val prepared.pointRequest :=
  NumericalPoint.atStartCached source cached entry.val (prepared.partition.valid entry.val entry.property)
    prepared.pointRequest

/-- Build the numerical frontier using the exact retained point observations selected for this mesh. -/
@[expose] def frontierCached {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) : NumericalFrontier source :=
  NumericalFrontier.ofSelectedRanges source prepared.partition prepared.pointRequest
    (readingRange prepared.variation prepared.variationPositive.le) (prepared.cachedStart cached)
    (fun interval member point lower upper state =>
      prepared.rangeOverlapSelected interval member (prepared.cachedStart cached ⟨interval, member⟩)
        point lower upper state)

/-- Request the actual point processes and construct the numerical frontier on the computed grid. -/
@[expose] def frontier {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus) : NumericalFrontier source :=
  NumericalFrontier.ofRanges source prepared.partition prepared.pointRequest
    (readingRange prepared.variation prepared.variationPositive.le) prepared.rangeOverlap

/-- The selected point widths and variation budget pay for their actual integral enclosure. -/
theorem selected_width_lt {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (selected : (entry : {interval // interval ∈ prepared.partition.intervals}) →
      NumericalPoint.StartObservation source entry.val prepared.pointRequest)
    (overlap : ∀ (interval : Partition.Interval) (member : interval ∈ prepared.partition.intervals)
      (point : Fraction.Rational), interval.start ≤ point → point ≤ interval.finish →
      ∀ state : (source point).State,
        (readingRange prepared.variation prepared.variationPositive.le (selected ⟨interval, member⟩).val).Overlaps
          ((source point).bound state)) :
    (integralBound (NumericalFrontier.ofSelectedRanges source prepared.partition prepared.pointRequest
      (readingRange prepared.variation prepared.variationPositive.le) selected overlap).cells).width <
        prepared.request.tolerance := by
  let frontier := NumericalFrontier.ofSelectedRanges source prepared.partition prepared.pointRequest
    (readingRange prepared.variation prepared.variationPositive.le) selected overlap
  let uniform := prepared.pointRequest.tolerance + (prepared.variation + prepared.variation)
  have uniformNonnegative : 0 ≤ uniform := by
    have twice := Arithmetic.add_le_add_direct prepared.variationPositive.le prepared.variationPositive.le
    change (0 : Fraction.Rational) ≤ prepared.variation + prepared.variation at twice
    have both := Arithmetic.add_le_add_direct prepared.pointRequest.positive.le twice
    change (0 : Fraction.Rational) ≤ uniform at both
    exact both
  have each : ∀ cell ∈ frontier.cells, cell.oscillation ≤ uniform := by
    intro cell member
    have width := NumericalFrontier.ofSelectedRanges_oscillation source prepared.partition prepared.pointRequest
      (readingRange prepared.variation prepared.variationPositive.le) selected overlap cell member
    rw [readingRange_width] at width
    rw [width]
    have reading := (NumericalFrontier.ofSelectedRanges_reading_width_lt source prepared.partition
      prepared.pointRequest (readingRange prepared.variation prepared.variationPositive.le)
      selected overlap cell member).le
    exact Arithmetic.add_le_add_direct reading (Fraction.Order.Basic.le_refl _)
  have budget : integrationWeight frontier.cells * uniform < prepared.request.tolerance := by
    rw [frontier.totalWeight, Fraction.Field.one_mul]
    dsimp [uniform]
    rw [prepared.pointRequest_eq, prepared.variation_eq, Bounds.Quarter.two_quarters]
    have paid := Bounds.Quarter.half_add_quarter_lt prepared.request.positive
    have commute : prepared.request.tolerance / 4 + prepared.request.tolerance / 2 =
        prepared.request.tolerance / 2 + prepared.request.tolerance / 4 := by ring1
    rw [commute]
    exact paid
  exact integralBound_width_lt_of_uniform uniformNonnegative each budget

/-- The original fresh frontier's point-width and variation budgets pay for its integral enclosure. -/
theorem frontier_width_lt {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus) :
    (integralBound prepared.frontier.cells).width < prepared.request.tolerance :=
  prepared.selected_width_lt (NumericalFrontier.freshStart source prepared.partition prepared.pointRequest)
    prepared.rangeOverlap

/-- The retained-point frontier also meets the original integral width request. -/
theorem frontierCached_width_lt {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (prepared : Preparation modulus)
    (cached : List (NumericalPoint source)) :
    (integralBound (prepared.frontierCached cached).cells).width < prepared.request.tolerance :=
  prepared.selected_width_lt (prepared.cachedStart cached)
    (fun interval member point lower upper state =>
      prepared.rangeOverlapSelected interval member (prepared.cachedStart cached ⟨interval, member⟩)
        point lower upper state)

end Preparation

set_option genInjectivity false in
/-- An actual finite numerical integration request and its cached point enclosures.

The original preparation and numerical frontier are retained together. The
frontier is exactly the computed result, and its integral enclosure meets the
original positive width request. -/
structure Result {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source) where
  /-- The original request and its computed point and variation budgets. -/ preparation : Preparation modulus
  /-- The actual frontier retaining every point-process state and reading. -/ frontier : NumericalFrontier source
  /-- The frontier is the exact output of the retained preparation. -/ frontier_eq : frontier = preparation.frontier
  /-- The integral enclosure meets the retained original request. -/ accurate :
    (integralBound frontier.cells).width < preparation.request.tolerance

constructive_injectivity Result

set_option genInjectivity false in
/-- A numerical request constructed from an actual retained bank of point observations.

The preparation, original bank and resulting numerical frontier remain
available together. The frontier is the one actually built from that bank,
and its integral enclosure meets the retained request. -/
structure CachedResult {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source) where
  /-- The original request and its computed point and variation budgets. -/ preparation : Preparation modulus
  /-- The original saved observations supplied to the construction. -/ cached : List (NumericalPoint source)
  /-- The actual frontier retaining its selected point states and readings. -/ frontier : NumericalFrontier source
  /-- The frontier is the exact construction from the retained preparation and bank. -/ frontier_eq :
    frontier = preparation.frontierCached cached
  /-- The actual integral enclosure meets the original positive request. -/ accurate :
    (integralBound frontier.cells).width < preparation.request.tolerance

constructive_injectivity CachedResult

namespace CachedResult

/-- Cached results with the same preparation, point bank and frontier are equal. -/
theorem ext {source : Fraction.Rational → BoundProcess} {modulus : Rational.Uniform.Numerical source}
    (left right : CachedResult modulus) (preparation_eq : left.preparation = right.preparation)
    (cached_eq : left.cached = right.cached) (frontier_eq : left.frontier = right.frontier) : left = right := by
  cases left with
  | mk leftPreparation leftCached leftFrontier leftEqual leftAccurate =>
    cases right with
    | mk rightPreparation rightCached rightFrontier rightEqual rightAccurate =>
      cases preparation_eq
      cases cached_eq
      cases frontier_eq
      rfl

/-- Construct a numerical request from the supplied saved point observations. -/
@[expose] def build {source : Fraction.Rational → BoundProcess} (modulus : Rational.Uniform.Numerical source)
    (cached : List (NumericalPoint source)) (request : AccuracyRequest) : CachedResult modulus :=
  let preparation := Preparation.prepare modulus request
  { preparation := preparation
    cached := cached
    frontier := preparation.frontierCached cached
    frontier_eq := rfl
    accurate := preparation.frontierCached_width_lt cached }

end CachedResult

namespace Result

/-- Select the midpoint of the retained numerical-source integral enclosure. -/
@[expose] def answer {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (result : Result modulus) : Fraction.Rational :=
  (integralBound result.frontier.cells).midpoint

/-- The selected answer lies in the original numerical-source integral enclosure. -/
theorem answer_contains {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (result : Result modulus) :
    (integralBound result.frontier.cells).Contains result.answer :=
  (integralBound result.frontier.cells).midpoint_contains

/-- Every admitted rational enclosure reading is within half the retained width of the answer. -/
theorem answer_error {source : Fraction.Rational → BoundProcess}
    {modulus : Rational.Uniform.Numerical source} (result : Result modulus) (reading : Fraction.Rational)
    (inside : (integralBound result.frontier.cells).Contains reading) :
    Fraction.abs (reading - result.answer) ≤ (integralBound result.frontier.cells).width * (1 / 2) :=
  Interval.abs_sub_midpoint_le inside

end Result

/-- Compute the finite numerical point requests and their certified integration enclosure. -/
@[expose] def build {source : Fraction.Rational → BoundProcess}
    (modulus : Rational.Uniform.Numerical source) (request : AccuracyRequest) : Result modulus :=
  let preparation := Preparation.prepare modulus request
  let frontier := preparation.frontier
  { preparation := preparation
    frontier := frontier
    frontier_eq := rfl
    accurate := preparation.frontier_width_lt }

end Purelib.Integration.NumericalFrontier.Continuous

end
