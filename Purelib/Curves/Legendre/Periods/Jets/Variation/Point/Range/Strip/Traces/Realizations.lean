module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Corners
import Purelib.Riemann.Paths.OwnerTracePath.Between
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic.Links
import Purelib.Riemann.RootContinuation.SquareRootProvenance.Trace
import Purelib.Riemann.Paths.OwnerTracePath.Pullback
import Purelib.Data.List.DependentProduct
import Purelib.Data.Gaussian.Cast
import Purelib.Polynomial.Dense.Gaussian.Basic

import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Vertices
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Edges
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.FixedRootBoxBudget
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Joint
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Spatial
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Links
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic.Advance
import Purelib.Riemann.Paths.OwnerTraceReadings.Trace

/-! # Realizing actual strip edges on shared incoming corner readings

The GIVEN native corner readings enter the temporal/spatial polynomials by
exact whole-Owner parameter transport. The retained endpoint-floor tables
and materialized incidence maxima pay their original link requirements.
Only actual interior readings are then acquired. The original stationary
moved-to-cached handoffs remain in every realized path.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices.Edges.Links.Requirements

namespace Readings

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.RootContinuation.SquareRootProvenance (traceAllowance)
open Purelib.Riemann.Paths.OwnerTracePath

attribute [local irreducible] timePolynomial spacePolynomial Time.Links.whole Space.Links.whole
attribute [local irreducible] Links Requirements Demands Targets Readings
open OwnerPath.Dyadic (AdvanceLinks)

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    {range : Range patch} {budget : FixedRootBoxBudget.Budget patch.base.seed.owner}
    {factory : budget = range.seedBudget}
    {ambient : Box} {start finish : Canonical}
    {segment : ClearSegment (Paths.polynomial parameter) ambient start finish}
    {firstInside : patch.box.Contains start} {lastInside : patch.box.Contains finish}
    {increment : Canonical} {admitted : Norm.Basic.normSq increment ≤ range.stripBound}
    {firstPath lastPath : PathData budget budget}
    {firstDepth lastDepth : Nat} {left right : Endpoint}
    {grid : JointGrid (range := range) (budget := budget) increment firstPath lastPath
      firstDepth lastDepth left right}
    {cached : Vertices range budget factory segment firstInside lastInside increment admitted firstPath lastPath grid}
    {ordered : left.parameter ≤ right.parameter} {zeroInside : Inside 0} {oneInside : Inside 1}
    {firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside}
    {lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside}
    {retained : Edges cached ordered zeroInside oneInside firstFactory lastFactory}
    {linked : Links retained} {required : Requirements linked} {demanded : Demands required}
    {targeted : Targets required demanded} (observed : Readings required demanded targeted)

/-- View the SAME shared coarse source reading in the actual temporal polynomial's exact endpoint Owner. -/
@[expose] def timeFirst (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    OwnerReading (OwnerPath.Dyadic.sourceOwner (source := retained.original.owner timeIndex.castSucc spaceIndex)
      (firstEq := Time.first_eq retained.original timeIndex spaceIndex)) :=
  (Readings.sample (observed := observed) timeIndex.castSucc spaceIndex).castParameter
    (Time.first_eq retained.original timeIndex spaceIndex)

/-- View the SAME shared coarse target reading in the actual temporal polynomial's exact endpoint Owner. -/
@[expose] def timeLast (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    OwnerReading (OwnerPath.Dyadic.targetOwner (target := retained.original.owner timeIndex.succ spaceIndex)
      (lastEq := Time.last_eq retained.original timeIndex spaceIndex)) :=
  (Readings.sample (observed := observed) timeIndex.succ spaceIndex).castParameter
    (Time.last_eq retained.original timeIndex spaceIndex)

/-- View the SAME shared coarse source reading in the actual spatial polynomial's exact endpoint Owner. -/
@[expose] def spaceFirst (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    OwnerReading (OwnerPath.Dyadic.sourceOwner (source := retained.original.owner timeIndex spaceIndex.castSucc)
      (firstEq := Space.first_eq retained.original timeIndex spaceIndex)) :=
  (Readings.sample (observed := observed) timeIndex spaceIndex.castSucc).castParameter
    (Space.first_eq retained.original timeIndex spaceIndex)

/-- View the SAME shared coarse target reading in the actual spatial polynomial's exact endpoint Owner. -/
@[expose] def spaceLast (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    OwnerReading (OwnerPath.Dyadic.targetOwner (target := retained.original.owner timeIndex spaceIndex.succ)
      (lastEq := Space.last_eq retained.original timeIndex spaceIndex)) :=
  (Readings.sample (observed := observed) timeIndex spaceIndex.succ).castParameter
    (Space.last_eq retained.original timeIndex spaceIndex)

/-- The actual temporal source link floor is paid by its SAME supplied global-corner reading. -/
theorem time_first_later (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (Time.Links.whole (linked := Links.time (linked := linked) timeIndex spaceIndex)).sourceMinimum ≤
      (observed.timeFirst timeIndex spaceIndex).index := by
  have original := OwnerPath.ReadingFloors.source_eq
    (path := Time.Links.whole
      (linked := Links.time (linked := linked) timeIndex spaceIndex))
    (floors := Requirements.time (linked := linked) (required := required) timeIndex spaceIndex)
  have paid := Requirements.time_source_le (linked := linked) (required := required) timeIndex spaceIndex
  have stored := Demands.floor_eq (linked := linked) (required := required) (demanded := demanded)
    timeIndex.castSucc spaceIndex
  have sampled := Readings.floor_le (linked := linked) (required := required) (demanded := demanded)
    (targeted := targeted) (observed := observed) timeIndex.castSucc spaceIndex
  have sameIndex := OwnerReading.castParameter_index (Time.first_eq retained.original timeIndex spaceIndex)
    (Readings.sample (observed := observed) timeIndex.castSucc spaceIndex)
  exact ((original.symm.trans_le paid).trans (stored.symm.trans_le sampled)).trans_eq sameIndex.symm

/-- The actual temporal target link floor is paid by its SAME supplied global-corner reading. -/
theorem time_last_later (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (Time.Links.whole (linked := Links.time (linked := linked) timeIndex spaceIndex)).targetMinimum ≤
      (observed.timeLast timeIndex spaceIndex).index := by
  have original := OwnerPath.ReadingFloors.target_eq
    (path := Time.Links.whole
      (linked := Links.time (linked := linked) timeIndex spaceIndex))
    (floors := Requirements.time (linked := linked) (required := required) timeIndex spaceIndex)
  have paid := Requirements.time_target_le (linked := linked) (required := required) timeIndex spaceIndex
  have stored := Demands.floor_eq (linked := linked) (required := required) (demanded := demanded)
    timeIndex.succ spaceIndex
  have sampled := Readings.floor_le (linked := linked) (required := required) (demanded := demanded)
    (targeted := targeted) (observed := observed) timeIndex.succ spaceIndex
  have sameIndex := OwnerReading.castParameter_index (Time.last_eq retained.original timeIndex spaceIndex)
    (Readings.sample (observed := observed) timeIndex.succ spaceIndex)
  exact ((original.symm.trans_le paid).trans (stored.symm.trans_le sampled)).trans_eq sameIndex.symm

/-- The actual spatial source link floor is paid by its SAME supplied global-corner reading. -/
theorem space_first_later (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (Space.Links.whole (linked := Links.space (linked := linked) timeIndex spaceIndex)).sourceMinimum ≤
      (observed.spaceFirst timeIndex spaceIndex).index := by
  have original := OwnerPath.ReadingFloors.source_eq
    (path := Space.Links.whole
      (linked := Links.space (linked := linked) timeIndex spaceIndex))
    (floors := Requirements.space (linked := linked) (required := required) timeIndex spaceIndex)
  have paid := Requirements.space_source_le (linked := linked) (required := required) timeIndex spaceIndex
  have stored := Demands.floor_eq (linked := linked) (required := required) (demanded := demanded)
    timeIndex spaceIndex.castSucc
  have sampled := Readings.floor_le (linked := linked) (required := required) (demanded := demanded)
    (targeted := targeted) (observed := observed) timeIndex spaceIndex.castSucc
  have sameIndex := OwnerReading.castParameter_index (Space.first_eq retained.original timeIndex spaceIndex)
    (Readings.sample (observed := observed) timeIndex spaceIndex.castSucc)
  exact ((original.symm.trans_le paid).trans (stored.symm.trans_le sampled)).trans_eq sameIndex.symm

/-- The actual spatial target link floor is paid by its SAME supplied global-corner reading. -/
theorem space_last_later (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (Space.Links.whole (linked := Links.space (linked := linked) timeIndex spaceIndex)).targetMinimum ≤
      (observed.spaceLast timeIndex spaceIndex).index := by
  have original := OwnerPath.ReadingFloors.target_eq
    (path := Space.Links.whole
      (linked := Links.space (linked := linked) timeIndex spaceIndex))
    (floors := Requirements.space (linked := linked) (required := required) timeIndex spaceIndex)
  have paid := Requirements.space_target_le (linked := linked) (required := required) timeIndex spaceIndex
  have stored := Demands.floor_eq (linked := linked) (required := required) (demanded := demanded)
    timeIndex spaceIndex.succ
  have sampled := Readings.floor_le (linked := linked) (required := required) (demanded := demanded)
    (targeted := targeted) (observed := observed) timeIndex spaceIndex.succ
  have sameIndex := OwnerReading.castParameter_index (Space.last_eq retained.original timeIndex spaceIndex)
    (Readings.sample (observed := observed) timeIndex spaceIndex.succ)
  exact ((original.symm.trans_le paid).trans (stored.symm.trans_le sampled)).trans_eq sameIndex.symm

/-- The SAME time first reading pays its original retained strict trace-request floor before observation. -/
theorem time_first_trace_later (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (AdvanceLinks.firstRequest
        (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
      (observed.timeFirst timeIndex spaceIndex).index := by
  have paid := Requirements.time_first_trace_le (linked := linked) (required := required) timeIndex spaceIndex
  have stored := Demands.floor_eq (linked := linked) (required := required) (demanded := demanded)
    timeIndex.castSucc spaceIndex
  have sampled := Readings.floor_le (linked := linked) (required := required) (demanded := demanded)
    (targeted := targeted) (observed := observed) timeIndex.castSucc spaceIndex
  have sameIndex := OwnerReading.castParameter_index (Time.first_eq retained.original timeIndex spaceIndex)
    (Readings.sample (observed := observed) timeIndex.castSucc spaceIndex)
  exact (paid.trans (stored.symm.trans_le sampled)).trans_eq sameIndex.symm

/-- The actual time first reading satisfies its SAME cached request's strict trace residual. -/
theorem time_first_trace_residual (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    Norm.Basic.normSq
      ((observed.timeFirst timeIndex spaceIndex).value *
          (observed.timeFirst timeIndex spaceIndex).value -
        OwnerPath.Dyadic.value (timePolynomial retained.original timeIndex spaceIndex) OwnerPath.Dyadic.first) <
      traceAllowance patch.rootLower :=
  AdvanceLinks.first_residual
    (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)
    (observed.timeFirst timeIndex spaceIndex)
    (Readings.time_first_trace_later (observed := observed) timeIndex spaceIndex)

/-- The SAME time target reading pays its original retained strict trace-request floor before observation. -/
theorem time_target_trace_later (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (AdvanceLinks.targetRequest
        (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
      (observed.timeLast timeIndex spaceIndex).index := by
  have paid := Requirements.time_target_trace_le (linked := linked) (required := required) timeIndex spaceIndex
  have stored := Demands.floor_eq (linked := linked) (required := required) (demanded := demanded)
    timeIndex.succ spaceIndex
  have sampled := Readings.floor_le (linked := linked) (required := required) (demanded := demanded)
    (targeted := targeted) (observed := observed) timeIndex.succ spaceIndex
  have sameIndex := OwnerReading.castParameter_index (Time.last_eq retained.original timeIndex spaceIndex)
    (Readings.sample (observed := observed) timeIndex.succ spaceIndex)
  exact (paid.trans (stored.symm.trans_le sampled)).trans_eq sameIndex.symm

/-- The actual time target reading satisfies its SAME cached request's strict trace residual. -/
theorem time_target_trace_residual (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    Norm.Basic.normSq
      ((observed.timeLast timeIndex spaceIndex).value *
          (observed.timeLast timeIndex spaceIndex).value -
        OwnerPath.Dyadic.value (timePolynomial retained.original timeIndex spaceIndex) OwnerPath.Dyadic.last) <
      traceAllowance patch.rootLower :=
  AdvanceLinks.target_residual
    (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)
    (observed.timeLast timeIndex spaceIndex)
    (Readings.time_target_trace_later (observed := observed) timeIndex spaceIndex)

/-- The SAME space first reading pays its original retained strict trace-request floor before observation. -/
theorem space_first_trace_later (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (AdvanceLinks.firstRequest
        (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
      (observed.spaceFirst timeIndex spaceIndex).index := by
  have paid := Requirements.space_first_trace_le (linked := linked) (required := required) timeIndex spaceIndex
  have stored := Demands.floor_eq (linked := linked) (required := required) (demanded := demanded)
    timeIndex spaceIndex.castSucc
  have sampled := Readings.floor_le (linked := linked) (required := required) (demanded := demanded)
    (targeted := targeted) (observed := observed) timeIndex spaceIndex.castSucc
  have sameIndex := OwnerReading.castParameter_index (Space.first_eq retained.original timeIndex spaceIndex)
    (Readings.sample (observed := observed) timeIndex spaceIndex.castSucc)
  exact (paid.trans (stored.symm.trans_le sampled)).trans_eq sameIndex.symm

/-- The actual space first reading satisfies its SAME cached request's strict trace residual. -/
theorem space_first_trace_residual (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    Norm.Basic.normSq
      ((observed.spaceFirst timeIndex spaceIndex).value *
          (observed.spaceFirst timeIndex spaceIndex).value -
        OwnerPath.Dyadic.value (spacePolynomial retained.original timeIndex spaceIndex) OwnerPath.Dyadic.first) <
      traceAllowance patch.rootLower :=
  AdvanceLinks.first_residual
    (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)
    (observed.spaceFirst timeIndex spaceIndex)
    (Readings.space_first_trace_later (observed := observed) timeIndex spaceIndex)

/-- The SAME space target reading pays its original retained strict trace-request floor before observation. -/
theorem space_target_trace_later (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (AdvanceLinks.targetRequest
        (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
      (observed.spaceLast timeIndex spaceIndex).index := by
  have paid := Requirements.space_target_trace_le (linked := linked) (required := required) timeIndex spaceIndex
  have stored := Demands.floor_eq (linked := linked) (required := required) (demanded := demanded)
    timeIndex spaceIndex.succ
  have sampled := Readings.floor_le (linked := linked) (required := required) (demanded := demanded)
    (targeted := targeted) (observed := observed) timeIndex spaceIndex.succ
  have sameIndex := OwnerReading.castParameter_index (Space.last_eq retained.original timeIndex spaceIndex)
    (Readings.sample (observed := observed) timeIndex spaceIndex.succ)
  exact (paid.trans (stored.symm.trans_le sampled)).trans_eq sameIndex.symm

/-- The actual space target reading satisfies its SAME cached request's strict trace residual. -/
theorem space_target_trace_residual (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    Norm.Basic.normSq
      ((observed.spaceLast timeIndex spaceIndex).value *
          (observed.spaceLast timeIndex spaceIndex).value -
        OwnerPath.Dyadic.value (spacePolynomial retained.original timeIndex spaceIndex) OwnerPath.Dyadic.last) <
      traceAllowance patch.rootLower :=
  AdvanceLinks.target_residual
    (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)
    (observed.spaceLast timeIndex spaceIndex)
    (Readings.space_target_trace_later (observed := observed) timeIndex spaceIndex)

/-- The original temporal realization on GIVEN shared endpoint readings retains its whole constructor factory. -/
@[expose] def TimeResult (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :=
  { result : OwnerPath.Between (Time.Links.whole (linked := Links.time (linked := linked) timeIndex spaceIndex))
      (observed.timeFirst timeIndex spaceIndex) (observed.timeLast timeIndex spaceIndex) //
    result = OwnerPath.between (polynomial := timePolynomial retained.original timeIndex spaceIndex)
      (Time.Links.whole (linked := Links.time (linked := linked) timeIndex spaceIndex))
      (Time.Links.nonempty (linked := Links.time (linked := linked) timeIndex spaceIndex))
      (observed.timeFirst timeIndex spaceIndex) (observed.timeLast timeIndex spaceIndex)
      (observed.time_first_later timeIndex spaceIndex) (observed.time_last_later timeIndex spaceIndex) }

/-- The original spatial realization on GIVEN shared endpoint readings retains its whole constructor factory. -/
@[expose] def SpaceResult (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :=
  { result : OwnerPath.Between (Space.Links.whole (linked := Links.space (linked := linked) timeIndex spaceIndex))
      (observed.spaceFirst timeIndex spaceIndex) (observed.spaceLast timeIndex spaceIndex) //
    result = OwnerPath.between (polynomial := spacePolynomial retained.original timeIndex spaceIndex)
      (Space.Links.whole (linked := Links.space (linked := linked) timeIndex spaceIndex))
      (Space.Links.nonempty (linked := Links.space (linked := linked) timeIndex spaceIndex))
      (observed.spaceFirst timeIndex spaceIndex) (observed.spaceLast timeIndex spaceIndex)
      (observed.space_first_later timeIndex spaceIndex) (observed.space_last_later timeIndex spaceIndex) }

/-- Realize the SAME temporal path with its two complete incoming corner readings and only interior observations. -/
def time (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    TimeResult (linked := linked) (required := required) (demanded := demanded)
      (targeted := targeted) observed timeIndex spaceIndex :=
  ⟨OwnerPath.between (polynomial := timePolynomial retained.original timeIndex spaceIndex)
      (Time.Links.whole (linked := Links.time (linked := linked) timeIndex spaceIndex))
      (Time.Links.nonempty (linked := Links.time (linked := linked) timeIndex spaceIndex))
      (observed.timeFirst timeIndex spaceIndex) (observed.timeLast timeIndex spaceIndex)
      (observed.time_first_later timeIndex spaceIndex) (observed.time_last_later timeIndex spaceIndex), rfl⟩

/-- Realize the SAME spatial path with its two complete incoming corner readings and only interior observations. -/
def space (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    SpaceResult (linked := linked) (required := required) (demanded := demanded)
      (targeted := targeted) observed timeIndex spaceIndex :=
  ⟨OwnerPath.between (polynomial := spacePolynomial retained.original timeIndex spaceIndex)
      (Space.Links.whole (linked := Links.space (linked := linked) timeIndex spaceIndex))
      (Space.Links.nonempty (linked := Links.space (linked := linked) timeIndex spaceIndex))
      (observed.spaceFirst timeIndex spaceIndex) (observed.spaceLast timeIndex spaceIndex)
      (observed.space_first_later timeIndex spaceIndex) (observed.space_last_later timeIndex spaceIndex), rfl⟩

/-- One genuine supplied-endpoint temporal realization per SAME retained unique edge occurrence. -/
@[expose] def TimeResults := DependentProduct retained.original.times (fun timeIndex =>
  DependentProduct (left :: retained.original.spaces) (fun spaceIndex =>
    TimeResult (linked := linked) (required := required) (demanded := demanded)
      (targeted := targeted) observed timeIndex spaceIndex))

/-- One genuine supplied-endpoint spatial realization per SAME retained unique edge occurrence. -/
@[expose] def SpaceResults := DependentProduct (left :: retained.original.times) (fun timeIndex =>
  DependentProduct retained.original.spaces (fun spaceIndex =>
    SpaceResult (linked := linked) (required := required) (demanded := demanded)
      (targeted := targeted) observed timeIndex spaceIndex))

/-- Bind each temporal supplied-endpoint realization once, consuming the SAME global corner table. -/
def timeResults : TimeResults observed :=
  DependentProduct.ofFn retained.original.times (fun timeIndex =>
    DependentProduct.ofFn (left :: retained.original.spaces) (fun spaceIndex =>
      time (linked := linked) (required := required) (demanded := demanded)
        (targeted := targeted) (observed := observed) timeIndex spaceIndex))

/-- Bind each spatial supplied-endpoint realization once, consuming the SAME global corner table. -/
def spaceResults : SpaceResults observed :=
  DependentProduct.ofFn (left :: retained.original.times) (fun timeIndex =>
    DependentProduct.ofFn retained.original.spaces (fun spaceIndex =>
      space (linked := linked) (required := required) (demanded := demanded)
        (targeted := targeted) (observed := observed) timeIndex spaceIndex))

/-- Both original realization tables on the SAME incoming corner readings, with complete one-pass factories. -/
@[expose] def Realizations :=
  (_observed : { value : Readings required demanded targeted // value = observed }) ×
  (_times : { value : TimeResults observed // value = timeResults observed }) ×
    { spaces : SpaceResults observed // spaces = spaceResults observed }

/-- Realize both unique edge tables once after the GIVEN entire corner reading table has been bound. -/
def realize : Realizations observed :=
  let times := timeResults observed
  let spaces := spaceResults observed
  ⟨⟨observed, rfl⟩, ⟨times, rfl⟩, ⟨spaces, rfl⟩⟩

namespace Realizations

variable {observed} (realized : Realizations observed)

/-- Read the SAME complete temporal supplied-endpoint realization cache at its original bounded occurrence. -/
@[expose] def time (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    TimeResult (linked := linked) (required := required) (demanded := demanded)
      (targeted := targeted) observed timeIndex spaceIndex :=
  DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get retained.original.times realized.2.1.val timeIndex) spaceIndex

/-- Read the SAME complete spatial supplied-endpoint realization cache at its original bounded occurrence. -/
@[expose] def space (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    SpaceResult (linked := linked) (required := required) (demanded := demanded)
      (targeted := targeted) observed timeIndex spaceIndex :=
  DependentProduct.get retained.original.spaces
    (DependentProduct.get (left :: retained.original.times) realized.2.2.val timeIndex) spaceIndex

/-- The temporal starting reading is the SAME incoming whole coarse-corner reading after exact parameter transport. -/
theorem time_first_heq (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    HEq (realized.time timeIndex spaceIndex).val.realization.first
      (Readings.sample (observed := observed) timeIndex.castSucc spaceIndex) :=
  (heq_of_eq (OwnerPath.Between.first_eq (cached := (realized.time timeIndex spaceIndex).val))).trans
    (OwnerReading.castParameter_heq _ _)

/-- The complete temporal final reading is the SAME incoming coarse-corner reading after exact parameter transport. -/
theorem time_last_heq (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    HEq (realized.time timeIndex spaceIndex).val.realization.last
      (Readings.sample (observed := observed) timeIndex.succ spaceIndex) :=
  (heq_of_eq (OwnerPath.Between.last_eq (cached := (realized.time timeIndex spaceIndex).val))).trans
    (OwnerReading.castParameter_heq _ _)

/-- The complete spatial starting reading is the SAME incoming coarse-corner reading after exact parameter transport. -/
theorem space_first_heq (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    HEq (realized.space timeIndex spaceIndex).val.realization.first
      (Readings.sample (observed := observed) timeIndex spaceIndex.castSucc) :=
  (heq_of_eq (OwnerPath.Between.first_eq (cached := (realized.space timeIndex spaceIndex).val))).trans
    (OwnerReading.castParameter_heq _ _)

/-- The complete spatial final reading is the SAME incoming coarse-corner reading after exact parameter transport. -/
theorem space_last_heq (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    HEq (realized.space timeIndex spaceIndex).val.realization.last
      (Readings.sample (observed := observed) timeIndex spaceIndex.succ) :=
  (heq_of_eq (OwnerPath.Between.last_eq (cached := (realized.space timeIndex spaceIndex).val))).trans
    (OwnerReading.castParameter_heq _ _)

/-- Actual temporal endpoint values are exactly the two SAME stored coarse-corner values. -/
theorem time_values (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (realized.time timeIndex spaceIndex).val.realization.first.value =
        (Readings.sample (observed := observed) timeIndex.castSucc spaceIndex).value ∧
      (realized.time timeIndex spaceIndex).val.realization.last.value =
        (Readings.sample (observed := observed) timeIndex.succ spaceIndex).value :=
  ⟨(congrArg OwnerReading.value (OwnerPath.Between.first_eq (cached := (realized.time timeIndex spaceIndex).val))).trans
      (OwnerReading.castParameter_value _ _),
    (congrArg OwnerReading.value (OwnerPath.Between.last_eq (cached := (realized.time timeIndex spaceIndex).val))).trans
      (OwnerReading.castParameter_value _ _)⟩

/-- Actual spatial endpoint values are exactly the two SAME stored coarse-corner values. -/
theorem space_values (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (realized.space timeIndex spaceIndex).val.realization.first.value =
        (Readings.sample (observed := observed) timeIndex spaceIndex.castSucc).value ∧
      (realized.space timeIndex spaceIndex).val.realization.last.value =
        (Readings.sample (observed := observed) timeIndex spaceIndex.succ).value :=
  ⟨(congrArg OwnerReading.value
      (OwnerPath.Between.first_eq (cached := (realized.space timeIndex spaceIndex).val))).trans
      (OwnerReading.castParameter_value _ _),
    (congrArg OwnerReading.value
      (OwnerPath.Between.last_eq (cached := (realized.space timeIndex spaceIndex).val))).trans
      (OwnerReading.castParameter_value _ _)⟩

/-- Both actual forward cell routes use the SAME four coarse-corner values, including all retained handoffs.

This is exact endpoint incidence of the supplied readings. The edge
polynomials remain independent, so these equations neither concatenate
their fixed-polynomial Chains nor provide a face filling.
-/
theorem cell_values (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (realized.time timeIndex spaceIndex.castSucc).val.realization.first.value =
        (realized.space timeIndex.castSucc spaceIndex).val.realization.first.value ∧
    (realized.time timeIndex spaceIndex.castSucc).val.realization.last.value =
        (realized.space timeIndex.succ spaceIndex).val.realization.first.value ∧
    (realized.space timeIndex.castSucc spaceIndex).val.realization.last.value =
        (realized.time timeIndex spaceIndex.succ).val.realization.first.value ∧
    (realized.space timeIndex.succ spaceIndex).val.realization.last.value =
        (realized.time timeIndex spaceIndex.succ).val.realization.last.value :=
  ⟨(realized.time_values timeIndex spaceIndex.castSucc).1.trans
      (realized.space_values timeIndex.castSucc spaceIndex).1.symm,
    (realized.time_values timeIndex spaceIndex.castSucc).2.trans
      (realized.space_values timeIndex.succ spaceIndex).1.symm,
    (realized.space_values timeIndex.castSucc spaceIndex).2.trans
      (realized.time_values timeIndex spaceIndex.succ).1.symm,
    (realized.space_values timeIndex.succ spaceIndex).2.trans
      (realized.time_values timeIndex spaceIndex.succ).2.symm⟩

end Realizations

end Readings

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices.Edges.Links.Requirements

end
