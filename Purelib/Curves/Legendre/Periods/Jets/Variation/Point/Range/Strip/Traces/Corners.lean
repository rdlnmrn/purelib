module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Traces.Links
public import Purelib.Data.Fin.Fold.Max
import Purelib.Data.List.DependentProduct
import Purelib.Data.Nat.Order
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.OwnerTracePath.Between
import Purelib.Riemann.Paths.OwnerTracePath.Dyadic.Links

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
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Riemann.Paths.OwnerTraceReadings.Trace

/-! # Incident native floors and one reading per retained coarse corner

Each incident requirement is read from the SAME actual stored whole edge
path. Bounded vertex occurrences, rather than coordinates, select its
source and target incidences. All finite maxima are materialized before
any corner sample. The original vertex Owner is then sampled once and
retained with its complete original tail and reading factory.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices.Edges.Links

open Purelib
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Fin.Fold
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.Paths.OwnerTraceReadings
open Purelib.Riemann.Paths.OwnerTracePath
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
    (linked : Links retained)

/-- One retained original pair of endpoint reading floors per actual temporal link prefix. -/
@[expose] def TimeRequirements := DependentProduct retained.original.times (fun timeIndex =>
  DependentProduct (left :: retained.original.spaces) (fun spaceIndex =>
    OwnerPath.ReadingFloors (Time.Links.whole (linked := Links.time (linked := linked) timeIndex spaceIndex))))

/-- One retained original pair of endpoint reading floors per actual spatial link prefix. -/
@[expose] def SpaceRequirements := DependentProduct (left :: retained.original.times) (fun timeIndex =>
  DependentProduct retained.original.spaces (fun spaceIndex =>
    OwnerPath.ReadingFloors (Space.Links.whole (linked := Links.space (linked := linked) timeIndex spaceIndex))))

/-- Read each temporal path's two actual endpoint floors once before any incidence scan. -/
def timeRequirements : TimeRequirements linked :=
  DependentProduct.ofFn retained.original.times (fun timeIndex =>
    DependentProduct.ofFn (left :: retained.original.spaces) (fun spaceIndex =>
      OwnerPath.readingFloors (Time.Links.whole (linked := Links.time (linked := linked) timeIndex spaceIndex))))

/-- Read each spatial path's two actual endpoint floors once before any incidence scan. -/
def spaceRequirements : SpaceRequirements linked :=
  DependentProduct.ofFn (left :: retained.original.times) (fun timeIndex =>
    DependentProduct.ofFn retained.original.spaces (fun spaceIndex =>
      OwnerPath.readingFloors (Space.Links.whole (linked := Links.space (linked := linked) timeIndex spaceIndex))))

/-- Both actual endpoint-floor tables, retaining their complete one-pass factories. -/
@[expose] def Requirements :=
  (_times : { value : TimeRequirements linked // value = timeRequirements linked }) ×
    { spaces : SpaceRequirements linked // spaces = spaceRequirements linked }

/-- Materialize the actual path-endpoint floors once before the finite corner maxima. -/
def requirements : Requirements linked :=
  let times := timeRequirements linked
  let spaces := spaceRequirements linked
  ⟨⟨times, rfl⟩, ⟨spaces, rfl⟩⟩

namespace Requirements

variable {linked} (required : Requirements linked)

/-- Read the SAME cached temporal source/target floor pair at its original bounded edge occurrence. -/
@[expose] def time (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    OwnerPath.ReadingFloors (Time.Links.whole (linked := Links.time (linked := linked) timeIndex spaceIndex)) :=
  DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get retained.original.times required.1.val timeIndex) spaceIndex

/-- Read the SAME cached spatial source/target floor pair at its original bounded edge occurrence. -/
@[expose] def space (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    OwnerPath.ReadingFloors (Space.Links.whole (linked := Links.space (linked := linked) timeIndex spaceIndex)) :=
  DependentProduct.get retained.original.spaces
    (DependentProduct.get (left :: retained.original.times) required.2.val timeIndex) spaceIndex

/-- One temporal occurrence contributes both actual path floors and original strict trace-request floors. -/
@[expose] def timeIncident (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length)
    (timeIndex : Fin retained.original.times.length) (spaceIndex : Fin (left :: retained.original.spaces).length) :
    Nat :=
  Nat.max
    (if timeVertex = timeIndex.castSucc ∧ spaceVertex = spaceIndex then
      Nat.max (Requirements.time (required := required) timeIndex spaceIndex).source
        (AdvanceLinks.firstRequest
          (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex else 0)
    (if timeVertex = timeIndex.succ ∧ spaceVertex = spaceIndex then
      Nat.max (Requirements.time (required := required) timeIndex spaceIndex).target
        (AdvanceLinks.targetRequest
          (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex else 0)

/-- One spatial occurrence contributes both actual path floors and original strict trace-request floors. -/
@[expose] def spaceIncident (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length)
    (timeIndex : Fin (left :: retained.original.times).length) (spaceIndex : Fin retained.original.spaces.length) :
    Nat :=
  Nat.max
    (if timeVertex = timeIndex ∧ spaceVertex = spaceIndex.castSucc then
      Nat.max (Requirements.space (required := required) timeIndex spaceIndex).source
        (AdvanceLinks.firstRequest
          (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex else 0)
    (if timeVertex = timeIndex ∧ spaceVertex = spaceIndex.succ then
      Nat.max (Requirements.space (required := required) timeIndex spaceIndex).target
        (AdvanceLinks.targetRequest
          (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex else 0)

/-- The exact finite maximum of all temporal incidences at the SAME bounded coarse corner. -/
@[expose] def timeDemand (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) : Nat :=
  Max.maxFin retained.original.times.length (fun timeIndex =>
    Max.maxFin (left :: retained.original.spaces).length
      (fun spaceIndex => required.timeIncident timeVertex spaceVertex timeIndex spaceIndex))

/-- The exact finite maximum of all spatial incidences at the SAME bounded coarse corner. -/
@[expose] def spaceDemand (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) : Nat :=
  Max.maxFin (left :: retained.original.times).length (fun timeIndex =>
    Max.maxFin retained.original.spaces.length
      (fun spaceIndex => required.spaceIncident timeVertex spaceVertex timeIndex spaceIndex))

/-- The retained corner demand is the actual maximum of its temporal and spatial incidence floors. -/
@[expose] def cornerDemand (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) : Nat :=
  Nat.max (required.timeDemand timeVertex spaceVertex) (required.spaceDemand timeVertex spaceVertex)

/-- The actual temporal source requirement is paid at its SAME bounded source corner. -/
theorem time_source_le (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (Requirements.time (required := required) timeIndex spaceIndex).source ≤
      required.cornerDemand timeIndex.castSucc spaceIndex := by
  have incident : (Requirements.time (required := required) timeIndex spaceIndex).source ≤
      required.timeIncident timeIndex.castSucc spaceIndex timeIndex spaceIndex := by
    change _ ≤ Nat.max (if _ then _ else 0) _
    rewrite [if_pos (⟨rfl, rfl⟩ : timeIndex.castSucc = timeIndex.castSucc ∧ spaceIndex = spaceIndex)]
    exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)
  have inner := Max.le_maxFin
    (fun index => required.timeIncident timeIndex.castSucc spaceIndex timeIndex index) spaceIndex
  have outer := Max.le_maxFin (fun index => Max.maxFin (left :: retained.original.spaces).length
    (fun other => required.timeIncident timeIndex.castSucc spaceIndex index other)) timeIndex
  exact (incident.trans (inner.trans outer)).trans (Data.Nat.Order.le_max_left _ _)

/-- The actual temporal target requirement is paid at its SAME bounded target corner. -/
theorem time_target_le (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (Requirements.time (required := required) timeIndex spaceIndex).target ≤
      required.cornerDemand timeIndex.succ spaceIndex := by
  have incident : (Requirements.time (required := required) timeIndex spaceIndex).target ≤
      required.timeIncident timeIndex.succ spaceIndex timeIndex spaceIndex := by
    change _ ≤ Nat.max _ (if _ then _ else 0)
    rewrite [if_pos (⟨rfl, rfl⟩ : timeIndex.succ = timeIndex.succ ∧ spaceIndex = spaceIndex)]
    exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  have inner := Max.le_maxFin
    (fun index => required.timeIncident timeIndex.succ spaceIndex timeIndex index) spaceIndex
  have outer := Max.le_maxFin (fun index => Max.maxFin (left :: retained.original.spaces).length
    (fun other => required.timeIncident timeIndex.succ spaceIndex index other)) timeIndex
  exact (incident.trans (inner.trans outer)).trans (Data.Nat.Order.le_max_left _ _)

/-- The actual spatial source requirement is paid at its SAME bounded source corner. -/
theorem space_source_le (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (Requirements.space (required := required) timeIndex spaceIndex).source ≤
      required.cornerDemand timeIndex spaceIndex.castSucc := by
  have incident : (Requirements.space (required := required) timeIndex spaceIndex).source ≤
      required.spaceIncident timeIndex spaceIndex.castSucc timeIndex spaceIndex := by
    change _ ≤ Nat.max (if _ then _ else 0) _
    rewrite [if_pos (⟨rfl, rfl⟩ : timeIndex = timeIndex ∧ spaceIndex.castSucc = spaceIndex.castSucc)]
    exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_left _ _)
  have inner := Max.le_maxFin
    (fun index => required.spaceIncident timeIndex spaceIndex.castSucc timeIndex index) spaceIndex
  have outer := Max.le_maxFin (fun index => Max.maxFin retained.original.spaces.length
    (fun other => required.spaceIncident timeIndex spaceIndex.castSucc index other)) timeIndex
  exact (incident.trans (inner.trans outer)).trans (Data.Nat.Order.le_max_right _ _)

/-- The actual spatial target requirement is paid at its SAME bounded target corner. -/
theorem space_target_le (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (Requirements.space (required := required) timeIndex spaceIndex).target ≤
      required.cornerDemand timeIndex spaceIndex.succ := by
  have incident : (Requirements.space (required := required) timeIndex spaceIndex).target ≤
      required.spaceIncident timeIndex spaceIndex.succ timeIndex spaceIndex := by
    change _ ≤ Nat.max _ (if _ then _ else 0)
    rewrite [if_pos (⟨rfl, rfl⟩ : timeIndex = timeIndex ∧ spaceIndex.succ = spaceIndex.succ)]
    exact (Data.Nat.Order.le_max_left _ _).trans (Data.Nat.Order.le_max_right _ _)
  have inner := Max.le_maxFin
    (fun index => required.spaceIncident timeIndex spaceIndex.succ timeIndex index) spaceIndex
  have outer := Max.le_maxFin (fun index => Max.maxFin retained.original.spaces.length
    (fun other => required.spaceIncident timeIndex spaceIndex.succ index other)) timeIndex
  exact (incident.trans (inner.trans outer)).trans (Data.Nat.Order.le_max_right _ _)

/-- The SAME cached time first trace-request floor is paid by its actual pre-observation corner demand. -/
theorem time_first_trace_le (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (AdvanceLinks.firstRequest
        (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
      required.cornerDemand timeIndex.castSucc spaceIndex := by
  have incident :
      (AdvanceLinks.firstRequest
          (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
        required.timeIncident timeIndex.castSucc spaceIndex timeIndex spaceIndex := by
    change _ ≤ Nat.max (if _ then _ else 0) _
    rewrite [if_pos (⟨rfl, rfl⟩ : timeIndex.castSucc = timeIndex.castSucc ∧ spaceIndex = spaceIndex)]
    exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)
  have inner := Max.le_maxFin
    (fun index => required.timeIncident timeIndex.castSucc spaceIndex timeIndex index) spaceIndex
  have outer := Max.le_maxFin (fun index => Max.maxFin (left :: retained.original.spaces).length
    (fun other => required.timeIncident timeIndex.castSucc spaceIndex index other)) timeIndex
  exact (incident.trans (inner.trans outer)).trans (Data.Nat.Order.le_max_left _ _)

/-- The SAME cached time target trace-request floor is paid by its actual pre-observation corner demand. -/
theorem time_target_trace_le (timeIndex : Fin retained.original.times.length)
    (spaceIndex : Fin (left :: retained.original.spaces).length) :
    (AdvanceLinks.targetRequest
        (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
      required.cornerDemand timeIndex.succ spaceIndex := by
  have incident :
      (AdvanceLinks.targetRequest
          (linked := (Links.time (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
        required.timeIncident timeIndex.succ spaceIndex timeIndex spaceIndex := by
    change _ ≤ Nat.max _ (if _ then _ else 0)
    rewrite [if_pos (⟨rfl, rfl⟩ : timeIndex.succ = timeIndex.succ ∧ spaceIndex = spaceIndex)]
    exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
  have inner := Max.le_maxFin
    (fun index => required.timeIncident timeIndex.succ spaceIndex timeIndex index) spaceIndex
  have outer := Max.le_maxFin (fun index => Max.maxFin (left :: retained.original.spaces).length
    (fun other => required.timeIncident timeIndex.succ spaceIndex index other)) timeIndex
  exact (incident.trans (inner.trans outer)).trans (Data.Nat.Order.le_max_left _ _)

/-- The SAME cached space first trace-request floor is paid by its actual pre-observation corner demand. -/
theorem space_first_trace_le (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (AdvanceLinks.firstRequest
        (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
      required.cornerDemand timeIndex spaceIndex.castSucc := by
  have incident :
      (AdvanceLinks.firstRequest
          (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
        required.spaceIncident timeIndex spaceIndex.castSucc timeIndex spaceIndex := by
    change _ ≤ Nat.max (if _ then _ else 0) _
    rewrite [if_pos (⟨rfl, rfl⟩ : timeIndex = timeIndex ∧ spaceIndex.castSucc = spaceIndex.castSucc)]
    exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_left _ _)
  have inner := Max.le_maxFin
    (fun index => required.spaceIncident timeIndex spaceIndex.castSucc timeIndex index) spaceIndex
  have outer := Max.le_maxFin (fun index => Max.maxFin retained.original.spaces.length
    (fun other => required.spaceIncident timeIndex spaceIndex.castSucc index other)) timeIndex
  exact (incident.trans (inner.trans outer)).trans (Data.Nat.Order.le_max_right _ _)

/-- The SAME cached space target trace-request floor is paid by its actual pre-observation corner demand. -/
theorem space_target_trace_le (timeIndex : Fin (left :: retained.original.times).length)
    (spaceIndex : Fin retained.original.spaces.length) :
    (AdvanceLinks.targetRequest
        (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
      required.cornerDemand timeIndex spaceIndex.succ := by
  have incident :
      (AdvanceLinks.targetRequest
          (linked := (Links.space (linked := linked) timeIndex spaceIndex).2)).val.compared.leftIndex ≤
        required.spaceIncident timeIndex spaceIndex.succ timeIndex spaceIndex := by
    change _ ≤ Nat.max _ (if _ then _ else 0)
    rewrite [if_pos (⟨rfl, rfl⟩ : timeIndex = timeIndex ∧ spaceIndex.succ = spaceIndex.succ)]
    exact (Data.Nat.Order.le_max_right _ _).trans (Data.Nat.Order.le_max_right _ _)
  have inner := Max.le_maxFin
    (fun index => required.spaceIncident timeIndex spaceIndex.succ timeIndex index) spaceIndex
  have outer := Max.le_maxFin (fun index => Max.maxFin retained.original.spaces.length
    (fun other => required.spaceIncident timeIndex spaceIndex.succ index other)) timeIndex
  exact (incident.trans (inner.trans outer)).trans (Data.Nat.Order.le_max_right _ _)

/-- One actual computed native floor at every original bounded coarse corner, with complete calculation factories. -/
@[expose] def Demands := DependentProduct (left :: retained.original.times) (fun timeVertex =>
  DependentProduct (left :: retained.original.spaces) (fun spaceVertex =>
    { value : Nat // value = required.cornerDemand timeVertex spaceVertex }))

/-- Materialize ALL original finite incidence maxima before any coarse-corner native sample. -/
def demands : Demands required :=
  DependentProduct.ofFn (left :: retained.original.times) (fun timeVertex =>
    DependentProduct.ofFn (left :: retained.original.spaces) (fun spaceVertex =>
      let value := required.cornerDemand timeVertex spaceVertex
      ⟨value, rfl⟩))

namespace Demands

variable {required} (demanded : Demands required)

/-- Read the SAME stored native floor at its two original bounded vertex occurrences. -/
@[expose] def floor (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) : Nat :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get (left :: retained.original.times) demanded timeVertex) spaceVertex).val

/-- The stored floor retains its actual finite temporal/spatial incidence maximum factory. -/
theorem floor_eq (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    demanded.floor timeVertex spaceVertex = required.cornerDemand timeVertex spaceVertex :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get (left :: retained.original.times) demanded timeVertex) spaceVertex).property

end Demands

variable (demanded : Demands required)

/-- One actual original tail and selected native index per bounded coarse corner, before any displayed sample. -/
@[expose] def Targets := DependentProduct (left :: retained.original.times) (fun timeVertex =>
  DependentProduct (left :: retained.original.spaces) (fun spaceVertex =>
    (tail : { value : OwnerTail (retained.original.owner timeVertex spaceVertex) //
      value = OwnerTail.acquire (retained.original.owner timeVertex spaceVertex) }) ×
      { index : Nat // index = Nat.max (Demands.floor (demanded := demanded) timeVertex spaceVertex) tail.val.first }))

/-- Bind ALL genuine original tails and final native indices after the whole incidence-maximum table. -/
def targets : Targets required demanded :=
  DependentProduct.ofFn (left :: retained.original.times) (fun timeVertex =>
    DependentProduct.ofFn (left :: retained.original.spaces) (fun spaceVertex =>
      let owner := retained.original.owner timeVertex spaceVertex
      let tail := OwnerTail.acquire owner
      let index := Nat.max (Demands.floor (demanded := demanded) timeVertex spaceVertex) tail.first
      ⟨⟨tail, rfl⟩, ⟨index, rfl⟩⟩))

namespace Targets

variable {required demanded} (targeted : Targets required demanded)

/-- Read the SAME actual original corner tail without acquiring it again. -/
@[expose] def tail (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    OwnerTail (retained.original.owner timeVertex spaceVertex) :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get (left :: retained.original.times) targeted timeVertex) spaceVertex).1.val

/-- The entire retained corner tail has its original acquisition factory. -/
theorem tail_eq (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    targeted.tail timeVertex spaceVertex = OwnerTail.acquire (retained.original.owner timeVertex spaceVertex) :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get (left :: retained.original.times) targeted timeVertex) spaceVertex).1.property

/-- Read the SAME final native index chosen before any displayed corner sample. -/
@[expose] def index (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) : Nat :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get (left :: retained.original.times) targeted timeVertex) spaceVertex).2.val

/-- The selected native index is exactly the maximum of the incidence demand and this SAME retained tail start. -/
theorem index_eq (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    targeted.index timeVertex spaceVertex =
      Nat.max (Demands.floor (demanded := demanded) timeVertex spaceVertex)
        (targeted.tail timeVertex spaceVertex).first :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get (left :: retained.original.times) targeted timeVertex) spaceVertex).2.property

/-- The final native index pays the complete already stored incidence demand. -/
theorem floor_le (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    Demands.floor (demanded := demanded) timeVertex spaceVertex ≤ targeted.index timeVertex spaceVertex :=
  (Data.Nat.Order.le_max_left _ _).trans_eq (targeted.index_eq timeVertex spaceVertex).symm

/-- The final native index lies in its SAME retained original tail. -/
theorem tail_le (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    (targeted.tail timeVertex spaceVertex).first ≤ targeted.index timeVertex spaceVertex :=
  (Data.Nat.Order.le_max_right _ _).trans_eq (targeted.index_eq timeVertex spaceVertex).symm

end Targets

variable (targeted : Targets required demanded)

/-- Take ONE original native corner sample on its already retained tail and preselected index. -/
def readCorner (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    OwnerReading (retained.original.owner timeVertex spaceVertex) :=
  let tail := Targets.tail (targeted := targeted) timeVertex spaceVertex
  let index := Targets.index (targeted := targeted) timeVertex spaceVertex
  let reading := OwnerTail.Reading.acquire tail index (Targets.tail_le (targeted := targeted) timeVertex spaceVertex)
  ⟨tail, reading⟩

/-- The one actual corner sample respects its whole incidence demand selected before all samples. -/
theorem readCorner_floor (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    Demands.floor (demanded := demanded) timeVertex spaceVertex ≤
      (readCorner required demanded targeted timeVertex spaceVertex).index := by
  unfold readCorner
  exact Targets.floor_le (targeted := targeted) timeVertex spaceVertex

/-- One complete original OwnerReading per bounded corner, with each original one-sample whole factory. -/
@[expose] def Readings := DependentProduct (left :: retained.original.times) (fun timeVertex =>
  DependentProduct (left :: retained.original.spaces) (fun spaceVertex =>
    { sample : OwnerReading (retained.original.owner timeVertex spaceVertex) //
      sample = readCorner required demanded targeted timeVertex spaceVertex }))

/-- Sample each coarse Owner once only after ALL corner tails and native indices have been retained. -/
def readings : Readings required demanded targeted :=
  DependentProduct.ofFn (left :: retained.original.times) (fun timeVertex =>
    DependentProduct.ofFn (left :: retained.original.spaces) (fun spaceVertex =>
      let sample := readCorner required demanded targeted timeVertex spaceVertex
      ⟨sample, rfl⟩))

namespace Readings

variable {required demanded targeted} (observed : Readings required demanded targeted)

/-- Project the SAME whole original corner reading without another tail or native observation. -/
@[expose] def sample (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    OwnerReading (retained.original.owner timeVertex spaceVertex) :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get (left :: retained.original.times) observed timeVertex) spaceVertex).val

/-- The complete retained reading has its original one-sample factory on the SAME supplied tail and index. -/
theorem sample_eq (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    observed.sample timeVertex spaceVertex = readCorner required demanded targeted timeVertex spaceVertex :=
  (DependentProduct.get (left :: retained.original.spaces)
    (DependentProduct.get (left :: retained.original.times) observed timeVertex) spaceVertex).property

/-- The SAME stored corner reading pays its whole precomputed incidence floor. -/
theorem floor_le (timeVertex : Fin (left :: retained.original.times).length)
    (spaceVertex : Fin (left :: retained.original.spaces).length) :
    Demands.floor (demanded := demanded) timeVertex spaceVertex ≤
      (observed.sample timeVertex spaceVertex).index :=
  (readCorner_floor (required := required) (demanded := demanded) (targeted := targeted)
    timeVertex spaceVertex).trans_eq
    (congrArg OwnerReading.index (observed.sample_eq timeVertex spaceVertex)).symm

/-- Equal bounded vertex occurrences retain the SAME stored whole reading, irrespective of coordinate coincidences. -/
theorem sample_index_heq {firstTime lastTime : Fin (left :: retained.original.times).length}
    {firstSpace lastSpace : Fin (left :: retained.original.spaces).length}
    (timeEq : firstTime = lastTime) (spaceEq : firstSpace = lastSpace) :
    HEq (observed.sample firstTime firstSpace) (observed.sample lastTime lastSpace) := by
  cases timeEq
  cases spaceEq
  rfl

end Readings

end Requirements

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.JointGrid.Vertices.Edges.Links

end
