module

public import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Stationary
public import Purelib.Approximation.Rational.Grid.Unit
public import Purelib.Data.Vector.Basic
public import Purelib.Data.Vector.Dependent
public import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Curves.Legendre.Paths.Path
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
import Purelib.Curves.Legendre.Paths.Preparation
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Rat.Interval.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Topology.Knot.Braid.Event

/-!
# Original owner windows covering separated axis segments

The computed uniform subdivision budget selects a finite closed-unit
grid. Its actual original stationary windows are materialized once.
Nearest rounding selects a retained window containing each unit
parameter, with the same frame, owner, side and radius caches.
-/

public section

namespace Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionSeparation

open Purelib.Data
open Purelib.Data.Rat
open Purelib.Approximation.Rational
open Fraction.Order
open ProjectionCollision.OwnerWindow

/-- Prepare the original stationary owner window at a bounded node of the same computed subdivision grid. -/
@[expose] def subdivisionWindow {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope)
    (index : Fin (separation.subdivisionCount + 1)) :
    ProjectionCollision.OwnerWindow (ProjectionCollision.ofParameter segment slope
      (Grid.Unit.node separation.subdivisionCount index)
      (Grid.Unit.node_bounds separation.subdivisionCount_positive index)) :=
  separation.windowAt (Grid.Unit.node separation.subdivisionCount index)
    (Grid.Unit.node_bounds separation.subdivisionCount_positive index)

/-- The computed half-mesh fits inside the same original parameter radius at every bounded subdivision node.

The node's two endpoint half-distance caps each pay the half-mesh.
The computed uniform allocation also pays that mesh inside the actual
window's velocity allocation, so the original minimum retains the bound.
-/
theorem halfMesh_le_subdivisionWindow {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope)
    (index : Fin (separation.subdivisionCount + 1)) :
    (1 / 2 : Coordinate) / separation.subdivisionCount ≤ segment.windowRadius
      (Grid.Unit.node separation.subdivisionCount index) ((separation.subdivisionWindow index).radius ^ 2) := by
  have caps := Grid.Unit.node_halfMesh_caps separation.subdivisionCount_positive index
  have allocation := separation.parameterAllocation_le_windowAt
    (Grid.Unit.node separation.subdivisionCount index)
    (Grid.Unit.node_bounds separation.subdivisionCount_positive index)
  exact Basic.le_min caps.1 (Basic.le_min caps.2 (separation.halfMesh_lt_allocation.le.trans allocation))

/-- A unit parameter within half the same grid mesh lies in its actual original subdivision window.

The original parameter window clips its centered endpoints to the
closed unit interval. Its retained radius pays the displayed half-mesh,
so both clipped bounds contain the same parameter.
-/
theorem subdivisionWindow_contains {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope)
    (index : Fin (separation.subdivisionCount + 1)) (parameter : Coordinate)
    (inside : 0 ≤ parameter ∧ parameter ≤ 1)
    (near : Grid.Unit.node separation.subdivisionCount index - (1 / 2 : Coordinate) /
        separation.subdivisionCount ≤ parameter ∧
      parameter ≤ Grid.Unit.node separation.subdivisionCount index + (1 / 2 : Coordinate) /
        separation.subdivisionCount) :
    (separation.subdivisionWindow index).parameters.Contains parameter := by
  let anchor := Grid.Unit.node separation.subdivisionCount index
  let window := separation.subdivisionWindow index
  let radius := segment.windowRadius anchor (window.radius ^ 2)
  have paid : (1 / 2 : Coordinate) / separation.subdivisionCount ≤ radius :=
    separation.halfMesh_le_subdivisionWindow index
  change max 0 (anchor - radius) ≤ parameter ∧ parameter ≤ min 1 (anchor + radius)
  constructor
  · exact Basic.max_le inside.1
      ((Arithmetic.sub_le_sub_left_direct paid anchor).trans near.1)
  · exact Basic.le_min inside.2
      (near.2.trans (Arithmetic.add_le_add_direct le_rfl paid))

/-- The original stationary window at the computed nearest bounded node contains each original unit parameter. -/
theorem nearestSubdivisionWindow_contains {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (separation.subdivisionWindow (Grid.Unit.nearestIndex parameter
      separation.subdivisionCount_positive inside)).parameters.Contains parameter :=
  separation.subdivisionWindow_contains _ parameter inside
    (Grid.Unit.nearestIndex_covers parameter separation.subdivisionCount_positive inside)

/-- A materialized finite family of the exact original subdivision windows with its complete indexed readback.

Each vector entry retains its bounded grid index and the original owner
window at that index. The readback certifies the complete cached frame,
owners, sides, radius and interval, rather than only interval equality.
-/
abbrev SubdivisionWindows {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) :=
  {windows : Data.Vector (Σ index : Fin (separation.subdivisionCount + 1),
      ProjectionCollision.OwnerWindow (ProjectionCollision.ofParameter segment slope
        (Grid.Unit.node separation.subdivisionCount index)
        (Grid.Unit.node_bounds separation.subdivisionCount_positive index))) (separation.subdivisionCount + 1) //
    ∀ index : Fin (separation.subdivisionCount + 1), windows index = ⟨index, separation.subdivisionWindow index⟩}

/-- Consecutive actual original subdivision windows contain their same computed unit-grid midpoint. -/
theorem subdivisionWindows_midpoint {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope)
    (index : Fin separation.subdivisionCount) :
    (separation.subdivisionWindow index.castSucc).parameters.Contains
        (Grid.Unit.midpoint separation.subdivisionCount index) ∧
      (separation.subdivisionWindow index.succ).parameters.Contains
        (Grid.Unit.midpoint separation.subdivisionCount index) := by
  have inside := Grid.Unit.midpoint_bounds separation.subdivisionCount_positive index
  have near := Grid.Unit.midpoint_near_nodes separation.subdivisionCount_positive index
  exact ⟨separation.subdivisionWindow_contains index.castSucc _ inside near.1,
    separation.subdivisionWindow_contains index.succ _ inside near.2⟩

/-- Materialize every original grid-node window once in bounded index order.

The retained structural vector caches the actual original windows.
Its complete readback identifies every entry with the same bounded
index and original constructor, including both endpoint windows.
-/
@[expose] def prepareSubdivisionWindows {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) : SubdivisionWindows separation :=
  ⟨Vector.Basic.vectorOfFn fun index => ⟨index, separation.subdivisionWindow index⟩,
    fun index => Vector.Basic.vectorOfFn_apply _ index⟩

/-- Select a retained original subdivision window containing a unit parameter.

The existing nearest-rounding operation computes the bounded index.
Coverage refers to that entry of the supplied materialized vector,
consuming its same cached window without preparing a replacement.
-/
@[expose] def coveringWindow {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    {index : Fin (separation.subdivisionCount + 1) //
      (windows.val index).2.parameters.Contains parameter} :=
  ⟨Grid.Unit.nearestIndex parameter separation.subdivisionCount_positive inside, by
    rewrite [windows.property]
    exact separation.nearestSubdivisionWindow_contains parameter inside⟩

/-- The selected retained covering-window index is exactly the original nearest bounded grid index. -/
theorem coveringWindow_index {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (separation.coveringWindow windows parameter inside).val =
      Grid.Unit.nearestIndex parameter separation.subdivisionCount_positive inside := rfl

/-- Consecutive entries of the same materialized original window cache contain their retained common midpoint.

The complete cache identities transport containment to both actual
stored windows. Their original owners and side/radius caches remain
separate while sharing the same original path parameter.
-/
theorem retainedWindows_midpoint {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (index : Fin separation.subdivisionCount) :
    (windows.val index.castSucc).2.parameters.Contains (Grid.Unit.midpoint separation.subdivisionCount index) ∧
      (windows.val index.succ).2.parameters.Contains (Grid.Unit.midpoint separation.subdivisionCount index) := by
  rewrite [windows.property index.castSucc, windows.property index.succ]
  exact separation.subdivisionWindows_midpoint index

/-- Compute one cached projection-sample frame refining both actual neighboring retained window-owner families.

The original common midpoint lies in both cached windows. Their same
root-derived sample caps determine a shared frame in the retained chart.
Both sample views use that identical frame and keep their own original
window and owner-refinement certificates.
-/
@[expose] def midpointSamples {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (index : Fin separation.subdivisionCount) :
    ProjectionCollision.OwnerWindow.SamplesAt.Shared (windows.val index.castSucc).2 (windows.val index.succ).2
      (Grid.Unit.midpoint separation.subdivisionCount index) := by
  let parameter := Grid.Unit.midpoint separation.subdivisionCount index
  have inside := Grid.Unit.midpoint_bounds separation.subdivisionCount_positive index
  have retained := separation.retainedWindows_midpoint windows index
  exact ProjectionCollision.OwnerWindow.SamplesAt.shared (windows.val index.castSucc).2 (windows.val index.succ).2
    parameter retained.1 retained.2 (separation.separates parameter inside.1 inside.2)

/-- A stored finite family of the same original shared midpoint-sample frames and both window views.

Each entry retains the two original neighboring windows and their actual
common parameter. Its complete readback identifies the cached shared
frame, both original views and all their owner-refinement certificates.
-/
abbrev MidpointSamples {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation) :=
  {samples : Vector.DependentVector (fun index : Fin separation.subdivisionCount =>
      SamplesAt.Shared (windows.val index.castSucc).2 (windows.val index.succ).2
        (Grid.Unit.midpoint separation.subdivisionCount index)) //
    ∀ index : Fin separation.subdivisionCount, samples.get index = separation.midpointSamples windows index}

/-- Materialize each original shared midpoint-sample frame once in bounded index order.

The original dependent vector stores the actual shared frame and its
two window views at every common midpoint. Its readback retains each
complete constructor result, allowing both neighboring cells to reuse it.
-/
@[expose] def prepareMidpointSamples {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation) :
    MidpointSamples separation windows :=
  ⟨Vector.DependentVector.ofFn (separation.midpointSamples windows),
    fun index => Vector.DependentVector.ofFn_get _ index⟩

/-- Two points of an actual retained subdivision window have the same original logical branch order.

The complete cache readback identifies the original stationary window
at its same grid anchor. Its all-point order law relates both retained
parameters to that same original anchor order.
-/
theorem subdivisionOrders {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (index : Fin (separation.subdivisionCount + 1)) (source target : Coordinate)
    (sourceInside : (windows.val index).2.parameters.Contains source)
    (targetInside : (windows.val index).2.parameters.Contains target) (position : Fin 3) :
    (branchOrder (segment.pointAt source) slope).forward position =
      (branchOrder (segment.pointAt target) slope).forward position := by
  have originalSource := sourceInside
  have originalTarget := targetInside
  rewrite [windows.property index] at originalSource originalTarget
  let parameter := Grid.Unit.node separation.subdivisionCount index
  let bounds := Grid.Unit.node_bounds separation.subdivisionCount_positive index
  let anchor := ProjectionCollision.ofParameter segment slope parameter bounds
  have separated := separation.separates parameter bounds.1 bounds.2
  have sourceOrder := anchor.prepareStationaryWindow_order separation.avoidsZero separation.avoidsOne separated
    source originalSource
  have targetOrder := anchor.prepareStationaryWindow_order separation.avoidsZero separation.avoidsOne separated
    target originalTarget
  rewrite [sourceOrder, targetOrder]
  rfl

/-- Read the original ordered unit-grid cell at a bounded index of the computed subdivision count. -/
abbrev subdivisionCell {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (index : Fin (separation.subdivisionCount + 1)) :
    Interval.Bounds :=
  Grid.Unit.cell separation.subdivisionCount_positive index

/-- Every point of a computed unit-grid cell lies in its same actual retained subdivision owner window.

The cell's unit and half-mesh bounds pay the original window's endpoint
caps and velocity allocation. The complete cache readback transports
containment to the actual stored window and its original owner records.
-/
theorem subdivisionCell_contains {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (index : Fin (separation.subdivisionCount + 1)) (parameter : Coordinate)
    (inside : (separation.subdivisionCell index).Contains parameter) :
    (windows.val index).2.parameters.Contains parameter := by
  have bounds := (Grid.Unit.cell_contains_iff separation.subdivisionCount_positive index parameter).mp inside
  rewrite [windows.property index]
  exact separation.subdivisionWindow_contains index parameter bounds.1 bounds.2

/-- Both endpoints of a computed unit-grid cell belong to its same actual retained original owner window. -/
theorem subdivisionCell_endpoints {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (index : Fin (separation.subdivisionCount + 1)) :
    (windows.val index).2.parameters.Contains (separation.subdivisionCell index).lower ∧
      (windows.val index).2.parameters.Contains (separation.subdivisionCell index).upper :=
  ⟨separation.subdivisionCell_contains windows index _ ⟨le_rfl, (separation.subdivisionCell index).valid⟩,
    separation.subdivisionCell_contains windows index _ ⟨(separation.subdivisionCell index).valid, le_rfl⟩⟩

/-- Read a cell's original source sample from its stored preceding midpoint, preparing only the first endpoint.

Every successor cell consumes the right-window view of the actual cached
shared midpoint. The grid endpoint identity transports that same complete
sample view to the cell's lower parameter without constructing a new frame.
-/
@[expose] def cellSourceSamples {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (index : Fin (separation.subdivisionCount + 1)) :
    SamplesAt (windows.val index).2 (separation.subdivisionCell index).lower := by
  rcases index with ⟨index, bound⟩
  cases index with
  | zero =>
    let first : Fin (separation.subdivisionCount + 1) := ⟨0, bound⟩
    have endpoints := separation.subdivisionCell_endpoints windows first
    have unit := Grid.Unit.cell_bounds separation.subdivisionCount_positive first
    exact (windows.val first).2.samplesAt (separation.subdivisionCell first).lower endpoints.1
      (separation.separates _ unit.1 ((separation.subdivisionCell first).valid.trans unit.2.2))
  | succ index =>
    let previous : Fin separation.subdivisionCount := ⟨index, Nat.lt_of_succ_lt_succ bound⟩
    exact ((midpoints.val.get previous).val.2).castParameter
      (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive previous).symm

/-- Read a cell's original target sample from its stored following midpoint, preparing only the final endpoint.

Every nonfinal cell consumes the left-window view of the actual cached
shared midpoint. The grid endpoint identity transports that same complete
sample view to the cell's upper parameter without constructing a new frame.
-/
@[expose] def cellTargetSamples {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (index : Fin (separation.subdivisionCount + 1)) :
    SamplesAt (windows.val index).2 (separation.subdivisionCell index).upper := by
  if interior : index.val < separation.subdivisionCount then
    let next : Fin separation.subdivisionCount := ⟨index.val, interior⟩
    exact ((midpoints.val.get next).val.1).castParameter
      (Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive next).symm
  else
    have endpoints := separation.subdivisionCell_endpoints windows index
    have unit := Grid.Unit.cell_bounds separation.subdivisionCount_positive index
    exact (windows.val index).2.samplesAt (separation.subdivisionCell index).upper endpoints.2
      (separation.separates _ (unit.1.trans (separation.subdivisionCell index).valid) unit.2.2)

/-- A successor cell's source retains the complete right-window view of its same stored shared midpoint. -/
theorem cellSourceSamples_midpoint {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (index : Fin separation.subdivisionCount) :
    (separation.cellSourceSamples windows midpoints index.succ).castParameter
        (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index) =
      (midpoints.val.get index).val.2 := by
  change (((midpoints.val.get index).val.2).castParameter
      (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index).symm).castParameter _ = _
  exact SamplesAt.castParameter_inverse _ _

/-- A nonfinal cell's target retains the complete left-window view of its same stored shared midpoint. -/
theorem cellTargetSamples_midpoint {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (index : Fin separation.subdivisionCount) :
    (separation.cellTargetSamples windows midpoints index.castSucc).castParameter
        (Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive index) =
      (midpoints.val.get index).val.1 := by
  unfold cellTargetSamples
  split
  · exact SamplesAt.castParameter_inverse _ _
  · rename_i last
    exact False.elim (last index.isLt)

/-- A stored family of both original endpoint sample views for every ordered cell of the same retained windows.

The dependent vector materializes the two boundary endpoint frames once
and reuses the supplied shared-midpoint cache for every interior endpoint.
Its complete readback retains each original window, parameter and sample view.
-/
abbrev SubdivisionSamples {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) :=
  {samples : Vector.DependentVector (fun index : Fin (separation.subdivisionCount + 1) =>
      SamplesAt (windows.val index).2 (separation.subdivisionCell index).lower ×
        SamplesAt (windows.val index).2 (separation.subdivisionCell index).upper) //
    ∀ index : Fin (separation.subdivisionCount + 1), samples.get index =
      (separation.cellSourceSamples windows midpoints index, separation.cellTargetSamples windows midpoints index)}

/-- Materialize both original endpoint sample views for every cell using the same retained shared-midpoint cache. -/
@[expose] def prepareSubdivisionSamples {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) : SubdivisionSamples separation windows midpoints :=
  ⟨Vector.DependentVector.ofFn fun index =>
      (separation.cellSourceSamples windows midpoints index, separation.cellTargetSamples windows midpoints index),
    fun index => Vector.DependentVector.ofFn_get _ index⟩

/-- The retained successor-cell source is the complete right-window view of its actual stored midpoint. -/
theorem subdivisionSamples_source_midpoint {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (index : Fin separation.subdivisionCount) :
    ((samples.val.get index.succ).1).castParameter
        (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index) =
      (midpoints.val.get index).val.2 := by
  rewrite [samples.property index.succ]
  exact separation.cellSourceSamples_midpoint windows midpoints index

/-- The retained nonfinal-cell target is the complete left-window view of its actual stored midpoint. -/
theorem subdivisionSamples_target_midpoint {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (index : Fin separation.subdivisionCount) :
    ((samples.val.get index.castSucc).2).castParameter
        (Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive index) =
      (midpoints.val.get index).val.1 := by
  rewrite [samples.property index.castSucc]
  exact separation.cellTargetSamples_midpoint windows midpoints index

/-- Construct the original bridge family between both endpoints of one actual retained ordered cell.

The cell containment laws derive both endpoint payments. The existing
window builder retains its same source-factor cache and all three
original source-to-target owner bridges.
-/
@[expose] def cellBridges {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (index : Fin (separation.subdivisionCount + 1)) :
    BridgesAt (windows.val index).2 (separation.subdivisionCell index).lower
      (separation.subdivisionCell index).upper :=
  (windows.val index).2.bridgesAt (separation.subdivisionCell index).lower (separation.subdivisionCell index).upper
    (separation.subdivisionCell_endpoints windows index).1 (separation.subdivisionCell_endpoints windows index).2

/-- A stored family of the complete original moving bridge packets for the ordered cells of the retained windows.

Every dependent entry keeps its original cell endpoints and window,
including the actual source-factor cache and all three owner bridges.
The indexed readback identifies the complete original builder result.
-/
abbrev SubdivisionBridges {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation) :=
  {bridges : Vector.DependentVector (fun index : Fin (separation.subdivisionCount + 1) =>
      BridgesAt (windows.val index).2 (separation.subdivisionCell index).lower
        (separation.subdivisionCell index).upper) //
    ∀ index : Fin (separation.subdivisionCount + 1), bridges.get index = separation.cellBridges windows index}

/-- Materialize each cell's original source factors and all three moving owner bridges once in bounded index order. -/
@[expose] def prepareSubdivisionBridges {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation) :
    SubdivisionBridges separation windows :=
  ⟨Vector.DependentVector.ofFn (separation.cellBridges windows),
    fun index => Vector.DependentVector.ofFn_get _ index⟩

/-- Assemble the actual original stationary segment between two retained points of a computed subdivision window.

The supplied samples and cached bridge family retain their original
endpoint owners. The window derives safety and projected-order agreement
internally, and the same actual overlap computes its bridge-clearance payment.
-/
@[expose] def subdivisionSegment {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (index : Fin (separation.subdivisionCount + 1)) {source target : Coordinate}
    (bridges : BridgesAt (windows.val index).2 source target)
    (sourceSamples : SamplesAt (windows.val index).2 source) (targetSamples : SamplesAt (windows.val index).2 target)
    (sourceInside : (windows.val index).2.parameters.Contains source)
    (targetInside : (windows.val index).2.parameters.Contains target) :
    Paths.Segment (bridges.sourceFrame sourceSamples sourceInside) (bridges.targetFrame targetSamples targetInside) :=
  bridges.stationarySegment sourceSamples targetSamples sourceInside targetInside
    (separation.subdivisionOrders windows index source target sourceInside targetInside)

/-- Read the original cell source frame from the actual retained left bridge owners and source sample view. -/
@[expose] def cellSourceFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin (separation.subdivisionCount + 1)) :
    Paths.Frame (segment.pointAt (separation.subdivisionCell index).lower) :=
  (bridges.val.get index).sourceFrame (samples.val.get index).1
    (separation.subdivisionCell_endpoints windows index).1

/-- Read the original cell target frame from the actual retained right bridge owners and target sample view. -/
@[expose] def cellTargetFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin (separation.subdivisionCount + 1)) :
    Paths.Frame (segment.pointAt (separation.subdivisionCell index).upper) :=
  (bridges.val.get index).targetFrame (samples.val.get index).2
    (separation.subdivisionCell_endpoints windows index).2

/-- Assemble one cell's original safe moving segment from its actual retained endpoint samples and bridge packet.

The stored entries supply the complete sample views, source factors and
owner bridges. The same original window derives safety and branch order;
its actual chamber overlap determines the original sheet-clearance payment.
-/
@[expose] def cellSegment {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin (separation.subdivisionCount + 1)) :
    Paths.Segment
      (separation.cellSourceFrame windows midpoints samples bridges index)
      (separation.cellTargetFrame windows midpoints samples bridges index) :=
  separation.subdivisionSegment windows index (bridges.val.get index) (samples.val.get index).1
    (samples.val.get index).2 (separation.subdivisionCell_endpoints windows index).1
    (separation.subdivisionCell_endpoints windows index).2

/-- The cached cell segment retains the complete original affine restriction to its actual ordered cell endpoints. -/
theorem cellSegment_geometry {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin (separation.subdivisionCount + 1)) :
    (separation.cellSegment windows midpoints samples bridges index).geometry =
      segment.restrict (separation.subdivisionCell index).lower (separation.subdivisionCell index).upper := rfl

/-- Every actual separated moving-cell segment retains its original stationary projected event. -/
theorem cellSegment_event {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin (separation.subdivisionCount + 1)) :
    (separation.cellSegment windows midpoints samples bridges index).projection.event = .stationary := rfl

/-- Join the actual target and source frames of consecutive retained moving-cell bridge packets.

The same stored midpoint packet supplies both original views. Its complete
endpoint readbacks and the exact grid parameter identities derive the
constant comparison segment between these actual broad-owner frames.
-/
@[expose] def cellJoin {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin separation.subdivisionCount) :
    Paths.Segment
      (separation.cellTargetFrame windows midpoints samples bridges index.castSucc)
      (separation.cellSourceFrame windows midpoints samples bridges index.succ) :=
  (midpoints.val.get index).joinBridgesAt (bridges.val.get index.castSucc) (bridges.val.get index.succ)
    (samples.val.get index.castSucc).2 (samples.val.get index.succ).1
    (separation.subdivisionCell_endpoints windows index.castSucc).2
    (separation.subdivisionCell_endpoints windows index.succ).1
    (Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive index)
    (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index)
    (separation.subdivisionSamples_target_midpoint windows midpoints samples index)
    (separation.subdivisionSamples_source_midpoint windows midpoints samples index)

/-- The actual cell-frame join retains the original axis restriction to the two equal consecutive endpoints. -/
theorem cellJoin_geometry {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin separation.subdivisionCount) :
    (separation.cellJoin windows midpoints samples bridges index).geometry =
      segment.restrict (separation.subdivisionCell index.castSucc).upper
        (separation.subdivisionCell index.succ).lower :=
  (midpoints.val.get index).joinBridgesAt_geometry (bridges.val.get index.castSucc) (bridges.val.get index.succ)
    (samples.val.get index.castSucc).2 (samples.val.get index.succ).1
    (separation.subdivisionCell_endpoints windows index.castSucc).2
    (separation.subdivisionCell_endpoints windows index.succ).1
    (Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive index)
    (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index)
    (separation.subdivisionSamples_target_midpoint windows midpoints samples index)
    (separation.subdivisionSamples_source_midpoint windows midpoints samples index)

/-- Every parameter of an actual original cell-frame join evaluates to its same retained shared midpoint. -/
theorem cellJoin_pointAt {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin separation.subdivisionCount)
    (parameter : Coordinate) :
    (separation.cellJoin windows midpoints samples bridges index).geometry.pointAt parameter =
      segment.pointAt (Grid.Unit.midpoint separation.subdivisionCount index) := by
  rewrite [separation.cellJoin_geometry windows midpoints samples bridges index, segment.restrict_pointAt,
    Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive index,
    Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index]
  apply congrArg segment.pointAt
  ring1

/-- The actual retained moving-cell frame join has a stationary projected event at its original common endpoint. -/
theorem cellJoin_event {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) (index : Fin separation.subdivisionCount) :
    (separation.cellJoin windows midpoints samples bridges index).projection.event = .stationary :=
  (midpoints.val.get index).joinBridgesAt_event (bridges.val.get index.castSucc) (bridges.val.get index.succ)
    (samples.val.get index.castSucc).2 (samples.val.get index.succ).1
    (separation.subdivisionCell_endpoints windows index.castSucc).2
    (separation.subdivisionCell_endpoints windows index.succ).1
    (Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive index)
    (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index)
    (separation.subdivisionSamples_target_midpoint windows midpoints samples index)
    (separation.subdivisionSamples_source_midpoint windows midpoints samples index)

/-- A stored family of the original moving segments with their actual cached endpoint frames and complete readbacks. -/
abbrev SubdivisionSegments {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) :=
  {pieces : Vector.DependentVector (fun index : Fin (separation.subdivisionCount + 1) =>
      Paths.Segment (separation.cellSourceFrame windows midpoints samples bridges index)
        (separation.cellTargetFrame windows midpoints samples bridges index)) //
    ∀ index : Fin (separation.subdivisionCount + 1), pieces.get index =
      separation.cellSegment windows midpoints samples bridges index}

/-- Materialize every original moving segment once from the actual retained sample and bridge caches. -/
@[expose] def prepareSubdivisionSegments {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) :
    SubdivisionSegments separation windows midpoints samples bridges :=
  ⟨Vector.DependentVector.ofFn (separation.cellSegment windows midpoints samples bridges),
    fun index => Vector.DependentVector.ofFn_get _ index⟩

/-- A stored family of the original comparisons between actual consecutive moving-cell endpoint frames.

Each dependent entry retains the two distinct broad-owner frames and the
same original shared midpoint. Its complete readback identifies the actual
constant comparison segment, including owner overlap and sheet clearance.
-/
abbrev SubdivisionJoins {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) :=
  {joins : Vector.DependentVector (fun index : Fin separation.subdivisionCount =>
      Paths.Segment (separation.cellTargetFrame windows midpoints samples bridges index.castSucc)
        (separation.cellSourceFrame windows midpoints samples bridges index.succ)) //
    ∀ index : Fin separation.subdivisionCount, joins.get index =
      separation.cellJoin windows midpoints samples bridges index}

/-- Materialize each original constant endpoint comparison once from the retained shared samples and bridges. -/
@[expose] def prepareSubdivisionJoins {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) :
    SubdivisionJoins separation windows midpoints samples bridges :=
  ⟨Vector.DependentVector.ofFn (separation.cellJoin windows midpoints samples bridges),
    fun index => Vector.DependentVector.ofFn_get _ index⟩

/-- Fold the same stored original moving segments and endpoint comparisons into the original certified path.

The exact cell source and target frames index the finite fold. It consumes
the supplied stored segments and comparisons in traversal order, keeping
both endpoint owner families and all original geometry and clearance data.
-/
@[expose] def subdivisionPath {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows)
    (pieces : SubdivisionSegments separation windows midpoints samples bridges)
    (joins : SubdivisionJoins separation windows midpoints samples bridges) :
    Paths.Path (separation.cellSourceFrame windows midpoints samples bridges 0)
      (separation.cellTargetFrame windows midpoints samples bridges
        ⟨separation.subdivisionCount, Nat.lt_succ_self separation.subdivisionCount⟩) :=
  Paths.Path.ofJoinedSegments separation.subdivisionCount
    (fun index => segment.pointAt (separation.subdivisionCell index).lower)
    (fun index => segment.pointAt (separation.subdivisionCell index).upper)
    (separation.cellSourceFrame windows midpoints samples bridges)
    (separation.cellTargetFrame windows midpoints samples bridges) pieces.val.get joins.val.get

/-- The original stored-cell path has one moving step per cell and one comparison per shared midpoint. -/
theorem subdivisionPath_stepCount {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows)
    (pieces : SubdivisionSegments separation windows midpoints samples bridges)
    (joins : SubdivisionJoins separation windows midpoints samples bridges) :
    (separation.subdivisionPath windows midpoints samples bridges pieces joins).stepCount =
      2 * separation.subdivisionCount + 1 :=
  Paths.Path.ofJoinedSegments_stepCount separation.subdivisionCount _ _ _ _ pieces.val.get joins.val.get

/-- The same actual separated moving-cell and comparison caches contribute the empty braid word.

Complete cache readbacks identify each original cell and join. Their actual
stationary event laws apply to those same stored segments, so the structural
fold proves emptiness without dropping any geometric or owner comparison.
-/
theorem subdivisionPath_word_nil {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows)
    (pieces : SubdivisionSegments separation windows midpoints samples bridges)
    (joins : SubdivisionJoins separation windows midpoints samples bridges) :
    (separation.subdivisionPath windows midpoints samples bridges pieces joins).word = [] := by
  apply Paths.Path.ofJoinedSegments_word_nil separation.subdivisionCount _ _ _ _ pieces.val.get joins.val.get
  · intro index
    rewrite [pieces.property index]
    exact separation.cellSegment_event windows midpoints samples bridges index
  · intro index
    rewrite [joins.property index]
    exact separation.cellJoin_event windows midpoints samples bridges index

/-- The actual cached moving-cell and comparison fold traverses the complete original axis interval in order.

Each stored segment and join retains its exact original cell restriction.
The original unit-grid bounds and shared cut equalities prove the ordered
physical refinement, with the same retained frame and geometry families.
-/
theorem subdivisionPath_refinesAxis {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows)
    (pieces : SubdivisionSegments separation windows midpoints samples bridges)
    (joins : SubdivisionJoins separation windows midpoints samples bridges) :
    (separation.subdivisionPath windows midpoints samples bridges pieces joins).RefinesAxis segment 0 1 := by
  have original := Paths.Path.ofJoinedSegments_refinesAxis segment separation.subdivisionCount
    (fun index => (separation.subdivisionCell index).lower) (fun index => (separation.subdivisionCell index).upper)
    (separation.cellSourceFrame windows midpoints samples bridges)
    (separation.cellTargetFrame windows midpoints samples bridges) pieces.val.get joins.val.get
    (fun index => (Grid.Unit.cell_bounds separation.subdivisionCount_positive index).2.1.le)
    (by
      intro index
      rewrite [Grid.Unit.cell_upper_one separation.subdivisionCount_positive
        ⟨separation.subdivisionCount, Nat.lt_succ_self separation.subdivisionCount⟩ rfl]
      exact (Grid.Unit.cell_bounds separation.subdivisionCount_positive index).2.2)
    (by
      intro index
      rewrite [Grid.Unit.cell_adjacent separation.subdivisionCount_positive index]
      exact Basic.le_refl _)
    (by
      intro index parameter
      rewrite [pieces.property index, separation.cellSegment_geometry windows midpoints samples bridges index]
      exact segment.restrict_pointAt _ _ parameter)
    (by
      intro index parameter
      rewrite [joins.property index, separation.cellJoin_geometry windows midpoints samples bridges index]
      exact segment.restrict_pointAt _ _ parameter)
  exact original.castCuts segment
    (Grid.Unit.cell_lower_zero separation.subdivisionCount_positive 0 rfl)
    (Grid.Unit.cell_upper_one separation.subdivisionCount_positive
      ⟨separation.subdivisionCount, Nat.lt_succ_self separation.subdivisionCount⟩ rfl)

/-- The first computed ordered cell starts at the original axis source parameter. -/
theorem subdivisionSource_eq {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) :
    segment.pointAt (separation.subdivisionCell 0).lower = start := by
  rewrite [Grid.Unit.cell_lower_zero separation.subdivisionCount_positive 0 rfl]
  exact segment.pointAt_zero

/-- The last computed ordered cell ends at the original axis target parameter. -/
theorem subdivisionTarget_eq {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) :
    segment.pointAt (separation.subdivisionCell
      ⟨separation.subdivisionCount, Nat.lt_succ_self separation.subdivisionCount⟩).upper = finish := by
  rewrite [Grid.Unit.cell_upper_one separation.subdivisionCount_positive _ rfl]
  exact segment.pointAt_one

/-- Read the retained first-cell source frame at the same original axis source parameter. -/
@[expose] def subdivisionSourceFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) : Paths.Frame start :=
  (separation.cellSourceFrame windows midpoints samples bridges 0).castParameter separation.subdivisionSource_eq

/-- Read the retained last-cell target frame at the same original axis target parameter. -/
@[expose] def subdivisionTargetFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows) : Paths.Frame finish :=
  (separation.cellTargetFrame windows midpoints samples bridges
    ⟨separation.subdivisionCount, Nat.lt_succ_self separation.subdivisionCount⟩).castParameter
      separation.subdivisionTarget_eq

/-- Read the original stored-cell path at the same original axis endpoints and retained owner frames. -/
@[expose] def subdivisionEndpointPath {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows)
    (pieces : SubdivisionSegments separation windows midpoints samples bridges)
    (joins : SubdivisionJoins separation windows midpoints samples bridges) :
    Paths.Path (separation.subdivisionSourceFrame windows midpoints samples bridges)
      (separation.subdivisionTargetFrame windows midpoints samples bridges) :=
  (separation.subdivisionPath windows midpoints samples bridges pieces joins).castParameters
    separation.subdivisionSource_eq separation.subdivisionTarget_eq

/-- Original endpoint reindexing preserves every moving cell and comparison in the stored subdivision path. -/
theorem subdivisionEndpointPath_stepCount {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows)
    (pieces : SubdivisionSegments separation windows midpoints samples bridges)
    (joins : SubdivisionJoins separation windows midpoints samples bridges) :
    (separation.subdivisionEndpointPath windows midpoints samples bridges pieces joins).stepCount =
      2 * separation.subdivisionCount + 1 :=
  (Paths.Path.castParameters_stepCount _ separation.subdivisionSource_eq separation.subdivisionTarget_eq).trans
    (separation.subdivisionPath_stepCount windows midpoints samples bridges pieces joins)

/-- Exact endpoint reindexing preserves the empty word of the same stored separated path. -/
theorem subdivisionEndpointPath_word_nil {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows)
    (pieces : SubdivisionSegments separation windows midpoints samples bridges)
    (joins : SubdivisionJoins separation windows midpoints samples bridges) :
    (separation.subdivisionEndpointPath windows midpoints samples bridges pieces joins).word = [] :=
  (Paths.Path.castParameters_word _ separation.subdivisionSource_eq separation.subdivisionTarget_eq).trans
    (separation.subdivisionPath_word_nil windows midpoints samples bridges pieces joins)

/-- Exact original endpoint transport preserves the same complete ordered physical subdivision refinement. -/
theorem subdivisionEndpointPath_refinesAxis {start finish : Gaussian} {segment : AxisSegment start finish}
    {slope : Coordinate} (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation)
    (midpoints : MidpointSamples separation windows) (samples : SubdivisionSamples separation windows midpoints)
    (bridges : SubdivisionBridges separation windows)
    (pieces : SubdivisionSegments separation windows midpoints samples bridges)
    (joins : SubdivisionJoins separation windows midpoints samples bridges) :
    (separation.subdivisionEndpointPath windows midpoints samples bridges pieces joins).RefinesAxis segment 0 1 :=
  (separation.subdivisionPath_refinesAxis windows midpoints samples bridges pieces joins).castParameters segment
    separation.subdivisionSource_eq separation.subdivisionTarget_eq

/-- Complete original preparation caches and the retained certified path at the same original axis endpoints.

The dependent packet retains the shared midpoint samples, cell endpoint
views, moving bridges, segments and joins from the same supplied window
cache. The final path has complete readback to the fold of those actual
stored pieces and comparisons, transported only by endpoint equalities.
-/
abbrev PreparedSubdivision {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation) :=
  Σ midpoints : MidpointSamples separation windows,
  Σ samples : SubdivisionSamples separation windows midpoints,
  Σ bridges : SubdivisionBridges separation windows,
  Σ pieces : SubdivisionSegments separation windows midpoints samples bridges,
  Σ joins : SubdivisionJoins separation windows midpoints samples bridges,
    {path : Paths.Path (separation.subdivisionSourceFrame windows midpoints samples bridges)
        (separation.subdivisionTargetFrame windows midpoints samples bridges) //
      path = separation.subdivisionEndpointPath windows midpoints samples bridges pieces joins}

/-- Prepare and retain each original subdivision cache and its folded certified path exactly once.

Every stage consumes the same earlier retained objects. The final fold
reads the materialized segment and comparison vectors, and endpoint
equality transports its original frames to the original axis parameters.
-/
@[expose] def prepareSubdivision {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    (separation : ProjectionSeparation segment slope) (windows : SubdivisionWindows separation) :
    PreparedSubdivision separation windows :=
  let midpoints := separation.prepareMidpointSamples windows
  let samples := separation.prepareSubdivisionSamples windows midpoints
  let bridges := separation.prepareSubdivisionBridges windows
  let pieces := separation.prepareSubdivisionSegments windows midpoints samples bridges
  let joins := separation.prepareSubdivisionJoins windows midpoints samples bridges
  let path := separation.subdivisionEndpointPath windows midpoints samples bridges pieces joins
  ⟨midpoints, samples, bridges, pieces, joins, path, rfl⟩

namespace PreparedSubdivision

/-- Read the actual stored original shared midpoint frames and both neighboring-window views. -/
@[expose] def midpoints {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : MidpointSamples separation windows := prepared.1

/-- Read the actual stored original source and target sample views of every ordered cell. -/
@[expose] def samples {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) :
    SubdivisionSamples separation windows prepared.midpoints := prepared.2.1

/-- Read the actual stored original source factors and moving owner bridges of every ordered cell. -/
@[expose] def bridges {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : SubdivisionBridges separation windows := prepared.2.2.1

/-- Read the same original moving segment vector retained by automatic preparation. -/
@[expose] def pieces {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) :
    SubdivisionSegments separation windows prepared.midpoints prepared.samples prepared.bridges := prepared.2.2.2.1

/-- Read the same original constant endpoint-comparison vector retained by automatic preparation. -/
@[expose] def joins {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) :
    SubdivisionJoins separation windows prepared.midpoints prepared.samples prepared.bridges := prepared.2.2.2.2.1

/-- Read the same original source frame at the original axis source parameter. -/
@[expose] def sourceFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : Paths.Frame start :=
  separation.subdivisionSourceFrame windows prepared.midpoints prepared.samples prepared.bridges

/-- Read the same original target frame at the original axis target parameter. -/
@[expose] def targetFrame {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : Paths.Frame finish :=
  separation.subdivisionTargetFrame windows prepared.midpoints prepared.samples prepared.bridges

/-- The retained source frame has the original displayed chart after its exact endpoint transport. -/
theorem sourceFrame_slope {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : prepared.sourceFrame.projectionSlope = slope := by
  let frame := separation.cellSourceFrame windows prepared.midpoints prepared.samples prepared.bridges 0
  exact (frame.castParameter_slope separation.subdivisionSource_eq).trans
    ((prepared.bridges.val.get 0).sourceFrame_slope (prepared.samples.val.get 0).1
      (separation.subdivisionCell_endpoints windows 0).1)

/-- The retained target frame has the original displayed chart after its exact endpoint transport. -/
theorem targetFrame_slope {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : prepared.targetFrame.projectionSlope = slope := by
  let index : Fin (separation.subdivisionCount + 1) :=
    ⟨separation.subdivisionCount, Nat.lt_succ_self separation.subdivisionCount⟩
  let frame := separation.cellTargetFrame windows prepared.midpoints prepared.samples prepared.bridges index
  exact (frame.castParameter_slope separation.subdivisionTarget_eq).trans
    ((prepared.bridges.val.get index).targetFrame_slope (prepared.samples.val.get index).2
      (separation.subdivisionCell_endpoints windows index).2)

/-- Each retained source projection position selects the actual logical branch at the original axis source. -/
theorem sourceFrame_logicalOrder {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) (position : Fin 3) :
    prepared.sourceFrame.labels.backward (prepared.sourceFrame.projectionOrder.forward position) =
      (branchOrder start slope).forward position := by
  let frame := separation.cellSourceFrame windows prepared.midpoints prepared.samples prepared.bridges 0
  have original := (prepared.bridges.val.get 0).sourceFrame_logicalOrder (prepared.samples.val.get 0).1
    (separation.subdivisionCell_endpoints windows 0).1 position
  exact (frame.castParameter_logicalOrder separation.subdivisionSource_eq position).trans
    (original.trans (congrArg (fun parameter => (branchOrder parameter slope).forward position)
      separation.subdivisionSource_eq))

/-- Each retained target projection position selects the actual logical branch at the original axis target. -/
theorem targetFrame_logicalOrder {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) (position : Fin 3) :
    prepared.targetFrame.labels.backward (prepared.targetFrame.projectionOrder.forward position) =
      (branchOrder finish slope).forward position := by
  let index : Fin (separation.subdivisionCount + 1) :=
    ⟨separation.subdivisionCount, Nat.lt_succ_self separation.subdivisionCount⟩
  let frame := separation.cellTargetFrame windows prepared.midpoints prepared.samples prepared.bridges index
  have original := (prepared.bridges.val.get index).targetFrame_logicalOrder (prepared.samples.val.get index).2
    (separation.subdivisionCell_endpoints windows index).2 position
  exact (frame.castParameter_logicalOrder separation.subdivisionTarget_eq position).trans
    (original.trans (congrArg (fun parameter => (branchOrder parameter slope).forward position)
      separation.subdivisionTarget_eq))

/-- The actual retained source frame presents the original displayed chart at the original axis source. -/
theorem sourceFrame_inChart {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : prepared.sourceFrame.InChart slope :=
  Paths.Frame.InChart.ofReadings prepared.sourceFrame_slope prepared.sourceFrame_logicalOrder

/-- The actual retained target frame presents the original displayed chart at the original axis target. -/
theorem targetFrame_inChart {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : prepared.targetFrame.InChart slope :=
  Paths.Frame.InChart.ofReadings prepared.targetFrame_slope prepared.targetFrame_logicalOrder

/-- Read the actual stored certified path rather than folding or preparing its retained data again. -/
@[expose] def path {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : Paths.Path prepared.sourceFrame prepared.targetFrame :=
  prepared.2.2.2.2.2.val

/-- The stored certified path is the complete original fold of those same retained segments and comparisons. -/
theorem path_eq {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) :
    prepared.path = separation.subdivisionEndpointPath windows prepared.midpoints prepared.samples prepared.bridges
      prepared.pieces prepared.joins := prepared.2.2.2.2.2.property

/-- The actual stored separated path has no braid crossings, including every retained owner-comparison step. -/
theorem path_word_nil {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : prepared.path.word = [] := by
  rewrite [prepared.path_eq]
  exact separation.subdivisionEndpointPath_word_nil windows prepared.midpoints prepared.samples prepared.bridges
    prepared.pieces prepared.joins

/-- The actual stored path is an ordered physical refinement of the same original complete axis segment. -/
theorem path_refinesAxis {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) : prepared.path.RefinesAxis segment 0 1 := by
  rewrite [prepared.path_eq]
  exact separation.subdivisionEndpointPath_refinesAxis windows prepared.midpoints prepared.samples prepared.bridges
    prepared.pieces prepared.joins

/-- The stored path retains the internally computed number of original moving cells and midpoint comparisons. -/
theorem path_stepCount {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : ProjectionSeparation segment slope} {windows : SubdivisionWindows separation}
    (prepared : PreparedSubdivision separation windows) :
    prepared.path.stepCount = 2 * separation.subdivisionCount + 1 := by
  rewrite [prepared.path_eq]
  exact separation.subdivisionEndpointPath_stepCount windows prepared.midpoints prepared.samples prepared.bridges
    prepared.pieces prepared.joins

end PreparedSubdivision

end Purelib.Curves.Legendre.Paths.AxisSegment.ProjectionSeparation

namespace Purelib.Curves.Legendre.Paths.AxisSegment

/-- Compute a finite original owner-window cover in a displayed chart, or retain an actual projected collision.

The original endpoint checks compute both clearances internally.
A separated chart derives the uniform count and materializes its
same original windows. A collision outcome retains the original
parameter witness; it is a chart event rather than physical invalidity.
-/
@[expose] def prepareProjectionWindows {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope : Coordinate) :
    (ProjectionCollision segment slope 0 ⊕ ProjectionCollision segment slope 1) ⊕
      (Σ separation : ProjectionSeparation segment slope, separation.SubdivisionWindows) :=
  match segment.checkProjectionSeparation slope with
  | .inl collision => .inl collision
  | .inr separation => .inr ⟨separation, separation.prepareSubdivisionWindows⟩

/-- Prepare the original path in a displayed separating chart, or retain its actual projected collision.

The original chart checker derives both quantitative clearances and the
same finite window budget internally. Success retains all original caches
and the certified path at the original axis endpoints. A collision identifies
an actual chart tie and does not assert physical singularity of the path.
-/
@[expose] def prepareProjectionPath {start finish : Gaussian} (segment : AxisSegment start finish)
    (slope : Coordinate) :
    (ProjectionCollision segment slope 0 ⊕ ProjectionCollision segment slope 1) ⊕
      (Σ separation : ProjectionSeparation segment slope,
        Σ windows : separation.SubdivisionWindows, separation.PreparedSubdivision windows) :=
  match segment.prepareProjectionWindows slope with
  | .inl collision => .inl collision
  | .inr ⟨separation, windows⟩ => .inr ⟨separation, windows, separation.prepareSubdivision windows⟩

end Purelib.Curves.Legendre.Paths.AxisSegment
