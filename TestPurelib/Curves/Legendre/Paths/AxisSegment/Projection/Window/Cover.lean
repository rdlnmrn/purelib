module

import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Cover
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Stationary
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Separation
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Samples
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Overlap
import Purelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Bridges
import Purelib.Curves.Legendre.Paths.AxisSegment.Window
import Purelib.RootIsolation.Owner.Local.Transport
import Purelib.RootIsolation.Owner.Bridge.Basic
import Purelib.RootIsolation.Progressive.Braid.Projected.Overlap
import Purelib.Topology.Knot.Braid.Event
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Paths.Frame
import Purelib.Curves.Legendre.Paths.Path
import Purelib.Curves.Legendre.Paths.Path.Refinement
import Purelib.Approximation.Rational.Grid.Unit
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent

/-! # Cached original window coverage without a caller subdivision certificate -/

namespace TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Cover

open Purelib.Curves.Legendre.Paths
open Purelib.Approximation.Rational
open Purelib.RootIsolation
open AxisSegment.ProjectionCollision

/-- An original separated horizontal segment has an internally computed finite cover. -/
def original : AxisSegment (gaussian (1 / 4) 1) (gaussian (3 / 4) 1) := .horizontal (1 / 4) (3 / 4) 1

/-- The original checker absence outcomes retain both exact endpoint clearances. -/
def separation : original.ProjectionSeparation 0 :=
  ⟨AxisSegment.ProjectionClearance.ofNotContained original 0 0 (by decide +kernel),
    AxisSegment.ProjectionClearance.ofNotContained original 0 1 (by decide +kernel)⟩

/-- Materialize the actual original grid windows with their frame, side and radius caches. -/
def retained : separation.SubdivisionWindows := separation.prepareSubdivisionWindows

/-- Read a successfully computed cover count without supplying any projection-clearance or subdivision certificate. -/
def computedCount {start finish : Gaussian} (segment : AxisSegment start finish) (slope : Coordinate) : Option Nat :=
  match segment.prepareProjectionWindows slope with
  | .inl _ => none
  | .inr prepared => some prepared.1.subdivisionCount

/-- The intrinsic pipeline computes the same finite cover budget from the original separated segment alone. -/
example : computedCount original 0 = some 1441 := by decide +kernel

/-- The intrinsic pipeline retains a projected tie as its original collision outcome. -/
example : computedCount (AxisSegment.horizontal (-1 / 8) (1 / 8) 1) 0 = none := by decide +kernel

/-- Every retained cache entry has its complete original constructor readback. -/
example (index : Fin (separation.subdivisionCount + 1)) :
    retained.val index = ⟨index, separation.subdivisionWindow index⟩ := retained.property index

/-- Every original unit parameter is contained in an actual entry of the same retained cache. -/
example (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (retained.val (separation.coveringWindow retained parameter inside).val).2.parameters.Contains parameter :=
  (separation.coveringWindow retained parameter inside).property

/-- Cover selection retains the exact original nearest-node index. -/
example (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (separation.coveringWindow retained parameter inside).val =
      Grid.Unit.nearestIndex parameter separation.subdivisionCount_positive inside :=
  separation.coveringWindow_index retained parameter inside

/-- Both actual cached neighboring windows contain the same original path midpoint. -/
example (index : Fin separation.subdivisionCount) :
    (retained.val index.castSucc).2.parameters.Contains (Grid.Unit.midpoint separation.subdivisionCount index) ∧
      (retained.val index.succ).2.parameters.Contains (Grid.Unit.midpoint separation.subdivisionCount index) :=
  separation.retainedWindows_midpoint retained index

/-- The two original cached neighboring-window views retain one identical complete sample frame. -/
example (index : Fin separation.subdivisionCount) :
    (separation.midpointSamples retained index).val.1.val = (separation.midpointSamples retained index).val.2.val :=
  (separation.midpointSamples retained index).property

/-- Every original logical branch of that shared sample refines the actual left cached window owner. -/
example (index : Fin separation.subdivisionCount) (label : Fin 3) :
    ((separation.midpointSamples retained index).val.1.val.rootOwner label).box.Refines
      ((retained.val index.castSucc).2.frame.rootOwner label).box :=
  (separation.midpointSamples retained index).val.1.property.2.2.1 label

/-- The same shared sample refines every original logical branch of the actual right cached window owner. -/
example (index : Fin separation.subdivisionCount) (label : Fin 3) :
    ((separation.midpointSamples retained index).val.2.val.rootOwner label).box.Refines
      ((retained.val index.succ).2.frame.rootOwner label).box :=
  (separation.midpointSamples retained index).val.2.property.2.2.1 label

/-- Join the original endpoint frames of actual neighboring cached bridge families at their shared grid midpoint. -/
def joinAt (index : Fin separation.subdivisionCount) {source target : Coordinate}
    (leftBridges : OwnerWindow.BridgesAt (retained.val index.castSucc).2 source
      (Grid.Unit.midpoint separation.subdivisionCount index))
    (rightBridges : OwnerWindow.BridgesAt (retained.val index.succ).2
      (Grid.Unit.midpoint separation.subdivisionCount index) target) :
    Segment (leftBridges.targetFrame (separation.midpointSamples retained index).val.1
      (separation.retainedWindows_midpoint retained index).1)
      (rightBridges.sourceFrame (separation.midpointSamples retained index).val.2
        (separation.retainedWindows_midpoint retained index).2) :=
  (separation.midpointSamples retained index).joinBridges
    (separation.retainedWindows_midpoint retained index).1 (separation.retainedWindows_midpoint retained index).2
    leftBridges rightBridges

/-- The actual cached-frame join retains the original axis geometry at its same grid midpoint. -/
example (index : Fin separation.subdivisionCount) {source target : Coordinate}
    (leftBridges : OwnerWindow.BridgesAt (retained.val index.castSucc).2 source
      (Grid.Unit.midpoint separation.subdivisionCount index))
    (rightBridges : OwnerWindow.BridgesAt (retained.val index.succ).2
      (Grid.Unit.midpoint separation.subdivisionCount index) target) :
    (joinAt index leftBridges rightBridges).geometry = original.restrict
      (Grid.Unit.midpoint separation.subdivisionCount index) (Grid.Unit.midpoint separation.subdivisionCount index) :=
  (separation.midpointSamples retained index).joinBridges_geometry
    (separation.retainedWindows_midpoint retained index).1 (separation.retainedWindows_midpoint retained index).2
    leftBridges rightBridges

/-- Joining the actual original cached endpoint frames contributes a stationary projected event. -/
example (index : Fin separation.subdivisionCount) {source target : Coordinate}
    (leftBridges : OwnerWindow.BridgesAt (retained.val index.castSucc).2 source
      (Grid.Unit.midpoint separation.subdivisionCount index))
    (rightBridges : OwnerWindow.BridgesAt (retained.val index.succ).2
      (Grid.Unit.midpoint separation.subdivisionCount index) target) :
    (joinAt index leftBridges rightBridges).projection.event = .stationary := rfl

/-- Each original cached-frame join retains the same actual common-sample owner box as its comparison bridge. -/
example (index : Fin separation.subdivisionCount) {source target : Coordinate}
    (leftBridges : OwnerWindow.BridgesAt (retained.val index.castSucc).2 source
      (Grid.Unit.midpoint separation.subdivisionCount index))
    (rightBridges : OwnerWindow.BridgesAt (retained.val index.succ).2
      (Grid.Unit.midpoint separation.subdivisionCount index) target) (label : Fin 3) :
    ((joinAt index leftBridges rightBridges).projection.chamberOverlap.bridge
      ((leftBridges.targetFrame (separation.midpointSamples retained index).val.1
        (separation.retainedWindows_midpoint retained index).1).labels.forward label)).box =
          ((separation.midpointSamples retained index).val.1.val.rootOwner label).box :=
  (separation.midpointSamples retained index).chamberOverlap_bridge_box
    (separation.retainedWindows_midpoint retained index).1 (separation.retainedWindows_midpoint retained index).2
    (fun entry => (leftBridges.get entry).rightOwner) (fun entry => (rightBridges.get entry).leftOwner)
    (fun entry => leftBridges.get_box entry) (fun entry => rightBridges.get_box entry) label

/-- The left compared frame retains the complete actual right owner of its original cached bridge at each label. -/
example (index : Fin separation.subdivisionCount) {source : Coordinate}
    (leftBridges : OwnerWindow.BridgesAt (retained.val index.castSucc).2 source
      (Grid.Unit.midpoint separation.subdivisionCount index)) (label : Fin 3) :
    ((leftBridges.targetFrame (separation.midpointSamples retained index).val.1
      (separation.retainedWindows_midpoint retained index).1).rootOwner label) =
      Owner.Local.Transport.castOwner (separation.midpointSamples retained index).val.1.val.polynomial_eq.symm
        (leftBridges.get label).rightOwner := leftBridges.targetFrame_rootOwner _ _ label

/-- The right compared frame retains the complete actual left owner of its original cached bridge at each label. -/
example (index : Fin separation.subdivisionCount) {target : Coordinate}
    (rightBridges : OwnerWindow.BridgesAt (retained.val index.succ).2
      (Grid.Unit.midpoint separation.subdivisionCount index) target) (label : Fin 3) :
    ((rightBridges.sourceFrame (separation.midpointSamples retained index).val.2
      (separation.retainedWindows_midpoint retained index).2).rootOwner label) =
      Owner.Local.Transport.castOwner (separation.midpointSamples retained index).val.2.val.polynomial_eq.symm
        (rightBridges.get label).leftOwner := rightBridges.sourceFrame_rootOwner _ _ label

/-- Any two retained points of a cached subdivision window produce their actual original safe segment.

The original samples and bridge family remain the supplied caches.
Window safety and projected branch-order agreement are derived internally.
-/
def restrictAt (index : Fin (separation.subdivisionCount + 1)) {source target : Coordinate}
    (bridges : OwnerWindow.BridgesAt (retained.val index).2 source target)
    (sourceSamples : OwnerWindow.SamplesAt (retained.val index).2 source)
    (targetSamples : OwnerWindow.SamplesAt (retained.val index).2 target)
    (sourceInside : (retained.val index).2.parameters.Contains source)
    (targetInside : (retained.val index).2.parameters.Contains target) :
    Segment (bridges.sourceFrame sourceSamples sourceInside) (bridges.targetFrame targetSamples targetInside) :=
  separation.subdivisionSegment retained index bridges sourceSamples targetSamples sourceInside targetInside

/-- Every actual point of a computed ordered cell lies in its same retained original owner window. -/
example (index : Fin (separation.subdivisionCount + 1)) (parameter : Coordinate)
    (inside : (separation.subdivisionCell index).Contains parameter) :
    (retained.val index).2.parameters.Contains parameter :=
  separation.subdivisionCell_contains retained index parameter inside

/-- Both actual cell endpoints are retained in the same original cached owner window. -/
example (index : Fin (separation.subdivisionCount + 1)) :
    (retained.val index).2.parameters.Contains (separation.subdivisionCell index).lower ∧
      (retained.val index).2.parameters.Contains (separation.subdivisionCell index).upper :=
  separation.subdivisionCell_endpoints retained index

/-- Every materialized midpoint retains the full shared frame and both original window views of its constructor. -/
example (index : Fin separation.subdivisionCount) :
    (separation.prepareMidpointSamples retained).val.get index = separation.midpointSamples retained index :=
  (separation.prepareMidpointSamples retained).property index

/-- Reading a retained successor endpoint reuses the complete right-window view of its actual midpoint cache. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (index : Fin separation.subdivisionCount) :
    ((samples.val.get index.succ).1).castParameter
        (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index) =
      (midpoints.val.get index).val.2 :=
  separation.subdivisionSamples_source_midpoint retained midpoints samples index

/-- Reading a retained nonfinal endpoint reuses the complete left-window view of its actual midpoint cache. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (index : Fin separation.subdivisionCount) :
    ((samples.val.get index.castSucc).2).castParameter
        (Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive index) =
      (midpoints.val.get index).val.1 :=
  separation.subdivisionSamples_target_midpoint retained midpoints samples index

/-- Actual neighboring cell endpoints retain one identical sample frame after their exact grid transports. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (index : Fin separation.subdivisionCount) :
    (((samples.val.get index.castSucc).2).castParameter
        (Grid.Unit.cell_upper_midpoint separation.subdivisionCount_positive index)).val =
      (((samples.val.get index.succ).1).castParameter
        (Grid.Unit.cell_lower_midpoint separation.subdivisionCount_positive index)).val := by
  rewrite [separation.subdivisionSamples_target_midpoint retained midpoints samples index,
    separation.subdivisionSamples_source_midpoint retained midpoints samples index]
  exact (midpoints.val.get index).property

/-- The endpoint cache preserves its complete constructor pair at every actual retained cell. -/
example (midpoints : separation.MidpointSamples retained) (index : Fin (separation.subdivisionCount + 1)) :
    (separation.prepareSubdivisionSamples retained midpoints).val.get index =
      (separation.cellSourceSamples retained midpoints index,
        separation.cellTargetSamples retained midpoints index) :=
  (separation.prepareSubdivisionSamples retained midpoints).property index

/-- Materializing a cell bridge retains its complete original source-factor and owner-bridge packet. -/
example (index : Fin (separation.subdivisionCount + 1)) :
    (separation.prepareSubdivisionBridges retained).val.get index = separation.cellBridges retained index :=
  (separation.prepareSubdivisionBridges retained).property index

/-- The actual stored sample and bridge packets produce the original restriction to the same ordered cell. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (index : Fin (separation.subdivisionCount + 1)) :
    (separation.cellSegment retained midpoints samples bridges index).geometry =
      original.restrict (separation.subdivisionCell index).lower (separation.subdivisionCell index).upper :=
  separation.cellSegment_geometry retained midpoints samples bridges index

/-- The actual moving cell's source retains the whole left owner record of its original stored bridge. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (index : Fin (separation.subdivisionCount + 1)) (label : Fin 3) :
    ((bridges.val.get index).sourceFrame (samples.val.get index).1
        (separation.subdivisionCell_endpoints retained index).1).rootOwner label =
      Owner.Local.Transport.castOwner (samples.val.get index).1.val.polynomial_eq.symm
        ((bridges.val.get index).get label).leftOwner :=
  (bridges.val.get index).sourceFrame_rootOwner _ _ label

/-- The actual moving cell's target retains the whole right owner record of its original stored bridge. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (index : Fin (separation.subdivisionCount + 1)) (label : Fin 3) :
    ((bridges.val.get index).targetFrame (samples.val.get index).2
        (separation.subdivisionCell_endpoints retained index).2).rootOwner label =
      Owner.Local.Transport.castOwner (samples.val.get index).2.val.polynomial_eq.symm
        ((bridges.val.get index).get label).rightOwner :=
  (bridges.val.get index).targetFrame_rootOwner _ _ label

/-- The actual adjacent-cell comparison keeps the complete original restriction between their equal endpoints. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (index : Fin separation.subdivisionCount) :
    (separation.cellJoin retained midpoints samples bridges index).geometry =
      original.restrict (separation.subdivisionCell index.castSucc).upper
        (separation.subdivisionCell index.succ).lower :=
  separation.cellJoin_geometry retained midpoints samples bridges index

/-- All parameters of the actual retained adjacent-cell comparison have the same original shared-midpoint geometry. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (index : Fin separation.subdivisionCount) (parameter : Coordinate) :
    (separation.cellJoin retained midpoints samples bridges index).geometry.pointAt parameter =
      original.pointAt (Grid.Unit.midpoint separation.subdivisionCount index) :=
  separation.cellJoin_pointAt retained midpoints samples bridges index parameter

/-- The actual adjacent-cell comparison derives its stationary event from the retained shared views. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (index : Fin separation.subdivisionCount) :
    (separation.cellJoin retained midpoints samples bridges index).projection.event = .stationary :=
  separation.cellJoin_event retained midpoints samples bridges index

/-- Every stored original moving segment retains its complete cached constructor result. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (index : Fin (separation.subdivisionCount + 1)) :
    (separation.prepareSubdivisionSegments retained midpoints samples bridges).val.get index =
      separation.cellSegment retained midpoints samples bridges index :=
  (separation.prepareSubdivisionSegments retained midpoints samples bridges).property index

/-- Every stored original endpoint comparison retains its complete cached constructor result. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (index : Fin separation.subdivisionCount) :
    (separation.prepareSubdivisionJoins retained midpoints samples bridges).val.get index =
      separation.cellJoin retained midpoints samples bridges index :=
  (separation.prepareSubdivisionJoins retained midpoints samples bridges).property index

/-- Folding the actual stored moving pieces and endpoint comparisons retains the internally computed step count. -/
example (midpoints : separation.MidpointSamples retained)
    (samples : separation.SubdivisionSamples retained midpoints) (bridges : separation.SubdivisionBridges retained)
    (pieces : separation.SubdivisionSegments retained midpoints samples bridges)
    (joins : separation.SubdivisionJoins retained midpoints samples bridges) :
    (separation.subdivisionPath retained midpoints samples bridges pieces joins).stepCount =
      2 * separation.subdivisionCount + 1 :=
  separation.subdivisionPath_stepCount retained midpoints samples bridges pieces joins

/-- The complete automatic preparation packet is constructed from the same original retained window cache. -/
def prepareRetained : separation.PreparedSubdivision retained := separation.prepareSubdivision retained

/-- Reading the retained source frame uses the original axis source parameter type. -/
def preparedSource (prepared : separation.PreparedSubdivision retained) : Frame (gaussian (1 / 4) 1) :=
  prepared.sourceFrame

/-- Reading the retained target frame uses the original axis target parameter type. -/
def preparedTarget (prepared : separation.PreparedSubdivision retained) : Frame (gaussian (3 / 4) 1) :=
  prepared.targetFrame

/-- Reading the actual stored path retains the original axis endpoint indices and the same cached owner frames. -/
def preparedPath (prepared : separation.PreparedSubdivision retained) :
    Path (preparedSource prepared) (preparedTarget prepared) := prepared.path

/-- The original endpoint reindexing certifies the internally computed number of retained path steps. -/
example (prepared : separation.PreparedSubdivision retained) :
    (preparedPath prepared).stepCount = 2 * separation.subdivisionCount + 1 := prepared.path_stepCount

/-- The actual stored path has complete readback to the fold of its same original materialized pieces and joins. -/
example (prepared : separation.PreparedSubdivision retained) :
    prepared.path = separation.subdivisionEndpointPath retained prepared.midpoints prepared.samples prepared.bridges
      prepared.pieces prepared.joins := prepared.path_eq

/-- The actual retained midpoint lookup has complete original shared-sample packet readback. -/
example (prepared : separation.PreparedSubdivision retained) (index : Fin separation.subdivisionCount) :
    prepared.midpoints.val.get index = separation.midpointSamples retained index := prepared.midpoints.property index

/-- The actual retained endpoint-sample lookup consumes those same stored original shared-midpoint views. -/
example (prepared : separation.PreparedSubdivision retained) (index : Fin (separation.subdivisionCount + 1)) :
    prepared.samples.val.get index =
      (separation.cellSourceSamples retained prepared.midpoints index,
        separation.cellTargetSamples retained prepared.midpoints index) := prepared.samples.property index

/-- The actual retained moving-bridge lookup has complete original source-factor and owner-bridge packet readback. -/
example (prepared : separation.PreparedSubdivision retained) (index : Fin (separation.subdivisionCount + 1)) :
    prepared.bridges.val.get index = separation.cellBridges retained index := prepared.bridges.property index

/-- The actual retained moving-segment lookup preserves its full constructor with the same sample and bridge caches. -/
example (prepared : separation.PreparedSubdivision retained) (index : Fin (separation.subdivisionCount + 1)) :
    prepared.pieces.val.get index = separation.cellSegment retained prepared.midpoints prepared.samples
      prepared.bridges index := prepared.pieces.property index

/-- The retained endpoint-comparison lookup preserves its full constructor with the same sample and bridge caches. -/
example (prepared : separation.PreparedSubdivision retained) (index : Fin separation.subdivisionCount) :
    prepared.joins.val.get index = separation.cellJoin retained prepared.midpoints prepared.samples
      prepared.bridges index := prepared.joins.property index

/-- A checked path collision identifies the original unit parameter and the actual violated chart reading. -/
example : ∃ collision : (AxisSegment.horizontal (-1 / 8) (1 / 8) 1).ProjectionCollision 0 0,
    (AxisSegment.horizontal (-1 / 8) (1 / 8) 1).prepareProjectionPath 0 = .inl (.inl collision) := by
  refine ⟨⟨(1 / 2 : Coordinate), by decide +kernel, by decide +kernel⟩, ?_⟩
  rfl

/-- Arbitrary cached subdivision restrictions retain their complete original affine geometry. -/
example (index : Fin (separation.subdivisionCount + 1)) {source target : Coordinate}
    (bridges : OwnerWindow.BridgesAt (retained.val index).2 source target)
    (sourceSamples : OwnerWindow.SamplesAt (retained.val index).2 source)
    (targetSamples : OwnerWindow.SamplesAt (retained.val index).2 target)
    (sourceInside : (retained.val index).2.parameters.Contains source)
    (targetInside : (retained.val index).2.parameters.Contains target) :
    (restrictAt index bridges sourceSamples targetSamples sourceInside targetInside).geometry =
      original.restrict source target := rfl

/-- The same arbitrary cached restriction derives its stationary projected event without an order certificate. -/
example (index : Fin (separation.subdivisionCount + 1)) {source target : Coordinate}
    (bridges : OwnerWindow.BridgesAt (retained.val index).2 source target)
    (sourceSamples : OwnerWindow.SamplesAt (retained.val index).2 source)
    (targetSamples : OwnerWindow.SamplesAt (retained.val index).2 target)
    (sourceInside : (retained.val index).2.parameters.Contains source)
    (targetInside : (retained.val index).2.parameters.Contains target) :
    (restrictAt index bridges sourceSamples targetSamples sourceInside targetInside).projection.event =
      .stationary := rfl

/-- The actual retained separated-path cache refines the same complete original axis interval in order. -/
example (prepared : separation.PreparedSubdivision retained) : prepared.path.RefinesAxis original 0 1 :=
  prepared.path_refinesAxis

/-- Physical refinement identifies the actual endpoint parameters of the same retained separated-path frames. -/
example (prepared : separation.PreparedSubdivision retained) :
    original.pointAt 0 = gaussian (1 / 4) 1 ∧ original.pointAt 1 = gaussian (3 / 4) 1 :=
  prepared.path_refinesAxis.endpoints original

/-- A zero-velocity original segment is admitted by the same intrinsic cover constructor. -/
def stationary : AxisSegment (gaussian (1 / 2) 1) (gaussian (1 / 2) 1) := .horizontal (1 / 2) (1 / 2) 1

/-- The original constant projection supplies its same exact positive clearance pair. -/
def stationarySeparation : stationary.ProjectionSeparation 0 :=
  ⟨AxisSegment.ProjectionClearance.ofNotContained stationary 0 0 (by decide +kernel),
    AxisSegment.ProjectionClearance.ofNotContained stationary 0 1 (by decide +kernel)⟩

/-- Stationary original geometry still yields a computed window containing every unit parameter. -/
example (parameter : Coordinate) (inside : 0 ≤ parameter ∧ parameter ≤ 1) :
    (stationarySeparation.subdivisionWindow (Grid.Unit.nearestIndex parameter
      stationarySeparation.subdivisionCount_positive inside)).parameters.Contains parameter :=
  stationarySeparation.nearestSubdivisionWindow_contains parameter inside

/-- The same retained separated path cache contributes no crossing word, including every actual comparison. -/
example {start finish : Gaussian} {segment : AxisSegment start finish} {slope : Coordinate}
    {separation : segment.ProjectionSeparation slope} {windows : separation.SubdivisionWindows}
    (prepared : separation.PreparedSubdivision windows) : prepared.path.word = [] := prepared.path_word_nil

end TestPurelib.Curves.Legendre.Paths.AxisSegment.Projection.Window.Cover
