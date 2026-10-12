module
import Purelib.Data.List.Map
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
public import Purelib.Integration.Path.IncrementArea
import Init.Data.List.Lemmas
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces

open Purelib.Integration.Path

open Purelib.Polynomial.Geometry.Grid

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathWinding

open Purelib.Riemann.Readings

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology.Polygon

@[expose] public section

/-!
# The four actual legs of the retained standard tours

Expose the shared-frame sheet on every leg of each owner-closed A/B tour.
The right branch loop changes the arriving sheet; the reverse connector
therefore does not start on the forward connector's arriving sheet. The
left branch loop makes the final return. All four indexed words are kept.

The numerical consumer retains the complete increment polygon of each leg,
as well as every cross term between their totals. In particular, deleting a
branch loop with zero total is not justified by the formula below. These are
the retained owner-closed tours, not an asserted identification with legacy
independently seeded period names.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes

open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Integration.Path.IncrementArea (Summary pathArea)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

set_option genInjectivity false in
/-- A materialized decomposition of one actual indexed word. -/
structure FourLegWord {count : Nat} (word : List (Stokes.OrientedEdge count)) where
  /-- The retained forward connector word or its exact numerical summary. -/ forward : List (Stokes.OrientedEdge count)
  /-- The retained right branch-boundary word or its exact numerical summary. -/ rightLoop : List (Stokes.OrientedEdge
    count)
  /-- The retained backward connector word or its exact numerical summary. -/ backward : List (Stokes.OrientedEdge
    count)
  /-- The retained left branch-boundary word or its exact numerical summary. -/ leftLoop : List (Stokes.OrientedEdge
    count)
  /-- The original indexed word is exactly the four retained legs in their actual traversal order. -/ word_eq : word =
    forward ++ (rightLoop ++ (backward ++ leftLoop))

constructive_injectivity FourLegWord

namespace FourLegWord

variable {count : Nat} {word : List (OrientedEdge count)}

/-- Transport the four retained legs along equality of their original indexed word. -/
def castWord (legs : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord word)
  {other : List (Stokes.OrientedEdge count)} (equal : word = other) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord other :=
  ⟨legs.forward, legs.rightLoop, legs.backward, legs.leftLoop, equal.symm.trans legs.word_eq⟩

set_option genInjectivity false in
/-- Local source increments or already sewn increments may be supplied. The statement never assumes they are an exact
global vertex primitive. -/
structure Sample (legs : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord word)
  (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical) where
  /-- The retained forward connector word or its exact numerical summary. -/ forward : IncrementArea.Summary
    (legs.forward.map value)
  /-- The retained right branch-boundary word or its exact numerical summary. -/ rightLoop : IncrementArea.Summary
    (legs.rightLoop.map value)
  /-- The retained backward connector word or its exact numerical summary. -/ backward : IncrementArea.Summary
    (legs.backward.map value)
  /-- The retained left branch-boundary word or its exact numerical summary. -/ leftLoop : IncrementArea.Summary
    (legs.leftLoop.map value)

constructive_injectivity Sample

namespace Sample

variable {legs : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord word}
  {value : OrientedEdge count → Canonical}

/-- Materialize each actual leg's increment summary once from the supplied edge readings. -/
def build (legs : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord word) (value :
  Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample legs value :=
  ⟨Summary.build (legs.forward.map value), IncrementArea.Summary.build (legs.rightLoop.map value),
    IncrementArea.Summary.build (legs.backward.map value), IncrementArea.Summary.build (legs.leftLoop.map value)⟩

/-- Compose the four retained summaries; do not evaluate any leg again. -/
def combined (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample
  legs value) : IncrementArea.Summary (word.map value) :=
  let summary := sample.forward.append (sample.rightLoop.append (sample.backward.append sample.leftLoop))
  have mapped : word.map value = legs.forward.map value ++
      (legs.rightLoop.map value ++ (legs.backward.map value ++ legs.leftLoop.map value)) := by
    have equal := congrArg (List.map value) legs.word_eq
    rw [Data.List.Map.map_append, Data.List.Map.map_append, Data.List.Map.map_append] at equal
    exact equal
  { total := summary.total
    total_eq := summary.total_eq.trans (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum mapped.symm)
    area := summary.area
    area_eq := summary.area_eq.trans (congrArg IncrementArea.pathArea mapped.symm) }

/-- The complete retained tour total is the sum of its four actual leg totals. -/
theorem total_eq (sample :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample legs value) :
    sample.combined.total = sample.forward.total + sample.rightLoop.total + sample.backward.total +
      sample.leftLoop.total := by
  change _ + (_ + (_ + _)) = _
  ring1

/-- Both internal branch-loop areas and all six inter-leg terms survive. This is the full cumulative polygon, not the
polygon of four totals alone. -/
theorem area_eq (sample : Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample
  legs value) :
    sample.combined.area =
      sample.forward.area + sample.rightLoop.area + sample.backward.area + sample.leftLoop.area +
      BoundaryRibbon.area sample.forward.total sample.rightLoop.total +
      BoundaryRibbon.area sample.forward.total sample.backward.total +
      BoundaryRibbon.area sample.forward.total sample.leftLoop.total +
      BoundaryRibbon.area sample.rightLoop.total sample.backward.total +
      BoundaryRibbon.area sample.rightLoop.total sample.leftLoop.total +
      BoundaryRibbon.area sample.backward.total sample.leftLoop.total := by
  change _ + (_ + (_ + _ + _) + _) + _ = _
  dsimp only [IncrementArea.Summary.append]
  rw [IncrementArea.area_add_right, IncrementArea.area_add_right, IncrementArea.area_add_right]
  ring1

/-- The exact correction incurred by suppressing both branch loops. All operands are retained numerical summaries,
independent of subdivision size. -/
def branchCorrection (sample :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample legs value) : Gaussian
  :=
  sample.rightLoop.area + sample.leftLoop.area +
    BoundaryRibbon.area sample.forward.total sample.rightLoop.total +
    BoundaryRibbon.area sample.forward.total sample.leftLoop.total +
    BoundaryRibbon.area sample.rightLoop.total sample.backward.total +
    BoundaryRibbon.area sample.rightLoop.total sample.leftLoop.total +
    BoundaryRibbon.area sample.backward.total sample.leftLoop.total

/-- Deleting both retained branch loops changes the complete area by exactly the cached branch correction. -/
theorem branchCorrection_eq (sample :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample legs value) :
    sample.combined.area - (sample.forward.append sample.backward).area = sample.branchCorrection := by
  rw [sample.area_eq]
  dsimp only [IncrementArea.Summary.append,
    branchCorrection]
  ring1

/-- Even vanishing loop totals leave their complete internal areas. -/
theorem branchCorrection_of_zero_totals (sample :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample legs value)
    (rightZero : sample.rightLoop.total = 0) (leftZero : sample.leftLoop.total = 0) :
    sample.branchCorrection = sample.rightLoop.area + sample.leftLoop.area := by
  unfold branchCorrection
  rw [rightZero, leftZero]
  simp only [-eq_self, -iff_self, IncrementArea.area_zero_left, IncrementArea.area_zero_right, add_zero]
  rfl

/-- The original full increment polygon has exactly the area of the composed retained summaries. -/
theorem polygon_eq (sample :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample legs value) :
    IncrementArea.pathArea (word.map value) = sample.combined.area := sample.combined.area_eq.symm

/-- The original full increment list sums to the total of the composed retained summaries. -/
theorem increments_eq (sample :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord.Sample legs value) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (word.map value) = sample.combined.total :=
      sample.combined.total_eq.symm

end Sample
end FourLegWord
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.RootEdgeBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Readings.PreparedBoundaryClosure (ClosedBoundaryDoublePath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes (FourLegWord)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open Purelib.Curves.Hyperelliptic.Branches.BranchGridPaths.Grid (splitTour splitTour_winding)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BranchGrid.Grid (ContainsTourVertices)
open _root_.Purelib.Polynomial.Geometry.Grid.FromStates (ContainsPathVertices)
open Purelib.Polynomial.Geometry.Grid.Walks (splitPath)
open Purelib.Polynomial.Geometry.Grid.Winding (splitPath_winding)
open Purelib.Riemann.Paths.PreparedPathWinding.ClearPath (rawWinding)

variable {genus : Nat} {curve : HyperellipticCurve genus} {ambient :
  Purelib.Geometry.Rational.Box}
  {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid}

/-- Split winding is enough to determine every actual sheet join. The constructor keeps the original backward split
rather than substituting an independently prepared or merely endpoint-equal reverse path. -/
def tourLegs (edges : RootEdgeBank frames) (vertices : LiftedVertices.VertexBank grid)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      OwnerLoopMonodromy.WindingOneLoop curve.polynomial point)
    (tour : PreparedBoundaryClosure.ClosedBoundaryDoublePath curve) (onGrid : Grid.ContainsTourVertices grid tour)
    (rightWinding : ClearPath.rawWinding tour.joined.data.rightBoundaryPath = 4)
    (leftWinding : ClearPath.rawWinding tour.joined.data.leftBoundaryPath = 4) (sheet : Fin 2) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord (edges.indexedEdges vertices
      (Grid.splitTour grid tour onGrid) sheet) := by
  let forward := Walks.splitPath grid tour.joined.data.connector onGrid.1
  let right := Walks.splitPath grid tour.joined.data.rightBoundaryPath onGrid.2.1
  let backward := Walks.splitPath grid (BranchCutLifts.ClearPath.reverse tour.joined.data.connector) onGrid.2.2.1
  let left := Walks.splitPath grid tour.joined.data.leftBoundaryPath onGrid.2.2.2
  have rightSwap (start : Fin 2) : RootEdgeBank.target edges right start = BranchCutLifts.otherSheet start :=
    RootEdgeBank.target_odd edges right (ContainsPathVertices.start grid _ onGrid.2.1) 0
      ((Winding.splitPath_winding grid _ _).trans (rightWinding.trans (by decide))) start
  have leftSwap (start : Fin 2) : RootEdgeBank.target edges left start = BranchCutLifts.otherSheet start :=
    RootEdgeBank.target_odd edges left (ContainsPathVertices.start grid _ onGrid.2.2.2) 0
      ((Winding.splitPath_winding grid _ _).trans (leftWinding.trans (by decide))) start
  have returned : RootEdgeBank.target edges (Grid.splitTour grid tour onGrid) sheet = sheet :=
    RootEdgeBank.target_even edges (reference _ (ContainsPathVertices.start grid _ onGrid.1))
      (Grid.splitTour grid tour onGrid) (ContainsPathVertices.start grid _ onGrid.1) 1
      (by rw [Grid.splitTour_winding, rightWinding, leftWinding]; decide) sheet
  change RootEdgeBank.target edges (forward.append (right.append (backward.append left))) sheet = sheet at returned
  rw [RootEdgeBank.target_append edges, RootEdgeBank.target_append edges, RootEdgeBank.target_append edges, rightSwap,
    leftSwap] at returned
  have backwardSheet : RootEdgeBank.target edges backward (BranchCutLifts.otherSheet (RootEdgeBank.target edges forward
    sheet)) =
      BranchCutLifts.otherSheet sheet := by
    have swapped := congrArg BranchCutLifts.otherSheet returned
    rw [BranchCutLifts.otherSheet_other] at swapped
    exact swapped
  refine ⟨edges.indexedEdges vertices forward sheet,
    edges.indexedEdges vertices right (RootEdgeBank.target edges forward sheet),
    edges.indexedEdges vertices backward (BranchCutLifts.otherSheet (RootEdgeBank.target edges forward sheet)),
    edges.indexedEdges vertices left (BranchCutLifts.otherSheet sheet), ?_⟩
  change edges.indexedEdges vertices (forward.append (right.append (backward.append left))) sheet = _
  rw [edges.indexedEdges_append, edges.indexedEdges_append, edges.indexedEdges_append, rightSwap, backwardSheet]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.RootEdgeBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.Pair

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes (FourLegWord)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.StandardTours (Pair
  aTourOfData_boundaryWindings bTourOfData_boundaryWindings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.RootEdgeBank (tourLegs)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base} {index : Fin genus}

/-- The actual A face word, using the already retained tour and sheet. -/
def aLegs (pair : StandardTours.Pair lifted index) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord pair.aFaces.geometry.indexed
  :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.RootEdgeBank.tourLegs lifted.edges lifted.vertices (fun
    point member => (BranchCellBank.referenceAt base.bank.toBranchCellBank point member).toLoop)
    pair.source.aTour pair.aOnGrid
    (by rw [pair.source_eq]; exact (StandardTours.aTourOfData_boundaryWindings curve branches index).1)
    (by rw [pair.source_eq]; exact (StandardTours.aTourOfData_boundaryWindings curve branches index).2)
      pair.aFaces.sheet).castWord
      ((congrArg (fun walk => lifted.edges.indexedEdges lifted.vertices walk pair.aFaces.sheet)
        pair.aWalk_eq.symm).trans
        pair.aFaces.indexed_eq.symm)

/-- The actual B face word includes both moving branch-boundary loops. -/
def bLegs (pair : StandardTours.Pair lifted index) :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.PolygonStokes.FourLegWord pair.bFaces.geometry.indexed
  :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.RootEdgeBank.tourLegs lifted.edges lifted.vertices (fun
    point member => (BranchCellBank.referenceAt base.bank.toBranchCellBank point member).toLoop)
    pair.source.bTour pair.bOnGrid
    (by rw [pair.source_eq]; exact (StandardTours.bTourOfData_boundaryWindings curve branches index).1)
    (by rw [pair.source_eq]; exact (StandardTours.bTourOfData_boundaryWindings curve branches index).2)
      pair.bFaces.sheet).castWord
      ((congrArg (fun walk => lifted.edges.indexedEdges lifted.vertices walk pair.bFaces.sheet)
        pair.bWalk_eq.symm).trans
        pair.bFaces.indexed_eq.symm)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourChains.Pair
