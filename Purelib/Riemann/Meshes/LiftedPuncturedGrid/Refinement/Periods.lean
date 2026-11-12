module

public import Purelib.Riemann.Meshes.LiftedPuncturedGrid.Refinement
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
public import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SkeletonFaceAssignments
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.BranchProducts
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Transport
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

/-! # Actual original period owners on the same clearance-refined grid

One retained resplit walk, one actual frame lookup, one Owner selection and
one face-assignment cache belong to the GIVEN old period. The original
vertex Owner and whole extended-frame identity derive its selected sheet;
labels and coordinate equality never replace a root comparison.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces.FramedPuncturedGrid (OwnerWalkFaces)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Periods.PreparedGridPeriodPrograms (PeriodWalk)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame OwnerSelection)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
variable {original : LiftedPuncturedGrid base}
variable {patches : List (ContinuedNeighborhood curve.polynomial count)}
variable {clearance : ClearancePreparation base.bank.toBranchCellBank patches}
variable (retained : ClearanceRefinement original clearance) (vertex : Fin original.vertices.count)
variable {source : Differential genus}
variable (period : PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
  (original.vertices.owner original.frames vertex) source)

/-- The actual original vertex reads its SAME whole root frame on the retained fine grid. -/
theorem period_frame : retained.fine.frames.frameAt (original.vertices.coordinate vertex)
      (retained.included.vertex (original.vertices.coordinate_onGrid vertex)) =
    original.frames.frameAt (original.vertices.coordinate vertex) (original.vertices.coordinate_onGrid vertex) :=
  (congrArg (fun frames : RootFrames retained.fineBase.bank.grid =>
    frames.frameAt (original.vertices.coordinate vertex)
      (retained.included.vertex (original.vertices.coordinate_onGrid vertex))) retained.fine_frames).trans
    (retained.frameAt (original.vertices.coordinate vertex) (original.vertices.coordinate_onGrid vertex))

/-- Read the retained fine frame at the actual original period vertex without constructing another frame. -/
@[expose] def periodFrame : OwnerFrame (curve.polynomial.eval (original.vertices.coordinate vertex)) :=
  retained.fine.frames.frameAt (original.vertices.coordinate vertex)
    (retained.included.vertex (original.vertices.coordinate_onGrid vertex))

/-- The original period and one real resplit/frame/selection/face cache on the SAME fine grid.

The actual OwnerSelection remains DATA alongside OwnerWalkFaces, whose
aligned field alone is only Nonempty. The original period is not rebuilt,
and its full source/trace/root-return/primitive-cover cache remains given.
-/
abbrev PeriodFaces :=
  {value : LiftedPuncturedGrid base × ClearanceRefinement original clearance × Fin original.vertices.count ×
      PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
        (original.vertices.owner original.frames vertex) source // value = (original, retained, vertex, period)} ×
  (Σ walk : {value : Walk retained.fineBase.bank.grid (original.vertices.coordinate vertex)
        (original.vertices.coordinate vertex) //
      value = retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)},
  {value : OwnerFrame (curve.polynomial.eval (original.vertices.coordinate vertex)) //
      value = retained.periodFrame vertex} ×
  (Σ selection : {value : OwnerSelection (retained.periodFrame vertex).owners
      (original.vertices.owner original.frames vertex) //
      value = (retained.periodFrame vertex).select (original.vertices.owner original.frames vertex)},
  {value : OwnerWalkFaces retained.fine.mesh walk.val (original.vertices.owner original.frames vertex) //
    value = OwnerWalkFaces.ofSelection retained.fine.mesh walk.val
      (retained.included.vertex (original.vertices.coordinate_onGrid vertex)) selection.val}))

/-- Resplit the GIVEN original period once and retain its one actual fine-frame Owner selection and face cache. -/
def periodFaces : PeriodFaces retained vertex period :=
  let walk : {value : Walk retained.fineBase.bank.grid (original.vertices.coordinate vertex)
        (original.vertices.coordinate vertex) //
      value = retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)} :=
    ⟨retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex), rfl⟩
  let frame : {value : OwnerFrame (curve.polynomial.eval (original.vertices.coordinate vertex)) //
      value = retained.periodFrame vertex} := ⟨retained.periodFrame vertex, rfl⟩
  let selection : {value : OwnerSelection (retained.periodFrame vertex).owners
      (original.vertices.owner original.frames vertex) //
      value = (retained.periodFrame vertex).select (original.vertices.owner original.frames vertex)} :=
    ⟨frame.val.select (original.vertices.owner original.frames vertex), rfl⟩
  let faces : {value : OwnerWalkFaces retained.fine.mesh walk.val (original.vertices.owner original.frames vertex) //
      value = OwnerWalkFaces.ofSelection retained.fine.mesh walk.val
        (retained.included.vertex (original.vertices.coordinate_onGrid vertex)) selection.val} :=
    ⟨OwnerWalkFaces.ofSelection retained.fine.mesh walk.val
      (retained.included.vertex (original.vertices.coordinate_onGrid vertex)) selection.val, rfl⟩
  ⟨⟨(original, retained, vertex, period), rfl⟩, walk, frame, selection, faces⟩

namespace PeriodFaces

variable {retained vertex period} (kept : PeriodFaces retained vertex period)

/-- Read the SAME complete original period, not a freshly prepared period at the same coordinate. -/
@[expose] def oldPeriod : PeriodWalk base.bank.grid (original.vertices.coordinate vertex)
    (original.vertices.owner original.frames vertex) source := kept.1.val.2.2.2

/-- Read the exact original resplit walk without deduplicating its ordered edge occurrences. -/
@[expose] def walk : Walk retained.fineBase.bank.grid (original.vertices.coordinate vertex)
    (original.vertices.coordinate vertex) := kept.2.1.val

/-- Read the SAME whole cached fine-grid root frame. -/
@[expose] def frame : OwnerFrame (curve.polynomial.eval (original.vertices.coordinate vertex)) := kept.2.2.1.val

/-- Read the actual cached selection and its executable named comparison from the original vertex Owner. -/
@[expose] def selection : OwnerSelection (retained.periodFrame vertex).owners
    (original.vertices.owner original.frames vertex) :=
  kept.2.2.2.1.val

/-- Read the whole actually constructed face cache before its original-walk index view. -/
@[expose] def faces : OwnerWalkFaces retained.fine.mesh kept.walk (original.vertices.owner original.frames vertex) :=
  kept.2.2.2.2.val

/-- Every complete old input remains its literal given cached value. -/
theorem originals_eq : kept.1.val = (original, retained, vertex, period) := kept.1.property

/-- The stored original period is the whole supplied period cache. -/
theorem oldPeriod_eq : kept.oldPeriod = period :=
  congrArg Prod.snd (congrArg Prod.snd (congrArg Prod.snd kept.originals_eq))

/-- The complete resplit walk has its one original factory on the given period walk. -/
theorem walk_eq : kept.walk =
    retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex) := kept.2.1.property

/-- The whole cached frame reads the same original vertex frame through actual extension-prefix preservation. -/
theorem frame_eq : kept.frame = original.frames.frameAt (original.vertices.coordinate vertex)
    (original.vertices.coordinate_onGrid vertex) := kept.2.2.1.property.trans (retained.period_frame vertex)

/-- The selected Owner cache retains its one original selector execution. -/
theorem selection_eq : kept.selection =
    (retained.periodFrame vertex).select (original.vertices.owner original.frames vertex) :=
  kept.2.2.2.1.property

/-- The fine-frame selector returns the actual original vertex sheet by whole-frame identity and select_self. -/
theorem selection_index : kept.selection.index = original.vertices.sheet vertex := by
  have actual := congrArg (fun frame : OwnerFrame (curve.polynomial.eval (original.vertices.coordinate vertex)) =>
    (frame.select (original.vertices.owner original.frames vertex)).index) (retained.period_frame vertex)
  have old : ((original.frames.frameAt (original.vertices.coordinate vertex)
      (original.vertices.coordinate_onGrid vertex)).select
        (original.vertices.owner original.frames vertex)).index = original.vertices.sheet vertex := by
    change ((original.frames.frameAt (original.vertices.coordinate vertex)
      (original.vertices.coordinate_onGrid vertex)).select
        ((original.frames.frameAt (original.vertices.coordinate vertex)
          (original.vertices.coordinate_onGrid vertex)).owners (original.vertices.sheet vertex))).index = _
    exact OwnerFrame.select_self _ _
  exact (congrArg (fun value : OwnerSelection (retained.periodFrame vertex).owners
    (original.vertices.owner original.frames vertex) => value.index) kept.selection_eq).trans (actual.trans old)

/-- The face cache retains its one actual constructor on this same walk and selection. -/
theorem faces_eq : kept.faces = OwnerWalkFaces.ofSelection retained.fine.mesh kept.walk
    (retained.included.vertex (original.vertices.coordinate_onGrid vertex)) kept.selection := kept.2.2.2.2.property

/-- View the SAME whole face cache under its original exact resplit-walk factory index. -/
@[expose] def view : OwnerWalkFaces retained.fine.mesh
    (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex))
    (original.vertices.owner original.frames vertex) := OwnerWalkFaces.castWalk kept.walk_eq kept.faces

/-- The original-walk view retains the complete actual face/selection cache heterogeneously. -/
theorem view_heq : HEq kept.view kept.faces := OwnerWalkFaces.castWalk_heq kept.walk_eq kept.faces

/-- The viewed face word starts on the actual original vertex sheet, not an input label. -/
theorem view_sheet : kept.view.sheet = original.vertices.sheet vertex := by
  have cached : kept.faces.sheet = kept.selection.index :=
    (congrArg (fun value : OwnerWalkFaces retained.fine.mesh kept.walk
      (original.vertices.owner original.frames vertex) => value.sheet) kept.faces_eq).trans
        (show (OwnerWalkFaces.ofSelection retained.fine.mesh kept.walk
          (retained.included.vertex (original.vertices.coordinate_onGrid vertex)) kept.selection).sheet =
            kept.selection.index from rfl)
  exact (OwnerWalkFaces.castWalk_sheet kept.walk_eq kept.faces).trans
    (cached.trans kept.selection_index)

/-- The exact given-walk face geometry is the original shared-frame assignment on the derived original sheet. -/
theorem view_geometry : kept.view.geometry = SkeletonFaceAssignments.walkFaces retained.fine.mesh
    (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex))
    (original.vertices.sheet vertex) := by
  have selected := kept.selection_index
  rcases kept with ⟨_inputs, ⟨walk, factory⟩, _frame, selection, faces⟩
  cases factory
  change selection.val.index = original.vertices.sheet vertex at selected
  have actual : (OwnerWalkFaces.castWalk rfl faces.val).geometry = faces.val.geometry := rfl
  have faceGeometry := congrArg (fun value : OwnerWalkFaces retained.fine.mesh
    (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex))
    (original.vertices.owner original.frames vertex) => value.geometry) faces.property
  have fromSelection : (OwnerWalkFaces.ofSelection retained.fine.mesh
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex))
      (retained.included.vertex (original.vertices.coordinate_onGrid vertex)) selection.val).geometry =
      SkeletonFaceAssignments.walkFaces retained.fine.mesh
        (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex))
        selection.val.index := rfl
  exact (actual.trans (faceGeometry.trans fromSelection)).trans
    (congrArg (SkeletonFaceAssignments.walkFaces retained.fine.mesh
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex)))
      selected)

/-- The literal viewed indexed word is the original same-grid lift on its internally derived actual sheet. -/
theorem view_indexed : kept.view.geometry.indexed = retained.fine.edges.indexedEdges retained.fine.vertices
    (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex))
    (original.vertices.sheet vertex) :=
  kept.view.indexed_eq.trans
    (congrArg (retained.fine.edges.indexedEdges retained.fine.vertices
      (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex))) kept.view_sheet)

/-- Joint base/whole-Owner transport preserves the SAME resplit indexed word.

The actual transported closed preparation must retain the whole original
preparation heterogeneously. This is not inferred from its coordinates or
sheet. The original castBase, resplit and indexed-edge laws do all transport.
-/
theorem indexed_castBase {point : Canonical}
    (pointEq : original.vertices.coordinate vertex = point)
    {owner : Owner (curve.polynomial.eval point)}
    (ownerEq : HEq (original.vertices.owner original.frames vertex) owner)
    (closed : RootClosedWalk base.bank.grid point owner) (whole : HEq closed period.closed) :
    kept.view.geometry.indexed = retained.fine.edges.indexedEdges retained.fine.vertices
      (retained.included.resplit closed.walk
        (pointEq ▸ original.vertices.coordinate_onGrid vertex)) (original.vertices.sheet vertex) := by
  have same : closed = period.closed.castBase pointEq ownerEq :=
    eq_of_heq (whole.trans (period.closed.castBase_heq pointEq ownerEq).symm)
  have transported := congrArg (fun value : RootClosedWalk base.bank.grid point owner =>
    retained.fine.edges.indexedEdges retained.fine.vertices
      (retained.included.resplit value.walk
        (pointEq ▸ original.vertices.coordinate_onGrid vertex)) (original.vertices.sheet vertex)) same
  have walk := congrArg (fun value : Walk base.bank.grid point point =>
    retained.fine.edges.indexedEdges retained.fine.vertices
      (retained.included.resplit value
        (pointEq ▸ original.vertices.coordinate_onGrid vertex)) (original.vertices.sheet vertex))
      (period.closed.castBase_walk pointEq ownerEq)
  have split := congrArg (fun value : Walk retained.fineBase.bank.grid point point =>
    retained.fine.edges.indexedEdges retained.fine.vertices value (original.vertices.sheet vertex))
    (retained.included.resplit_castEndpoints period.closed.walk pointEq pointEq
      (original.vertices.coordinate_onGrid vertex))
  have indexed := retained.fine.edges.indexedEdges_castEndpoints retained.fine.vertices
    (retained.included.resplit period.closed.walk (original.vertices.coordinate_onGrid vertex))
    pointEq pointEq (original.vertices.sheet vertex)
  exact kept.view_indexed.trans (transported.trans (walk.trans (split.trans indexed))).symm

end PeriodFaces

end Purelib.Riemann.Meshes.LiftedPuncturedGrid.ClearanceRefinement
