module

public import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank.Clearance.Refinement
public import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Data.List.Append
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Polynomial.Geometry.Grid.FromStates
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.GridLiftedMesh

/-! # Related lifted grids retaining the old root-frame and connection prefix

The original lifted grid and cut remain separate inputs. The related framed
bank comes from the supplied whole-clearance preparation. New frames extend
the old complete frame bank, and new edges extend its actual connection
prefix. Only absent entries execute new original root-frame/edge work.
-/

public section

namespace Purelib.Riemann.Meshes.LiftedPuncturedGrid

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.BranchCellBank (ClearancePreparation)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Polynomial.Geometry.Grid
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    (original : LiftedPuncturedGrid base)
    {patches : List (ContinuedNeighborhood curve.polynomial count)}
    (prepared : ClearancePreparation base.bank.toBranchCellBank patches)

/-- Transport the original coordinate inclusion to a GIVEN once-built related framed grid. -/
theorem related_included
    (related : prepared.FramedRefinement base.bank.frame)
    (fineBase : FramedPuncturedGrid curve branches higher)
    (factory : fineBase = FramedPuncturedGrid.ofBank related.fine) :
    Extension.CoordinateInclusion base.bank.grid fineBase.bank.grid :=
  Eq.mpr (congrArg (fun grid => Extension.CoordinateInclusion base.bank.grid grid)
    ((congrArg (fun value : FramedPuncturedGrid curve branches higher => value.bank.grid) factory).trans
      related.grid_eq)) prepared.included

/-- Related bank/base and original extended root caches with their complete actual factories.

The appended frame list is literally empty. Old frames and connection rows
stay first, and every new vertex/edge is constructed only by the existing
missing-entry extension operations. The final mesh uses those exact caches.
-/
@[expose] def ClearanceRefinement : Type _ :=
  (related : {value : prepared.FramedRefinement base.bank.frame //
    value = prepared.refineFramed base.bank.frame}) ×
  (fineBase : {value : FramedPuncturedGrid curve branches higher //
    value = FramedPuncturedGrid.ofBank related.val.fine}) ×
  (vertices : {value : VertexBank fineBase.val.bank.grid //
    value = VertexBank.build fineBase.val.bank.grid}) ×
  (frames : {value : RootFrames fineBase.val.bank.grid //
    value = (original.frames.appendEntries []).extend fineBase.val.bank.grid}) ×
  (edges : {value : RootEdgeBank frames.val //
    value = original.edges.extend frames.val [] frames.property
      (fun _ member => (related_included prepared related.val fineBase.val fineBase.property).vertex member)}) ×
  {fine : LiftedPuncturedGrid fineBase.val //
    fine = {
      vertices := vertices.val
      frames := frames.val
      edges := edges.val
      mesh := GridLiftedMesh.LiftedMesh.build vertices.val edges.val fineBase.val.faces } }

/-- Construct one related lifted grid while retaining the SAME old square-root frames and connections.

The clearance preparation and original lifted bank are given caches. One
related framed-bank run and face classification precede one frame extension,
one edge extension and one lifted mesh. No original bank, isolation result,
Point or source query is reconstructed. Missing new frames and edges remain
real finite operations of the original extension algorithms.
-/
def refineClearance : ClearanceRefinement original prepared :=
  let related := prepared.refineFramed base.bank.frame
  let fineBase := FramedPuncturedGrid.ofBank related.fine
  let vertices := VertexBank.build fineBase.bank.grid
  let frames := (original.frames.appendEntries []).extend fineBase.bank.grid
  let included := related_included prepared related fineBase rfl
  let edges := original.edges.extend frames [] rfl (fun _ member => included.vertex member)
  let mesh := GridLiftedMesh.LiftedMesh.build vertices edges fineBase.faces
  let fine : LiftedPuncturedGrid fineBase := ⟨vertices, frames, edges, mesh⟩
  ⟨⟨related, rfl⟩, ⟨fineBase, rfl⟩, ⟨vertices, rfl⟩, ⟨frames, rfl⟩, ⟨edges, rfl⟩, ⟨fine, rfl⟩⟩

namespace ClearanceRefinement

variable {original prepared} (retained : ClearanceRefinement original prepared)

/-- Read the SAME actual related framed-grid cache. -/
@[expose] def fineBase : FramedPuncturedGrid curve branches higher := retained.2.1.val

/-- Read the exact original-prefix frame extension retained by this construction. -/
@[expose] def frames : RootFrames retained.fineBase.bank.grid := retained.2.2.2.1.val

/-- Read the SAME actual once-built related lifted mesh. -/
@[expose] def fine : LiftedPuncturedGrid retained.fineBase := retained.2.2.2.2.2.val

/-- The whole actual lifted grid retains exactly its original supplied component caches. -/
theorem fine_eq : retained.fine =
    { vertices := retained.2.2.1.val
      frames := retained.frames
      edges := retained.2.2.2.2.1.val
      mesh := GridLiftedMesh.LiftedMesh.build retained.2.2.1.val retained.2.2.2.2.1.val retained.fineBase.faces } :=
  retained.2.2.2.2.2.property

/-- The actual lifted grid reads the SAME complete retained frame-extension cache. -/
theorem fine_frames : retained.fine.frames = retained.frames :=
  congrArg (fun value : LiftedPuncturedGrid retained.fineBase => value.frames) retained.fine_eq

/-- The original bank-grid coordinates include in this SAME actual related grid. -/
theorem included : Extension.CoordinateInclusion base.bank.grid retained.fineBase.bank.grid :=
  related_included prepared retained.1.val retained.fineBase retained.2.1.property

/-- Every old grid vertex reads its whole SAME original square-root frame after extension. -/
theorem frameAt (point : Canonical)
    (member : FromStates.ContainsVertex base.bank.grid point) :
    retained.frames.frameAt point (retained.included.vertex member) = original.frames.frameAt point member :=
  (congrArg (fun frames : RootFrames retained.fineBase.bank.grid =>
    frames.frameAt point (retained.included.vertex member)) retained.2.2.2.1.property).trans
    (((original.frames.appendEntries []).extend_frameAt retained.fineBase.bank.grid
      point (retained.included.vertex member) member).trans
      (original.frames.appendEntries_frameAt [] point member))

/-- The complete retained old frame-entry list is the actual ordered prefix of the new frame bank. -/
theorem frame_entries : retained.frames.entries.take original.frames.entries.length = original.frames.entries := by
  have oldEntries := (original.frames.appendEntries_entries []).trans
    (Append.append_nil original.frames.entries)
  have result := (original.frames.appendEntries []).extend_take_entries retained.fineBase.bank.grid
  have transported := congrArg₂ (fun entries size => entries.take size)
    (congrArg (fun frames : RootFrames retained.fineBase.bank.grid => frames.entries)
      retained.2.2.2.1.property) (congrArg List.length oldEntries.symm)
  exact transported.trans (result.trans oldEntries)

/-- The actual extended edge list retains the COMPLETE reframed original prefix before new edge operations. -/
theorem edge_entries : retained.2.2.2.2.1.val.entries =
    original.edges.reframeEntries retained.frames [] retained.2.2.2.1.property
      (fun _ member => retained.included.vertex member) ++
    RootEdgeBank.missingEntries retained.frames
      ((original.edges.reframeEntries retained.frames [] retained.2.2.2.1.property
        (fun _ member => retained.included.vertex member)).map RootEdgeBank.RootEdgeEntry.key) :=
  (congrArg (fun edges : RootEdgeBank retained.frames => edges.entries) retained.2.2.2.2.1.property).trans
    (original.edges.extend_entries retained.frames [] retained.2.2.2.1.property
      (fun _ member => retained.included.vertex member))

/-- The whole original entry prefix is the SAME retained original map at the derived frame equalities. -/
theorem original_entries :
    original.edges.reframeEntries retained.frames [] retained.2.2.2.1.property
      (fun _ member => retained.included.vertex member) =
    original.edges.entries.map (RootEdgeBank.RootEdgeEntry.reframe retained.frames
      (fun _ member => retained.included.vertex member) (fun point member => retained.frameAt point member)) :=
  original.edges.reframeEntries_eq retained.frames [] retained.2.2.2.1.property
    (fun _ member => retained.included.vertex member) (fun point member => retained.frameAt point member)

/-- Transporting an original cached connection retains both directions, original traces, selections and row data. -/
theorem original_connection (entry : RootEdgeBank.RootEdgeEntry original.frames) :
    HEq (RootEdgeBank.RootEdgeEntry.reframe retained.frames
      (fun _ member => retained.included.vertex member) (fun point member => retained.frameAt point member)
      entry).connection entry.connection :=
  RootEdgeBank.RootEdgeEntry.reframe_connection_heq retained.frames
    (fun _ member => retained.included.vertex member) (fun point member => retained.frameAt point member) entry

/-- Every original ordered edge key survives whole-connection transport unchanged. -/
theorem original_edge_keys :
    (original.edges.reframeEntries retained.frames [] retained.2.2.2.1.property
      (fun _ member => retained.included.vertex member)).map RootEdgeBank.RootEdgeEntry.key =
      original.edges.entries.map RootEdgeBank.RootEdgeEntry.key :=
  original.edges.reframeEntries_keys retained.frames [] retained.2.2.2.1.property
    (fun _ member => retained.included.vertex member)

end ClearanceRefinement

end Purelib.Riemann.Meshes.LiftedPuncturedGrid

end
