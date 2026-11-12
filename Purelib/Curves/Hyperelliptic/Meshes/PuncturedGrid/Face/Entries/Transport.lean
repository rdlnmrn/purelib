module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
public import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Polynomial.Winding.Polygon.Stationary
import Purelib.Data.Int.Arithmetic

/-! # Original face entries along retained contained transport rows

Only the original stored trace and its endpoint selection are consumed.
The returned Entry keeps the same old face sheet; no trace, root frame,
query, Point or stationary observation is acquired.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (InBox)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Polynomial.Winding
open Purelib.Riemann
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (OwnerJoin)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.RootIsolation.SquareRoot.Grid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}

/-- A stored contained trace reaches its actual finish with the original face-potential difference. -/
private theorem trace_reached {ambient : Box} {first last : Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
    {owner : Owner (curve.polynomial.eval first)} (traced : TracedPath path owner)
    (inside : InBox face.cell.box path) : Reached face.cell.box owner traced.finishOwner :=
  ⟨traced.trace.get,
    (Paths.PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original traced).trans
      (Paths.ClearBoxPathWinding.ClearPath.rawWinding_eq_potential face.clearance
        (BranchIsolation.degreePositive curve) path inside)⟩

/-- Propagate the original face Entry through one SAME retained contained trace.

Only the supplied trace and its original winding law are consumed. The
actual finish Owner and the original face-sheet index remain unchanged;
no trace, selection, Point or observation is acquired.
-/
def followTrace {ambient : Box} {first last : Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
    {owner : Owner (curve.polynomial.eval first)} (entry : Entry models first owner)
    (traced : TracedPath path owner) (inside : InBox face.cell.box path) :
    Entry models last traced.finishOwner :=
  ⟨entry.sheet, entry.reached.append (trace_reached (face := face) traced inside)⟩

/-- Following the same retained trace preserves the exact original face sheet. -/
theorem followTrace_sheet {ambient : Box} {first last : Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
    {owner : Owner (curve.polynomial.eval first)} (entry : Entry models first owner)
    (traced : TracedPath path owner) (inside : InBox face.cell.box path) :
    (entry.followTrace traced inside).sheet = entry.sheet := by rfl

/-- Extend the original Entry to a separate actual Owner through its retained same-point comparison. -/
def followEquivalent {point : Canonical} {first last : Owner (curve.polynomial.eval point)}
    (entry : Entry models point first)
    (equivalent : Approximation.Gaussian.Equivalence.NamedEquivalent
      (Paths.OwnerTraceReadings.ownerName first) (Paths.OwnerTraceReadings.ownerName last)) :
    Entry models point last :=
  ⟨entry.sheet, entry.reached.append (Reached.ofEquivalent equivalent)⟩

/-- Same-point operational Entry transport retains the exact original face sheet. -/
theorem followEquivalent_sheet {point : Canonical} {first last : Owner (curve.polynomial.eval point)}
    (entry : Entry models point first)
    (equivalent : Approximation.Gaussian.Equivalence.NamedEquivalent
      (Paths.OwnerTraceReadings.ownerName first) (Paths.OwnerTraceReadings.ownerName last)) :
    (entry.followEquivalent equivalent).sheet = entry.sheet := by rfl

/-- Propagate an Entry through the actual retained same-point root join.

The stationary link consumes the join's original tails and comparison.
Its constant base path has zero winding, so the original face sheet is
preserved without acquiring a new join or requiring a whole-name relation.
-/
def followJoin {point : Canonical} {first last : Owner (curve.polynomial.eval point)}
    (entry : Entry models point first) (join : OwnerJoin first last) :
    Entry models point last := by
  let path : OwnerPath curve.polynomial point first point last :=
    .cons (OwnerLink.stationary curve.polynomial point join) (.nil point last)
  refine ⟨entry.sheet, entry.reached.append ⟨path, ?_⟩⟩
  change Polygon.Basic.chainRaw curve.polynomial point [point] = _
  rewrite [Polygon.Stationary.chainRaw_cons_self curve.polynomial point first.parameterNonzero []]
  exact (Data.Int.Arithmetic.sub_eq_zero_of_eq rfl).symm

/-- Following the unchanged retained join preserves the original face-sheet index. -/
theorem followJoin_sheet {point : Canonical} {first last : Owner (curve.polynomial.eval point)}
    (entry : Entry models point first) (join : OwnerJoin first last) :
    (entry.followJoin join).sheet = entry.sheet := by rfl

/-- Follow one SAME cached transport row and its stored endpoint selection inside the original face.

The trace finish and selected frame Owner stay distinct inputs. Their
retained operational selection supplies the erased final reachability
step; it is not replaced by coordinate or root-name equality.
-/
def followRow {ambient : Box} {first last : Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
    {firstFrame : OwnerFrame (curve.polynomial.eval first)}
    {lastFrame : OwnerFrame (curve.polynomial.eval last)} {index : Fin 2}
    (entry : Entry models first (firstFrame.owners index))
    (row : TransportRow path firstFrame lastFrame index) (inside : InBox face.cell.box path) :
    Entry models last (lastFrame.owners row.target) :=
  ⟨entry.sheet, entry.reached.append
    ((trace_reached (face := face) row.traced inside).append (Reached.ofEquivalent row.equivalent))⟩

/-- Following the retained row preserves the original face-sheet index. -/
theorem followRow_sheet {ambient : Box} {first last : Canonical}
    {path : Polynomial.Geometry.ClearPath curve.polynomial ambient first last}
    {firstFrame : OwnerFrame (curve.polynomial.eval first)}
    {lastFrame : OwnerFrame (curve.polynomial.eval last)} {index : Fin 2}
    (entry : Entry models first (firstFrame.owners index))
    (row : TransportRow path firstFrame lastFrame index) (inside : InBox face.cell.box path) :
    (entry.followRow (firstFrame := firstFrame) (lastFrame := lastFrame) (index := index)
      row inside).sheet = entry.sheet := by rfl

section Grid

variable {ambient : Box} {grid : Polynomial.Geometry.Grid.ClearGrid curve.polynomial ambient}
variable {localFrames : RootFrames grid} (edges : RootEdgeBank localFrames)

/-- Propagate an original Entry through the SAME ordered retained bank rows of a contained walk.

Each step reads the actual forward row and its existing target selection.
Its endpoint containment comes from the supplied literal path, even when
the cached clear segment has a different clearance payload. Empty and
repeated occurrences keep their original index and owner semantics.
-/
def followWalk : {first last : Canonical} → (walk : Walk grid first last) →
    (firstMember : ContainsVertex grid first) → (lastMember : ContainsVertex grid last) →
    InBox face.cell.box walk.path → (index : Fin 2) →
    Entry models first ((localFrames.frameAt first firstMember).owners index) →
    Entry models last ((localFrames.frameAt last lastMember).owners
      (EdgeBank.RootEdgeBank.target edges walk index))
  | _, _, .nil _, _, _, _, _, entry => entry
  | _, _, .cons edge tail, _, lastMember, inside, index, entry =>
      let connection := edges.edge edge
      let row := connection.forward.row index
      let next := entry.followRow (firstFrame := localFrames.frameAt _ edge.vertices.1)
        (lastFrame := localFrames.frameAt _ edge.vertices.2) (index := index)
        row ⟨inside.1, InBox.start inside.2⟩
      followWalk tail edge.vertices.2 lastMember inside.2 (connection.forward.target index) next

/-- The whole ordered bank traversal retains the same original face-sheet index. -/
theorem followWalk_sheet : {first last : Canonical} → (walk : Walk grid first last) →
    (firstMember : ContainsVertex grid first) → (lastMember : ContainsVertex grid last) →
    (inside : InBox face.cell.box walk.path) → (index : Fin 2) →
    (entry : Entry models first ((localFrames.frameAt first firstMember).owners index)) →
    (followWalk edges walk firstMember lastMember inside index entry).sheet = entry.sheet
  | _, _, .nil _, _, _, _, _, _ => by rfl
  | _, _, .cons edge tail, _, lastMember, inside, index, entry =>
      (followWalk_sheet tail edge.vertices.2 lastMember inside.2
        ((edges.edge edge).forward.target index)
        (entry.followRow (firstFrame := localFrames.frameAt _ edge.vertices.1)
          (lastFrame := localFrames.frameAt _ edge.vertices.2) (index := index)
          ((edges.edge edge).forward.row index) ⟨inside.1, InBox.start inside.2⟩)).trans
      (entry.followRow_sheet (firstFrame := localFrames.frameAt _ edge.vertices.1)
        (lastFrame := localFrames.frameAt _ edge.vertices.2) (index := index)
        ((edges.edge edge).forward.row index) ⟨inside.1, InBox.start inside.2⟩)

end Grid

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry
