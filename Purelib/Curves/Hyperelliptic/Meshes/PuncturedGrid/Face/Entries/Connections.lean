module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.TracedPoint
import Purelib.Riemann.Paths.OwnerTracePath
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.PreparedPathWinding

/-! # Actual source-row connections to one retained continued Point

Each connection prepares a genuinely new contained source trace, selects
its finish in the Point's retained frame, and composes those actual
selections. The original Point and its neighborhood are never acquired
again. The stationary finish-to-Point join has its own observation/payment
boundary; no analytic primitive constant is identified by this operation.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.TracedPoint

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Riemann.Paths.ClearBoxPaths (Route)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath OwnerLink)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName OwnerJoin)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerFrame)
open Purelib.Riemann.RootContinuation.RootPathTransport (TransportRow)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : BranchIsolation.Data curve}
variable {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches higher}
variable {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face}
variable {sheet : Fin 2} {point : Canonical} {inside : face.cell.box.Contains point}
variable {count : Nat} {targetFrame : OwnerFrame (curve.polynomial.eval point)}
variable (cached : TracedPoint models sheet point inside count targetFrame)
variable {source : Canonical} {sourceFrame : OwnerFrame (curve.polynomial.eval source)} {index : Fin 2}
variable (sourceEntry : Entry models source (sourceFrame.owners index))
variable (same : sourceEntry.sheet = sheet) (sourceInside : face.cell.box.Contains source)

/-- Retain one actual source trace, its original row, and the signed connection to the SAME stored Point.

The comparison is derived from the original source Entry and the actual
two retained frame selections. Its stationary join is stored as part of
the whole path; sampling and paying that join is separate new work.
-/
abbrev Connection :=
  Σ route : {value : Route curve.polynomial face.cell.box source point //
    value = Route.build face.clearance source point sourceInside inside},
  Σ traced : {value : TracedPath route.val.path (sourceFrame.owners index) //
    value = TracedPath.build route.val.path route.val.within (sourceFrame.owners index)},
  Σ row : {value : TransportRow route.val.path sourceFrame cached.frame index //
    value = TransportRow.ofTraced cached.frame traced.val},
  Σ equivalent : {value : NamedEquivalent (ownerName row.val.traced.finishOwner)
      (ownerName cached.sample.owner) //
    value = cached.sourceEquivalent sourceEntry same sourceInside route.val row.val},
  Σ join : {value : OwnerJoin row.val.traced.finishOwner cached.sample.owner //
    value = OwnerJoin.acquire row.val.traced.finishOwner cached.sample.owner equivalent.val},
  {value : OwnerPath curve.polynomial source (sourceFrame.owners index) point cached.sample.owner //
    value = row.val.traced.trace.get.append
      (.cons (OwnerLink.stationary curve.polynomial point join.val) (.nil point cached.sample.owner))}

/-- Prepare one genuinely new source trace and connect its actual finish to the existing cached Point.

The Point, original anchor trace, frame and neighborhood remain the SAME
supplied caches. Only this source route/trace and its target selection are
new preparation. No old endpoint observation is relabelled as a new join.
-/
def connect : cached.Connection sourceEntry same sourceInside :=
  let route := Route.build face.clearance source point sourceInside inside
  let traced := TracedPath.build route.path route.within (sourceFrame.owners index)
  let row := TransportRow.ofTraced cached.frame traced
  let equivalent := cached.sourceEquivalent sourceEntry same sourceInside route row
  let join := OwnerJoin.acquire row.traced.finishOwner cached.sample.owner equivalent
  let path := row.traced.trace.get.append
    (.cons (OwnerLink.stationary curve.polynomial point join) (.nil point cached.sample.owner))
  ⟨⟨route, rfl⟩, ⟨traced, rfl⟩, ⟨row, rfl⟩, ⟨equivalent, rfl⟩, ⟨join, rfl⟩, ⟨path, rfl⟩⟩

namespace Connection

variable {cached sourceEntry same sourceInside}
variable (connected : cached.Connection sourceEntry same sourceInside)

/-- Read the actual contained source-to-Point route. -/
def route : Route curve.polynomial face.cell.box source point := connected.1.val

/-- Read the one genuinely new source trace, retaining its original source Owner. -/
def traced : TracedPath connected.route.path (sourceFrame.owners index) := connected.2.1.val

/-- Read the row reusing that complete trace and the SAME retained Point frame. -/
def row : TransportRow connected.route.path sourceFrame cached.frame index := connected.2.2.1.val

/-- Read the derived signed comparison of the actual row finish with the actual retained Point. -/
def equivalent : NamedEquivalent (ownerName connected.row.traced.finishOwner)
    (ownerName cached.sample.owner) := connected.2.2.2.1.val

/-- Read the whole newly acquired stationary join, retaining both tails and its actual comparison indices. -/
def join : OwnerJoin connected.row.traced.finishOwner cached.sample.owner := connected.2.2.2.2.1.val

/-- Read the complete original-source-to-cached-Point path, including that SAME retained stationary join. -/
def path : OwnerPath curve.polynomial source (sourceFrame.owners index) point cached.sample.owner :=
  connected.2.2.2.2.2.val

/-- The route retains its whole original finite connector factory. -/
theorem route_eq : connected.route = Route.build face.clearance source point sourceInside inside :=
  connected.1.property

/-- The new trace retains its whole original preparation factory. -/
theorem traced_eq : connected.traced = TracedPath.build connected.route.path connected.route.within
    (sourceFrame.owners index) := connected.2.1.property

/-- The row is the original constructor on this SAME stored source trace. -/
theorem row_eq : connected.row = TransportRow.ofTraced cached.frame connected.traced := connected.2.2.1.property

/-- The retained signed relation is the exact comparison derived from the two actual selections. -/
theorem equivalent_eq : connected.equivalent =
    cached.sourceEquivalent sourceEntry same sourceInside connected.route connected.row := connected.2.2.2.1.property

/-- The whole new join retains the exact original tail/comparison acquisition factory. -/
theorem join_eq : connected.join =
    OwnerJoin.acquire connected.row.traced.finishOwner cached.sample.owner connected.equivalent :=
  connected.2.2.2.2.1.property

/-- The stored path consumes the SAME retained join rather than executing its factory again. -/
theorem path_eq : connected.path = connected.row.traced.trace.get.append
    (.cons (OwnerLink.stationary curve.polynomial point connected.join) (.nil point cached.sample.owner)) :=
  connected.2.2.2.2.2.property

/-- The connection has the true open winding of its SAME contained route, rather than zero winding. -/
theorem winding : Polynomial.Winding.Polygon.Basic.chainRaw curve.polynomial source connected.path.vertices =
    Paths.PreparedPathWinding.ClearPath.rawWinding connected.route.path := by
  rw [connected.path_eq, RootContinuation.RootPathTransport.OwnerPath.append_winding, connected.join_eq]
  change Polynomial.Winding.Polygon.Basic.chainRaw curve.polynomial source connected.row.traced.trace.get.vertices +
    Polynomial.Winding.Polygon.Basic.chainRaw curve.polynomial point
      (RootContinuation.RootPathTransport.OwnerPath.join curve.polynomial point connected.row.traced.finishOwner
        cached.sample.owner connected.equivalent).vertices = _
  rw [RootContinuation.RootPathTransport.OwnerPath.join_winding,
    Paths.PreparedPathWinding.PreparedClearPathModels.TracedPath.winding_original]
  exact Int.add_zero _

end Connection

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry.TracedPoint

end
