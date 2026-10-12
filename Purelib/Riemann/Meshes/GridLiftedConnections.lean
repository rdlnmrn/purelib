module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Topology.Polygon.Stokes
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Polynomial.Geometry.Grid.FromStates
public import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.Reversal
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops

open Purelib

public section

/-!
# Constructed connections between specified sheets of grid vertices

A retained walk is tied to its actual shared-root transport.  Composition
and reversal preserve its endpoint owners.  On a branch grid, the canonical
connector uses a two-leg base walk, followed, only when needed, by the
already available winding-one reference loop at its destination.  Thus both
sheets are connected by actual moving grid paths, not stationary swaps.

This constructs connections on the grid skeleton.  It does not assert that
the selected connectors are disjoint embedded cuts or that they already
present a fundamental polygon.
-/

section

open Purelib.Polynomial.Geometry.ClearPath (GaussianPolynomial)
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

section

namespace Purelib.Riemann.Meshes.GridLiftedConnections.Grid

open Purelib.Curves in
/-- A certified choice of whether a two-sheet arrival needs one sheet exchange.

Each constructor retains the exact equality between the arrived or exchanged sheet and the requested sheet. -/
inductive SheetAlignment (arrival requested : Fin 2) where
  /-- The arrived sheet already equals the requested sheet. -/ | same (equal : arrival = requested)
  /-- Exchanging the arrived sheet gives the requested sheet. -/ | swapped (equal :
    Hyperelliptic.Branches.BranchCutLifts.otherSheet arrival = requested)

end Purelib.Riemann.Meshes.GridLiftedConnections.Grid

section

namespace Purelib.Riemann.Meshes.GridLiftedConnections.Grid.SheetAlignment

/-- Compare two sheet indices and retain the matching alignment equation. -/
@[expose] def build (arrival requested : Fin 2) : Grid.SheetAlignment arrival requested :=
  if equal : arrival = requested then .same equal
  else .swapped (by
    apply Fin.ext
    change 1 - arrival.val = requested.val
    have different : arrival.val ≠ requested.val := fun same => equal (Fin.ext same)
    have firstBound := arrival.isLt
    have lastBound := requested.isLt
    omega)

/-- Read whether the certified alignment requires a sheet exchange. -/
@[expose] def usesSwap {arrival requested : Fin 2} : Grid.SheetAlignment arrival requested → Bool
  | .same _ => false
  | .swapped _ => true

open Purelib.Curves in
/-- Applying the retained alignment decision reaches the requested sheet. -/
theorem applied {arrival requested : Fin 2} (alignment : Grid.SheetAlignment arrival requested) :
    (if alignment.usesSwap then Hyperelliptic.Branches.BranchCutLifts.otherSheet arrival else arrival) = requested := by
  cases alignment with
  | same equal => exact equal
  | swapped equal => exact equal

end Purelib.Riemann.Meshes.GridLiftedConnections.Grid.SheetAlignment

end
end

section

variable {polynomial : GaussianPolynomial} {ambient :
  Box} {grid : Polynomial.Geometry.Grid.ClearGrid polynomial
  ambient} {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
set_option genInjectivity false in
/-- A grid walk with certified transport between specified endpoint sheets.

The retained vertex membership proofs and sheet equation concern the supplied root-edge bank and the actual walk
transport. -/
structure LiftedWalk (edges :
  SquareRoot.Grid.RootEdgeBank frames) (start : Gaussian.Basic.Canonical) (firstSheet : Fin 2)
    (finish : Gaussian.Basic.Canonical) (lastSheet : Fin 2) where
  /-- The retained base walk connecting the endpoint coordinates. -/ walk : Geometry.Grid.Walks.Walk grid start finish
  /-- The starting coordinate belongs to the retained grid. -/ first :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid
    start
  /-- The finishing coordinate belongs to the retained grid. -/ last :
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid
    finish
  /-- Transport along the actual walk reaches the requested finishing sheet. -/ sheet_eq :
    SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges walk firstSheet = lastSheet

-- Preserve the original constructor certificate names of this unchanged nominal datatype.

constructive_injectivity Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.LiftedWalk

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank

open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank (LiftedWalk)

section

variable {edges : RootEdgeBank frames} {start middle finish :
  Canonical} {firstSheet middleSheet lastSheet : Fin 2}

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.LiftedWalk

open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The empty walk connects a retained vertex and sheet to itself. -/
@[expose] def nil (edges :
  SquareRoot.Grid.RootEdgeBank frames) (base : Gaussian.Basic.Canonical) (member :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex grid base) (sheet : Fin 2) :
    SquareRoot.Grid.RootEdgeBank.LiftedWalk edges base sheet base sheet := ⟨.nil base, member, member, rfl⟩

open Purelib.RootIsolation in
/-- Compose two lifted walks sharing the exact intermediate coordinate and sheet. -/
@[expose] def append (left :
  SquareRoot.Grid.RootEdgeBank.LiftedWalk edges start firstSheet middle middleSheet)
    (right : SquareRoot.Grid.RootEdgeBank.LiftedWalk edges middle middleSheet finish lastSheet) :
      SquareRoot.Grid.RootEdgeBank.LiftedWalk edges start firstSheet finish lastSheet :=
  ⟨left.walk.append right.walk, left.first, right.last, by rw [SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append
    edges, left.sheet_eq, right.sheet_eq]⟩

open Purelib.Riemann in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Reverse a lifted walk with its actual inverse sheet transport.

Winding-one reference loops certify transport reversibility at the retained grid vertices. -/
@[expose] def reverse (path :
  SquareRoot.Grid.RootEdgeBank.LiftedWalk edges start firstSheet finish lastSheet)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    SquareRoot.Grid.RootEdgeBank.LiftedWalk edges finish lastSheet start firstSheet :=
  ⟨path.walk.reverse, path.last, path.first,
    (congrArg (SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges path.walk.reverse) path.sheet_eq.symm).trans
      (edges.target_reverse reference path.walk firstSheet)⟩

open Purelib.Topology in
open Purelib.RootIsolation in
/-- Read the lifted walk as an indexed edge path with its specified endpoint owners. -/
theorem endpoints (path :
  SquareRoot.Grid.RootEdgeBank.LiftedWalk edges start firstSheet finish lastSheet) (vertices :
  SquareRoot.Grid.LiftedVertices.VertexBank grid) :
    Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish (edges.indexedEdges vertices path.walk
      firstSheet)
      (vertices.index start path.first firstSheet) (vertices.index finish path.last lastSheet) :=
  (edges.indexedEdges_endpoints vertices path.walk path.first path.last firstSheet).castFinish
    (congrArg (vertices.index finish path.last) path.sheet_eq)

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.LiftedWalk

end
end

section

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

namespace Purelib.Curves.Hyperelliptic.Branches.BranchCellBank

open Purelib.Curves in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- Connect two specified sheets using a grid connector and, if needed, one winding-one loop.

The existing branch and edge banks determine the actual transports; a destination reference loop exchanges sheets only
when the direct connector arrives on the other sheet. -/
@[expose] def connectSheets (bank :
  Hyperelliptic.Branches.BranchCellBank curve branches higher) {frames : RootIsolation.SquareRoot.Grid.RootFrames
  bank.grid}
    (edges : SquareRoot.Grid.RootEdgeBank frames) (start finish : Gaussian.Basic.Canonical)
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start) (last :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid finish)
    (firstSheet lastSheet : Fin 2) : SquareRoot.Grid.RootEdgeBank.LiftedWalk edges start firstSheet finish
      lastSheet :=
  let connector := Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.Grid.connect bank.grid start finish first last
  let arrival := SquareRoot.Grid.EdgeBank.RootEdgeBank.target edges connector firstSheet
  match Purelib.Riemann.Meshes.GridLiftedConnections.Grid.SheetAlignment.build arrival lastSheet with
  | .same reached => ⟨connector, first, last, reached⟩
  | .swapped reached =>
      let reference := Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy.BranchCellBank.referenceAt bank finish last
      ⟨connector.append reference.walk, first, last, by
        rw [SquareRoot.Grid.EdgeBank.RootEdgeBank.target_append edges, SquareRoot.Grid.EdgeBank.RootEdgeBank.target_odd
          edges reference.walk last 0 (reference.winding.trans (by decide))]
        exact reached⟩

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
open Purelib.Polynomial in
open Purelib.RootIsolation in
/-- The constructed sheet connector has the requested endpoints in the actual indexed vertex bank. -/
theorem connectSheets_endpoints (bank :
  Hyperelliptic.Branches.BranchCellBank curve branches higher) {frames : RootIsolation.SquareRoot.Grid.RootFrames
  bank.grid}
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid) (edges : SquareRoot.Grid.RootEdgeBank
      frames) (start finish : Gaussian.Basic.Canonical)
    (first : Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid start) (last :
      Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid finish) (firstSheet lastSheet : Fin 2) :
    Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish
      (edges.indexedEdges vertices (bank.connectSheets edges start finish first last firstSheet lastSheet).walk
        firstSheet)
      (vertices.index start first firstSheet) (vertices.index finish last lastSheet) :=
  (bank.connectSheets edges start finish first last firstSheet lastSheet).endpoints vertices

end Purelib.Curves.Hyperelliptic.Branches.BranchCellBank

end

end
