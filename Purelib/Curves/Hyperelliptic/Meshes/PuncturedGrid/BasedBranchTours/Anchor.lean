module

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
public import Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Transport
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Differentials.Basic
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BranchArea
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.AxisChainCoherence
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices

/-! # Actual common-anchor projections of retained branch walks

Scalar endpoint transport uses coordinate_index. Heterogeneous Owner
transport separately uses owner_index_heq on the SAME retained frame.
The original branch/pair/preparation caches are never reconstructed.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Branches.BranchIsolation (Data)
open Purelib.Curves.Hyperelliptic.Branches.Cuts (Ambient)
open Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts (otherSheet otherSheet_other)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid
open Purelib.Polynomial.Geometry.Grid.Walks (Walk)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.PreparedGridRootClosure.Grid (RootClosedWalk)
open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex (VertexWalk)
open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches : Data curve}
    {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
    {lifted : LiftedPuncturedGrid base}

/-- The actual cached anchor index reads the original exterior coordinate. -/
theorem anchor_coordinate (sheet : Fin 2) :
    lifted.vertices.coordinate (anchor lifted sheet) = (Ambient curve).anchor :=
  lifted.vertices.coordinate_index _ (FramedBranchCellBank.baseMember base.bank) sheet

/-- The actual cached anchor index reads the SAME whole original frame Owner, independently of scalar coordinates. -/
theorem anchor_owner_heq (sheet : Fin 2) :
    HEq (lifted.vertices.owner lifted.frames (anchor lifted sheet))
      ((lifted.frames.frameAt _ (FramedBranchCellBank.baseMember base.bank)).owners sheet) :=
  lifted.vertices.owner_index_heq lifted.frames _ (FramedBranchCellBank.baseMember base.bank) sheet

/-- Reindex only the projected endpoints of a GIVEN actual anchor-indexed vertex walk.

The starting and finishing sheets are separate explicit indices. This may
be a one-branch walk that changes root sheet; coordinate closure is not
asserted to be root closure or Owner identity.
-/
@[expose] def atAnchor (firstSheet lastSheet : Fin 2)
    (path : VertexWalk lifted.vertices lifted.edges (anchor lifted firstSheet) (anchor lifted lastSheet)) :
    Walk base.bank.grid (Ambient curve).anchor (Ambient curve).anchor :=
  path.walk.castEndpoints (anchor_coordinate (lifted := lifted) firstSheet)
    (anchor_coordinate (lifted := lifted) lastSheet)

/-- Actual projected anchor transport commutes with the SAME cached vertex-walk append. -/
theorem atAnchor_append (firstSheet middleSheet lastSheet : Fin 2)
    (first : VertexWalk lifted.vertices lifted.edges (anchor lifted firstSheet) (anchor lifted middleSheet))
    (last : VertexWalk lifted.vertices lifted.edges (anchor lifted middleSheet) (anchor lifted lastSheet)) :
    atAnchor (lifted := lifted) firstSheet lastSheet (first.append last) =
      (atAnchor (lifted := lifted) firstSheet middleSheet first).append (atAnchor middleSheet lastSheet last) :=
  AxisChainCoherence.Walk.castEndpoints_append first.walk last.walk
    (anchor_coordinate (lifted := lifted) firstSheet) (anchor_coordinate (lifted := lifted) middleSheet)
    (anchor_coordinate (lifted := lifted) lastSheet)

/-- The actual stationary anchor vertex walk projects to the genuine empty walk. -/
theorem atAnchor_nil (sheet : Fin 2) :
    atAnchor (lifted := lifted) sheet sheet (VertexWalk.nil lifted.vertices lifted.edges (anchor lifted sheet)) =
      Walk.nil (Ambient curve).anchor := by
  have stationary : ∀ first last (same : first = last),
      (Walk.nil first : Walk base.bank.grid first first).castEndpoints same same = Walk.nil last := by
    intro first last same
    cases same
    rfl
  exact stationary _ _ (anchor_coordinate (lifted := lifted) sheet)

/-- Transporting genuine endpoint vertex equalities preserves the SAME projected anchor walk.

Only equality of the actual retained lifted indices is accepted here.
Scalar coordinate equality or a sheet label is not used to identify roots.
-/
theorem atAnchor_cast (firstSheet lastSheet nextFirst nextLast : Fin 2)
    (path : VertexWalk lifted.vertices lifted.edges (anchor lifted firstSheet) (anchor lifted lastSheet))
    (firstEq : anchor lifted firstSheet = anchor lifted nextFirst)
    (lastEq : anchor lifted lastSheet = anchor lifted nextLast) :
    atAnchor (lifted := lifted) nextFirst nextLast (path.castVertices firstEq lastEq) =
      atAnchor (lifted := lifted) firstSheet lastSheet path := by
  have project : ∀ {first last nextFirst nextLast : Fin lifted.vertices.count}
      (path : VertexWalk lifted.vertices lifted.edges first last) (firstEq : first = nextFirst)
      (lastEq : last = nextLast)
      (firstCoordinate : lifted.vertices.coordinate first = (Ambient curve).anchor)
      (lastCoordinate : lifted.vertices.coordinate last = (Ambient curve).anchor)
      (nextFirstCoordinate : lifted.vertices.coordinate nextFirst = (Ambient curve).anchor)
      (nextLastCoordinate : lifted.vertices.coordinate nextLast = (Ambient curve).anchor),
      (path.castVertices firstEq lastEq).walk.castEndpoints nextFirstCoordinate nextLastCoordinate =
        path.walk.castEndpoints firstCoordinate lastCoordinate := by
    intro first last nextFirst nextLast path firstEq lastEq firstCoordinate lastCoordinate
      nextFirstCoordinate nextLastCoordinate
    cases firstEq
    cases lastEq
    rfl
  exact project path firstEq lastEq (anchor_coordinate (lifted := lifted) firstSheet)
    (anchor_coordinate (lifted := lifted) lastSheet)
    (anchor_coordinate (lifted := lifted) nextFirst) (anchor_coordinate (lifted := lifted) nextLast)

/-- The actual retained one-branch lift projects to its SAME original reference walk. -/
theorem atAnchor_liftedLoop (bank : BasedBranchBank lifted) (index : Data.Index branches) (sheet : Fin 2) :
    atAnchor (lifted := lifted) sheet (otherSheet sheet) (bank.liftedLoop index sheet) =
      (bank.rows.get index).reference.walk := by
  have undo : ∀ {first last a b : Canonical} (path : Walk base.bank.grid first last)
      (firstEq : a = first) (lastEq : b = last),
      (path.castEndpoints firstEq.symm lastEq.symm).castEndpoints firstEq lastEq = path := by
    intro first last a b path firstEq lastEq
    cases firstEq
    cases lastEq
    rfl
  exact undo (bank.rows.get index).reference.walk (anchor_coordinate (lifted := lifted) sheet)
    (anchor_coordinate (lifted := lifted) (otherSheet sheet))

namespace Pair

variable {bank : BasedBranchBank lifted} {first last : Data.Index branches} {sheet : Fin 2}

/-- The GIVEN closed pair projects to its two original branch references in their true original order. -/
theorem atAnchor_closed (pair : Pair bank first last sheet) :
    atAnchor (lifted := lifted) sheet sheet pair.closed = bank.loopProduct [first, last] := by
  have divided := (congrArg (atAnchor (lifted := lifted) sheet sheet) pair.closed_eq).trans
    (atAnchor_append sheet (otherSheet sheet) sheet pair.outward pair.returning)
  have outward := (congrArg (atAnchor (lifted := lifted) sheet (otherSheet sheet)) pair.outward_eq).trans
    (atAnchor_liftedLoop bank first sheet)
  have returning := (congrArg (atAnchor (lifted := lifted) (otherSheet sheet) sheet) pair.returning_eq).trans
    ((atAnchor_cast (otherSheet sheet) (otherSheet (otherSheet sheet)) (otherSheet sheet) sheet
      (bank.liftedLoop last (otherSheet sheet)) rfl
      (congrArg (anchor lifted) (otherSheet_other sheet))).trans
      (atAnchor_liftedLoop bank last (otherSheet sheet)))
  have result := divided.trans (congrArg₂ Walk.append outward returning)
  exact result.trans (congrArg (fun walk => (bank.rows.get first).reference.walk.append walk)
    (bank.rows.get last).reference.walk.append_nil.symm)

namespace Prepared

variable {pair : Pair bank first last sheet} {source : Differential genus}

/-- Reindex the SAME GIVEN pair period's full closed preparation through the genuine common point/Owner readbacks. -/
def atAnchor (prepared : Prepared pair source) : RootClosedWalk base.bank.grid (Ambient curve).anchor
    ((lifted.frames.frameAt _ (FramedBranchCellBank.baseMember base.bank)).owners sheet) :=
  prepared.period.closed.castBase (anchor_coordinate (lifted := lifted) sheet)
    (anchor_owner_heq (lifted := lifted) sheet)

/-- The original traced preparation, cover, cached names and operational return remain the SAME complete value. -/
theorem atAnchor_heq (prepared : Prepared pair source) : HEq prepared.atAnchor prepared.period.closed :=
  prepared.period.closed.castBase_heq (anchor_coordinate (lifted := lifted) sheet)
    (anchor_owner_heq (lifted := lifted) sheet)

/-- The transported whole pair preparation has the actual original two-factor common-anchor walk. -/
theorem atAnchor_walk (prepared : Prepared pair source) :
    prepared.atAnchor.walk = bank.loopProduct [first, last] :=
  (prepared.period.closed.castBase_walk (anchor_coordinate (lifted := lifted) sheet)
    (anchor_owner_heq (lifted := lifted) sheet)).trans
    ((congrArg (fun walk => walk.castEndpoints (anchor_coordinate (lifted := lifted) sheet)
      (anchor_coordinate (lifted := lifted) sheet))
      prepared.walk_eq).trans pair.atAnchor_closed)

end Prepared
end Pair

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank

end
