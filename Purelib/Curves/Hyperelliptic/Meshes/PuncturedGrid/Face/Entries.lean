module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Int.Arithmetic
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Winding.Polygon.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.ClearBoxPathWinding
import Purelib.Riemann.Paths.ClearBoxPaths
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.RootContinuation.RootPathTransport
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
public import Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Init.Data.Int.Basic
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Automatic face-sheet assignment for an actual incoming owner

The incoming point may be any contained grid vertex, not only the face
anchor. One retained return preparation and endpoint classification identify
its sheet. The forward trace needed to justify that identification occurs
only in the erased reachability proof, never in later numerical requests.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Integration.Observation

open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy

open Purelib.Geometry

open Purelib.Polynomial.Geometry

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Polynomial.Geometry.Grid.FromStates

open Purelib.Polynomial.Winding

open Purelib.Riemann.Integration

open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.ClearBoxPathWinding

open Purelib.Riemann.Paths.ClearBoxPaths

open Purelib.Riemann.Paths.OwnerLoopMonodromy

open Purelib.Riemann.Paths.PreparedPathTrace

open Purelib.Riemann.Paths.PreparedPathWinding.PreparedClearPathModels

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.RootContinuation.RootPathTransport

open Purelib.Riemann.Topology

namespace Reached

open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached)

/-- Operationally equivalent original owners at the same point have a retained zero-winding reachability certificate.

The supplied operational comparison gives a join trace between the same two owners. Its zero winding equals the
difference of the identical face potentials at their retained point. -/
theorem ofEquivalent {polynomial : ClearPath.GaussianPolynomial} {box : Rational.Box} {point :
  Data.Gaussian.Basic.Canonical}
    {first last : SquareRootContinuationChain.Owner (polynomial.eval point)}
    (equivalent : Gaussian.Equivalence.NamedEquivalent (OwnerTraceReadings.ownerName first)
      (OwnerTraceReadings.ownerName last)) :
    PreparedFaceTracePrefixes.Reached box first last :=
  ⟨OwnerPath.join polynomial point first last equivalent,
    (OwnerPath.join_winding polynomial point first last equivalent).trans (Data.Int.Arithmetic.sub_eq_zero_of_eq
      rfl).symm⟩

end Reached

namespace FaceModels

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.RootContinuation.RootOwnerFrames (OwnerSelection)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.Paths.PreparedPathTrace (TracedPath)
open Purelib.Curves.Hyperelliptic.Integration.Observation.PreparedFaceTracePrefixes (Reached ParentReached)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels.BranchCellBank (FaceModels)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {face :
    RegularFace bank} {models :
    FaceModels frames face}
  {base : Purelib.Data.Gaussian.Basic.Canonical} {owner : Owner
    (curve.polynomial.eval base)}

set_option genInjectivity false in
/-- The computed sheet and its actual-owner reachability contract.

The retained sheet selects an original face-frame occurrence. The reachability certificate connects that exact
occurrence to the supplied incoming owner inside the same face box. -/
structure Entry (models : BranchCellBank.FaceModels frames face) (base : Data.Gaussian.Basic.Canonical) (owner :
  SquareRootContinuationChain.Owner (curve.polynomial.eval base)) where
  /-- The retained actual source-frame sheet assigned to the original incoming owner. -/ sheet : Fin 2
  /-- The original incoming owner is reached from this exact retained face-frame occurrence inside the face. -/ reached
    : PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners sheet) owner

constructive_injectivity Entry

namespace Entry

/-- No return preparation or classification is needed at a retained origin owner.

The supplied sheet and its original frame owner are retained directly. Reflexive reachability certifies the face
occurrence without constructing a return trace. -/
@[expose] def origin (models : BranchCellBank.FaceModels frames face) (sheet : Fin 2) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry models face.cell.box.anchor
      (models.frame.owners sheet) :=
  ⟨sheet, Reached.refl _⟩

/-- Reuse an actual or generated return trace and its cached classification.

The supplied return trace and classification determine the retained sheet index. Reachability is a proposition: the
auxiliary forward trace proves the owner relationship without adding executable work to later requests. -/
@[expose] def ofReturn (models : BranchCellBank.FaceModels frames face) (member :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid base)
    (inside : face.cell.box.Contains base)
    (route : ClearBoxPaths.Route curve.polynomial face.cell.box base face.cell.box.anchor)
    (returned : PreparedPathTrace.TracedPath route.path owner) (selected : RootOwnerFrames.OwnerSelection
      models.frame.owners returned.finishOwner) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry models base owner := by
  refine ⟨selected.index, ?_⟩
  let forward := Route.build face.clearance face.cell.box.anchor base face.cell.box.contains_anchor inside
  let traced := TracedPath.build forward.path forward.within (models.frame.owners selected.index)
  let join := OwnerPath.join curve.polynomial face.cell.box.anchor returned.finishOwner
    (models.frame.owners selected.index) selected.equivalent
  let loop := returned.trace.get.append (join.append traced.trace.get)
  have winding : Polygon.Basic.chainRaw curve.polynomial base loop.vertices = 8 * (0 : Int) := by
    rw [OwnerPath.append_winding, OwnerPath.append_winding, TracedPath.winding_original returned,
      TracedPath.winding_original traced,
      OwnerPath.join_winding, Route.winding face.clearance (BranchIsolation.degreePositive curve) route inside,
      Route.winding face.clearance (BranchIsolation.degreePositive curve) forward face.cell.box.contains_anchor]
    omega
  have equivalent := OwnerPath.rootEquivalent_of_even_with_reference (BranchCellBank.referenceAt bank base
    member).toLoop loop 0 winding
  have reached : PreparedFaceTracePrefixes.Reached face.cell.box (models.frame.owners selected.index) traced.finishOwner
    :=
    ⟨traced.trace.get, (TracedPath.winding_original traced).trans
      (Route.winding face.clearance (BranchIsolation.degreePositive curve) forward face.cell.box.contains_anchor)⟩
  exact reached.append (Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.Reached.ofEquivalent equivalent)

/-- A total finite assignment for the supplied incoming owner.

The retained clear face constructs a return route to its anchor. That route's prepared terminal owner is classified
against the same original frame, and its selected sheet is retained with actual-owner reachability. -/
@[expose] def acquire (models : BranchCellBank.FaceModels frames face) (member :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex bank.grid base)
    (inside : face.cell.box.Contains base) (owner : SquareRootContinuationChain.Owner (curve.polynomial.eval base)) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry models base owner :=
  let route := Route.build face.clearance base face.cell.box.anchor inside face.cell.box.contains_anchor
  let returned := TracedPath.build route.path route.within owner
  let selected := models.frame.select returned.finishOwner
  ofReturn models member inside route returned
    selected

/-- Propagate the assigned face occurrence through the actual inherited owners and query handoffs of any contained
retained preparation.

The supplied preparation stays inside the same face box and retains its original lineage. Membership in its
centered-parent list transports the same incoming face occurrence to the actual parent owner. -/
theorem parent_reached (entry : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels.Entry models base
  owner) (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {ambient : Rational.Box} {finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath
      curve.polynomial ambient base finish}
    (traced : PreparedPathTrace.TracedPath path owner) (inside : ClearPath.InBox face.cell.box path)
    (parent : PreparedSubdivisionModelCore.CenteredEdge curve differential)
    (membership : parent ∈ (CenteredPathChain.ofPreparedPath
      curve differential parentSheet traced.prepared).parents) :
    PreparedFaceTracePrefixes.ParentReached face.cell.box (models.frame.owners entry.sheet) parent :=
  (PreparedFaceTracePrefixes.lineage_reached face.clearance differential parentSheet traced.lineage inside
    entry.reached).1 parent membership

end Entry

end FaceModels

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
