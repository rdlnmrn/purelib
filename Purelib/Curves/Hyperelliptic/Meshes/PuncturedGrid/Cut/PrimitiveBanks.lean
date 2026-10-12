module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.PreparedSegmentParentBanks
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshFaceEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PeriodSegmentBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedOwnerAlignment
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Paths.PreparedPathTrace
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.CutCycleChains
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.VertexSewing

open Purelib

open Purelib.Approximation

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Polynomial.Geometry

open Purelib.Riemann.Integration

open Purelib.Riemann.Meshes.GridLiftedMesh

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathDecomposition

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels.PreparedPath

open Purelib.Riemann.Paths.PreparedSegmentParentBanks.PreparedPath

open Purelib.Riemann.Topology

@[expose] public section

/-!
# Local primitive comparisons of the actual retained cut-cycle segments

Every occurrence uses its original owner, cached integration parents and
cover. Face models and both sheet domains come from one shared finite bank.
This constructs the local analytic comparisons without a caller-supplied
sheet or parent certificate; the global primitive-jump identity is separate.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedClearPathModels (PreparedPath)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Riemann.Paths.PreparedPathDecomposition.PreparedPath (CoveredSegments)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomains FaceDomainBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh (SegmentFace)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PreparedFaceSegments (AssignedSegments)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces} {ambient :
    Purelib.Geometry.Rational.Box}

set_option genInjectivity false in
/-- The local primitive comparison of one actual retained cut-cycle segment.

The original face-domain cache, selected sheet, incoming owner and integration parents remain attached to this exact
segment occurrence. -/
structure SegmentComparison {start finish : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment
  curve.polynomial ambient start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} (placement : LiftedMesh.SegmentFace mesh
      segment)
    (piece : PreparedPathDecomposition.CoveredSegment segment owner) (differential : Differentials.Basic.Differential
      genus) (parentSheet : Fin 2) where
  /-- The cached analytic domains for the actual face containing this segment occurrence. -/ domains :
    DomainBanks.FaceDomains frames placement.face
  /-- The retained local comparison using the original covered segment and integration cache. -/ entered :
    EnteredPaths.EnteredPath domains.models piece.path differential parentSheet
  /-- The comparison uses exactly the cached domain selected by its retained entry sheet. -/ domain_eq : entered.domain
    = domains.domain entered.entry.sheet
  /-- The selected analytic sheet is the actual sheet of the retained lifted face occurrence. -/ sheet_eq :
    entered.entry.sheet = placement.location.sheet

constructive_injectivity SegmentComparison

namespace SegmentComparison

/-- Construct the local comparisons by reusing each original segment parent cache and its retained owner alignment. -/
def build {start finish : Data.Gaussian.Basic.Canonical} {segment : ClearPath.ClearSegment curve.polynomial ambient
  start finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} (placement : LiftedMesh.SegmentFace mesh
      segment)
    (piece : PreparedPathDecomposition.CoveredSegment segment owner) (differential : Differentials.Basic.Differential
      genus) (parentSheet : Fin 2)
    (domains : DomainBanks.FaceDomainBank frames faces.regulars) (cache : PreparedClearPathModels.ParentCache piece.path
      differential parentSheet)
    (aligned : Nonempty (Gaussian.Equivalence.NamedEquivalent
      (OwnerTraceReadings.ownerName owner) (OwnerTraceReadings.ownerName (vertices.owner frames
        placement.indexed.start)))) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement piece
      differential parentSheet :=
  let localDomains := domains.atRoute placement.location
  let entry : FaceModels.Entry localDomains.models start owner :=
    placement.entry localDomains.models aligned
  let entered : EnteredPaths.EnteredPath localDomains.models piece.path differential parentSheet :=
    EnteredPath.ofEntry entry (localDomains.domain entry.sheet) piece.path placement.inside differential parentSheet
      cache
  ⟨localDomains, entered, rfl, rfl⟩

end SegmentComparison

namespace AssignedSegments

/-- A dependent bank of local primitive comparisons in exact retained segment-occurrence order. -/
def Comparisons (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2)
    {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient start
      finish}
    {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
      PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
    (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) : Type 2 := by
  induction assigned with
  | nil => exact PUnit
  | @cons start middle finish head tail owner first rest pieces placement remaining ih =>
      exact Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.SegmentComparison placement first
        differential parentSheet × ih

namespace Comparisons

/-- Construct the local comparisons by reusing each original segment parent cache and its retained owner alignment. -/
def build (domains : DomainBanks.FaceDomainBank frames faces.regulars) (differential : Differentials.Basic.Differential
  genus) (parentSheet : Fin 2) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces), CoveredSegments.ParentCaches differential
        parentSheet pieces →
      assigned.OwnersAligned →
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
        differential parentSheet assigned
  | _, _, _, _, _, _, .nil _ _, _, _ => ⟨⟩
  | _, _, _, _, _, _, .cons placement remaining, caches, aligned =>
      ⟨SegmentComparison.build placement _ differential parentSheet domains caches.1 aligned.1,

          build
          domains differential parentSheet remaining caches.2 aligned.2⟩

/-- Repeated occurrences really share the supplied finite domain bank. This is stronger than separately valid local
models on the same face. -/
def UsesDomains (domains : DomainBanks.FaceDomainBank frames faces.regulars) (differential :
  Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces),
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
        differential parentSheet assigned → Prop
  | _, _, _, _, _, _, .nil _ _, _ => True
  | _, _, _, _, _, _, .cons placement remaining, compared =>
      compared.1.domains = domains.atRoute placement.location ∧
        UsesDomains
        domains differential parentSheet remaining compared.2

/-- Every constructed segment comparison uses the exact entry of the supplied shared face-domain bank. -/
theorem build_usesDomains (domains : DomainBanks.FaceDomainBank frames faces.regulars) (differential :
  Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (caches : CoveredSegments.ParentCaches differential
        parentSheet pieces)
      (aligned : assigned.OwnersAligned),
      UsesDomains
        domains differential parentSheet assigned
        (build
        domains differential parentSheet assigned caches aligned)
  | _, _, _, _, _, _, .nil _ _, _, _ => trivial
  | _, _, _, _, _, _, .cons _ remaining, caches, aligned =>
      ⟨rfl,
        build_usesDomains
        domains differential parentSheet remaining caches.2 aligned.2⟩

/-- Read the actual retained integration parents in segment-occurrence order. -/
def parents (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces),
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
        differential parentSheet assigned →
        List (PreparedSubdivisionModelCore.CenteredEdge curve differential)
  | _, _, _, _, _, _, .nil _ _, _ => []
  | _, _, _, _, _, _, .cons _ remaining, compared =>
      compared.1.entered.cache.parents ++
        parents
        differential parentSheet remaining compared.2

/-- The local comparison parents equal the exact ordered parent list of the original covered segments. -/
theorem parents_eq (differential : Differentials.Basic.Differential genus) (parentSheet : Fin 2) :
    ∀ {start finish : Data.Gaussian.Basic.Canonical} {path : Polynomial.Geometry.ClearPath curve.polynomial ambient
      start finish}
      {owner : SquareRootContinuationChain.Owner (curve.polynomial.eval start)} {prepared :
        PreparedClearPathModels.PreparedPath path owner} {pieces : PreparedPath.CoveredSegments prepared}
      (assigned : PreparedFaceSegments.AssignedSegments mesh pieces) (compared :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons
        differential parentSheet assigned),
      parents
        differential parentSheet assigned compared = CoveredSegments.parents differential parentSheet pieces
  | _, _, _, _, _, _, .nil _ _, _ => rfl
  | _, _, _, _, _, _, .cons _ remaining, compared =>
      congrArg₂ List.append compared.1.entered.cache.parents_eq
        (parents_eq
        differential parentSheet remaining compared.2)

end Comparisons
end AssignedSegments
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.FaceBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.FaceBanks (FaceBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments (Comparisons)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.CyclePrograms (CutCycleProgram)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {source :
    Differential genus} {prepared :
    CutCycleProgram lifted source}

/-- The complete per-segment local comparison bank is constructed from the actual cut program; no incoming-owner
agreement or local preparation is an input. -/
def comparisons (bank : FaceBanks.FaceBank prepared) (domains : DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (differential : Differentials.Basic.Differential genus) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons differential
      0 bank.assigned :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.build domains
    differential 0 bank.assigned (bank.segments.parentCaches differential) bank.ownersAligned

/-- Every comparison in the retained cut-cycle face bank uses the supplied shared finite domain cache. -/
theorem comparisons_sharedDomains (bank : FaceBanks.FaceBank prepared) (domains : DomainBanks.FaceDomainBank
  lifted.frames base.faces.regulars)
    (differential : Differentials.Basic.Differential genus) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.UsesDomains
      domains differential 0 bank.assigned
      (comparisons bank domains differential) :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.build_usesDomains
    domains differential 0 bank.assigned (bank.segments.parentCaches differential) bank.ownersAligned

/-- Local comparisons retain the exact ordered integration parents consumed by the original period program, including
repeated segment occurrences. -/
theorem comparisons_parents (bank : FaceBanks.FaceBank prepared) (domains : DomainBanks.FaceDomainBank lifted.frames
  base.faces.regulars)
    (differential : Differentials.Basic.Differential genus) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents
      differential 0 bank.assigned
      (comparisons bank domains differential) =
      prepared.period.initial.state.parents.map (PreparedEdgeRecasting.recastCenteredEdge differential) :=
  (Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.LiftedMesh.AssignedSegments.Comparisons.parents_eq
    differential 0 bank.assigned _).trans (bank.parents_eq differential)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks.FaceBank
