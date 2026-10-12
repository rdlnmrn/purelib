module
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.SourceContactPositivity
import Purelib.Topology.Surface.Boundary.BoundaryContactSources
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveAccounting
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Topology.Surface.Word.ProjectedEdgePairs
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
public import Purelib.Topology.Surface.Boundary.BoundaryContactErrors
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch

open Purelib.Data.Rat

open Purelib.Curves

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

/-!
# One retained contact preparation for sewn and exposed internal edges

The assembly contacts control inherited changes of face values. The exposed
cut pairs need their own original face comparisons as well. Both finite lists
are prepared together before any accuracy request, without dropping genuine
one-sided boundary components or asserting that a cut jump vanishes.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {patch : Topology.Surface.Sewing.SewingTree.SewnPatch mesh.triangulation.faces}

set_option genInjectivity false in
/-- One retained contact preparation for the original sewing contacts and exposed boundary pairs.

The actual concatenated contacts, assembly shape and pair count are cached before an accuracy request. -/
structure BoundaryContactPreparations (patch : Topology.Surface.Sewing.SewingTree.SewnPatch mesh.triangulation.faces)
    (pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels patch.cut.boundary)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) where
  /-- The original assembly's sewing-contact bank. -/ sewing : Topology.Surface.Sewing.SewnPrimitiveContacts.ContactBank
    patch.assembly
  /-- The actual contact bank for the original projected boundary pairing. -/ boundary :
    Topology.Surface.Boundary.BoundaryContactSources.BoundaryContactBank patch.cut pairing
  /-- The cached concatenation of both original contact lists. -/ contacts : List
    (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
  /-- The combined list is exactly sewing contacts followed by boundary contacts. -/ contacts_eq : contacts =
    sewing.entries ++ boundary.contacts
  /-- The retained original assembly shape. -/ profile : Topology.Surface.Sewing.SewnPrimitiveAccounting.Shape
  /-- The profile equals the actual assembly shape. -/ profile_eq : profile =
    Topology.Surface.Sewing.SewnPrimitiveAccounting.shape patch.assembly
  /-- The cached number of original boundary pairs. -/ pairCount : Nat
  /-- The count equals the actual pairing length. -/ pairCount_eq : pairCount = pairing.pairs.length
  /-- The shared preparation of those exact original contacts. -/ prepared :
    Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts differential domains

constructive_injectivity BoundaryContactPreparations

namespace BoundaryContactPreparations

variable {pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels
  patch.cut.boundary}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}

/-- Prepare the concatenated contacts of the supplied original sewing and boundary banks using their retained positivity
proofs. -/
@[expose] def ofBanks (sewing : Topology.Surface.Sewing.SewnPrimitiveContacts.ContactBank patch.assembly) (boundary :
  Topology.Surface.Boundary.BoundaryContactSources.BoundaryContactBank patch.cut pairing)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) :
    Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations patch pairing differential domains
      :=
  let contacts := sewing.entries ++ boundary.contacts
  let prepared := Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.build contacts (fun contact member
    =>
    (Data.List.Membership.mem_append.mp member).elim
      (Topology.Mesh.SourceContactPositivity.ContactBank.positive sewing contact)
      (boundary.positive contact)) differential domains
  ⟨sewing, boundary, contacts, rfl, Topology.Surface.Sewing.SewnPrimitiveAccounting.shape patch.assembly, rfl,
    pairing.pairs.length, rfl, prepared⟩

/-- Build the original sewing and boundary banks, then prepare their exact combined contact list. -/
@[expose] def build (patch : Topology.Surface.Sewing.SewingTree.SewnPatch mesh.triangulation.faces)
    (pairing : Topology.Surface.Word.ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels patch.cut.boundary)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) :
    Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations patch pairing differential domains
      :=
  Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations.ofBanks
    (Topology.Surface.Sewing.SewnPrimitiveContacts.ContactBank.build patch.assembly)
    (Topology.Surface.Boundary.BoundaryContactSources.BoundaryContactBank.build patch.cut pairing) differential domains

/-- Every original assembly contact occurs in the retained combined list. -/
theorem sewing_mem (prepared : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations patch
  pairing differential domains)
    (contact : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces) (member : contact ∈
      Topology.Surface.Sewing.SewnPrimitiveContacts.sourceContacts patch.assembly) : contact ∈ prepared.contacts := by
  rw [prepared.contacts_eq]
  exact Data.List.Membership.mem_append.mpr (Or.inl (prepared.sewing.entries_eq.symm ▸ member))

/-- Each retained projected boundary pair contributes its actual contact to the combined list. -/
theorem boundary_mem (prepared : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations patch
  pairing differential domains) (entry : Fin pairing.pairs.length) :
    (prepared.boundary.entries.get entry).contact ∈ prepared.contacts := by
  rw [prepared.contacts_eq]
  exact Data.List.Membership.mem_append.mpr (Or.inr (prepared.boundary.contact_mem entry))

/-- A sufficiently late shared triangle reading satisfies the original assembly's local accuracy from the retained
contact coverage. -/
theorem localAccuracy (prepared : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations patch
  pairing differential domains)
    {target tolerance : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat} (request :
      Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request prepared.prepared target floor)
    (within : target ≤ tolerance) {index : Nat} (later : request.index ≤ index)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
      (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh)
    {values : Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues patch.cut.count} (readings :
      Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly.Readings triangles.values patch.assembly values) :
    Topology.Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy tolerance readings :=
  request.localAccuracy_of_coverage prepared.sewing_mem within later triangles readings

/-- The retained boundary mismatch is below its target at every sufficiently late shared reading. -/
theorem boundary_accurate (prepared : Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts.BoundaryContactPreparations
  patch pairing differential domains)
    {target tolerance : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} (boundary :
      Topology.Surface.Boundary.BoundaryContactErrors.BoundaryContactRequest patch.assembly target)
    {floor : Nat} (request : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request
      prepared.prepared tolerance floor) (within : tolerance ≤ boundary.tolerance)
    {index : Nat} (later : request.index ≤ index) {shared :
      Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
    (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh) {values :
      Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues patch.cut.count}
    (readings : Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly.Readings triangles.values patch.assembly
      values) (entry : Fin pairing.pairs.length) :
    Topology.Surface.Boundary.BoundaryContactErrors.BoundaryContactSources.mismatch
      (prepared.boundary.entries.get entry) values < target :=
  boundary.accurate (prepared.boundary.entries.get entry) readings (prepared.localAccuracy request within later
    triangles readings)
    ((request.mismatch_lt later triangles _ (prepared.boundary_mem entry)).le.trans within)

end BoundaryContactPreparations
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
