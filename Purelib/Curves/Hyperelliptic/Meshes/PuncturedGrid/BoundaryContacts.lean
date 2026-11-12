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

open Purelib.Topology.Surface

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

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {patch : Sewing.SewingTree.SewnPatch mesh.triangulation.faces}

set_option genInjectivity false in
/-- One retained contact preparation for the original sewing contacts and exposed boundary pairs.

The actual concatenated contacts, assembly shape and pair count are cached before an accuracy request. -/
structure BoundaryContactPreparations (patch : Sewing.SewingTree.SewnPatch mesh.triangulation.faces)
    (pairing : Word.ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels patch.cut.boundary)
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames faces.regulars) where
  /-- The original assembly's sewing-contact bank. -/ sewing : Sewing.SewnPrimitiveContacts.ContactBank
    patch.assembly
  /-- The actual contact bank for the original projected boundary pairing. -/ boundary :
    Boundary.BoundaryContactSources.BoundaryContactBank patch.cut pairing
  /-- The cached concatenation of both original contact lists. -/ contacts : List
    (Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
  /-- The combined list is exactly sewing contacts followed by boundary contacts. -/ contacts_eq : contacts =
    sewing.entries ++ boundary.contacts
  /-- The retained original assembly shape. -/ profile : Sewing.SewnPrimitiveAccounting.Shape
  /-- The profile equals the actual assembly shape. -/ profile_eq : profile =
    Sewing.SewnPrimitiveAccounting.shape patch.assembly
  /-- The cached number of original boundary pairs. -/ pairCount : Nat
  /-- The count equals the actual pairing length. -/ pairCount_eq : pairCount = pairing.pairs.length
  /-- The shared preparation of those exact original contacts. -/ prepared :
    ContactBanks.ContactPreparations contacts differential domains

constructive_injectivity BoundaryContactPreparations

namespace BoundaryContactPreparations

variable {pairing : Word.ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels
  patch.cut.boundary}
  {differential : Differentials.Basic.Differential genus} {domains :
    Face.DomainBanks.FaceDomainBank frames faces.regulars}

/-- Prepare the concatenated contacts of the supplied original sewing and boundary banks using their retained positivity
proofs. -/
@[expose] def ofBanks (sewing : Sewing.SewnPrimitiveContacts.ContactBank patch.assembly) (boundary :
  Boundary.BoundaryContactSources.BoundaryContactBank patch.cut pairing)
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames faces.regulars) :
    BoundaryContactPreparations patch pairing differential domains
      :=
  let contacts := sewing.entries ++ boundary.contacts
  let prepared := ContactBanks.ContactPreparations.build contacts (fun contact member
    =>
    (Data.List.Membership.mem_append.mp member).elim
      (Topology.Mesh.SourceContactPositivity.ContactBank.positive sewing contact)
      (boundary.positive contact)) differential domains
  ⟨sewing, boundary, contacts, rfl, Sewing.SewnPrimitiveAccounting.shape patch.assembly, rfl,
    pairing.pairs.length, rfl, prepared⟩

/-- Build the original sewing and boundary banks, then prepare their exact combined contact list. -/
@[expose] def build (patch : Sewing.SewingTree.SewnPatch mesh.triangulation.faces)
    (pairing : Word.ProjectedEdgePairs.ProjectedEdgePairing patch.cut.vertexLabels patch.cut.boundary)
    (differential : Differentials.Basic.Differential genus) (domains :
      Face.DomainBanks.FaceDomainBank frames faces.regulars) :
    BoundaryContactPreparations patch pairing differential domains
      :=
  BoundaryContactPreparations.ofBanks
    (Sewing.SewnPrimitiveContacts.ContactBank.build patch.assembly)
    (Boundary.BoundaryContactSources.BoundaryContactBank.build patch.cut pairing) differential domains

/-- Every original assembly contact occurs in the retained combined list. -/
theorem sewing_mem (prepared : BoundaryContactPreparations patch
  pairing differential domains)
    (contact : Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces) (member : contact ∈
      Sewing.SewnPrimitiveContacts.sourceContacts patch.assembly) : contact ∈ prepared.contacts := by
  rw [prepared.contacts_eq]
  exact Data.List.Membership.mem_append.mpr (Or.inl (prepared.sewing.entries_eq.symm ▸ member))

/-- Each retained projected boundary pair contributes its actual contact to the combined list. -/
theorem boundary_mem (prepared : BoundaryContactPreparations patch
  pairing differential domains) (entry : Fin pairing.pairs.length) :
    (prepared.boundary.entries.get entry).contact ∈ prepared.contacts := by
  rw [prepared.contacts_eq]
  exact Data.List.Membership.mem_append.mpr (Or.inr (prepared.boundary.contact_mem entry))

/-- A sufficiently late shared triangle reading satisfies the original assembly's local accuracy from the retained
contact coverage. -/
theorem localAccuracy (prepared : BoundaryContactPreparations patch
  pairing differential domains)
    {target tolerance : Coordinate} {floor : Nat} (request :
      ContactBanks.ContactPreparations.Request prepared.prepared target floor)
    (within : target ≤ tolerance) {index : Nat} (later : request.index ≤ index)
    {shared : Face.PrimitiveData.FacePrimitiveBank differential index domains}
      (triangles : TrianglePrimitiveReadings.TriangleReadings shared mesh)
    {values : Sewing.PrimitiveSewing.PrimitiveValues patch.cut.count} (readings :
      Sewing.PrimitiveSewing.CutPatch.Assembly.Readings triangles.values patch.assembly values) :
    Sewing.SewnPrimitiveRequests.LocalAccuracy tolerance readings :=
  request.localAccuracy_of_coverage prepared.sewing_mem within later triangles readings

/-- The retained boundary mismatch is below its target at every sufficiently late shared reading. -/
theorem boundary_accurate (prepared : BoundaryContactPreparations
  patch pairing differential domains)
    {target tolerance : Coordinate} (boundary :
      Boundary.BoundaryContactErrors.BoundaryContactRequest patch.assembly target)
    {floor : Nat} (request : ContactBanks.ContactPreparations.Request
      prepared.prepared tolerance floor) (within : tolerance ≤ boundary.tolerance)
    {index : Nat} (later : request.index ≤ index) {shared :
      Face.PrimitiveData.FacePrimitiveBank differential index domains}
    (triangles : TrianglePrimitiveReadings.TriangleReadings shared mesh) {values :
      Sewing.PrimitiveSewing.PrimitiveValues patch.cut.count}
    (readings : Sewing.PrimitiveSewing.CutPatch.Assembly.Readings triangles.values patch.assembly
      values) (entry : Fin pairing.pairs.length) :
    Boundary.BoundaryContactErrors.BoundaryContactSources.mismatch
      (prepared.boundary.entries.get entry) values < target :=
  boundary.accurate (prepared.boundary.entries.get entry) readings (prepared.localAccuracy request within later
    triangles readings)
    ((request.mismatch_lt later triangles _ (prepared.boundary_mem entry)).le.trans within)

end BoundaryContactPreparations
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BoundaryContacts
