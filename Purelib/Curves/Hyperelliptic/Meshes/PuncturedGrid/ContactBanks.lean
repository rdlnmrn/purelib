module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
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
import Purelib.Topology.Mesh.TriangleSourceUniqueness
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactPreparation
public import Purelib.Topology.Mesh.SourceContactPositivity
public import Purelib.Data.Vector.Dependent
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.QuotientFreeOmega

public section

open Purelib.Curves

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

/-!
# Automatically covered contact banks and common accuracy thresholds

Every supplied positive contact is prepared once from retained mesh geometry,
including contacts on cuts left exposed by the sewing tree. Generated banks
can replace these preparations through their checked types.
Requests cache all scalar budgets and their finite maximum before numerical
face data are built. The bound applies to every later shared sample, not just
to one chosen evaluation or a family with an assumed geometric error rate.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open Purelib.Data.Vector (DependentVector)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {indices : List (Fin mesh.triangles.length)} {boundary : List (Topology.Polygon.Stokes.OrientedEdge vertices.count)}
  {patch : Topology.Surface.Cut.Patch.CutPatch mesh.triangulation.faces indices boundary} {assembly :
    Topology.Surface.Cut.Patch.CutPatch.Assembly mesh.triangulation.faces patch}

set_option genInjectivity false in
/-- The original positive-contact preparations aligned with every retained contact occurrence.

Keep their actual source owners and the supplied differential and shared domain bank. -/
structure ContactPreparations (contacts : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact
  mesh.triangulation.faces)) (differential : Hyperelliptic.Differentials.Basic.Differential genus)
    (domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) where
  /-- The dependent original preparation for every retained contact occurrence. -/ entries : Data.Vector.DependentVector
    (fun index : Fin contacts.length =>
    ContactPreparation contacts[index.val] differential domains)

constructive_injectivity ContactPreparations

namespace ContactPreparations

variable {contacts : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)}
  {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}

/-- Prepare every retained positive contact once from its actual mesh geometry and original containment evidence. -/
@[expose] def build (contacts : List (Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact
  mesh.triangulation.faces))
    (positive : ∀ contact ∈ contacts,
      Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive contact.left mesh.triangulation.faces ∧
      Topology.Mesh.TriangleSourceUniqueness.SourceEdge.Positive contact.right mesh.triangulation.faces)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) :
    Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts differential domains :=
  ⟨DependentVector.ofFn fun index => ContactPreparation.build mesh
    contacts[index.val]
    (positive _ (List.getElem_mem _)) differential domains⟩

/-- Sewing contacts obtain positivity from their retained boundary owners. -/
@[expose] def ofAssembly (contacts : Topology.Surface.Sewing.SewnPrimitiveContacts.ContactBank assembly)
    (differential : Hyperelliptic.Differentials.Basic.Differential genus) (domains :
      Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars) :
    Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts.entries differential domains :=
  Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.build contacts.entries
    (Topology.Mesh.SourceContactPositivity.ContactBank.positive contacts) differential domains

set_option genInjectivity false in
/-- The cached maximum includes every occurrence, including repeated
contacts, and preserves an independently selected lower index. -/
structure Request (prepared : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts differential
  domains) (target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate) (floor : Nat) where
  /-- The original contact-error target is positive. -/ positive : 0 < target
  /-- The actual scalar budget for every retained contact preparation. -/ budgets : Data.Vector.DependentVector (fun
    index => (prepared.entries.get index).Budget target)
  /-- The cached maximum of the original contact-budget stages. -/ maximum : Nat
  /-- The cached maximum is the exact dependent fold over all retained contact occurrences. -/ maximum_eq : maximum =
    budgets.maximum (fun index budget => (prepared.entries.get index).budgetIndex budget)
  /-- The common contact stage including the original requested floor. -/ index : Nat
  /-- The stage equals the maximum of the floor and actual original budget maximum. -/ index_eq : index = max floor
    maximum

constructive_injectivity Request

namespace Request

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts
  differential domains} {target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- Cache every original scalar contact budget and their exact maximum above the supplied stage floor. -/
@[expose] def build (prepared : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations contacts
  differential domains) (target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate) (positive : 0 < target)
    (floor : Nat) : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request prepared target floor :=
  let budgets := Data.Vector.DependentVector.ofFn fun index => (prepared.entries.get index).budget target positive
  let maximum := budgets.maximum (fun index budget => (prepared.entries.get index).budgetIndex budget)
  ⟨positive, budgets, maximum, rfl, max floor maximum, rfl⟩

/-- The retained common contact stage meets the original requested floor. -/
theorem floor_le (request : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request prepared target
  floor) : floor ≤ request.index := by
  rw [request.index_eq]
  exact Purelib.Data.Nat.Order.le_max_left _ _

/-- Every original contact budget is ready by the retained common stage. -/
theorem entry_le (request : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request prepared target
  floor) (entry : Fin contacts.length) :
    (prepared.entries.get entry).budgetIndex (request.budgets.get entry) ≤ request.index := by
  rw [request.index_eq, request.maximum_eq]
  exact (request.budgets.get_le_maximum (fun index budget => (prepared.entries.get index).budgetIndex budget)
    entry).trans
    (Purelib.Data.Nat.Order.le_max_right _ _)

/-- Every retained contact has mismatch below the original target at any sufficiently late shared sample. -/
theorem mismatch_lt (request : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request prepared
  target floor) {index : Nat} (later : request.index ≤ index)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
      (readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh)
    (contact : Topology.Surface.Sewing.SewnPrimitiveContacts.SourceContact mesh.triangulation.faces) (member : contact ∈
      contacts) :
    contact.mismatch readings.values < target := by
  rcases List.mem_iff_getElem.mp member with ⟨position, bound, equal⟩
  rw [← equal]
  exact (prepared.entries.get ⟨position, bound⟩).accurate request.positive (request.budgets.get ⟨position, bound⟩)
    ((request.entry_le ⟨position, bound⟩).trans later) readings

/-- This discharges the entire actual assembly, including every ancestor
correction; no local mismatch premise remains for the supplied sample. -/
theorem localAccuracy_of_coverage (request : Hyperelliptic.Meshes.PuncturedGrid.ContactBanks.ContactPreparations.Request
  prepared target floor)
    (coverage : ∀ contact ∈ Topology.Surface.Sewing.SewnPrimitiveContacts.sourceContacts assembly, contact ∈ contacts)
      {tolerance : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} (within : target ≤ tolerance)
    {index : Nat} (later : request.index ≤ index)
    {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
      (triangles : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared mesh)
    {values : Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues patch.count}
    (readings : Topology.Surface.Sewing.PrimitiveSewing.CutPatch.Assembly.Readings triangles.values assembly values) :
    Topology.Surface.Sewing.SewnPrimitiveRequests.LocalAccuracy tolerance readings :=
  Topology.Surface.Sewing.SewnPrimitiveContacts.localAccuracy_of_sourceContacts readings (fun contact member =>
    (request.mismatch_lt later triangles contact (coverage contact member)).le.trans within)

end Request
end ContactPreparations
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
