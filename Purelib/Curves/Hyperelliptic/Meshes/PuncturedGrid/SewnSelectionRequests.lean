module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic

import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
public import Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveRequests
import Purelib.Data.Nat.Order
open Purelib.Data.Nat

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

@[expose] public section

/-!
# Automatic selected-area requests on the retained shared face bank

Geometry and coarse references are prepared once. Every requested tolerance
then supplies a common late index, before the numerical triangles are built.
The result holds simultaneously for every selection mask and every later
shared sample; no numerical success assumption is supplied by the caller.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (FacePrimitiveBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Topology.Surface.Sewing.SewingTree (SewnPatch)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (SourceContact ContactBank sourceContacts)
open Purelib.Topology.Surface.Sewing.SewnFaceAreaComparison (FaceAreaRequest)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {patch : SewnPatch mesh.triangulation.faces} {domains :
    FaceDomainBank frames faces.regulars}
  {differential : Differential genus}

set_option genInjectivity false in
/-- The original differential's magnitude references and covered sewing contacts on a retained shared face bank. -/
structure SelectionAreaPreparation (patch : SewingTree.SewnPatch mesh.triangulation.faces)
    (domains : DomainBanks.FaceDomainBank frames faces.regulars) (differential : Differentials.Basic.Differential genus)
      where
  /-- The cached magnitude references on the exact original differential and face domains. -/ references :
    MagnitudeBank.FaceMagnitudeBank domains differential
  /-- The retained list of actual source contacts, possibly containing an existing covered superset. -/ contacts : List
    (SewnPrimitiveContacts.SourceContact mesh.triangulation.faces)
  /-- Every original polygon assembly contact belongs to the retained contact list. -/ coverage : ∀ contact ∈
    SewnPrimitiveContacts.sourceContacts patch.assembly, contact ∈ contacts
  /-- The differential's actual preparations on this exact retained contact list and domains. -/ covered :
    ContactBanks.ContactPreparations contacts differential domains

constructive_injectivity SelectionAreaPreparation

namespace SelectionAreaPreparation

/-- A caller with an existing covered contact superset may retain it directly in the structure. The default constructor
discharges coverage from the actual assembly and reuses the supplied domains unchanged. -/
def build (patch : SewingTree.SewnPatch mesh.triangulation.faces) (domains : DomainBanks.FaceDomainBank frames
  faces.regulars)
    (differential : Differentials.Basic.Differential genus) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation patch domains
      differential :=
  let contacts := ContactBank.build patch.assembly
  ⟨FaceMagnitudeBank.build domains differential, contacts.entries,
    fun _ member => contacts.entries_eq.symm ▸ member, ContactPreparations.ofAssembly contacts differential domains⟩

set_option genInjectivity false in
/-- A selected-area budget and complete paid contact request on the original preparation. -/
structure Request (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation
  patch domains differential) (target : SewnPrimitiveFaces.Coordinate) (floor : Nat) where
  /-- The retained face-area budget using the original cached magnitude bound. -/ budget :
    SewnFaceAreaComparison.FaceAreaRequest patch.assembly prepared.references.bound target
  /-- The retained contact request meeting both the caller floor and magnitude-reference stage. -/ contact :
    ContactPreparations.Request prepared.covered budget.sewing.tolerance (max floor prepared.references.index)

constructive_injectivity Request

namespace Request

variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation
  patch domains differential} {target : Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- Allocate the original positive selected-area target and cache its covered contact request above both retained stage
floors. -/
def build (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation patch
  domains differential) (target : SewnPrimitiveFaces.Coordinate)
    (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation.Request prepared target
      floor :=
  let budget := FaceAreaRequest.build patch.assembly prepared.references.bound target prepared.references.nonnegative
    positive
  ⟨budget, ContactPreparations.Request.build prepared.covered budget.sewing.tolerance budget.sewing.tolerance_positive
    (max floor prepared.references.index)⟩

/-- The actual retained contact stage meets the original caller floor. -/
theorem floor_le (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation.Request prepared target
  floor) : floor ≤ request.contact.index :=
  (Order.le_max_left _ _).trans request.contact.floor_le

/-- Every actual selection mask and shared later sample satisfy the original selected-area target. -/
theorem accurate (request :
  Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests.SelectionAreaPreparation.Request prepared target
  floor) {index : Nat} (later : request.contact.index ≤ index)
    {shared : PrimitiveData.FacePrimitiveBank differential index domains} (triangles :
      TrianglePrimitiveReadings.TriangleReadings shared mesh)
    (sample : SewnPrimitiveSamples.CachedSample patch triangles.values) {keep : Fin mesh.triangles.length → Bool}
    (selected : CachedSample.FaceSelection sample keep)
    (area : selected.LocalArea) : Data.Gaussian.Norm.Basic.normSq (selected.area - area.value) < target :=
  request.budget.accurate sample selected area
    (fun source which => prepared.references.triangle_bounded
      ((Order.le_max_right _ _).trans (request.contact.floor_le.trans later)) triangles source which)
    (request.contact.localAccuracy_of_coverage prepared.coverage le_rfl later triangles sample.sewn.readings)

end Request
end SelectionAreaPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSelectionRequests
