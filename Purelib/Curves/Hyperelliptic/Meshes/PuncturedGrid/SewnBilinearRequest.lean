module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Nat.Order
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.Bilinear.Errors
public import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Topology.Surface.Sewing.Bilinear.Coverage
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Topology.Surface.Sewing.Bilinear.Requests

open Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

/-! Automatic two-row sewing comparison on the original shared triangle bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Data

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ContactBanks (ContactPreparations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Topology.Surface.Sewing (SewingForest)
open Purelib.Topology.Surface.Sewing.SewingConnected.SewingForest (SinglePolygon)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts (ContactBank sourceContacts)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Topology.Surface.Sewing.Bilinear.Requests (AreaRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {forest : Topology.Surface.Sewing.SewingForest mesh.triangulation.faces} {domains :
    FaceDomainBank frames faces.regulars}
  {i j : Fin genus}

set_option genInjectivity false in
/-- The original paired differential magnitude and contact preparations on one retained sewn polygon. -/
structure BilinearPreparation (polygon : SewingForest.SinglePolygon forest)
    (domains : DomainBanks.FaceDomainBank frames faces.regulars) (i j : Fin genus) where
  /-- The cached magnitude request for the original first standard differential. -/ leftMagnitude :
    MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential i)
  /-- The cached magnitude request for the original second standard differential. -/ rightMagnitude :
    MagnitudeBank.FaceMagnitudeBank domains (PeriodMatrix.standardDifferential j)
  /-- The retained complete contact bank of this exact original polygon assembly. -/ contacts :
    SewnPrimitiveContacts.ContactBank polygon.patch.assembly
  /-- The first differential's preparations on these exact retained contacts and domains. -/ leftContacts :
    ContactBanks.ContactPreparations contacts.entries (PeriodMatrix.standardDifferential i) domains
  /-- The second differential's preparations on the same retained contacts and domains. -/ rightContacts :
    ContactBanks.ContactPreparations contacts.entries (PeriodMatrix.standardDifferential j) domains

constructive_injectivity BilinearPreparation

namespace BilinearPreparation
variable {polygon : SinglePolygon forest}

/-- Cache the original polygon's complete contact bank and both differential magnitude and contact preparations. -/
@[expose] def build (polygon : SewingForest.SinglePolygon forest) (domains : DomainBanks.FaceDomainBank frames
  faces.regulars) (i j : Fin genus) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation polygon domains i j :=
  let contacts := ContactBank.build polygon.patch.assembly
  ⟨FaceMagnitudeBank.build domains (PeriodMatrix.standardDifferential i),
    FaceMagnitudeBank.build domains (PeriodMatrix.standardDifferential j), contacts,
    ContactPreparations.ofAssembly contacts (PeriodMatrix.standardDifferential i) domains,
    ContactPreparations.ofAssembly contacts (PeriodMatrix.standardDifferential j) domains⟩

set_option genInjectivity false in
/-- A paid paired sewing-area budget and both contact requests on the original preparation. -/
structure Request (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation polygon
  domains i j) (target : SewnPrimitiveFaces.Coordinate) (floor : Nat) where
  /-- The retained area budget using the sum of the two original magnitude bounds. -/ budget : Requests.AreaRequest
    polygon.patch
    (prepared.leftMagnitude.bound + prepared.rightMagnitude.bound) target
  /-- The first contact request meeting both the caller floor and original first magnitude stage. -/ left :
    ContactPreparations.Request prepared.leftContacts budget.tolerance (max floor prepared.leftMagnitude.index)
  /-- The second contact request meeting both the caller floor and original second magnitude stage. -/ right :
    ContactPreparations.Request prepared.rightContacts budget.tolerance (max floor prepared.rightMagnitude.index)
  /-- The cached common stage paying both retained contact requests. -/ index : Nat
  /-- The common stage is exactly the maximum of the two retained contact stages. -/ index_eq : index = max left.index
    right.index

constructive_injectivity Request

namespace Request
variable {prepared : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation polygon
  domains i j} {target : Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- Allocate the positive original area target and cache both paid contact requests at their exact common maximum stage.
-/
@[expose] def build (prepared : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation
  polygon domains i j) (target : SewnPrimitiveFaces.Coordinate)
    (positive : 0 < target) (floor : Nat) :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request prepared target floor :=
  let budget := AreaRequest.build polygon.patch
    (prepared.leftMagnitude.bound + prepared.rightMagnitude.bound) target
    (add_nonneg prepared.leftMagnitude.nonnegative prepared.rightMagnitude.nonnegative) positive
  let left := ContactPreparations.Request.build prepared.leftContacts budget.tolerance budget.tolerance_positive
    (max floor prepared.leftMagnitude.index)
  let right := ContactPreparations.Request.build prepared.rightContacts budget.tolerance budget.tolerance_positive
    (max floor prepared.rightMagnitude.index)
  ⟨budget, left, right, max left.index right.index, rfl⟩

/-- The first retained contact request is paid at the common stage. -/
theorem left_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request
  prepared target floor) : request.left.index ≤ request.index := by
  rw [request.index_eq]
  exact Nat.Order.le_max_left _ _

/-- The second retained contact request is paid at the common stage. -/
theorem right_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request
  prepared target floor) : request.right.index ≤ request.index := by
  rw [request.index_eq]
  exact Nat.Order.le_max_right _ _

/-- The retained common stage meets the original caller floor. -/
theorem floor_le (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request
  prepared target floor) : floor ≤ request.index :=
  (Nat.Order.le_max_left _ _).trans (request.left.floor_le.trans request.left_le)

/-- All contact and magnitude premises are discharged at the shared later stage. Coverage reads every actual mesh
triangle exactly once. -/
theorem accurate (request : Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request
  prepared target floor) {stage : Nat} (later : request.index ≤ stage)
    {cache : RegularMeshes.Numerics domains stage}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    {leftSurface : SewnPrimitiveSamples.CachedSample polygon.patch left.values} {rightSurface :
      SewnPrimitiveSamples.CachedSample polygon.patch right.values}
    (sample : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface) :
    Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (TriangleReadings.bilinearArea
      left right)) < target := by
  have coverage : ∀ contact ∈ SewnPrimitiveContacts.sourceContacts polygon.patch.assembly, contact ∈
    prepared.contacts.entries := by
    intro contact member
    rw [prepared.contacts.entries_eq]
    exact member
  have leftAccuracy := request.left.localAccuracy_of_coverage coverage le_rfl
    (request.left_le.trans later) left leftSurface.sewn.readings
  have rightAccuracy := request.right.localAccuracy_of_coverage coverage le_rfl
    (request.right_le.trans later) right rightSurface.sewn.readings
  have bounded (source : Fin mesh.triangles.length) (which : Fin 3) :
      PrimitivePoint.Bounded
        (⟨left.values source which - left.values source 0,
          right.values source which - right.values source 0⟩ : Topology.Polygon.Stokes.PrimitivePoint)
        (prepared.leftMagnitude.bound + prepared.rightMagnitude.bound) := by
    constructor
    · have scalar := (FaceMagnitudeBank.triangle_bounded prepared.leftMagnitude
        ((Nat.Order.le_max_right _ _).trans (request.left.floor_le.trans (request.left_le.trans later))) left source
          which).trans
        (le_add_of_nonneg_right prepared.rightMagnitude.nonnegative)
      simpa only [-eq_self, -iff_self, Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
    · have scalar := (FaceMagnitudeBank.triangle_bounded prepared.rightMagnitude
        ((Nat.Order.le_max_right _ _).trans (request.right.floor_le.trans (request.right_le.trans later))) right source
          which).trans
        (le_add_of_nonneg_left prepared.leftMagnitude.nonnegative)
      simpa only [-eq_self, -iff_self, Data.Gaussian.Norm.Basic.normSq_eq_canonical] using scalar
  have estimate := request.budget.accurate sample leftAccuracy rightAccuracy
    (fun position => bounded (Errors.traceAt leftSurface position).source)
  change Data.Gaussian.Norm.Basic.normSq (sample.boundaryArea - FiniteSum.Fin.sumFin (fun position =>
    TriangleReadings.bilinearArea left right (Errors.traceAt leftSurface position).source)) < target at estimate
  rw [Coverage.source_sum polygon leftSurface (TriangleReadings.bilinearArea left right)] at estimate
  exact estimate

end Request
end BilinearPreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
