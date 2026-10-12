module
import Purelib.Data.Nat.Order
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Surface.Sewn.Selection.Basic
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Riemann.Topology.NewtonBandSewnHoleRequest
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Init.Data.List.Lemmas
import Init.Data.Nat.MinMax
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
import Purelib.Riemann.RootContinuation.NewtonBandWindowHole
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes

open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces

open Purelib.Riemann.Topology

open Purelib.Riemann.Topology.NewtonSewnExcision

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

public section

open Purelib.Data

/-! One later stage pays the physical-hole cancellation for every retained
annular entry, on the existing prepared tours and a shared primitive cache. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.SewnPhysicalRequests

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison.NewtonPreparation.FamilyAreaRequest
  (PairedAnnulus)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Integration.Surface.Sewn.Selection.Basic.SewnPrimitiveFaces.CachedSample (FaceSelection)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (sourceMask)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Riemann.Topology.NewtonBandSewnHoleRequest (sewnHoleRequest)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint OrientedTriangle edgeListArea)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {request : FamilyAreaRequest
    preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedAnnulus

/-- The exact selected area and the excision entry's positive physical polygons. -/
@[expose] def PhysicalSmallAt (entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains) (threshold :
  Nat) : Prop :=
  ∀ stage (cache : RegularMeshes.Numerics domains stage)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get first) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get second) lifted.mesh)
    (leftSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values)
    (rightSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values)
    (selected : CachedSample.FaceSelection leftSurface (AllHoleExcision.sourceMask entry.source.entry)),
    threshold ≤ stage →
    Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea (fun vertex =>
      (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint))
      (selected.triangles.flatMap OrientedTriangle.boundary) + AnnularEntry.physicalHoleArea entry.source.entry left
        right) ≤
        82 * (request.perHole / 4)

/-- Pay the bilinear physical-hole cancellation for the retained annular entry on the original shared primitive cache.
-/
@[expose] def physicalRequest (entry : FamilyAreaRequest.PairedAnnulus request lifted first second domains)
    (sewing : SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first second) (floor : Nat) :
    {threshold : Nat // floor ≤ threshold ∧
      PhysicalSmallAt entry threshold} :=
      by
  let acquired := NewtonBandSewnHoleRequest.sewnHoleRequest entry.sewn.comparison sewing floor
  refine ⟨acquired.val, acquired.property.1, ?_⟩
  intro stage cache left right leftSurface rightSurface selected later
  have estimate := acquired.property.2 stage cache left right leftSurface rightSurface selected later
  have same := AnnularEntry.band_physicalHoleArea entry.source.entry left right
  exact (congrArg (fun physical => Data.Gaussian.Norm.Basic.normSq (Stokes.edgeListArea (fun vertex =>
    (⟨leftSurface.sewn.values vertex, rightSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint))
      (selected.triangles.flatMap OrientedTriangle.boundary) + physical)) same).symm.trans_le estimate

/-- Prepare one common stage paying the bilinear physical-hole cancellation for every original annular entry.

The finite recursion retains the actual entry list, the shared sewing preparation and the requested minimum stage. -/
@[expose] def physicalRequests (sewing : SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first second)
    (floor : Nat) : (entries : List (FamilyAreaRequest.PairedAnnulus request lifted first second domains)) →
    {threshold : Nat // floor ≤ threshold ∧ ∀ entry ∈ entries,
      PhysicalSmallAt entry threshold}
  | [] => ⟨floor, le_rfl, by intro entry member; exact (List.not_mem_nil member).elim⟩
  | entry :: rest =>
      let head := physicalRequest entry
        sewing floor
      let tail :=
        physicalRequests sewing
        floor rest
      ⟨max head.val tail.val, head.property.1.trans (Nat.Order.le_max_left _ _), by
        intro candidate member stage cache left right leftSurface rightSurface selected later
        rcases List.Membership.mem_cons.mp member with same | present
        · cases same
          exact head.property.2 stage cache left right leftSurface rightSurface selected
            ((Nat.Order.le_max_left _ _).trans later)
        · exact tail.property.2 candidate present stage cache left right leftSurface rightSurface selected
            ((Nat.Order.le_max_right _ _).trans later)⟩

end PairedAnnulus
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.SewnPhysicalRequests
