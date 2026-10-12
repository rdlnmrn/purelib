module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowSelectedRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest
import Purelib.Riemann.Periods.BilinearBoundaryReadback
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnBilinearRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleSums

open Purelib.Data.Rat

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

open Purelib.Riemann.Topology.NewtonSewnExcision

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.Bilinear.Samples
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear

@[expose] public section

/-! The original branch-region receipt uses exactly the fine triangles
selected inside its enclosing cell, with the hole absent from that list. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.SelectedSewing

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance (PairedSample)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (sourceFace sourcePosition_triangleIndex)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings (bilinearArea)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedTrianglePartition (selectedFullTriangleArea)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Numerics
    domains stage}

/-- The actual source triangles selected inside the original branch cell sum to its complete retained fine triangle
area. -/
private theorem source_sum (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh)
    (right : TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) :
    FiniteSum.Fin.sumFin (fun source => if decide ((AllHoleExcision.sourceFace current source).cell.box.Refines
      (base.bank.cell index).box)
      then TriangleReadings.bilinearArea left right source else 0) =
      SelectedTrianglePartition.selectedFullTriangleArea left right (fun position =>
        decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (base.bank.cell index).box)) := by
  rw [LiftedMesh.triangle_sum current.mesh]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  apply FiniteSum.Fin.sumFin_congr
  intro sheet
  have mask (upper : Bool) :
      decide ((AllHoleExcision.sourceFace current (current.mesh.triangleIndex position sheet upper)).cell.box.Refines
        (base.bank.cell index).box) =
      decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (base.bank.cell index).box) :=
    congrArg (fun position : Fin grid.faces.regulars.length =>
      decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (base.bank.cell index).box))
      (AllHoleExcision.sourcePosition_triangleIndex current position sheet upper)
  rw [mask false, mask true]
  rfl

/-- The sewing estimate is read on the actual cached original branch region, retaining its own selected cut triangles
and both primitive owners. -/
theorem selected_accurate
    {outer : NewtonOriginalAnnularFaces.OriginalAnnularFaces grid index} {annulus : Faces.AnnularFaces grid index}
    {region : LiftedBoundary.Lifted annulus current}
    {geometry : HoleSewing.IncludedHoleSewing bank grid.shrunk.included index domains (PeriodMatrix.standardDifferential
      i)}
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh)
    {leftSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample current.cutPolygon.patch right.values}
    {balance : OriginalCutBalance outer region geometry leftSurface}
    (sample : OriginalPairedCutBalance.PairedSample balance rightSurface)
    {prepared : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i j} {error : Fraction.Rational}
      {floor : Nat}
    (request : BilinearPreparation.Request prepared error floor) (later : request.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (sample.area - SelectedTrianglePartition.selectedFullTriangleArea left
      right (fun position =>
      decide ((grid.faces.regulars[position.val]'position.isLt).cell.box.Refines (base.bank.cell index).box))) < error
        := by
  let bilinear := Bilinear.build leftSurface rightSurface
  have estimated := BilinearPreparation.Request.selected_accurate request later left right bilinear balance.selected
  have area : Stokes.edgeListArea bilinear.values (balance.selected.triangles.flatMap OrientedTriangle.boundary) =
    sample.area :=
    (BilinearBoundaryReadback.triangles_eq_raw bilinear _).trans sample.area_eq.symm
  rw [area] at estimated
  exact (congrArg (fun triangles => Data.Gaussian.Norm.Basic.normSq (sample.area - triangles))
    (source_sum (index := index) left right)).symm.trans_lt
      estimated

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.SelectedSewing
