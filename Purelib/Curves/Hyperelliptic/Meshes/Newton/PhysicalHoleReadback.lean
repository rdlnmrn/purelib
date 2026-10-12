module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
public import Purelib.Riemann.RootContinuation.NewtonBandWindowHole
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.WindowHole
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.PhysicalCorrection
import Purelib.Riemann.Topology.NewtonBandSewnHoleRequest
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.Riemann.RootContinuation

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Topology.Polygon

@[expose] public section

/-! The two window compilers retain the same physical-hole polygons.
Read them on the actual excision entry before aggregating either estimate. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion (PairedBranchRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

/-- Equal original branch-hole indices give identical lifted positive boundary words on the same edge and vertex banks.
-/
private theorem positive_boundary_eq {bank : Branches.BranchCellBank curve branches higher}
    {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} (edges : RootEdgeBank frames) (vertices :
      LiftedVertices.VertexBank bank.grid)
    {first last : PuncturedGridFaces.BranchHole bank} (same : first.index = last.index) (sheet : Fin 2) :
    edges.indexedEdges vertices first.boundary sheet = edges.indexedEdges vertices last.boundary sheet := by
  rcases first with ⟨index, cell, member, cellEq, state, boxEq⟩
  rcases last with ⟨other, otherCell, otherMember, otherEq, otherState, otherBoxEq⟩
  change index = other at same
  cases same
  cases cellEq
  cases otherEq
  rfl

namespace AnnularEntry

variable {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {preparation :
  Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original}
  {target radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {current : Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
    domains stage}

/-- Positive boundary polygons on both sheets of the literal excision hole. -/
def physicalHoleArea (entry : Excision.AnnularEntry grid current)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) : Gaussian :=
  let value := fun edge => (⟨edgeValuation current.mesh left.values edge,
    CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
  let polygon := fun sheet => PairedIncrementArea.area
    ((current.edges.indexedEdges current.vertices entry.hole.boundary sheet).map value)
  polygon 0 + polygon 1

/-- The band compiler's two positive polygons equal the original excision entry's physical-hole area. -/
theorem band_physicalHoleArea (entry : Excision.AnnularEntry grid current)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) :
    let value := fun edge => (⟨edgeValuation current.mesh left.values edge,
      CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
    let polygon := fun sheet => PairedIncrementArea.area
      ((current.edges.indexedEdges current.vertices (NewtonBandWindowHole.fineHole entry.annulus (current :=
        current)).hole.boundary sheet).map value)
    polygon 0 + polygon 1 = Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback.AnnularEntry.physicalHoleArea entry
      left right := by
  intro value polygon
  apply congrArg₂ (· + ·)
  · exact congrArg (fun word => PairedIncrementArea.area (word.map value))
      (Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback.positive_boundary_eq current.edges current.vertices
        (NewtonBandWindowHole.fineHole entry.annulus (current := current)).hole_index 0)
  · exact congrArg (fun word => PairedIncrementArea.area (word.map value))
      (Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback.positive_boundary_eq current.edges current.vertices
        (NewtonBandWindowHole.fineHole entry.annulus (current := current)).hole_index 1)

end AnnularEntry

namespace PairedBranchRequest

variable {base : Purelib.Riemann.Meshes.FramedPuncturedGrid curve branches higher} {lifted :
  Purelib.Riemann.Meshes.LiftedPuncturedGrid base}
  {bank : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid.BasedBranchBank lifted}
    {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation
    base.bank.toBranchCellBank}
  {target radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {current : Purelib.Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {entry : Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry grid current} {sheet : Fin 2}
  {leftFixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)}
  {rightFixed : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank.FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)}
  {error : Purelib.Data.Rat.Fraction.Rational} {floor stage : Nat} {cache :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}

/-- The paired branch request reads exactly the original excision entry's physical-hole area on the supplied triangle
readings. -/
theorem physicalHoleArea_eq (request : PairedBranchRegion.PairedBranchRequest bank entry sheet leftFixed rightFixed
  error floor)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) :
    PhysicalCorrection.physicalHoleArea request left right =
      Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback.AnnularEntry.physicalHoleArea entry left right := by
  let value := fun edge => (⟨edgeValuation current.mesh left.values edge,
    CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
  apply congrArg₂ (· + ·)
  · exact congrArg (fun word => PairedIncrementArea.area (word.map value))
      (Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback.positive_boundary_eq current.edges current.vertices
        (WindowHole.fineHole request.outer (current := current)).hole_index 0)
  · exact congrArg (fun word => PairedIncrementArea.area (word.map value))
      (Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback.positive_boundary_eq current.edges current.vertices
        (WindowHole.fineHole request.outer (current := current)).hole_index 1)

end PairedBranchRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.PhysicalHoleReadback
