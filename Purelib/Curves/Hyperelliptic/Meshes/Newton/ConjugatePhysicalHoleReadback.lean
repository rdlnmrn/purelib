module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
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
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch.ConjugatePhysicalCorrection
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib

open Purelib.Curves.Hyperelliptic

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Branch

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Integration.Path

open Purelib.Riemann.Meshes

open Purelib.RootIsolation.SquareRoot.Grid

open Purelib.Topology.Polygon

public section

/-! The two window compilers retain the same physical-hole polygons.
Read them on the actual excision entry before aggregating either estimate. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (BranchHole)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AnnularEntry)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion (PairedBranchRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback

/-- Original branch holes with the same retained bank index have identical positive lifted boundaries. -/
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

end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback

section
variable {original : BranchCellBank curve branches higher} {preparation :
  NewtonPreparation original}
  {target radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Numerics
    domains stage}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry

/-- Positive boundary polygons on both sheets of the literal excision hole. -/
@[expose] def conjugatePhysicalHoleArea
  (entry : Excision.AnnularEntry grid current)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) : Gaussian :=
  let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
    left.values edge),
    CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
  let polygon := fun sheet => PairedIncrementArea.area
    ((current.edges.indexedEdges current.vertices entry.hole.boundary sheet).map value)
  polygon 0 + polygon 1

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry

end

section
variable {base : FramedPuncturedGrid curve branches higher} {lifted :
  LiftedPuncturedGrid base}
  {bank : BasedBranchBank lifted}
    {preparation : NewtonPreparation
    base.bank.toBranchCellBank}
  {target radius : Rational} {grid :
    NewtonGrid preparation target radius}
  {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {entry : AnnularEntry grid current} {sheet : Fin 2}
  {leftFixed : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)}
  {rightFixed : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)}
  {error : Rational} {floor stage : Nat} {cache :
    Numerics domains stage}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest

/-- The request's physical hole area equals the actual excision entry's two-sheet boundary readback. -/
theorem
  conjugatePhysicalHoleArea_eq
  (request : PairedBranchRegion.PairedBranchRequest bank entry sheet leftFixed rightFixed error floor)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) :
    request.conjugatePhysicalHoleArea left right = entry.conjugatePhysicalHoleArea left right := by
  let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
    left.values edge),
    CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
  apply congrArg₂ (· + ·)
  · exact congrArg (fun word => PairedIncrementArea.area (word.map value))
      (Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback.positive_boundary_eq current.edges
        current.vertices (WindowHole.fineHole (current := current) request.outer).hole_index 0)
  · exact congrArg (fun word => PairedIncrementArea.area (word.map value))
      (Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback.positive_boundary_eq current.edges
        current.vertices (WindowHole.fineHole (current := current) request.outer).hole_index 1)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion.PairedBranchRequest

end
end
