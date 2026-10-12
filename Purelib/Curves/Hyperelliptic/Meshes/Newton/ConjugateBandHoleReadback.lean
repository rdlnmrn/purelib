module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
public import Purelib.Riemann.RootContinuation.NewtonBandWindowHole
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugatePhysicalHoleReadback
import Purelib.Riemann.Topology.NewtonBandConjugateSewnHoleRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SingleHoleCircuit
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandWindowCircuits
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

public section

/-! Identify the band compiler's positive polygons with the literal
excision hole before aggregating the conjugate annular estimates. -/
section

open Purelib
open Purelib.Curves.Hyperelliptic
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Integration.Path
open Purelib.Riemann.Meshes
open Purelib.Riemann.RootContinuation
open Purelib.RootIsolation.SquareRoot.Grid
open Purelib.Topology.Polygon
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
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
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion (PairedBranchRequest)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBandHoleReadback

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

end Purelib.Curves.Hyperelliptic.Meshes.Newton.ConjugateBandHoleReadback

variable {original : Curves.Hyperelliptic.Branches.BranchCellBank curve branches higher} {preparation :
  Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original}
  {target radius : Data.Rat.Fraction.Rational} {grid :
    Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {current : Riemann.Meshes.LiftedPuncturedGrid grid.punctured}
  {domains : Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {stage : Nat} {cache : Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains
    stage}

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry

/-- The band compiler's two positive conjugate polygons equal the actual excision entry's conjugate physical-hole area.

The equality retains both original sheets and the exact shared numerical readings, transporting only the certified
equality of hole indices. -/
theorem band_conjugatePhysicalHoleArea
  (entry : Excision.AnnularEntry grid current)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) current.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) current.mesh) :
    let value := fun edge => (⟨Data.Gaussian.Basic.conj (CanonicalEdgeValues.edgeValuation current.mesh
      left.values edge),
      CanonicalEdgeValues.edgeValuation current.mesh right.values edge⟩ : Stokes.PrimitivePoint)
    let polygon := fun sheet => PairedIncrementArea.area
      ((current.edges.indexedEdges current.vertices (NewtonBandWindowHole.fineHole (current := current)
        entry.annulus).hole.boundary sheet).map value)
    polygon 0 + polygon 1 = entry.conjugatePhysicalHoleArea left right := by
  intro value polygon
  apply congrArg₂ (· + ·)
  · exact congrArg (fun word => PairedIncrementArea.area (word.map value))
      (Newton.ConjugateBandHoleReadback.positive_boundary_eq current.edges current.vertices
        (NewtonBandWindowHole.fineHole (current := current) entry.annulus).hole_index 0)
  · exact congrArg (fun word => PairedIncrementArea.area (word.map value))
      (Newton.ConjugateBandHoleReadback.positive_boundary_eq current.edges current.vertices
        (NewtonBandWindowHole.fineHole (current := current) entry.annulus).hole_index 1)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision.AnnularEntry

end
