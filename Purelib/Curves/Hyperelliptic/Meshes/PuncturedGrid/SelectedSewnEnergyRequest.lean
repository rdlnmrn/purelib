module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingForest
import Purelib.Topology.Surface.Sewing.SewnEnergyCombination
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnConjugateRequest
public import Purelib.Topology.Surface.Sewing.SewnSelectedEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! The existing shared sewing request controls cached selected energy
for arbitrary homogeneous coefficient vectors at every later sample. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnEnergyRequest

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank
    bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {forest : Topology.Surface.Sewing.SewingForest mesh.triangulation.faces} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}

namespace EnergyPreparation.Request

variable {polygon : Topology.Surface.Sewing.SewingConnected.SewingForest.SinglePolygon forest} {prepared :
  Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation polygon domains}
  {target : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate} {floor : Nat}

/-- At every sufficient common stage, the cached selected sewn energy approximates the actual selected local energy
within the original homogeneous coefficient bound. -/
theorem selected_accurate (request : Hyperelliptic.Meshes.PuncturedGrid.SewnEnergyRequest.EnergyPreparation.Request
  prepared target floor) {stage : Nat} (later : request.index ≤ stage)
    {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
    (triangles : Data.Vector.DependentVector (fun basis : Fin genus =>
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get basis) mesh))
    {surfaces : Topology.Surface.Sewing.SewnEnergyCombination.EnergySurfaces polygon.patch (fun basis => (triangles.get
      basis).values)}
    {pairs : Topology.Surface.Sewing.SewnEnergyCombination.EnergyPairs surfaces} {keep : Fin mesh.triangles.length →
      Bool}
    (samples : Topology.Surface.Sewing.SewnSelectedEnergy.SelectedEnergySamples surfaces pairs keep) (coefficients : Fin
      genus → Gaussian.Basic.Canonical) :
    Data.Gaussian.Norm.Basic.normSq (Topology.Surface.Sewing.SewnSelectedEnergy.SelectedEnergySamples.energy samples
      coefficients - FiniteSum.Fin.sumFin (fun source => if keep source then
      Topology.Surface.Sewing.SewnEnergyCombination.localEnergy (fun basis => (triangles.get basis).values) coefficients
        source else 0)) ≤
        (genus : Topology.Surface.Sewing.SewnPrimitiveFaces.Coordinate)^2 * (FiniteSum.Fin.sumFin (fun basis =>
          Data.Gaussian.Norm.Basic.normSq (coefficients basis)))^2 * target := by
  apply Topology.Surface.Sewing.SewnSelectedEnergy.SelectedEnergySamples.error_bound samples coefficients
  intro first second
  rw [samples.areas_eq]
  exact (Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request.selected_conjugate_accurate
    ((request.entries.get first).get second)
    ((request.index_ge first second).trans later) (triangles.get first) (triangles.get second)
    ((pairs.get first).get second) (samples.selections.get first)).le

end EnergyPreparation.Request
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SelectedSewnEnergyRequest
