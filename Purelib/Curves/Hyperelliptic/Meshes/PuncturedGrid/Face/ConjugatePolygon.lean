module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.SewnConjugateSamples
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PairedPolygon

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings

open Purelib.Integration.Path

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing.SewnConjugateSamples

public section

/-! The conjugate polygon of the four actual face sources reads the same
cached corners as the two retained source triangles. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Data.Gaussian.Basic (conj)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : PuncturedFaces bank} {mesh :
    LiftedMesh vertices edges faces}
  {domains : FaceDomainBank frames faces.regulars}
    {stage : Nat} {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
    domains stage}
  {i j : Fin genus}

/-- The closed four-increment polygon area is exactly the sum of its two original diagonal triangle areas. -/
private theorem quadrilateral_area (a b c d : Stokes.PrimitivePoint) :
    PairedIncrementArea.area [b.sub a, c.sub b, d.sub c, a.sub d] =
      Stokes.triangleWedgeArea a b c + Stokes.triangleWedgeArea a c d := by
  simp only [-eq_self, -iff_self, PairedIncrementArea.area, PairedIncrementArea.terms, PairedIncrementArea.total,
    List.map_cons, List.map_nil, Data.Gaussian.Norm.Sum.Basic.gaussianSum, PrimitivePoint.sub,
    Stokes.edgeArea, Stokes.triangleWedgeArea]
  ring1

/-- Closure of the increment polygon does not assert that its area is zero. -/
theorem faceSources_conjugate_area
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (position : Fin faces.regulars.length) (sheet : Fin 2) :
    PairedIncrementArea.area ((LiftedMesh.faceSources mesh position sheet).map (fun source =>
      (⟨conj (source.increment left.values), source.increment right.values⟩ : Stokes.PrimitivePoint))) =
      left.conjugateArea right (mesh.triangleIndex position sheet false) +
        left.conjugateArea right (mesh.triangleIndex position sheet true) := by
  let point := fun corner => (⟨conj ((((cache.get i).get position).atSheet sheet).corners.values corner),
    (((cache.get j).get position).atSheet sheet).corners.values corner⟩ : Stokes.PrimitivePoint)
  have triangle (upper : Bool) : left.conjugateArea right (mesh.triangleIndex position sheet upper) =
      if upper then Stokes.triangleWedgeArea (point 0) (point 2) (point 3)
      else Stokes.triangleWedgeArea (point 0) (point 1) (point 2) := by
    unfold TriangleReadings.conjugateArea
    rw [left.values_eq, right.values_eq]
    cases upper <;> simp only [-eq_self, -iff_self, FaceCorners.triangleValues,
      Data.Vector.Basic.vectorOfFn_apply] <;> rfl
  simp only [-eq_self, -iff_self, LiftedMesh.faceSources, List.map_cons, List.map_nil,
    TriangleReadings.faceSource_increment left, TriangleReadings.faceSource_increment right]
  rw [triangle false, triangle true]
  simp only [-eq_self, -iff_self, if_neg (show (false : Bool) ≠ true by decide), if_pos (rfl : (true : Bool) = true),
    ConjugatePair.conj_sub]
  exact quadrilateral_area (point
    0) (point 1) (point 2) (point 3)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
