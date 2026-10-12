module
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnConjugateRequest
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.PrimitiveSewing

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Topology.Polygon

open Purelib

@[expose] public section

/-! Actual source triangle areas for the conjugate pairing, grouped by
retained regular-face positions and both sheets. -/
section

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Topology.Polygon.Stokes (triangleWedgeArea)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open _root_.Purelib.Data.Gaussian.Basic (conj)
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
  {domains : FaceDomainBank frames faces.regulars}
    {stage : Nat}
  {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {i j : Fin genus}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

/-- The actual source triangle wedge area with the first reading conjugated and the second reading unchanged. -/
def conjugateArea
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh)
    (right : TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) (source : Fin mesh.triangles.length) :
      Gaussian :=
  Stokes.triangleWedgeArea ⟨conj (left.values source 0), right.values source 0⟩
    ⟨conj (left.values source 1), right.values source 1⟩ ⟨conj (left.values source 2), right.values source 2⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas

/-- The mask selects whole regular faces; each contributes its two actual triangles on each of the two retained sheets.
-/
def selectedConjugateFullTriangleArea (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh)
    (right : TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh) (keep : Fin faces.regulars.length → Bool) :
      Gaussian :=
  FiniteSum.Fin.sumFin fun position => FiniteSum.Fin.sumFin fun sheet =>
    (if keep position then left.conjugateArea right (mesh.triangleIndex position sheet false) else 0) +
    (if keep position then left.conjugateArea right (mesh.triangleIndex position sheet true) else 0)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ConjugateTriangleAreas

end
