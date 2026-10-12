module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib

open Purelib.Riemann

open Purelib.RootIsolation

@[expose] public section

/-! Fixed corner jumps are the actual cached source triangle wedge areas. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid}

variable {vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
  SquareRoot.Grid.RootEdgeBank frames}
  {faces : Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars} {stage : Nat}
    {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {i j : Fin genus}

namespace TriangleReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Corners.FaceCorners in
/-- The wedge area of the three actual paired triangle readings. -/
def bilinearArea (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i)
  mesh) (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (triangle : Fin mesh.triangles.length) : Gaussian.Basic.Canonical :=
  Topology.Polygon.Stokes.triangleWedgeArea
    ⟨left.values triangle 0, right.values triangle 0⟩
    ⟨left.values triangle 1, right.values triangle 1⟩
    ⟨left.values triangle 2, right.values triangle 2⟩

/-- The actual paired triangle area is exactly its upper or lower original face-corner wedge.

The retained paired readings use their original bounded triangle index and
face-corner values. Scalar coordinate identities preserve the original upper
or lower orientation and its exact cached wedge. -/
theorem bilinearArea_eq_corners (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  (cache.get i) mesh) (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get
  j) mesh)
    (position : Fin faces.regulars.length) (sheet : Fin 2) (upper : Bool) :
    Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right (mesh.triangleIndex
      position sheet upper) =
      if upper then Topology.Polygon.Stokes.triangleWedgeArea
        (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cache i j
          position sheet 0)
          (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cache i j
          position sheet 2)
          (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cache i j
          position sheet 3)
      else Topology.Polygon.Stokes.triangleWedgeArea
        (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cache i j
          position sheet 0)
          (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cache i j
          position sheet 1)
          (Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair cache i j
          position sheet 2) := by
  unfold Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea
  rw [left.values_eq, right.values_eq]
  cases upper <;>
    simp only [Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.FaceCorners.triangleValues,
      Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self] <;> rfl

/-- The normalized horizontal corner jump is the negative actual upper-triangle wedge area.

The retained paired readings use their original bounded triangle index and
face-corner values. Scalar coordinate identities preserve the original upper
or lower orientation and its exact cached wedge. -/
theorem normalized_horizontal_jump (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  (cache.get i) mesh) (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get
  j) mesh)
    (position nextPosition : Fin faces.regulars.length) (sheet nextSheet : Fin 2) :
  Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerJump
    cache.normalize i j position nextPosition sheet nextSheet 3 2 =
      -Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
        (mesh.triangleIndex position sheet true) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea_eq_corners left right]
  rw [if_pos rfl]
  unfold Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerJump
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair
  rw [cache.normalize_atDomain, cache.normalize_atDomain, cache.normalize_atDomain, cache.normalize_atDomain]
  simp only [Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.normalize_corner,
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics.atDomain,
    Topology.Polygon.Stokes.triangleWedgeArea, Topology.Polygon.Stokes.edgeArea,
      Topology.Polygon.Stokes.PrimitivePoint.sub, -eq_self, -iff_self]
  ring1

/-- The normalized vertical corner jump equals the actual lower-triangle wedge area.

The retained paired readings use their original bounded triangle index and
face-corner values. Scalar coordinate identities preserve the original upper
or lower orientation and its exact cached wedge. -/
theorem normalized_vertical_jump (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings
  (cache.get i) mesh) (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get
  j) mesh)
    (position nextPosition : Fin faces.regulars.length) (sheet nextSheet : Fin 2) :
  Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerJump
    cache.normalize i j position nextPosition sheet nextSheet 1 2 =
      Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea left right
        (mesh.triangleIndex position sheet false) := by
  rw [Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas.TriangleReadings.bilinearArea_eq_corners left right]
  rw [if_neg Bool.false_ne_true]
  unfold Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerJump
    Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes.Numerics.cornerPair
  rw [cache.normalize_atDomain, cache.normalize_atDomain, cache.normalize_atDomain, cache.normalize_atDomain]
  simp only [Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.DomainPrimitives.normalize_corner,
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics.atDomain,
    Topology.Polygon.Stokes.triangleWedgeArea, Topology.Polygon.Stokes.edgeArea,
      Topology.Polygon.Stokes.PrimitivePoint.sub, -eq_self, -iff_self]
  ring1

end TriangleReadings
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
