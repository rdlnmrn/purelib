module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedPrimitives
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Riemann.Meshes.GridLiftedDualSteps
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
import Init.Prelude
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Tactic.Ring

public section

/-! Source triangle counterterms are the endpoint chords of the normalized
side values. The physical remainder retains each side's internal excursions. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CornerTriangleAreas
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedCornerMagnitude.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
open Purelib.Riemann.Meshes
open Purelib.Topology.Polygon
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (edgeArea)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData (DomainPrimitives)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve branches
    higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}
  {faces : Purelib.Riemann.Meshes.PuncturedGridFaces.PuncturedFaces bank} {mesh :
    Purelib.Riemann.Meshes.GridLiftedMesh.LiftedMesh vertices edges faces}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames faces.regulars}
    {stage : Nat} {cache : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics
    domains stage}
  {i j : Fin genus}

/-- The oriented endpoint-chord area of one retained regular-face side. -/
@[expose] def RegularMeshes.Numerics.sideChord (cache : RegularMeshes.Numerics domains stage) (i j : Fin genus)
    (position : Fin faces.regulars.length) (sheet : Fin 2) : GridLiftedDualSteps.GridSide →
      Data.Gaussian.Basic.Canonical
  | .bottom => Stokes.edgeArea (Numerics.cornerPair cache i j position sheet 0) (Numerics.cornerPair cache i j position
    sheet 1)
  | .right => Stokes.edgeArea (Numerics.cornerPair cache i j position sheet 1) (Numerics.cornerPair cache i j position
    sheet 2)
  | .top => Stokes.edgeArea (Numerics.cornerPair cache i j position sheet 3) (Numerics.cornerPair cache i j position
    sheet 2)
  | .left => Stokes.edgeArea (Numerics.cornerPair cache i j position sheet 0) (Numerics.cornerPair cache i j position
    sheet 3)

/-- The normalized bottom side has zero endpoint-chord area. -/
theorem RegularMeshes.Numerics.normalized_bottom_chord (cache : RegularMeshes.Numerics domains stage)
    (i j : Fin genus) (position : Fin faces.regulars.length) (sheet : Fin 2) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes.Numerics.sideChord cache.normalize i j
      position sheet .bottom = 0 := by
  unfold sideChord Numerics.cornerPair
  rw [cache.normalize_atDomain, cache.normalize_atDomain]
  simp only [-eq_self, -iff_self, DomainPrimitives.normalize_corner, Stokes.edgeArea]
  ring1

/-- The normalized left side has zero endpoint-chord area. -/
theorem RegularMeshes.Numerics.normalized_left_chord (cache : RegularMeshes.Numerics domains stage)
    (i j : Fin genus) (position : Fin faces.regulars.length) (sheet : Fin 2) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes.Numerics.sideChord cache.normalize i j
      position sheet .left = 0 := by
  unfold sideChord Numerics.cornerPair
  rw [cache.normalize_atDomain, cache.normalize_atDomain]
  simp only [-eq_self, -iff_self, DomainPrimitives.normalize_corner, Stokes.edgeArea]
  ring1

/-- The normalized right endpoint chord equals the actual first source-triangle area. -/
theorem TriangleReadings.normalized_right_chord
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (position : Fin faces.regulars.length) (sheet : Fin 2) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes.Numerics.sideChord
      cache.normalize i j position sheet .right =
      TriangleReadings.bilinearArea left right (mesh.triangleIndex position sheet false) := by
  rw [TriangleReadings.bilinearArea_eq_corners left right]
  simp only [-eq_self, -iff_self, if_neg (show (false : Bool) ≠ true by decide)]
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes.Numerics.sideChord
    Numerics.cornerPair
  rw [cache.normalize_atDomain, cache.normalize_atDomain]
  simp only [-eq_self, -iff_self, DomainPrimitives.normalize_corner, Numerics.atDomain,
    Stokes.triangleWedgeArea, Stokes.edgeArea]
  rfl

/-- The normalized top endpoint chord is the negative of the actual second source-triangle area. -/
theorem TriangleReadings.normalized_top_chord
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) mesh)
    (position : Fin faces.regulars.length) (sheet : Fin 2) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes.Numerics.sideChord
      cache.normalize i j position sheet .top =
      -TriangleReadings.bilinearArea left right (mesh.triangleIndex position sheet true) := by
  rw [TriangleReadings.bilinearArea_eq_corners left right]
  simp only [-eq_self, -iff_self, if_pos (Eq.refl true)]
  unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords.RegularMeshes.Numerics.sideChord
    Numerics.cornerPair
  rw [cache.normalize_atDomain, cache.normalize_atDomain]
  simp only [-eq_self, -iff_self, DomainPrimitives.normalize_corner, Numerics.atDomain,
    Stokes.triangleWedgeArea, Stokes.edgeArea]
  ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalSideChords

end
