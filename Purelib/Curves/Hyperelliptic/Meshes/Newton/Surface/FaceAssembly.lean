module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Vector.Basic
import Purelib.Topology.BranchedCover.Double.Attachment

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ConjugateRequest
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Polynomial.Rectangle.Boundary.Assembly
import Purelib.Riemann.Periods.BilinearGridBoundary
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy
import Purelib.Riemann.RootContinuation.NewtonProtectedObservations
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfaceLower
import Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.PieceIndices
public import Purelib.Riemann.Integration.RectangularStitchedPerimeter
import Init.Data.Fin.Basic
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.DomainConjugateExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.LinearAlgebra.Grid.Offsets
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.RectangularPrimitiveGluing
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.NewtonObservationSurfaceEnergy
import Purelib.Riemann.Topology.NewtonObservationSurfacePartition
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.ExteriorRequest

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.LocalEnergy

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Integration.Polynomial.Rectangle.Boundary

open Purelib.Riemann.Periods

open Purelib.Riemann.Readings

open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh.ClippedAssembly

open Purelib.Riemann.Topology

open Purelib.Topology.BranchedCover.Double

public section

/-!
# Whole-face exteriors from the complete observation-cut surface

Reindex the retained piece perimeters on their actual Cartesian partition.
Internal sides cancel only up to their corrected seam ribbons and corner
polygons. The new exterior retains the joining edges at observation cuts.
No equality of independently owned primitive traces is assumed.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes (Numerics)
open Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy (Preflights)
open Purelib.Riemann.Readings.RectangularObservationAssembly.ObservationMesh (ClippedAssembly)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonProtectedObservations (ProtectedObservations)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy (SurfacePartitions SurfaceMeshes SurfaceRequest)

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Purelib.Curves.Hyperelliptic.Branches.BranchCellBank curve
    branches higher}
  {preparation : Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target
    radius : Purelib.Data.Rat.Fraction.Rational} {grid :
    Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius}
  {observations : Purelib.Riemann.RootContinuation.NewtonProtectedObservations.ProtectedObservations original} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames grid.shrunk.prepared.grid}
  {domains : Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank frames
    grid.faces.regulars} {sheet : Fin 2}
  {partitions : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfacePartitions observations grid} {coarse :
    Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceMeshes partitions domains sheet}
  {fixed : Purelib.Riemann.RootContinuation.NewtonRequestedObservationEnergy.Preflights domains sheet} {energyTarget :
    Purelib.Data.Rat.Fraction.Rational}
  {energy : Purelib.Riemann.Topology.NewtonRequestedSurfaceEnergy.SurfaceRequest partitions coarse fixed energyTarget}
    {stage : Nat} {cache : Purelib.Riemann.RootContinuation.NewtonObservationLocalEnergy.LocalMeshes.Numerics domains
    stage}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace FaceAssembly

/-- The dependent perimeter cache for every actual observation piece on every original regular face. -/
@[expose] def Perimeters (assemblies : ExteriorRequest.Assemblies energy cache coefficients) :=
  Data.Vector.DependentVector (fun position => Data.Vector.DependentVector (fun piece : Fin (partitions.get
    position).cuts.boxes.length =>
    ((assemblies.get position).get piece).Perimeter))

/-- Acquire each actual clipped piece perimeter while preserving the original face and piece indices. -/
@[expose] def perimeters (assemblies : ExteriorRequest.Assemblies energy cache coefficients) :
  Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters assemblies :=
  DependentVector.ofFn fun position => DependentVector.ofFn fun piece =>
    Perimeter.build ((assemblies.get position).get piece)

end FaceAssembly

variable {assemblies : ExteriorRequest.Assemblies
  energy cache coefficients}

namespace FaceAssembly.Perimeters

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly in
/-- The exact Cartesian side grid read from the retained original piece perimeters. -/
@[expose] def faceSides (perimeters : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters
  assemblies) (position : Fin grid.faces.regulars.length) :
    Assembly.SideGrid (PieceIndices.columns (partitions.get position)) (PieceIndices.rows (partitions.get position)) :=
  fun column row =>
    let perimeter := (perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) column row)
    ⟨perimeter.bottom, perimeter.right, perimeter.top, perimeter.left⟩

end FaceAssembly.Perimeters

namespace FaceAssembly

/-- Each corner reads the owner at the endpoint of the corresponding cached piece perimeter, including when a model-grid
cut meets an observation cut. -/
@[expose] def faceCorners (assemblies : ExteriorRequest.Assemblies energy cache coefficients) (position : Fin
  grid.faces.regulars.length)
    (column : Fin ((PieceIndices.columns (partitions.get position)) + 1)) (row : Fin ((PieceIndices.rows (partitions.get
      position)) + 1)) :
    BilinearGridBoundary.CornerValues :=
  let piece := PieceIndices.pieceIndex (partitions.get position) column row
  let assembly := (assemblies.get position).get piece
  let mesh := (energy.meshes.get position).entries.get piece
  ⟨(assembly.corners 0 0).lowerLeft,
    (assembly.corners (Fin.last mesh.boundaryColumns) 0).lowerRight,
    (assembly.corners 0 (Fin.last mesh.boundaryRows)).upperLeft,
    (assembly.corners (Fin.last mesh.boundaryColumns) (Fin.last mesh.boundaryRows)).upperRight⟩

end FaceAssembly

namespace FaceAssembly.Perimeters

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly in
/-- The retained Cartesian side-grid boundary equals the complete original piece exterior sum. -/
theorem localBoundary_eq (perimeters : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters
  assemblies) (position : Fin grid.faces.regulars.length) :
    Assembly.localBoundary (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.faceSides perimeters
      position) =
      FiniteSum.Fin.sumFin (fun piece => ((assemblies.get position).get piece).exterior) := by
  rw [PieceIndices.sum_pieces (partitions.get position)]
  apply FiniteSum.Fin.sumFin_congr
  intro column
  apply FiniteSum.Fin.sumFin_congr
  intro row
  exact ((perimeters.get position).get (PieceIndices.pieceIndex (partitions.get position) column row)).exterior_eq.symm

end FaceAssembly.Perimeters

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly in
set_option genInjectivity false in
/-- Cached face exterior and the exact internal defect, with every side and corner tied to the original piece
assemblies. -/
structure FaceAssembly (perimeters : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters assemblies)
  (position : Fin grid.faces.regulars.length) where
  /-- The cached Cartesian corner values of the original piece assemblies. -/ corners : BilinearGridBoundary.Values
    (PieceIndices.columns (partitions.get position)) (PieceIndices.rows (partitions.get position))
  /-- Each cached corner reads exactly the original retained piece corner at its Cartesian index. -/ corners_eq : ∀
    column row, corners column row = Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.faceCorners assemblies
    position column row
  /-- The cached whole-face exterior, including all actual observation-cut joining edges. -/ exterior :
    Data.Gaussian.Basic.Canonical
  /-- The cached face exterior is exactly its retained outer sides plus all original exterior joins. -/ exterior_eq :
    exterior = Assembly.exteriorSides (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.faceSides
    perimeters position) +
    BilinearGridBoundary.exteriorJoins corners
  /-- The cached complete corrected internal seam sum. -/ seams : Data.Gaussian.Basic.Canonical
  /-- The seam cache is exactly the corrected sum for the original sides and retained corners. -/ seams_eq : seams =
    BilinearGridBoundary.correctedSeamSum (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.faceSides
    perimeters position) corners
  /-- The cached complete internal corner-polygon contribution. -/ cornerTotal : Data.Gaussian.Basic.Canonical
  /-- The corner cache is exactly the sum on the retained original corner grid. -/ cornerTotal_eq : cornerTotal =
    BilinearGridBoundary.cornerSum corners
  /-- The original piece exterior sum decomposes into the retained whole-face exterior, corrected seams and corner
    polygons. -/ decomposition : FiniteSum.Fin.sumFin (fun piece => ((assemblies.get position).get piece).exterior) =
    exterior + seams + cornerTotal

constructive_injectivity FaceAssembly

namespace FaceAssembly

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly in
/-- Cache the original face corner grid and whole exterior together with every exact internal defect. -/
@[expose] def build (perimeters : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters
  assemblies) (position : Fin grid.faces.regulars.length) :
    FaceAssembly perimeters position := by
  let corners := Data.Vector.Basic.vectorOfFn fun column => Data.Vector.Basic.vectorOfFn fun row =>
    Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.faceCorners assemblies position column row
  have readback (column : Fin ((PieceIndices.columns (partitions.get position)) + 1))
      (row : Fin ((PieceIndices.rows (partitions.get position)) + 1)) : corners column row =
        Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.faceCorners assemblies position column row := by
    dsimp only [corners]
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
  refine ⟨corners, readback,
    Assembly.exteriorSides (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.faceSides perimeters
      position) + BilinearGridBoundary.exteriorJoins corners, rfl,
    BilinearGridBoundary.correctedSeamSum (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.faceSides
      perimeters position) corners, rfl,
    BilinearGridBoundary.cornerSum corners, rfl, ?_⟩
  have equal := BilinearGridBoundary.localBoundary_sub_stitchedExterior
    (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.faceSides perimeters position) corners
  rw [Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.localBoundary_eq perimeters position] at equal
  calc
    _ = (FiniteSum.Fin.sumFin (fun piece => ((assemblies.get position).get piece).exterior) -
        (Assembly.exteriorSides (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.faceSides perimeters
          position) + BilinearGridBoundary.exteriorJoins corners)) +
        (Assembly.exteriorSides (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters.faceSides perimeters
          position) + BilinearGridBoundary.exteriorJoins corners) := by ring1
    _ = _ := by rw [equal]; ring1

end FaceAssembly

section
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
namespace FaceAssembly

/-- The dependent vector of whole-face assemblies on the exact original retained perimeter family. -/
@[expose] def FaceAssemblies (perimeters : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters
  assemblies) :=
  Data.Vector.DependentVector (fun position : Fin grid.faces.regulars.length =>
    FaceAssembly perimeters position)

/-- Build each whole-face assembly from its actual retained perimeter cache. -/
@[expose] def faceAssemblies (perimeters : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.Perimeters
  assemblies) : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies perimeters :=
  DependentVector.ofFn (build perimeters)

end FaceAssembly

end

variable {perimeters : FaceAssembly.Perimeters assemblies}

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly
namespace FaceAssembly.FaceAssemblies

/-- The complete cached whole-face exterior sum on the original retained face family. -/
@[expose] def exterior (faces : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies
  perimeters) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => (faces.get position).exterior)

/-- The complete actual internal seam and corner defect summed over all retained faces. -/
@[expose] def defect (faces : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies
  perimeters) : Gaussian :=
  FiniteSum.Fin.sumFin (fun position => (faces.get position).seams + (faces.get position).cornerTotal)

/-- The original piece exterior sum is exactly the whole-face exterior sum plus its full retained internal defect. -/
theorem decomposition (faces : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies
  perimeters) :
    ExteriorRequest.exterior assemblies =
      Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies.exterior faces +
      Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies.defect faces := by
  unfold ExteriorRequest.exterior Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies.exterior
    Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies.defect
  rw [← FiniteSum.Fin.sumFin_add]
  apply FiniteSum.Fin.sumFin_congr
  intro position
  exact (faces.get position).decomposition.trans (by ring1)

/-- The lower bound now concerns whole-face exteriors. The exact remaining internal defect is displayed, not silently
discarded or declared small. -/
theorem energy_lower (faces : Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies
  perimeters)
    {ownershipAllowance exteriorAllowance : Fraction.Rational}
    (ownership : ConjugateRequest energy (ConjugateRequest.energyAllowanceTarget genus
      ownershipAllowance))
    (request : ExteriorRequest energy (ConjugateRequest.energyAllowanceTarget genus exteriorAllowance)
      ownership.index)
    (ownershipPositive : 0 < ownershipAllowance) (exteriorPositive : 0 < exteriorAllowance)
    (later : request.index ≤ stage) (samples : energy.Readings cache) (face : Attachment.Face) :
    (NewtonObservationSurfaceLower.surfaceLowerConstant observations - energyTarget - ownershipAllowance -
      exteriorAllowance) * PreparedObservationCoercivity.coefficientNormSq coefficients -
        (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies.defect faces).im / 4 ≤
          (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies.exterior faces).im / 4 := by
  have lower := ExteriorRequest.energy_lower ownership request ownershipPositive exteriorPositive later samples
    coefficients face assemblies
  rw [Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies.decomposition faces,
    Data.Gaussian.Basic.add_im] at lower
  exact (Fraction.Order.Arithmetic.sub_le_sub_direct lower (le_rfl (a :=
    (Curves.Hyperelliptic.Meshes.Newton.Surface.FaceAssembly.FaceAssemblies.defect faces).im / 4))).trans_eq
    (by simp only [Fraction.Field.div_eq_mul_inv_direct]; ring1)

end FaceAssembly.FaceAssemblies

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Surface
