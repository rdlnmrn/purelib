module
import Purelib.Data.Rat.Fraction
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected

public section

/-! Read the global physical correction on the cached annular hole sides. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalReadback

open Purelib
open Purelib.Algebra
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison
open
  PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Data.List
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Data.Rat

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Approximation.Rational.Budget.Aggregate (perTerm)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation (FamilyAreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles (PairedComparison)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison (Sample)
open
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison
  (SewnSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection (holeCorrection
  physicalCorrection_eq_holes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection (holeCorrection_eq_fourSides)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (holeAreaRemainder
  rootedHoleCorrection_eq_remainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (rootedHoleCorrection_eq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas (physicalTriangleArea)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}

namespace NewtonPreparation.FamilyAreaRequest

variable {request :
  FamilyAreaRequest
  preparation target radius}
  {lifted : LiftedPuncturedGrid request.single.grid.punctured}
  {excision : AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedComparison

variable {stage : Nat}
  {cache : Numerics domains stage}
  {left : TriangleReadings (cache.get first)
    lifted.mesh} {right : TriangleReadings
    (cache.get second) lifted.mesh}
  {firstSurface : CachedSample lifted.cutPolygon.patch left.values}
  {secondSurface : CachedSample lifted.cutPolygon.patch
    right.values}

variable {prepared :
  Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations
  excision} {comparison :
  PairedComparison
  prepared first second domains}
  {source :
    PairedComparison.Sample
    comparison left right}

namespace SewnSample.PhysicalSides

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {sample :
  PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {physicalTarget : Rational}
  {physicalRequest : TwoSheetRequest (fun
    sheet => RegularMeshes.build domains cuts
    sheet coarseDepth) fixed physicalTarget}

/-- Sum the remainders of these exact retained annuli over all physical holes. -/
theorem remainders_eq (cached : PhysicalSides sample)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := physicalRequest) cache.normalize first second) :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (cached.entries.map (fun entry => HoleAreaRemainder.holeAreaRemainder
      perimeters entry.sides.sides)) =
      FiniteSum.Fin.sumFin (fun hole => HoleComponentCorrection.holeCorrection perimeters left right hole) := by
  have mapped : cached.entries.map (fun entry => HoleAreaRemainder.holeAreaRemainder perimeters entry.sides.sides) =
      cached.entries.map (fun entry => HoleComponentCorrection.holeCorrection perimeters left right
        entry.sides.position) := by
    apply Map.map_congr_left
    intro entry _
    rw [← HoleAreaRemainder.rootedHoleCorrection_eq_remainder perimeters left right entry.sides.sides,
      HoleRootedCorrection.rootedHoleCorrection_eq perimeters left right entry.sides.sides,
      ← HoleFourSideCorrection.holeCorrection_eq_fourSides perimeters left right entry.sides.position
        entry.sides.adjacent]
    rfl
  exact (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum mapped).trans (PhysicalSides.sum_positions cached
    (HoleComponentCorrection.holeCorrection perimeters left right))

/-- The full physical correction uses the same indexed hole remainders as the annular cancellation theorem. Only its
exterior component is separate. -/
theorem physical_correction_eq (cached : PhysicalSides sample)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := physicalRequest) cache.normalize first second)
    (neighbors : PuncturedFaces.NeighborBank request.single.grid.faces) :
    FacePerimeters.physicalPerimeter perimeters neighbors - CrossingTriangleAreas.physicalTriangleArea neighbors left
      right =
      PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors left right .exterior +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (cached.entries.map (fun entry =>
        HoleAreaRemainder.holeAreaRemainder perimeters entry.sides.sides)) := by
  rw
    [remainders_eq
    cached perimeters]
  exact HoleComponentCorrection.physicalCorrection_eq_holes perimeters neighbors left right

end SewnSample.PhysicalSides
end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalReadback
