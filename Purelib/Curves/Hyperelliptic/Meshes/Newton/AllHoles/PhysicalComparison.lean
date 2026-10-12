module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PairedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PhysicalRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalReadback
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Path.PairedOccurrenceArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Branches.NewtonCutPrimitiveArea
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Branches.NewtonPairedCutRequests
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPathBudget
import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Aggregate the proved annular source-chord cancellations on the full physical boundary. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalComparison

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalReadback.NewtonPreparation.FamilyAreaRequest
open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}

namespace NewtonPreparation.FamilyAreaRequest

variable {request : Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonPreparation.FamilyAreaRequest
  preparation target radius}
  {lifted : Meshes.LiftedPuncturedGrid request.single.grid.punctured}
  {excision : Hyperelliptic.Meshes.Newton.AllHoles.Excision.AllHoleExcision request.single.grid lifted}
  {first second : Fin genus} {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames
    request.single.grid.faces.regulars}

namespace PairedComparison

variable {stage : Nat}
  {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get first) lifted.mesh}
    {right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get second)
    lifted.mesh}
  {firstSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values}
  {secondSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values}

variable {prepared :
  Hyperelliptic.Meshes.Newton.AllHoles.PrimitiveComparison.NewtonGrid.AllHoleExcision.OuterPreparations excision}
  {comparison :
  PairedComparison prepared
  first second domains}
  {source :
    PairedComparison.Sample
    comparison left right}

namespace SewnSample.PhysicalSides

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest

variable {sample :
  Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.SewnSample
  source firstSurface secondSurface}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {physicalTarget : Fraction.Rational}
  {physicalRequest : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    physicalTarget}

/-- Remaining terms after the actual inner source chords have cancelled.
All inputs are retained surface, side and annular numerical caches. -/
@[expose] def remainingCorrection (entry :
  Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.PhysicalTerm
  left right firstSurface secondSurface)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := physicalRequest)
      cache.normalize first second) : Gaussian :=
  let raw := fun vertex => (⟨firstSurface.sewn.values vertex, secondSurface.sewn.values vertex⟩ :
    Topology.Polygon.Stokes.PrimitivePoint)
  Annulus.HoleSides.finePerimeter entry.sides perimeters +
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (entry.term.data.balance.inner.word.sources.entries.map (fun route =>
      Topology.Polygon.Stokes.edgeArea (raw lifted.cutPolygon.patch.cut.triangles[route.owner.position.val].first)
        ((raw route.cutEdge.finish).sub (raw route.cutEdge.start)))) +
    entry.term.data.paired.jumpSum + entry.term.data.paired.defectSum + entry.term.data.outer.correction

/-- Simultaneous cancellation on the actual global physical correction.
The exterior and every remaining annular term are displayed explicitly. -/
theorem global_correction_accurate (cached :
  PhysicalSides
  sample)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := physicalRequest)
      cache.normalize first second)
    (neighbors : Meshes.PuncturedGridFaces.PuncturedFaces.NeighborBank request.single.grid.faces)
    {global : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains first
      second}
    {sewingTarget : Fraction.Rational} {sewingFloor : Nat}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request global sewingTarget
      sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples firstSurface
      secondSurface) :
    Data.Gaussian.Norm.Basic.normSq (sample.correction +
      (Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters.physicalPerimeter perimeters neighbors
      - Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas.physicalTriangleArea neighbors left right) -
      (Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors
        left right .exterior +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (cached.entries.map (fun entry =>
          remainingCorrection
          entry perimeters)))) ≤
      (request.single.grid.faces.holes.length : Fraction.Rational) *
        ((request.single.grid.faces.holes.length : Fraction.Rational) * (8 * (8 * (sewing.budget.weight *
          sewing.budget.error)))) := by
  let residual := fun entry :
    Hyperelliptic.Meshes.Newton.AllHoles.PhysicalSides.NewtonPreparation.FamilyAreaRequest.PairedComparison.PhysicalTerm
    left right firstSurface secondSurface =>
    entry.term.data.correction + Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.holeAreaRemainder perimeters
      entry.sides.sides -
      remainingCorrection
      entry perimeters
  have bounds : ∀ value ∈ cached.entries.map residual,
      Data.Gaussian.Norm.Basic.normSq value ≤ 8 * (8 * (sewing.budget.weight * sewing.budget.error)) := by
    intro value member
    obtain ⟨entry, _, equal⟩ := Data.List.Map.mem_map.mp member
    rw [← equal]
    exact Hyperelliptic.Meshes.Newton.Annulus.PhysicalRemainder.AnnularSample.correction_add_remainder_accurate
      entry.term.data entry.sides perimeters sewing later bilinear
  have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le _ _ bounds
  simp only [Data.List.Map.length_map,
    PhysicalSides.entries_count
    cached, -eq_self, -iff_self] at estimate
  have corrections : Data.Gaussian.Norm.Sum.Basic.gaussianSum (cached.entries.map (fun entry =>
    entry.term.data.correction)) = sample.correction := by
    have terms := congrArg (List.map (fun term :
      Hyperelliptic.Meshes.Newton.AllHoles.PairedAnnuli.NewtonPreparation.FamilyAreaRequest.PairedComparison.AnnularTerm
      left right firstSurface secondSurface => term.data.correction)) cached.terms_eq
    simp only [Data.List.Map.map_map, Function.comp_def, -eq_self, -iff_self] at terms
    exact (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum terms).trans sample.correction_eq.symm
  have balance : Data.Gaussian.Norm.Sum.Basic.gaussianSum (cached.entries.map residual) = sample.correction +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (cached.entries.map (fun entry =>
        Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.holeAreaRemainder perimeters entry.sides.sides)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (cached.entries.map (fun entry =>
        remainingCorrection
        entry perimeters)) := by
    rw [← corrections]
    induction cached.entries with
    | nil => change (0 : Gaussian.Basic.Canonical) = 0 + 0 - 0; ring1
    | cons entry tail ih =>
      simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, -eq_self, -iff_self]
      rw [ih]
      dsimp only [residual, -eq_self, -iff_self]
      ring1
  rw [balance] at estimate
  rw

      [PairedComparison.SewnSample.PhysicalSides.physical_correction_eq
    cached perimeters neighbors]
  have cancel (a b c d : Gaussian.Basic.Canonical) : a + (b + c) - (b + d) = a + c - d := by ring1
  rw [cancel]
  exact estimate

end SewnSample.PhysicalSides
end PairedComparison
end NewtonPreparation.FamilyAreaRequest
end Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.PhysicalComparison
