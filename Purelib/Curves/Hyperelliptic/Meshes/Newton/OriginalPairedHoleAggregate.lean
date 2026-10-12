module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Riemann.RootContinuation.NewtonOriginalPairedHoleCorrection
import Purelib.Riemann.RootContinuation.NewtonOriginalHolePositions
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.WalkOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentValues
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.PairedOccurrenceArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.Extension
import Purelib.Riemann.Branches.NewtonCutPrimitiveSources
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
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
import Purelib.Data.List.Membership

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.Newton

open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles

open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest

open Purelib.Data.List

open Purelib.Data.Rat

open Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Riemann.RootContinuation

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Sewing.Bilinear

@[expose] public section

/-! Cancel every physical hole chord on the original branch-region samples.
The original cached corrections and all remaining boundary terms are retained. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedHoleAggregate

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision (AllHoleExcision AnnularEntry)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus (HoleSides)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank (FaceMagnitudeBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics CommonCuts
  Preflights)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Topology.Polygon.Stokes (edgeArea)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchRegion (PairedBranchRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate (PairedBranchRequests)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.PairedBranchAggregate.PairedBranchRequests (Samples)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance (pairedValues)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (holeAreaRemainder
  rootedHoleCorrection_eq_remainder)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleRootedCorrection (rootedHoleCorrection_eq)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleFourSideCorrection (holeCorrection_eq_fourSides)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleComponentCorrection (holeCorrection
  physicalCorrection_eq_holes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PhysicalComponentCorrection (physicalComponentCorrection)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity.FacePerimeters (physicalPerimeter)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas (physicalTriangleArea)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Algebra.FiniteSum.Fin (sumFin)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {preparation : NewtonPreparation
    base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {current : LiftedPuncturedGrid grid.punctured}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus}
  {leftFixed : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential i)}
  {rightFixed : FaceMagnitudeBank domains
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j)}
  {sheet : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches → Fin 2} {error :
    Rational} {floor stage : Nat}
  {cache : Numerics domains stage}
  {left : TriangleReadings (cache.get i)
    current.mesh} {right : TriangleReadings
    (cache.get j) current.mesh}
  {leftSurface : CachedSample current.cutPolygon.patch left.values}
  {rightSurface : CachedSample current.cutPolygon.patch
    right.values}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {physicalTarget : Rational}
  {physicalRequest : TwoSheetRequest (fun
    sheet => RegularMeshes.build domains cuts
    sheet coarseDepth) fixed physicalTarget}
  (sides : (entry : AnnularEntry grid current) →
    Annulus.HoleSides entry.region)
  (perimeters : PuncturedGrid.Matched.FacePerimeters (request :=
    physicalRequest) cache.normalize i j)

/-- These are precisely the fine perimeter and the remaining sewn terms of one original branch-region receipt after its
physical chords cancel. -/
def holeBoundaryTerm {entry : Excision.AnnularEntry grid current}
    {request : PairedBranchRegion.PairedBranchRequest bank entry (sheet entry.hole.index) leftFixed rightFixed error
      floor}
    (sample : request.Sample left right leftSurface rightSurface) : Gaussian :=
  let raw := OriginalPairedCutBalance.pairedValues leftSurface rightSurface
  (sides entry).finePerimeter perimeters +
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.balance.inner.word.sources.entries.map (fun route =>
      Stokes.edgeArea (raw current.cutPolygon.patch.cut.triangles[route.owner.position.val].first)
        ((raw route.cutEdge.finish).sub (raw route.cutEdge.start)))) +
    sample.cut.pairing.jumpSum + sample.cut.pairing.defectSum + sample.cut.readback.correction

/-- The exact remaining boundary terms of the original branch samples in their retained entry order. -/
def holeBoundaryTerms : {entries : List (Excision.AnnularEntry grid current)} →
    {requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor entries} →
    PairedBranchRequests.Samples left right leftSurface rightSurface requests → List Data.Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons first last => holeBoundaryTerm sides
    perimeters first :: holeBoundaryTerms last

/-- The original per-hole discrepancy after subtracting its retained fine-perimeter and sewn boundary terms. -/
private def holeResiduals : {entries : List (Excision.AnnularEntry grid current)} →
    {requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor entries} →
    PairedBranchRequests.Samples left right leftSurface rightSurface requests → List Data.Gaussian.Basic.Canonical
  | _, _, .nil => []
  | _, _, .cons (entry := entry) first last =>
      (first.cut.correction + HoleAreaRemainder.holeAreaRemainder perimeters (sides entry).sides -
        holeBoundaryTerm sides perimeters first) ::
        holeResiduals last

variable {entries : List (AnnularEntry grid current)}
  {requests : PairedBranchRequests bank sheet leftFixed
    rightFixed error floor entries}

/-- The residual list contains exactly one discrepancy per original annular entry. -/
private theorem holeResiduals_length (samples : PairedBranchRequests.Samples left right leftSurface rightSurface
  requests) :
    (holeResiduals sides perimeters samples).length =
      entries.length := by
  induction samples with
  | nil => rfl
  | cons first last ih => exact congrArg Nat.succ ih

/-- The residual sum is exactly the original aggregate correction plus physical-hole remainders minus the retained
boundary terms. -/
private theorem holeResiduals_sum (samples : PairedBranchRequests.Samples left right leftSurface rightSurface requests)
  :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (holeResiduals sides perimeters samples) =
      samples.corrections +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => HoleAreaRemainder.holeAreaRemainder
        perimeters (sides entry).sides)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (holeBoundaryTerms sides perimeters samples) :=
        by
  induction samples with
  | nil => change (0 : Data.Gaussian.Basic.Canonical) = 0 + 0 - 0; ring1
  | cons first last ih =>
      change (_ + _ - _) + Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (holeResiduals sides perimeters last) =
        (first.cut.correction + last.corrections) + (_ + _) - (_ + _)
      rw [ih]
      ring1

/-- One global sewing request pays all original branch regions, with the actual number of retained holes and all eight
occurrences per hole. -/
theorem hole_corrections_bound (samples : PairedBranchRequests.Samples left right leftSurface rightSurface requests)
    {global : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i j}
    {sewingTarget : Fraction.Rational} {sewingFloor : Nat}
    (sewing : BilinearPreparation.Request global sewingTarget sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface) :
    Data.Gaussian.Norm.Basic.normSq (samples.corrections +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => HoleAreaRemainder.holeAreaRemainder
        perimeters (sides entry).sides)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (holeBoundaryTerms sides perimeters samples)) ≤
      (entries.length : Fraction.Rational) * ((entries.length : Fraction.Rational) *
        (8 * (8 * (sewing.budget.weight * sewing.budget.error)))) := by
  have bounds : ∀ value ∈ holeResiduals sides perimeters
    samples,
      Data.Gaussian.Norm.Basic.normSq value ≤ 8 * (8 * (sewing.budget.weight * sewing.budget.error)) := by
    induction samples with
    | nil => intro value member; exact (List.not_mem_nil member).elim
    | cons first last ih =>
        intro value member
        rcases Data.List.Membership.mem_cons.mp member with rfl | member
        · exact NewtonOriginalPairedHoleCorrection.correction_add_remainder_accurate first.cut (sides _) perimeters
            sewing later bilinear
        · exact ih value member
  have bound := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le _ _ bounds
  rw [holeResiduals_length,
    holeResiduals_sum] at bound
  exact bound

/-- The sum is the complete physical hole correction, with no missing or repeated physical component and no replacement
annular sample. -/
theorem all_hole_corrections_bound (excision : Excision.AllHoleExcision grid current)
    {requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor excision.entries}
    (samples : PairedBranchRequests.Samples left right leftSurface rightSurface requests)
    {global : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i j}
    {sewingTarget : Fraction.Rational} {sewingFloor : Nat}
    (sewing : BilinearPreparation.Request global sewingTarget sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface) :
    Data.Gaussian.Norm.Basic.normSq (samples.corrections + FiniteSum.Fin.sumFin (fun hole =>
      HoleComponentCorrection.holeCorrection perimeters left right hole) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (holeBoundaryTerms sides perimeters samples)) ≤
      (excision.entries.length : Fraction.Rational) * ((excision.entries.length : Fraction.Rational) *
        (8 * (8 * (sewing.budget.weight * sewing.budget.error)))) := by
  have equal (entry : Excision.AnnularEntry grid current) : HoleAreaRemainder.holeAreaRemainder perimeters (sides
    entry).sides =
      HoleComponentCorrection.holeCorrection perimeters left right (sides entry).position := by
    exact (HoleAreaRemainder.rootedHoleCorrection_eq_remainder perimeters left right (sides entry).sides).symm.trans
      ((HoleRootedCorrection.rootedHoleCorrection_eq perimeters left right (sides entry).sides).trans
        (HoleFourSideCorrection.holeCorrection_eq_fourSides perimeters left right (sides entry).position (sides
          entry).adjacent).symm)
  have mapped := Map.map_congr_left (values := excision.entries) (fun entry _ => equal entry)
  have total := (congrArg Data.Gaussian.Norm.Sum.Basic.gaussianSum mapped).trans
    (NewtonOriginalHolePositions.original_side_sum excision sides (fun hole => HoleComponentCorrection.holeCorrection
      perimeters left right hole))
  have bound := hole_corrections_bound sides perimeters
    samples sewing later bilinear
  rw [total] at bound
  exact bound

/-- Replace the hole part of the full physical correction on these same readings. The actual exterior component remains,
with its original sign. -/
theorem physical_correction_bound (excision : Excision.AllHoleExcision grid current)
    {requests : PairedBranchAggregate.PairedBranchRequests bank sheet leftFixed rightFixed error floor excision.entries}
    (samples : PairedBranchRequests.Samples left right leftSurface rightSurface requests)
    (neighbors : PuncturedFaces.NeighborBank grid.faces)
    {global : SewnBilinearRequest.BilinearPreparation current.cutPolygon domains i j}
    {sewingTarget : Fraction.Rational} {sewingFloor : Nat}
    (sewing : BilinearPreparation.Request global sewingTarget sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface) :
    Data.Gaussian.Norm.Basic.normSq (samples.corrections +
      (FacePerimeters.physicalPerimeter perimeters neighbors - CrossingTriangleAreas.physicalTriangleArea neighbors left
        right) -
      (PhysicalComponentCorrection.physicalComponentCorrection perimeters neighbors left right .exterior +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum
          (holeBoundaryTerms sides perimeters samples)))
          ≤
      (excision.entries.length : Fraction.Rational) * ((excision.entries.length : Fraction.Rational) *
        (8 * (8 * (sewing.budget.weight * sewing.budget.error)))) := by
  have split := HoleComponentCorrection.physicalCorrection_eq_holes perimeters neighbors left right
  have equal (correction physical exterior holes terms : Data.Gaussian.Basic.Canonical)
      (split : physical = exterior + holes) :
      correction + physical - (exterior + terms) = correction + holes - terms := by
    rw [split]
    ring1
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (equal samples.corrections _ _ _
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (holeBoundaryTerms sides perimeters samples))
      split)).trans_le
      (all_hole_corrections_bound sides perimeters
        excision samples sewing later bilinear)

end Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedHoleAggregate
