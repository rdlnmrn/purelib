module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularSideNeighbors
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.WordArea
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Topology.Surface.Word.Pairing
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalSewnFormula
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularClippedRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularLocalBoundaryRequest
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Tactic.Ring

public section

/-! The local comparison consumes the actual canonical cut-word pairing,
including its physical matrix and full closed correction. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalCutPairing

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.GlobalPerimeterIdentity
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalPairBound
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingSamples
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.CrossingTotal.CrossingRequests
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
open Purelib.Data.Rat
open Purelib.Riemann.Meshes.PuncturedGridFaces
open Purelib.Topology.Surface.Cut.IntegralPairing
open Purelib.Topology.Surface.Cut.WordArea
open Purelib.Topology.Surface.Sewing
open Purelib.Topology.Surface.Sewing.Bilinear
open Purelib.Topology.Surface.Sewing.Bilinear.Samples
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Topology.Surface.Word

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularExteriorRequest (ExteriorBoundaryRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingCornerBudget (CornerRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CrossingTriangleAreas (physicalTriangleArea)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {target : Rational} {i j : Fin genus} {firstParent secondParent : Fin 2} {floor stage : Nat}
  {cache : Numerics domains stage}

/-- The actual local perimeter sum approximates the complete cut pairing plus physical boundary correction.

The paid sewing, crossing and corner requests preserve the paired and remaining matrices and the closed-word correction.
-/
theorem local_cut_pairing_bound
    (exterior : RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet => RegularMeshes.build domains cuts sheet
      coarseDepth) fixed (((target / 4) / 4) / 4))
    {retained : Matched.CrossingBank exterior.prepared.energy lifted.mesh}
    (total : CrossingRequests.TotalRequest retained i j firstParent secondParent ((((target / 4) / 4) / 4) / 4) floor)
    (corner : CrossingCornerBudget.CornerRequest fixed i j ((target / 4) / 4))
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    (samples : CrossingRequests.Samples total.allocated cache.normalize)
    (original : Matched.FacePerimeters (request := exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request := exterior.prepared.energy) cache.normalize i j)
    {prepared : SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains i j}
    (sewing : BilinearPreparation.Request prepared (target / 4) floor)
    {leftSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values}
    (surface : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface)
    (word : CutBoundaryWord.AreaSample lifted.cutBoundaryWord surface.values
      (surface.values lifted.cutPolygon.patch.cut.anchor))
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (sewingLater : sewing.index ≤ stage)
    (neighbors : PuncturedFaces.NeighborBank base.faces) (positive : 0 < target)
    (later : total.allocated.index ≤ stage) (cornerLater : corner.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (original.localTotalSum - (2 * Pairing.contract (fun row column =>
      integral.paired row column) word.values +
      Pairing.contract (fun row column => integral.remaining row column) word.values + word.closedCorrection) -
      (FacePerimeters.physicalPerimeter normalized neighbors - CrossingTriangleAreas.physicalTriangleArea neighbors left
        right)) ≤ target := by
  have estimate := TotalRequest.local_sewn_boundary_bound exterior total corner left right samples original normalized
    sewing surface
    sewingLater neighbors
    (Fraction.Order.Field.div_pos_direct positive (by decide)) later cornerLater
  rw [Bilinear.boundary_eq_word surface word, integral.contract_eq] at estimate
  apply estimate.trans_eq
  calc
    4 * (target / 4) = target / 4 * 4 := by ring1
    _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)

/-- The complete corrected cut pairing satisfies the combined local comparison bound.

The estimate also pays the original ownership threshold and retains every physical perimeter and source-triangle term.
-/
theorem corrected_cut_pairing_bound
    (exterior : RegularExteriorRequest.ExteriorBoundaryRequest (fun sheet => RegularMeshes.build domains cuts sheet
      coarseDepth) fixed (((target / 4) / 4) / 4))
    {retained : Matched.CrossingBank exterior.prepared.energy lifted.mesh}
    (total : CrossingRequests.TotalRequest retained i j firstParent secondParent ((((target / 4) / 4) / 4) / 4) floor)
    (corner : CrossingCornerBudget.CornerRequest fixed i j ((target / 4) / 4))
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    (samples : CrossingRequests.Samples total.allocated cache.normalize)
    (original : Matched.FacePerimeters (request := exterior.prepared.energy) cache i j)
    (normalized : Matched.FacePerimeters (request := exterior.prepared.energy) cache.normalize i j)
    {prepared : SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains i j}
    (sewing : BilinearPreparation.Request prepared (target / 4) floor)
    {leftSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch left.values}
    {rightSurface : SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch right.values}
    (surface : Topology.Surface.Sewing.Bilinear.Samples leftSurface rightSurface)
    (word : CutBoundaryWord.AreaSample lifted.cutBoundaryWord surface.values
      (surface.values lifted.cutPolygon.patch.cut.anchor))
    (integral : Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord)
    (sewingLater : sewing.index ≤ stage)
    (ownershipLater : exterior.prepared.ownership.index ≤ stage)
    (neighbors : PuncturedFaces.NeighborBank base.faces) (positive : 0 < target)
    (later : total.allocated.index ≤ stage) (cornerLater : corner.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq ((2 * Pairing.contract (fun row column => integral.paired row column)
      word.values +
      Pairing.contract (fun row column => integral.remaining row column) word.values + word.closedCorrection) +
      (FacePerimeters.physicalPerimeter normalized neighbors - CrossingTriangleAreas.physicalTriangleArea neighbors left
        right)) ≤ 2 * (target + exterior.localTarget) := by
  have comparison := local_cut_pairing_bound exterior total
    corner left right samples original normalized sewing surface word integral
    sewingLater neighbors positive later cornerLater
  have localBound := FacePerimeters.local_bound exterior.prepared original ownershipLater
  let paired := 2 * Pairing.contract (fun row column => integral.paired row column) word.values +
    Pairing.contract (fun row column => integral.remaining row column) word.values + word.closedCorrection
  let physical := FacePerimeters.physicalPerimeter normalized neighbors - CrossingTriangleAreas.physicalTriangleArea
    neighbors left right
  change Data.Gaussian.Norm.Basic.normSq (paired + physical) ≤ _
  have equal : paired + physical = original.localTotalSum - (original.localTotalSum - paired - physical) := by ring1
  rw [equal]
  exact (Data.Gaussian.Norm.Bounds.normSq_sub_le_two _ _).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add localBound comparison) (by decide)).trans_eq (by ring1))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LocalCutPairing
