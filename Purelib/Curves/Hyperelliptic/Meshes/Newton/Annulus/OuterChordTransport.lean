module
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSourceChordRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerChordTransport
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
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
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Boundary.ProjectedAreaCancellation
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Sewing.Bilinear.Requests
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Topology.Surface.Sewing.SewnPrimitiveBoundary
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! The outer source-chord readback uses the original prepared cut word.
Every sewn owner-origin term is retained when the fine side area replaces
that same chord list. Projected closure does not erase these origins. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Riemann
open Purelib

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {error radius :
    Fraction.Rational}
  {request : Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation.AreaRequest preparation (error / 4)
    radius} {lifted : Meshes.LiftedPuncturedGrid request.grid.punctured}
  {differential other : Fin genus} {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank
    lifted.frames request.grid.faces.regulars} {stage floor : Nat}
  {cache : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {readings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get differential)
    lifted.mesh} {surface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
    readings.values}
  {otherReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get other)
    lifted.mesh}
  {otherSurface : Topology.Surface.Sewing.SewnPrimitiveSamples.CachedSample lifted.cutPolygon.patch
    otherReadings.values}

namespace AnnularSample
variable {annulus : Topology.NewtonSewnExcision.AllHoleExcision.SewnAnnulus surface} {prepared :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation annulus.source.region}
  {requested : Topology.NewtonPairedSewnAreaRequests.PairedSewnRequest request prepared differential other domains
    floor}

/-- Read the origins of the very same oriented owners as the outer cut word. -/
@[expose] def outerOrigins (_sample : Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests.AnnularSample annulus
  prepared requested otherSurface) : Gaussian :=
  let raw := fun vertex => (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ :
    Topology.Polygon.Stokes.PrimitivePoint)
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (requested.sewing.first.word.sources.entries.map (fun route =>
    Topology.Polygon.Stokes.edgeArea (raw lifted.cutPolygon.patch.cut.triangles[route.owner.position.val].first)
      ((raw route.cutEdge.finish).sub (raw route.cutEdge.start))))

/-- The original outer sewn word, after subtracting its retained owner origins, approximates the identical prepared
source-chord list.

The paid global sewing request controls the error with the squared original outer-word length. -/
theorem outer_source_chord_accurate (sample : Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests.AnnularSample
  annulus prepared requested otherSurface)
    {global : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains
      differential other}
    {sewingTarget : Fraction.Rational} {sewingFloor : Nat}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request global sewingTarget
      sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples surface otherSurface) :
    Data.Gaussian.Norm.Basic.normSq (sample.outer.raw -
      (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins sample) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord readings
      otherReadings))) ≤
      (annulus.source.region.outer.length : Fraction.Rational) *
        ((annulus.source.region.outer.length : Fraction.Rational) * (sewing.budget.weight * sewing.budget.error)) := by
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.SewnSourceChordRequest.BilinearPreparation.Request.raw_path_source_chord_accurate
    sewing later readings otherReadings bilinear requested.sewing.first.word.sources
  dsimp only at estimate
  rw [requested.sewing.first.word.sources_eq, ← sample.outer.raw_eq] at estimate
  have count := congrArg List.length prepared.sources_project
  rw [Data.List.Map.length_map] at count
  rw [requested.sewing.first.word.length_eq, count] at estimate
  exact estimate

/-- Selected annular area minus the original inner boundary, cut jumps and
cut defects reads the raw outer word exactly. No origin terms are discarded. -/
theorem selected_outer_eq (sample : Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests.AnnularSample annulus prepared
  requested otherSurface) :
    sample.selectedArea - (sample.innerArea + sample.paired.jumpSum + sample.paired.defectSum +
      (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins sample)) =
      sample.outer.raw - (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins sample) :=
        by
  have balance := sample.corrected_eq
  rw [sample.correction_eq] at balance
  calc
    _ = (sample.selectedArea - (sample.innerArea + sample.paired.jumpSum + sample.paired.defectSum +
      sample.outer.correction)) +
      sample.outer.correction - (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins
        sample) := by ring1
    _ = _ := by rw [balance]; ring1

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
variable {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth :
  Nat} {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights
  domains sheet}
  {meshTarget : Fraction.Rational}
  {meshRequest : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    meshTarget}

/-- The two estimates cancel the identical source-chord sum. This helper's
fine premise is supplied by the all-hole allocator on the retained bank. -/
theorem selected_fine_bound (sample : Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests.AnnularSample annulus
  prepared requested otherSurface)
    {global : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains
      differential other}
    {sewingTarget : Fraction.Rational} {sewingFloor : Nat}
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request global sewingTarget
      sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples surface otherSurface)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := meshRequest)
      cache.normalize differential other)
    {fineTarget : Fraction.Rational}
    (fine : Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea prepared
      perimeters - Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord readings
      otherReadings))) ≤ fineTarget) :
    Data.Gaussian.Norm.Basic.normSq (sample.selectedArea -
      (sample.innerArea + sample.paired.jumpSum + sample.paired.defectSum +
        (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins sample)) -
        Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea prepared perimeters) ≤
      2 * ((annulus.source.region.outer.length : Fraction.Rational) *
        ((annulus.source.region.outer.length : Fraction.Rational) * (sewing.budget.weight * sewing.budget.error)) +
          fineTarget) := by
  have coarse := Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outer_source_chord_accurate
    sample sewing later bilinear
  have estimate := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (sample.outer.raw - (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins sample) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord readings
      otherReadings)))
    (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea prepared perimeters -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord readings
      otherReadings)))).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct coarse fine) (by decide))
  rw [Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.selected_outer_eq sample]
  exact (show sample.outer.raw - (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins
    sample) - Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea prepared perimeters =
    (sample.outer.raw - (Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport.AnnularSample.outerOrigins sample) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord readings
      otherReadings))) -
      (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea prepared perimeters -
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
        (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord readings
        otherReadings))) by ring1) ▸ estimate

end AnnularSample
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.OuterChordTransport
