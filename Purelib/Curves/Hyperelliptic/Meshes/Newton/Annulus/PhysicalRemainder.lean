module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests
import Purelib.Riemann.Topology.NewtonSewnExcision
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerChordTransport
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.Newton.AllHoles.Excision
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.CutBalance
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedAreaRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.MagnitudeBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
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
import Purelib.Topology.Surface.Sewing.SewnPrimitiveFaces
import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

public section

/-! Cancel actual source chords in the annular physical correction. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PhysicalRemainder

open Purelib
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.InnerChordTransport
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
open Purelib.Data.Rat
open Purelib.Topology.Polygon
open Purelib.Topology.Surface.Sewing.Bilinear

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.AreaRequests.NewtonPreparation (AreaRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Riemann.Topology.NewtonSewnExcision.AllHoleExcision (SewnAnnulus)
open Purelib.Riemann.Topology.NewtonPairedSewnAreaRequests (PairedSewnRequest)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PairedCutRequests (AnnularSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {error
    radius : Rational}
  {request : AreaRequest preparation
    (error / 4) radius} {lifted : LiftedPuncturedGrid request.grid.punctured}
  {differential other : Fin genus} {domains :
    FaceDomainBank lifted.frames
    request.grid.faces.regulars} {stage floor : Nat}
  {cache : Numerics domains stage}
  {readings : TriangleReadings (cache.get
    differential) lifted.mesh} {surface : CachedSample
    lifted.cutPolygon.patch readings.values}
  {otherReadings : TriangleReadings
    (cache.get other) lifted.mesh}
  {otherSurface : CachedSample lifted.cutPolygon.patch
    otherReadings.values}

namespace AnnularSample

variable {annulus : SewnAnnulus surface} {prepared :
  OuterPreparation annulus.source.region}
  {requested : PairedSewnRequest request prepared differential
    other domains floor}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest
variable {cuts : CommonCuts domains}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
  Preflights domains sheet}
  {physicalTarget : Rational}
  {physicalRequest : TwoSheetRequest (fun
    sheet => RegularMeshes.build domains cuts
    sheet coarseDepth) fixed physicalTarget}

/-- Actual source-chord cancellation between the cached annular correction and its indexed fine physical hole remainder.
The fine perimeter, origins, jumps, defects and outer offsets remain explicit. -/
theorem correction_add_remainder_accurate (sample : PairedCutRequests.AnnularSample annulus prepared requested
  otherSurface)
    (sides : HoleSides annulus.source.region)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := physicalRequest) cache.normalize differential other)
    {global : SewnBilinearRequest.BilinearPreparation lifted.cutPolygon domains differential other}
    {sewingTarget : Fraction.Rational} {sewingFloor : Nat}
    (sewing : BilinearPreparation.Request global sewingTarget sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples surface otherSurface) :
    let raw := fun vertex => (⟨surface.sewn.values vertex, otherSurface.sewn.values vertex⟩ : Stokes.PrimitivePoint)
    Data.Gaussian.Norm.Basic.normSq (sample.correction + HoleAreaRemainder.holeAreaRemainder perimeters
      sides.sides -
      (HoleSides.finePerimeter sides perimeters +
      Data.Gaussian.Norm.Sum.Basic.gaussianSum
        (sample.balance.inner.word.sources.entries.map (fun route =>
          Stokes.edgeArea (raw lifted.cutPolygon.patch.cut.triangles[route.owner.position.val].first)
            ((raw route.cutEdge.finish).sub (raw route.cutEdge.start)))) +
      sample.paired.jumpSum + sample.paired.defectSum + sample.outer.correction)) ≤
      8 * (8 * (sewing.budget.weight * sewing.budget.error)) := by
  intro raw
  rw [← HoleSides.remainder_add_inner_chords sides sample.balance.inner perimeters readings otherReadings]
  have cancel (a b c d e f g : Data.Gaussian.Basic.Canonical) :
      a + b - (b + c + d + e + f + g) = a - (c + d + e + f + g) := by ring1
  rw [cancel]
  exact AnnularSample.correction_source_chord_accurate sample sewing later bilinear

end AnnularSample
end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PhysicalRemainder
