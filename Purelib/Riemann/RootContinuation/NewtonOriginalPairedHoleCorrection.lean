module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic

import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Topology.Surface.Sewing.Bilinear.Samples
import Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnSourceChordRequest
import Purelib.Tactic.QuotientFreeOmega
import Purelib.Tactic.Ring

open Purelib.Data

public section

/-! Cancel the physical inner source chords for the original branch regions
used by the ordered period comparison. All remaining cut terms are retained. -/
namespace Purelib.Riemann.RootContinuation.NewtonOriginalPairedHoleCorrection

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedBranchTours.LiftedPuncturedGrid (BasedBranchBank)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Riemann.RootContinuation.NewtonOriginalAnnularFaces (OriginalAnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Inclusion.HoleSewing (IncludedHoleSewing)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton (OriginalCutBalance)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance (PairedSample pairedValues)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance.PairedSample (correction)
open Purelib.Topology.Surface.Sewing.SewnPrimitiveSamples (CachedSample)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (Numerics CommonCuts
  Preflights)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched (FacePerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest (BilinearPreparation)
open _root_.Purelib.Topology.Surface.Sewing.Bilinear renaming Samples -> Bilinear
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder (holeAreaRemainder)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus (HoleSides)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Topology.Polygon.Stokes
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.LinearAlgebra.Gaussian.QuadraticForm (GaussianMatrix)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {bank :
    BasedBranchBank lifted}
  {preparation : NewtonPreparation base.bank.toBranchCellBank} {target radius : Rational}
  {grid : NewtonGrid preparation target radius} {current : LiftedPuncturedGrid grid.punctured}
  {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {outer : OriginalAnnularFaces grid index} {annulus :
    AnnularFaces grid index}
  {region : Lifted annulus current}
  {domains : FaceDomainBank current.frames
    grid.faces.regulars} {i j : Fin genus} {stage : Nat}
  {cache : Numerics domains stage}
  {geometry : IncludedHoleSewing bank grid.shrunk.included index domains (standardDifferential i)}
  {leftReadings : TriangleReadings
    (cache.get i) current.mesh}
  {rightReadings : TriangleReadings
    (cache.get j) current.mesh}
  {left : CachedSample current.cutPolygon.patch
    leftReadings.values}
  {right : CachedSample current.cutPolygon.patch
    rightReadings.values}
  {balance : Curves.Hyperelliptic.Meshes.Newton.OriginalCutBalance outer region geometry
    left}
  {global : BilinearPreparation current.cutPolygon
    domains i j}
  {sewingTarget : Rational} {sewingFloor : Nat}

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- Bound the original annulus's inner reading after removing its origin and source-chord sums.

The retained physical inner word has eight edge occurrences. At a stage satisfying the sewing request, its error is
bounded by 64 times the same sewing weight and error. -/
theorem inner_source_chord_accurate (sample : Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance.PairedSample balance
  right)
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request global sewingTarget
      sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples left right) :
    let raw := Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance.pairedValues left right
    Data.Gaussian.Norm.Basic.normSq (sample.inner - Data.Gaussian.Norm.Sum.Basic.gaussianSum
      (balance.inner.word.sources.entries.map (fun route =>
        edgeArea (raw current.cutPolygon.patch.cut.triangles[route.owner.position.val].first)
          ((raw route.cutEdge.finish).sub (raw route.cutEdge.start)))) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (balance.inner.word.sources.sources.map
        (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord leftReadings
        rightReadings))) ≤
      8 * (8 * (sewing.budget.weight * sewing.budget.error)) := by
  intro raw
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.SewnSourceChordRequest.BilinearPreparation.Request.raw_path_source_chord_accurate
    sewing later leftReadings rightReadings bilinear
    balance.inner.word.sources
  have count : balance.inner.word.edges.length = 8 := by
    have equal := congrArg List.length (balance.inner.project.trans region.inner_eq)
    rw [List.Map.length_map] at equal
    exact equal.trans (region.hole.liftedBoundary_length current.vertices current.edges)
  dsimp only at estimate
  rw [count] at estimate
  rw [sample.inner_eq]
  exact estimate

variable {cuts : CommonCuts domains}
  {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
  Preflights domains sheet}
  {physicalTarget : Rational}
  {physicalRequest : TwoSheetRequest (fun
    sheet => RegularMeshes.build domains cuts
    sheet coarseDepth) fixed physicalTarget}

open Purelib.Curves in
open Purelib.Topology in
open Purelib.Data in
/-- Cancel the physical hole remainder against the retained original-region inner chords.

The bounded difference keeps the fine perimeter, origin contributions, pairing jumps, defects and readback correction,
using the same side receipts and sewing budget. -/
theorem correction_add_remainder_accurate (sample : Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance.PairedSample
  balance right)
    (sides : Curves.Hyperelliptic.Meshes.Newton.Annulus.HoleSides region)
    (perimeters : Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters (request := physicalRequest)
      cache.normalize i j)
    (sewing : Hyperelliptic.Meshes.PuncturedGrid.SewnBilinearRequest.BilinearPreparation.Request global sewingTarget
      sewingFloor)
    (later : sewing.index ≤ stage) (bilinear : Topology.Surface.Sewing.Bilinear.Samples left right) :
    let raw := Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance.pairedValues left right
    Data.Gaussian.Norm.Basic.normSq (sample.correction +
      Hyperelliptic.Meshes.PuncturedGrid.HoleAreaRemainder.holeAreaRemainder perimeters sides.sides -
      (sides.finePerimeter perimeters +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (balance.inner.word.sources.entries.map (fun route =>
          edgeArea (raw current.cutPolygon.patch.cut.triangles[route.owner.position.val].first)
            ((raw route.cutEdge.finish).sub (raw route.cutEdge.start)))) +
        sample.pairing.jumpSum + sample.pairing.defectSum + sample.readback.correction)) ≤
      8 * (8 * (sewing.budget.weight * sewing.budget.error)) := by
  intro raw
  rw [← sides.remainder_add_inner_chords balance.inner perimeters leftReadings rightReadings]
  have equal (inner remainder chords origins jumps defects offsets : Gaussian.Basic.Canonical) :
      (inner + jumps + defects + offsets) + remainder -
        (remainder + chords + origins + jumps + defects + offsets) = inner - origins - chords := by ring1
  unfold Hyperelliptic.Meshes.Newton.OriginalPairedCutBalance.PairedSample.correction
  rw [equal]
  exact inner_source_chord_accurate sample sewing later bilinear

end Purelib.Riemann.RootContinuation.NewtonOriginalPairedHoleCorrection
