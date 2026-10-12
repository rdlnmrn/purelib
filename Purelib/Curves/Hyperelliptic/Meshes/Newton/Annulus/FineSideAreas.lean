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
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.ShrinkingPuncturedGrid
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Tactic.Ring

public section

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus

open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid

open Purelib.Data.List

open Purelib.Data.Rat

/-! Full fine-side readback for the original annular outer occurrences.
The original source chords remain explicit, and all endpoint discrepancies
are paid before any further annular or physical cancellation is attempted. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (LiftedPuncturedGrid)
open Purelib.Riemann.RootContinuation.NewtonPuncturedGrid.BranchCellBank (NewtonPreparation NewtonGrid)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces (AnnularFaces)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary (Lifted)
open Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted (OuterPreparation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SegmentSideSources.LiftedMesh (SideOccurrence)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.SideOccurrenceReadings.LiftedPuncturedGrid (occurrenceFineArea)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings (TriangleReadings)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)

open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : BranchCellBank curve
    branches higher}
  {preparation : NewtonPreparation original} {target
    radius : Rational}
  {grid : NewtonGrid preparation target radius}
    {index : Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : AnnularFaces grid index} {lifted :
    LiftedPuncturedGrid grid.punctured} {region :
    Lifted annulus lifted}
  {domains : FaceDomainBank lifted.frames
    grid.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {meshTarget : Rational} {i j : Fin genus} {stage : Nat} {cache :
    Numerics domains stage}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed meshTarget}

/-- A numerical read of the retained occurrence list, preserving every side excursion and both laps. No fresh path
preparation enters this value. -/
@[expose] def fineSideArea (prepared : Lifted.OuterPreparation region)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j) : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SideOccurrences.sideOccurrences prepared).map
    (LiftedPuncturedGrid.occurrenceFineArea perimeters))

/-- The centered area sum on the exact retained annular side-occurrence list, including both laps and all reversals. -/
@[expose] def centeredSideArea (prepared : Lifted.OuterPreparation region)
    (samples : RequestedHoleCentering.CenteredPerimeters request cache i j) : Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SideOccurrences.sideOccurrences prepared).map
    (CenteredPerimeters.occurrenceArea samples))

/-- The area correction reads the original sources of the annular prepared word, not newly selected triangle chords.
Counts refer to that same word. -/
theorem fineSideArea_readback (prepared : Lifted.OuterPreparation region)
    (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := request) cache.normalize i j)
    (left : TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh) (right :
      TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    {error : Fraction.Rational} (allocated : PuncturedGrid.PerimeterEndpointRequest fixed i j error)
    (later : allocated.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (fineSideArea
      prepared perimeters - Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (TriangleReadings.sourceChord left right)) -
      centeredSideArea prepared samples) ≤
      (region.outer.length : Fraction.Rational) * ((region.outer.length : Fraction.Rational) * error) := by
  let residual := fun occurrence : LiftedMesh.SideOccurrence lifted.mesh =>
    LiftedPuncturedGrid.occurrenceFineArea perimeters occurrence - TriangleReadings.sourceChord left right
      occurrence.source - CenteredPerimeters.occurrenceArea samples occurrence
  have bounded : ∀ value ∈ (SideOccurrences.sideOccurrences prepared).map residual,
    Data.Gaussian.Norm.Basic.normSq value ≤ error := by
    intro value member
    obtain ⟨occurrence, _, equal⟩ := Map.mem_map.mp member
    rw [← equal]
    exact PerimeterEndpointRequest.occurrence_bound allocated later samples perimeters left right occurrence
  have estimate := Data.Gaussian.Norm.Sum.Bounds.normSq_sum_le _ _ bounded
  rw [Purelib.Data.List.Map.length_map, SideOccurrences.sideOccurrences_count prepared] at estimate
  have sumIdentity : Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SideOccurrences.sideOccurrences prepared).map
    residual) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SideOccurrences.sideOccurrences prepared).map
        (LiftedPuncturedGrid.occurrenceFineArea perimeters)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SideOccurrences.sideOccurrences prepared).map (fun occurrence =>
        TriangleReadings.sourceChord left right occurrence.source)) -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum ((SideOccurrences.sideOccurrences prepared).map
        (CenteredPerimeters.occurrenceArea samples)) := by
    induction (SideOccurrences.sideOccurrences prepared) with
    | nil => change (0 : Data.Gaussian.Basic.Canonical) = 0 - 0 - 0; ring1
    | cons occurrence tail ih =>
        simp only [List.map_cons, Data.Gaussian.Norm.Sum.Basic.gaussianSum, -eq_self, -iff_self]
        rw [ih]
        dsimp only [residual, -eq_self, -iff_self]
        ring1
  have sources : (SideOccurrences.sideOccurrences prepared).map (fun occurrence => TriangleReadings.sourceChord left
    right occurrence.source) =
      prepared.sources.map (TriangleReadings.sourceChord left right) :=
    (Purelib.Data.List.Map.map_map ..).symm.trans (congrArg (List.map (TriangleReadings.sourceChord left right))
      (SideOccurrences.sideOccurrences_sources prepared))
  rw [sumIdentity, sources] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas
