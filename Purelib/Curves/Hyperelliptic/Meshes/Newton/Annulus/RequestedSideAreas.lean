module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCellWinding
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.Faces
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison
import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.PerimeterEndpointRequest
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.RootContinuation.NewtonPuncturedGrid
import Purelib.Riemann.RootContinuation.PreparedNewtonAreaRate
public import Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Basic
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
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.PreparedNewtonBandFamilies
import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts

public section

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Riemann

/-! Requested shrinking bounds on the actual annular outer-side readings.
The shared band, source occurrence order, face sheets and fine traces all
come from the retained excision and numerical banks. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.RequestedSideAreas

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {original : Hyperelliptic.Branches.BranchCellBank curve branches higher}
  {preparation : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonPreparation original} {target radius :
    Fraction.Rational}
  {grid : RootContinuation.NewtonPuncturedGrid.BranchCellBank.NewtonGrid preparation target radius} {index :
    Hyperelliptic.Branches.BranchIsolation.Data.Index branches}
  {annulus : Hyperelliptic.Meshes.Newton.Annulus.Faces.AnnularFaces grid index} {lifted : Meshes.LiftedPuncturedGrid
    grid.punctured} {region : Hyperelliptic.Meshes.Newton.Annulus.LiftedBoundary.Lifted annulus lifted}
  {domains : Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames grid.faces.regulars}
  {cuts : Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.CommonCuts domains} {coarseDepth : Nat}
    {fixed : (sheet : Fin 2) → Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Preflights domains
    sheet}
  {meshTarget : Fraction.Rational} {i j : Fin genus} {stage : Nat} {cache :
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.Numerics domains stage}
  {request : Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest.TwoSheetRequest (fun sheet =>
    Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes.build domains cuts sheet coarseDepth) fixed
    meshTarget}

/-- Prepare the original annular outer-side requests on the supplied trace bank before selecting a shared numerical
stage. -/
@[expose] def sideRequests (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region) (traces : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.PerimeterTraceBank request) (i j : Fin
  genus) :=
  Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank.build traces (grid.bands.entries.get
    index) i j (Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences prepared)

/-- Bound the centered original annular outer area by its squared occurrence count and retained Newton radius estimate.

The retained annular path certifies every fine-side boundary premise; the exact band requests and common late cache
determine the area readings. -/
theorem centeredSideArea_bound (prepared :
  Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation region)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j) (lengths
      : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (references : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank samples.traces
      (grid.bands.entries.get index) i j (Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences prepared))
    (later : references.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.centeredSideArea prepared
      samples) ≤
      (region.outer.length : Fraction.Rational) * ((region.outer.length : Fraction.Rational) *
        (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient (curve := curve) (current :=
          (Hyperelliptic.Branches.BranchCellWinding.state original index).raw) (preparation.profiles.get
          index).differentials *
          (grid.bands.entries.get index).selection.sample.output.radius^2)) := by
  have estimate := Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank.sum_bound samples
    lengths references (Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences_onBoundary prepared) later
  rw [(Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences_count prepared)] at estimate
  exact estimate

/-- Bound the fine annular outer area after subtracting its original source chords.

The estimate retains both the endpoint allowance and shrinking Newton contribution at their common late sample stage,
including the complete fine-path and primitive-origin contributions. -/
theorem fineSideArea_bound (prepared : Hyperelliptic.Meshes.Newton.Annulus.PrimitiveComparison.Lifted.OuterPreparation
  region)
    (samples : Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering.CenteredPerimeters request cache i j) (lengths
      : Hyperelliptic.Meshes.PuncturedGrid.WeightedPerimeterAreas.CenteredPerimeters.Lengths samples)
    (perimeters : PuncturedGrid.Matched.FacePerimeters (request := request)
      cache.normalize i j)
    (left : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get i) lifted.mesh)
      (right : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings (cache.get j) lifted.mesh)
    (references : Hyperelliptic.Meshes.PuncturedGrid.BandOccurrenceRequests.BandOccurrenceBank samples.traces
      (grid.bands.entries.get index) i j (Hyperelliptic.Meshes.Newton.Annulus.SideOccurrences.sideOccurrences prepared))
    {error : Fraction.Rational} (endpoints :
      PuncturedGrid.PerimeterEndpointRequest fixed i j error)
    (later : references.index ≤ stage) (endpointsLater : endpoints.index ≤ stage) :
    Data.Gaussian.Norm.Basic.normSq (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea prepared
      perimeters - Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right))) ≤
      2 * ((region.outer.length : Fraction.Rational) * ((region.outer.length : Fraction.Rational) * error) +
        (region.outer.length : Fraction.Rational) * ((region.outer.length : Fraction.Rational) *
          (RootContinuation.PreparedNewtonAreaRate.PreparedBandFamily.areaCoefficient (curve := curve) (current :=
            (Hyperelliptic.Branches.BranchCellWinding.state original index).raw) (preparation.profiles.get
            index).differentials *
            (grid.bands.entries.get index).selection.sample.output.radius^2))) := by
  have discrepancy := Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea_readback prepared samples
    perimeters left right endpoints endpointsLater
  have centered := Hyperelliptic.Meshes.Newton.Annulus.RequestedSideAreas.centeredSideArea_bound prepared samples
    lengths references later
  have estimate := (Gaussian.Norm.Bounds.normSq_add_le_two
    (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.fineSideArea prepared perimeters -
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (prepared.sources.map
      (Hyperelliptic.Meshes.PuncturedGrid.HoleSourceChords.BranchCellBank.TriangleReadings.sourceChord left right)) -
      Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.centeredSideArea prepared samples)
    (Hyperelliptic.Meshes.Newton.Annulus.FineSideAreas.centeredSideArea prepared samples)).trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
        (Fraction.Order.Arithmetic.add_le_add_direct discrepancy centered) (by decide))
  rw [sub_add_cancel] at estimate
  exact estimate

end Purelib.Curves.Hyperelliptic.Meshes.Newton.Annulus.RequestedSideAreas
