module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.RootIsolation.State.Raw

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Paths.ClearBoxPathWinding
public import Purelib.Riemann.Paths.PreparedBoundarySegments
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.RootContinuation.NewtonBandBounds
import Purelib.Riemann.RootContinuation.NewtonBandDifferentials
public import Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonTraceReferences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Matched.FacePerimeters
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NormalizedNumerics
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Geometry.Rectangle.Partition.PreparedRectangleCuts
import Purelib.Integration.Path.JoinedTrace
import Purelib.Integration.Polynomial.Rectangle.Accuracy.Fragment
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Integration.PreparedParentSplitting
import Purelib.Riemann.Integration.RectangularCenteredPerimeter
import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularObservationMesh
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.RectangularMatchedSideTrace
import Purelib.Riemann.Paths.RectangularMatchedVerticalSideTrace
import Purelib.Riemann.Paths.RectangularPerimeterTraces
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.RectangularObservationAssembly
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.Topology.Polygon.Stokes

open Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries

open Purelib.Polynomial.Geometry.ClearPath
open _root_.Purelib.Polynomial.Geometry renaming ClearPath -> ClearPath

open Purelib.Riemann.Paths

open Purelib.Riemann.Paths.PreparedPathParentCaches

open Purelib.Riemann.Periods

open Purelib.Riemann.RootContinuation

@[expose] public section

/-! Consume Newton path references in the same normalized perimeter bank as
the requested cut pairing. Entry ownership and the original parent cache are
retained; the shared domain is selected before any reference is requested. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonCenteredPerimeters

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Geometry (ClearPath)
open _root_.Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Purelib.Riemann.Paths.PreparedPathDecomposition (CoveredSegment)
open Purelib.Riemann.Paths.PreparedPathParentCaches.PreparedClearPathModels (ParentCache)
open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks (FaceDomainBank)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes (RegularMeshes)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RegularDomainMeshes.RegularMeshes (CommonCuts Preflights
  Numerics)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TwoSheetBilinearRequest (TwoSheetRequest)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RequestedHoleCentering (CenteredPerimeters)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveReferences (Reference)
open Purelib.Riemann.Periods.PeriodMatrix (standardDifferential)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonTraceReferences (newton_bottom_centered_density_bound
  newton_top_centered_density_bound newton_left_centered_density_bound newton_right_centered_density_bound)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths (EnteredPath)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries.FaceModels (Entry)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples (PreparedBandRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonBandSamples.Sample (preparedDensity)
open Purelib.Riemann.Paths.PreparedBoundarySegments (SameSide)
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {domains :
    FaceDomainBank lifted.frames base.faces.regulars}
  {cuts : CommonCuts domains}
    {coarseDepth : Nat} {fixed : (sheet : Fin 2) →
    Preflights domains sheet}
  {meshTarget : Rational} {i j : Fin genus} {stage : Nat} {cache :
    Numerics domains stage}
  {request : TwoSheetRequest (fun sheet =>
    RegularMeshes.build domains cuts sheet
    coarseDepth) fixed meshTarget}
  {position : Fin base.faces.regulars.length}
  {ambient : Purelib.Geometry.Rational.Box} {start finish : Purelib.Data.Gaussian.Basic.Canonical}
  {segment : ClearSegment curve.polynomial ambient start finish}
  {owner : Owner (curve.polynomial.eval start)} {piece :
    CoveredSegment segment owner}
  {parentSheet : Fin 2}

/-- Attach the supplied original preparation to the selected shared face and sheet. This constructs comparison geometry,
not another path preparation. -/
def perimeterEntry (entry : FaceModels.Entry (domains.get position).models start owner)
    (inside : ClearPath.InBox (base.faces.regulars[position.val]'position.isLt).cell.box (.cons segment (.nil finish)))
    (parents : PreparedClearPathModels.ParentCache piece.path (PeriodMatrix.standardDifferential j) parentSheet) :=
  EnteredPath.ofEntry entry ((domains.get position).domain entry.sheet) piece.path inside
    (PeriodMatrix.standardDifferential j) parentSheet parents

variable {entry : Entry (domains.get
  position).models start owner}
  {inside : Polynomial.Geometry.ClearPath.InBox
    (base.faces.regulars[position.val]'position.isLt).cell.box (.cons segment (.nil finish))}
  {parents : ParentCache piece.path
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j) parentSheet}
  {bandAmbient : Purelib.Geometry.Rational.Box} {current :
    Purelib.RootIsolation.State.Raw.RawWindingState curve.polynomial bandAmbient}
  {profile : Purelib.Riemann.RootContinuation.NewtonBandBounds.Profile curve.squarefree current.box}
  {differentialProfile : Purelib.Riemann.RootContinuation.NewtonBandDifferentials.DifferentialProfile profile
    (Purelib.Riemann.Periods.PeriodMatrix.standardDifferential j).exponent}
  {target tolerance : Rational}

namespace CenteredPerimeters

/-- The actual normalized bottom perimeter retains its coordinate-sensitive Newton bound. Both sheet selection and local
offset data come from the cache. -/
theorem newton_bottom_bound
    (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (reference : PrimitiveReferences.Reference
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonCenteredPerimeters.perimeterEntry entry inside parents)
      tolerance)
    (band : PreparedNewtonBandSamples.PreparedBandRequest differentialProfile target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ stage)
    (vertex : Fin ((((samples.traces.get position).get entry.sheet).bottom).vertices.rest.length + 1))
    (firstEq : ((samples.traces.get position).get entry.sheet).bottom.point
      (((samples.traces.get position).get entry.sheet).bottom.vertices.indexed 0) = start)
    (lastEq : ((samples.traces.get position).get entry.sheet).bottom.point
      (((samples.traces.get position).get entry.sheet).bottom.vertices.indexed vertex) = finish) :
    Data.Gaussian.Norm.Basic.normSq ((((samples.samples.get position).get entry.sheet).bottom.centered
      vertex).right) ≤
      3 * tolerance + 4 * (PreparedNewtonBandSamples.Sample.preparedDensity band.sample differentialProfile band.error *
        Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  exact NewtonTraceReferences.newton_bottom_centered_density_bound reference band firstInside lastInside side later
    (cache.normalize.atDomain position entry.sheet j)
    (fun column row point => (cache.normalize.atDomain position entry.sheet i).anchors.alignedValue
      (cache.normalize.atDomain position entry.sheet i).offsets column row point)
    ((samples.samples.get position).get entry.sheet) vertex firstEq lastEq

/-- The actual normalized top perimeter retains its coordinate-sensitive Newton bound. Both sheet selection and local
offset data come from the cache. -/
theorem newton_top_bound
    (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (reference : PrimitiveReferences.Reference
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonCenteredPerimeters.perimeterEntry entry inside parents)
      tolerance)
    (band : PreparedNewtonBandSamples.PreparedBandRequest differentialProfile target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ stage)
    (vertex : Fin ((((samples.traces.get position).get entry.sheet).top).vertices.rest.length + 1))
    (firstEq : ((samples.traces.get position).get entry.sheet).top.point
      (((samples.traces.get position).get entry.sheet).top.vertices.indexed 0) = start)
    (lastEq : ((samples.traces.get position).get entry.sheet).top.point
      (((samples.traces.get position).get entry.sheet).top.vertices.indexed vertex) = finish) :
    Data.Gaussian.Norm.Basic.normSq ((((samples.samples.get position).get entry.sheet).top.centered
      vertex).right) ≤
      3 * tolerance + 4 * (PreparedNewtonBandSamples.Sample.preparedDensity band.sample differentialProfile band.error *
        Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  exact NewtonTraceReferences.newton_top_centered_density_bound reference band firstInside lastInside side later
    (cache.normalize.atDomain position entry.sheet j)
    (fun column row point => (cache.normalize.atDomain position entry.sheet i).anchors.alignedValue
      (cache.normalize.atDomain position entry.sheet i).offsets column row point)
    ((samples.samples.get position).get entry.sheet) vertex firstEq lastEq

/-- The actual normalized left perimeter retains its coordinate-sensitive Newton bound. Both sheet selection and local
offset data come from the cache. -/
theorem newton_left_bound
    (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (reference : PrimitiveReferences.Reference
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonCenteredPerimeters.perimeterEntry entry inside parents)
      tolerance)
    (band : PreparedNewtonBandSamples.PreparedBandRequest differentialProfile target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ stage)
    (vertex : Fin ((((samples.traces.get position).get entry.sheet).left).vertices.rest.length + 1))
    (firstEq : ((samples.traces.get position).get entry.sheet).left.point
      (((samples.traces.get position).get entry.sheet).left.vertices.indexed 0) = start)
    (lastEq : ((samples.traces.get position).get entry.sheet).left.point
      (((samples.traces.get position).get entry.sheet).left.vertices.indexed vertex) = finish) :
    Data.Gaussian.Norm.Basic.normSq ((((samples.samples.get position).get entry.sheet).left.centered
      vertex).right) ≤
      3 * tolerance + 4 * (PreparedNewtonBandSamples.Sample.preparedDensity band.sample differentialProfile band.error *
        Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  exact NewtonTraceReferences.newton_left_centered_density_bound reference band firstInside lastInside side later
    (cache.normalize.atDomain position entry.sheet j)
    (fun column row point => (cache.normalize.atDomain position entry.sheet i).anchors.alignedValue
      (cache.normalize.atDomain position entry.sheet i).offsets column row point)
    ((samples.samples.get position).get entry.sheet) vertex firstEq lastEq

/-- The actual normalized right perimeter retains its coordinate-sensitive Newton bound. Both sheet selection and local
offset data come from the cache. -/
theorem newton_right_bound
    (samples : RequestedHoleCentering.CenteredPerimeters request cache i j)
    (reference : PrimitiveReferences.Reference
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonCenteredPerimeters.perimeterEntry entry inside parents)
      tolerance)
    (band : PreparedNewtonBandSamples.PreparedBandRequest differentialProfile target)
    (firstInside : band.sample.output.box.Contains start)
    (lastInside : band.sample.output.box.Contains finish)
    (side : PreparedBoundarySegments.SameSide band.sample.output.box start finish)
    (later : reference.budget.grid.index ≤ stage)
    (vertex : Fin ((((samples.traces.get position).get entry.sheet).right).vertices.rest.length + 1))
    (firstEq : ((samples.traces.get position).get entry.sheet).right.point
      (((samples.traces.get position).get entry.sheet).right.vertices.indexed 0) = start)
    (lastEq : ((samples.traces.get position).get entry.sheet).right.point
      (((samples.traces.get position).get entry.sheet).right.vertices.indexed vertex) = finish) :
    Data.Gaussian.Norm.Basic.normSq ((((samples.samples.get position).get entry.sheet).right.centered
      vertex).right) ≤
      3 * tolerance + 4 * (PreparedNewtonBandSamples.Sample.preparedDensity band.sample differentialProfile band.error *
        Data.Gaussian.Norm.Basic.normSq (finish - start)) := by
  exact NewtonTraceReferences.newton_right_centered_density_bound reference band firstInside lastInside side later
    (cache.normalize.atDomain position entry.sheet j)
    (fun column row point => (cache.normalize.atDomain position entry.sheet i).anchors.alignedValue
      (cache.normalize.atDomain position entry.sheet i).offsets column row point)
    ((samples.samples.get position).get entry.sheet) vertex firstEq lastEq

end CenteredPerimeters
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.NewtonCenteredPerimeters
