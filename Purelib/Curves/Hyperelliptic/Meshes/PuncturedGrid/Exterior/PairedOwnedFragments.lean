module
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.NoisyPathArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Periods.CenteredBilinearPath
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Riemann.Readings.RectangularPointReadings
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest
import Purelib.Integration.Path.OwnedPathComparison
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedPreparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Entries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.InverseModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Geometry.Rectangle.Partition.PreparedAxisPartitions
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Branches.RectangularSheetGauge
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.RectangularRefinementSigns
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Meshes.RectangularFaceModels
import Purelib.Riemann.Normalization.RectangularInverseModels
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Paths.RectangularSegmentSplitting
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

public section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

/-! Complete fragment areas with the fine trace's actual point owners.
Owner changes are paid by an automatically selected grid request, including
at repeated coordinates. The cached source samples remain unchanged. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (PrimitivePoint)

open Purelib.Data.Rat.Fraction.Compatibility
variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential} {target : Normalization.InverseRootPolynomial.Coordinate} {minimum stage fine : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {plan : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan occurrence other target
    minimum}

/-- The actual first-differential point-owner readings at the selected original parent parameters. -/
@[expose] def FirstReadings (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) {index count : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (parameters :
      Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate) :=
  Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => entry.plan.parent.edge.point
    (parameters vertex))

/-- The actual recast second-differential point-owner readings at those same parameters. -/
@[expose] def SecondReadings (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine) {index count : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index)
      (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate) :=
  Readings.RectangularPointReadings.PointReadings data.anchors data.offsets (fun vertex => entry.plan.parent.edge.point
    (parameters vertex))

/-- Pair the two retained original point-owner values at one shared sample index. -/
@[expose] def ownedValues {entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan
  sample otherSample fine} {index count : Nat}
    {data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index} {otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index}
    {parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate}
    (first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.FirstReadings entry data parameters)
      (second : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.SecondReadings entry otherData
      parameters)
    (vertex : Fin (count + 1)) : PrimitivePoint := ⟨first.values vertex, second.values vertex⟩

/-- Bound the original owned increment error against both retained source increments.

The paid common owner stage and same-fragment query density retain the actual start and finish observations. -/
theorem owned_fragment_increment_error (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) {index count : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    {tolerance : Normalization.InverseRootPolynomial.Coordinate} (owners :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other tolerance) (later :
      owners.index ≤ index)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.FirstReadings entry data parameters)
      (second : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.SecondReadings entry otherData
      parameters)
    (start finish : Fin (count + 1)) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second finish).sub
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second start)).sub
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters finish)).sub
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters start))))
      (2 * (tolerance + Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.queryDensity entry piece index
        * Data.Gaussian.Norm.Basic.normSq
        (entry.plan.parent.edge.point (parameters finish) - entry.plan.parent.edge.point (parameters start)))) := open
          Purelib.Data.Rat in by
  have ownerError := Path.OwnedPathComparison.increment_difference
    (first := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second)
    (second := fun vertex => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece
      data otherData (parameters vertex))
    (fun vertex => ⟨by simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues,
        Topology.Polygon.Stokes.PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        (owners.first_bound later data first vertex piece.column piece.row
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside
            vertex))),
      by simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues,
        Topology.Polygon.Stokes.PrimitivePoint.sub,
        Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
        (owners.second_bound later otherData second vertex piece.column piece.row
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside
            vertex)))⟩) start finish
  have queryError := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.paired_query_error evaluated entry
    member piece data otherData
    (parameters start) (parameters finish) (inside start) (inside finish)
  have scalar {a b c : Normalization.InverseRootPolynomial.Gaussian} {error :
    Normalization.InverseRootPolynomial.Coordinate}
      (owned : Gaussian.Basic.Canonical.normSq (a - b) ≤ tolerance) (source : Gaussian.Basic.Canonical.normSq (b - c) ≤
        error) :
      Gaussian.Basic.Canonical.normSq (a - c) ≤ 2 * (tolerance + error) := by
    rw [show a - c = (a - b) + (b - c) by ring1]
    have estimate := Gaussian.Norm.Bounds.normSq_add_le_two (a - b) (b - c)
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] at estimate
    exact estimate.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct owned source) (by decide))
  exact ⟨scalar ownerError.1 queryError.1, scalar ownerError.2 queryError.2⟩

/-- Bound the complete owned fragment area against its original cached source sample.

The retained length budget pays point-owner changes, while the same monotone fragment parameters pay the full
grid-to-source area error without a vertex-count factor. -/
theorem owned_fragment_area_bound (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedSourceReferences.PairedSourcePlan.ParentEvaluation plan sample
  otherSample fine)
    (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.SourceEntry plan sample otherSample fine)
      (member : entry ∈ evaluated.retained)
    (piece : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentQueries.Fragment entry) {index count : Nat}
    (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.FirstData occurrence index) (otherData :
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.SecondData occurrence other index)
    (parameters : Fin (count + 1) → Normalization.InverseRootPolynomial.Coordinate)
    (inside : ∀ vertex, piece.interval.lower ≤ parameters vertex ∧ parameters vertex ≤ piece.interval.upper)
    (forward : Bool)
    (ordered : ∀ edge : Fin count, if forward then parameters edge.castSucc ≤ parameters edge.succ
      else parameters edge.succ ≤ parameters edge.castSucc)
    {allowance : Normalization.InverseRootPolynomial.Coordinate} (budget : Path.NoisyPathArea.LengthErrorBudget count
      allowance)
    (owners : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnerRequest.OwnerRequest occurrence other
      budget.tolerance) (later : owners.index ≤ index)
    (first : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.FirstReadings entry data parameters)
      (second : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.SecondReadings entry otherData
      parameters)
    (owned : Periods.CenteredBilinearPath.Sample
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second))
    (source : Periods.CenteredBilinearPath.Sample (fun vertex =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.sourceValues entry (parameters vertex))) :
    Data.Gaussian.Norm.Basic.normSq (owned.centeredArea - source.centeredArea) ≤
      2 * (40 * budget.tolerance * (4 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity
        entry piece index + 3) *
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0) (parameters
          (Fin.last count)) + allowance)^2 +
        40 * Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceError entry piece index *
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece index *
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward (parameters 0)
            (parameters (Fin.last count)))^2) := open Purelib.Data.Rat in by
  let fixed := Periods.CenteredBilinearPath.Sample.build (fun vertex =>
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData (parameters
    vertex))
  have densityNonnegative : 0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.traceDensity entry piece
    index :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.queryDensity_nonnegative entry piece index)
        (Gaussian.Norm.Basic.normSq_nonneg (entry.plan.parent.edge.point 1 - entry.plan.parent.edge.point 0)))
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.sourceDensity_nonnegative entry))
  have ownerError := Path.OwnedPathComparison.LengthErrorBudget.reading_comparison budget owned fixed
    (fun edge : Fin count => Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep forward
      (parameters edge.castSucc) (parameters edge.succ))
    densityNonnegative (fun edge =>
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_nonnegative forward _ _ (ordered
      edge))
    (fun vertex => show Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues first second vertex).sub
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues entry piece data otherData
        (parameters vertex))) (budget.tolerance / 4) from
      ⟨by simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues,
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues,
          Topology.Polygon.Stokes.PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
          (owners.first_bound later data first vertex piece.column piece.row
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside
            vertex))),
        by simpa only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments.ownedValues,
          Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentValues.gridValues,
          Topology.Polygon.Stokes.PrimitivePoint.sub,
          Gaussian.Norm.Basic.normSq_eq_canonical, -eq_self, -iff_self] using
          (owners.second_bound later otherData second vertex piece.column piece.row
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_contains entry piece _ (inside
            vertex)))⟩)
    (fun edge => by
      rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterStep_sq]
      exact Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.grid_increment_bound evaluated entry member
        piece data otherData _ _ (inside edge.castSucc) (inside edge.succ))
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.parameterSteps_total] at ownerError
  have sourceError := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentArea.fragment_area_bound evaluated entry
    member piece data otherData parameters inside forward ordered fixed source
  have identity : owned.centeredArea - source.centeredArea =
      (owned.centeredArea - fixed.centeredArea) + (fixed.centeredArea - source.centeredArea) := by ring1
  rw [identity]
  exact (Gaussian.Norm.Bounds.normSq_add_le_two _ _).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct ownerError sourceError) (by decide))

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedOwnedFragments
