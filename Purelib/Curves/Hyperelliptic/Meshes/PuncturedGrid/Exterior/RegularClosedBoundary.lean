module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.Paths.PreparedPathGluing
import Purelib.Riemann.RootContinuation.PreparedCachedParentRoots
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.Readings.PrimitiveAreaBounds

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.PairedIncrementArea
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedClosedBoundary
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonRibbonOrigins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentCharts
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalPrimitives
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedDyadicRefinements
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Normalization.OwnerSeededInverseRoot
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.Readings.PreparedControlledPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Polygon.Stokes
import Purelib.Tactic.Ring

public section

/-! Acquire the requested regular reciprocal boundary comparison for the
actual closed exterior program, preserving its source covers and cap owners. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation

open Purelib.Curves
open Purelib.Data
open Purelib
open Purelib.Integration
open Purelib.Riemann
open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate Gaussian)
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

open Purelib.Riemann.Normalization

open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)

open Purelib.Data.Rat.Fraction.Compatibility

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} (prepared :
    ExteriorProgram.SurfacePreparation
    regular domains program)

/-- Keep the actual exterior program's parent cache and first-differential
covers as the owner of the regular source comparison. -/
@[expose] def
  regularSourceRequest
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (error : Coordinate) (positive : 0 < error) (minimum : Nat) :
    Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request regular other program.cache.parents error minimum
      :=
  Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.Request.build regular other prepared.sourceCovers right
    program.cache.proper error positive minimum

/-- The regular parent bank chosen for this literal exterior program. -/
@[expose] def
  regularClosedBoundaryRequest
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (error : Coordinate) (positive : 0 < error) (minimum : Nat) :
    Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest
      (prepared.regularSourceRequest other right error positive minimum) (min (error / 64) 1) :=
  open Purelib.Data.Rat in Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest.build
    (prepared.regularSourceRequest other right error positive minimum) (min (error / 64) 1)
    (Fraction.Order.Basic.lt_min (Fraction.Order.Field.div_pos_direct positive (by decide +kernel)) (by decide))

/-- The even-degree exterior program supplies its own closed chain. The
computed shared bank pays the corrected source-area request with no caller
geometric depth, chart-arc budget or fan certificate. -/
theorem
  regular_closed_boundary_accurate
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (error : Coordinate) (positive : 0 < error) (minimum : Nat)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) :
    let selected := prepared.regularClosedBoundaryRequest other right error positive minimum
    let evaluated := selected.request.acquire
    Data.Gaussian.Norm.Basic.normSq (evaluated.sourceArea - evaluated.correction) < error := by
  exact Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest.source_closed_requested
    (prepared.regularSourceRequest other right error positive minimum) error positive unramified
    (by obtain ⟨chain⟩ := program.cache.chain; exact ⟨chain.toDirectPathChain⟩) rfl

section
open Purelib.Approximation
/-- The exterior program's actual root return bounds the literal raw source
total on the same bank as the corrected area estimate. -/
theorem
  regular_source_total_accurate
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (error : Coordinate) (positive : 0 < error) (minimum : Nat)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) :
    let selected := prepared.regularClosedBoundaryRequest other right error positive minimum
    let evaluated := selected.request.acquire
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total evaluated.sourcePaths.flatten)
      error := by
  exact Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest.source_total_requested
    (prepared.regularSourceRequest other right error positive minimum) error positive unramified
    (by obtain ⟨chain⟩ := program.cache.chain; exact ⟨chain.toDirectPathChain⟩)
      (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain program.cache) rfl (by
      change Gaussian.Equivalence.NamedEquivalent
        (Paths.OwnerTraceReadings.ownerName (Paths.PreparedPathGluing.finishOwner
          program.period.closed.traced.prepared))
        (Paths.OwnerTraceReadings.ownerName ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorOwner
          lifted program.sheet)))
      rw [← program.period.closed.traced.finishOwner_eq]
      exact program.period.closed.rootReturn)

/-- Bound the full raw source area on the literal exterior program, using
the same selected samples as its raw total and corrected area bounds. -/
theorem
  regular_source_area_accurate
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (error : Coordinate) (positive : 0 < error) (minimum : Nat)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) :
    let selected := prepared.regularClosedBoundaryRequest other right error positive minimum
    let evaluated := selected.request.acquire
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area evaluated.sourcePaths.flatten) < error := by
  exact Hyperelliptic.Charts.Reciprocal.ReciprocalRegularParentRequest.RegularParentRequest.source_area_requested
    (prepared.regularSourceRequest other right error positive minimum) error positive unramified
    (by obtain ⟨chain⟩ := program.cache.chain; exact ⟨chain.toDirectPathChain⟩)
      (RootContinuation.PreparedCachedParentRoots.ParentCache.rootChain program.cache) rfl (by
      change Gaussian.Equivalence.NamedEquivalent
        (Paths.OwnerTraceReadings.ownerName (Paths.PreparedPathGluing.finishOwner
          program.period.closed.traced.prepared))
        (Paths.OwnerTraceReadings.ownerName ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.exteriorOwner
          lifted program.sheet)))
      rw [← program.period.closed.traced.finishOwner_eq]
      exact program.period.closed.rootReturn)

end

/-- Retain the actual regular exterior source samples and reference depths as a closed source comparison.

For an unramified reciprocal origin, the original program's root return pays both complete raw source area and component
totals. -/
@[expose] def
  regularSourceComparison
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (requested : Coordinate) (positive : 0 < requested) (minimum : Nat)
    (unramified : Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder curve = 0) :
    prepared.ClosedBoundaryComparison other requested minimum := open Purelib.Data.Rat in by
  let localTarget := requested / 128
  have localPositive : 0 < localTarget := Fraction.Order.Field.div_pos_direct positive (by decide +kernel)
  let selected := prepared.regularClosedBoundaryRequest other right localTarget localPositive minimum
  let evaluated := selected.request.acquire
  let controlled := Hyperelliptic.Charts.Reciprocal.Disk.ChartSourceRequests.controlledEntries evaluated
  let entries : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison.SourceReferenceEntries
    (prepared.regularSourceRequest other right localTarget localPositive minimum) :=
    Data.Vector.DependentVector.ofFn (fun i =>
      ⟨selected.request.index, (evaluated.entries.get i).samples.source, (evaluated.entries.get i).samples.otherSource,
        (controlled.get i).first, (controlled.get i).second, (controlled.get i).first_eq, (controlled.get i).second_eq,
        (prepared.regularSourceRequest other right localTarget localPositive minimum).depth + selected.depth,
        selected.referenceError, (selected.source_reference_rate i).le⟩)
  have paths : Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison.sourceReferencePaths entries =
    evaluated.sourcePaths := by
    apply Data.List.OfFn.Basic.ofFn_congr
    intro i
    dsimp only [Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison.sourceReferencePaths, entries, -eq_self,
      -iff_self]
    rw [Data.Vector.DependentVector.ofFn_get]
  let path := Path.PairedIncrementArea.Summary.build
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SourceComparison.sourceReferencePaths entries).flatten
  have localLe : localTarget ≤ requested := by
    apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Coordinate) < 128)).mpr
    exact (show requested = requested * 1 by ring1).le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) positive.le)
  have shareLe : min (localTarget / 64) 1 ≤ localTarget := by
    apply (Fraction.Order.Basic.min_le_left _ _).trans
    apply (Fraction.Order.Field.div_le_iff_pos (by decide +kernel : (0 : Coordinate) < 64)).mpr
    exact (show localTarget = localTarget * 1 by ring1).le.trans
      (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (by decide +kernel) localPositive.le)
  have paid : ((prepared.regularSourceRequest other right localTarget localPositive minimum).plans.length : Coordinate)
    *
      (((prepared.regularSourceRequest other right localTarget localPositive minimum).plans.length : Coordinate) *
        selected.referenceError) < localTarget :=
    (by ring1 : ((prepared.regularSourceRequest other right localTarget localPositive minimum).plans.length :
      Coordinate) *
      (((prepared.regularSourceRequest other right localTarget localPositive minimum).plans.length : Coordinate) *
        selected.referenceError) =
      ((prepared.regularSourceRequest other right localTarget localPositive minimum).plans.length : Coordinate)^2 *
        selected.referenceError).trans_lt
        (selected.reference_paid.trans_le shareLe)
  refine ⟨prepared.regularSourceRequest other right localTarget localPositive minimum, rfl, entries,
    selected.referenceError, selected.reference_positive, ?_, paid, path, ?_, ?_⟩
  · intro i
    dsimp only [entries, -eq_self, -iff_self]
    rw [Data.Vector.DependentVector.ofFn_get]
  · rw [path.area_eq, paths]
    exact (prepared.regular_source_area_accurate other right localTarget localPositive minimum unramified).trans_le
      localLe
  · rw [path.total_eq, paths]
    have bounded := prepared.regular_source_total_accurate other right localTarget localPositive minimum unramified
    exact ⟨bounded.1.trans localLe, bounded.2.trans localLe⟩

/-- Both displayed degree shapes construct the same physical-source
interface, retaining their actual source owners and reference depths. -/
@[expose] def
  closedBoundaryComparison
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (requested : Coordinate) (positive : 0 < requested) (minimum : Nat) :
    prepared.ClosedBoundaryComparison other requested minimum :=
  match shape : curve.degreeShape with
  | .odd _ => (prepared.oddClosedBoundaryComparison other right requested positive minimum
      (by
        simp only [Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder,
          shape, -eq_self, -iff_self]; rfl)).toSourceComparison prepared
  | .even _ => prepared.regularSourceComparison other right requested positive minimum
      (by
        simp only [Hyperelliptic.Charts.Reciprocal.HyperellipticReciprocal.originOrder,
          shape, -eq_self, -iff_self]; rfl)

/-- The parity-independent closed comparison retains exactly the supplied second source covers. -/
theorem
  closedBoundaryComparison_right
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (requested : Coordinate) (positive : 0 < requested) (minimum : Nat) :
    (prepared.closedBoundaryComparison other right requested positive minimum).original.right = right := by
  unfold
    closedBoundaryComparison
  split <;> rfl

/-- The parity-independent closed comparison retains the maximum of the two original source-cover slopes. -/
theorem
  closedBoundaryComparison_slope
  (other : Hyperelliptic.Differentials.Basic.Differential genus)
    (right : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers
      (program.cache.parents.map (recastCenteredEdge other)))
    (requested : Coordinate) (positive : 0 < requested) (minimum : Nat) :
    (prepared.closedBoundaryComparison other right requested positive minimum).original.slope =
      max (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum prepared.sourceCovers)
        (Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest.sourceMaximum right) := by
  unfold
    closedBoundaryComparison
  split <;> rfl

end SurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
