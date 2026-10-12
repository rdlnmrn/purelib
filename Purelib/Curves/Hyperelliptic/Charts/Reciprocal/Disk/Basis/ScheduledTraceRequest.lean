module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.AffineTriangle

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Integration.PreparedWeightedCoefficientBudget
import Purelib.Riemann.Integration.PreparedWeightedScheduleBudgets
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedScheduledPrimitivePaths
import Purelib.Riemann.Paths.PreparedWeightedTraceAllocation
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.Topology.PreparedRootSafeCycleStates
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceComparison
public import Purelib.Riemann.Paths.PreparedWeightedTraceStage
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSwitchedRefinements
import Purelib.Riemann.Readings.PreparedPrimitiveChargeBounds
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Requested trace accuracy on the retained common-parent bank. The cover
floor and coefficient tolerance are fixed before acquisition; the original
schedule stage is then selected internally from the acquired depth and budgets. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {bounds :
    Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential} {patch :
    Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent}
  {data : Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor : Nat}
  {index minimum readingIndex : Nat} {box : Rational.Box}
  {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

variable {stage energyFloor radialDepth : Nat} {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector
  genus}

namespace Samples

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility

/-- The original parent-count and genus-weighted sum of retained source slope bounds. -/
@[expose] def traceSourceBound {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve
  differential)}
    (sources : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) : Coordinate
      :=
  (parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * (genus :
    Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin (fun row =>
    Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum (sources.get row))

/-- The original squared parent count times the fourfold squared common weighted source slope. -/
@[expose] def traceResamplingScale {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve
  differential)}
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents) : Coordinate :=
  (parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * (4 *
    (WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
    anchors sources)^2)

/-- Compute the complete trace allocation from original covers and the
chosen origin ceiling, before any source polynomial acquisition. -/
@[expose] def traceAllocation {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve
  differential)}
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents)
    (target originBound : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < target) (originNonnegative : 0
      ≤ originBound) :
    Paths.PreparedWeightedTraceAllocation.WeightedTraceAllocation target
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceSourceBound sources) originBound
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceResamplingScale anchors sources) :=
  open Purelib.Data.Rat in Paths.PreparedWeightedTraceAllocation.WeightedTraceAllocation.build _ _ _ _ positive
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.sq_nonneg_direct _) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le genus)))
      (FiniteSum.Fin.sumFin_zero.symm.trans_le
        (FiniteSum.Rational.Order.Positivity.sumFin_mono _ _ (fun row =>
          Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum_nonnegative (sources.get
          row)))))
    originNonnegative
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.sq_nonneg_direct _)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤
      4) (Fraction.Order.Arithmetic.sq_nonneg_direct _)))

/-- The original source-depth maximum is zero when the retained parent bank is empty. -/
theorem depth_nil {parents : List (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
    (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers parents) (sources :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers parents)
    (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
      allowance coefficientTarget coverFloor floor)
    (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
      sources bank) (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
      sources)
    (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
      stage)
    (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors
      sources bank plans inputs readings)
    (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
      sources bank plans inputs readings prepared)
    (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
      sources bank plans inputs readings prepared samples)
    (empty : parents = []) :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceDepthMaximum
      anchors sources bank plans inputs readings prepared samples comparisons = 0 := by
  subst parents
  cases anchors
  rfl

namespace TraceRequest

variable {root : Topology.PreparedRefinementRootChains.Named} {target originBound :
  Normalization.InverseRootPolynomial.Coordinate}
  (initial : Topology.PreparedRootSafeCycleStates.PreparedRefinementRootEndpoints.RootClosedState curve differential
    root) (targets : List (Hyperelliptic.Differentials.Basic.Differential genus))
  (anchors : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.ParentCovers initial.state.parents) (sources :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisParentSourceCovers initial.state.parents)
  (allocation : Paths.PreparedWeightedTraceAllocation.WeightedTraceAllocation target
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceSourceBound sources)
    originBound
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceResamplingScale
    anchors sources))
  (bank : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank.BasisCommonParentBank anchors sources basis
    allowance coefficientTarget coverFloor floor)
  (plans : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Plans capSample polynomials minimum anchors
    sources bank) (inputs : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.NumericalBank index anchors
    sources)
  (readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings anchors sources bank plans inputs
    stage)
  (prepared : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.FanPreparations energyFloor anchors sources
    bank plans inputs readings)
  (samples : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentSamples.Samples coefficients radialDepth anchors
    sources bank plans inputs readings prepared)
  (comparisons : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPreparedBank.Samples.PreparedComparisons anchors
    sources bank plans inputs readings prepared samples)
  (coefficientNonnegative : 0 ≤ coefficientTarget)
  (coefficientLe : coefficientTarget ≤ Integration.PreparedWeightedCoefficientBudget.coefficientTolerance initial
    allocation.half)
  (members : ∀ row : Fin genus, Periods.PeriodMatrix.standardDifferential row ∈ targets)
  (oriented : ∀ parent ∈ initial.state.parents,
    0 < Energy.AffineTriangle.crossEnergy (parent.edge.point 0) (parent.edge.point 1))

/-- Cache the row budgets attached to these very acquired source requests. -/
@[expose] def budgets := Integration.PreparedWeightedScheduleBudgets.ScheduleBudgets.build initial targets
  (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests anchors sources bank plans
    inputs readings prepared samples comparisons)

/-- The selection is total, including an empty original bank, and contains
both the spatial-depth and model-error certificates for one original stage. -/
@[expose] def select : Paths.PreparedWeightedTraceStage.WeightedTraceStage
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.TraceRequest.budgets initial targets
      anchors sources bank plans inputs readings prepared samples comparisons)
    allocation
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceDepthMaximum
      anchors sources bank plans inputs readings prepared samples comparisons) := by
  apply Paths.PreparedWeightedTraceStage.WeightedTraceStage.build _ allocation members
    (fun row => (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests_coefficient
      coefficientNonnegative
      anchors sources bank plans inputs readings prepared samples comparisons row).trans coefficientLe)
    oriented
  intro empty
  exact Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.depth_nil anchors sources bank plans
    inputs readings prepared samples comparisons empty

open Purelib.Approximation in
open Purelib.Data.Rat in
/-- The selected original stage pays the requested homogeneous error on the
literal cached prepared source trace and actual weighted period children. -/
theorem accurate (coverLater : allocation.coverFloor ≤ coverFloor) (start :
  Normalization.InverseRootPolynomial.Gaussian)
    (origin : Data.Gaussian.Norm.Basic.normSq start ≤ originBound *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
    (predecessor : Nat)
    (later : (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.TraceRequest.select initial
      targets anchors sources allocation bank plans inputs readings prepared samples comparisons
      coefficientNonnegative coefficientLe members oriented).predecessor ≤ predecessor) :
    let current := initial.states targets (predecessor + 1)
    let pairs :=
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceResamplingPairs
      (Paths.PreparedScheduledPrimitivePaths.RootClosedState.spatialDepth initial targets (predecessor + 1))
      anchors sources bank plans inputs readings prepared samples comparisons
    Data.Gaussian.Norm.Basic.normSq (Path.IncrementArea.traceArea start (pairs.map Prod.snd).flatten -
      Path.IncrementArea.traceArea start (current.state.parents.map (fun child =>
      FiniteSum.Fin.sumFin (fun row => coefficients row *
        (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential row)
          child).model.integralSample)))) ≤
      target * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
  let selected := Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.TraceRequest.select initial
    targets anchors sources allocation bank plans inputs readings prepared samples comparisons coefficientNonnegative
    coefficientLe members oriented
  have radiusNonnegative := Rational.Geometric.Basic.quarterRadius_nonneg
    (initial.state.scheduleBase_positive targets).le (predecessor + 1)
  have bound :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceComparison.Samples.prepared_source_scheduled_trace_bound
    anchors sources bank plans inputs readings prepared samples comparisons
    (initial.statesSubedges targets (predecessor + 1))
    (Paths.PreparedScheduledPrimitivePaths.RootClosedState.states_dyadicPaths initial targets (predecessor + 1))
      (selected.depth_enough predecessor later) start radiusNonnegative
    (fun child member => Integration.PreparedRefinementMovement.RootClosedState.states_childMovement_le initial targets
      predecessor member) origin
  have resampling : (initial.state.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
      Rational.Geometric.Basic.quarterRadius (4 *
        (WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
        anchors sources)^2) coverFloor =
      Rational.Geometric.Basic.quarterRadius
        (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceResamplingScale anchors sources)
        coverFloor := by
    rw [Rational.Geometric.Basic.quarterRadius_eq_mul_pow, Rational.Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest.Samples.traceResamplingScale
    ring1
  rw [resampling] at bound
  exact bound.trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct (selected.paid predecessor later
    coverLater) (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end TraceRequest
end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceRequest
