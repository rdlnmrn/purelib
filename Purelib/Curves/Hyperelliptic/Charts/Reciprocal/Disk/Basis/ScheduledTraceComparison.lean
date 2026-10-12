module
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

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
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Paths.PreparedNestedDyadicPaths
import Purelib.Riemann.Paths.PreparedWeightedRefinementTrace
import Purelib.Riemann.Periods.PeriodMatrix
import Purelib.Riemann.Readings.PreparedObservationCoercivity
public import Purelib.Riemann.Readings.PreparedWeightedRefinementArea
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledWeightedPaths
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Compare the retained prepared source trace with the actual weighted
refinement samples, paying both mesh resampling and model errors. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceComparison

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

/-- Two coefficient-weighted comparisons through the same original trace bound their endpoint difference by twice the
summed budgets. -/
private theorem comparison_triangle (first common last : Normalization.InverseRootPolynomial.Gaussian) {resampling model
  coefficient : Normalization.InverseRootPolynomial.Coordinate}
    (firstBound : Data.Gaussian.Norm.Basic.normSq (common - first) ≤ resampling * coefficient ^ 2)
    (lastBound : Data.Gaussian.Norm.Basic.normSq (common - last) ≤ model * coefficient ^ 2) :
    Data.Gaussian.Norm.Basic.normSq (first - last) ≤ 2 * (resampling + model) * coefficient ^ 2 := open
      Purelib.Data.Rat in by
  have bound := (Gaussian.Norm.Bounds.normSq_sub_le_two (common - last) (common - first)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Fraction.Order.Arithmetic.add_le_add_direct lastBound firstBound) (by
          decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2))
  rw [show common - last - (common - first) = first - last by ring1] at bound
  exact bound.trans_eq (by ring1)

/-- One homogeneous comparison on the exact retained source bank and actual
refinement; the schedule must still be selected to pay the displayed budget. -/
theorem prepared_source_scheduled_trace_bound {parents children : List
  (Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential)}
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
    (refinement : RootContinuation.PreparedSubedgeRootQueries.RootSubedgeRefinement parents children) {scheduled : Nat}
    (paths : Paths.PreparedNestedDyadicPaths.DyadicPaths scheduled refinement)
    (later :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceDepthMaximum
      anchors sources bank plans inputs readings prepared samples comparisons ≤ scheduled)
    (start : Normalization.InverseRootPolynomial.Gaussian) {distance originBound :
      Normalization.InverseRootPolynomial.Coordinate}
    (nonnegative : 0 ≤ distance) (movements : ∀ child ∈ children, child.edge.pointMovement ≤ distance)
    (origin : Data.Gaussian.Norm.Basic.normSq start ≤ originBound *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :
    let requests := Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests anchors
      sources bank plans inputs readings prepared samples comparisons
    let error := (genus : Normalization.InverseRootPolynomial.Coordinate) * FiniteSum.Fin.sumFin
      (Readings.PreparedWeightedRefinementArea.WeightedRefinement.errorBudget requests children distance)
    let sample := (parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * (genus :
      Normalization.InverseRootPolynomial.Coordinate) *
      FiniteSum.Fin.sumFin (fun row =>
        (Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum (sources.get row)))
    let pairs :=
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.sourceResamplingPairs
      scheduled anchors sources bank plans inputs readings prepared samples comparisons
    Data.Gaussian.Norm.Basic.normSq
      (Path.IncrementArea.traceArea start (pairs.map Prod.snd).flatten - Path.IncrementArea.traceArea start
        (children.map (fun child =>
        FiniteSum.Fin.sumFin (fun row => coefficients row *
          (Integration.PreparedEdgeRecasting.recastCenteredEdge (Periods.PeriodMatrix.standardDifferential row)
            child).model.integralSample)))) ≤
      2 * ((parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * Rational.Geometric.Basic.quarterRadius
        (4 *
        (WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
        anchors sources)^2) coverFloor +
        (64 * error * (sample + error) + 8 * originBound * error)) *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ^ 2 := by
  let weighted := Readings.PreparedWeightedRefinementArea.WeightedRefinement.build
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests anchors sources bank
      plans inputs readings prepared samples comparisons) refinement
  have originScalar := origin
  rw [Gaussian.Norm.Basic.normSq_eq_canonical] at originScalar
  have model := Paths.PreparedWeightedRefinementTrace.trace_bound weighted paths (fun row =>
    (Hyperelliptic.Charts.Reciprocal.ReciprocalSideArea.ParentCovers.sourceSlopeMaximum (sources.get row)))
    (fun row => Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledRequests.Samples.scheduledRowRequests_slope anchors
      sources bank plans inputs readings prepared samples comparisons row le_rfl)
    coefficients start (originBound := originBound) nonnegative movements originScalar
  rw [Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledWeightedPaths.Samples.scheduledWeightedSource_path anchors
    sources bank plans inputs readings prepared samples comparisons refinement paths weighted,
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledWeightedPaths.Samples.weightedSample_path] at model
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical] at model
  exact Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceComparison.Samples.comparison_triangle _ _ _

      (WeightedResampling.BasisCommonParentBank.Samples.source_trace_resampling_bound
      anchors sources bank plans inputs readings prepared samples comparisons scheduled later start) model

end Samples
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.ScheduledTraceComparison
