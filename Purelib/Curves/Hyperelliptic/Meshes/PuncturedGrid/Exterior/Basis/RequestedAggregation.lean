module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceAssembly
public import Purelib.Integration.Budget.Path.Aggregation
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonArcRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonDepthRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-! Pay the occurrence and component comparisons with explicit homogeneous requests. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedAggregation

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared}
  {basis : Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : Normalization.InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

open Purelib.Integration.Budget.Path.Aggregation (aggregationTolerance aggregationTolerance_positive
  aggregationTolerance_area_scaled aggregationTolerance_total_scaled)

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)

/-- A single positive local tolerance pays the complete occurrence area,
including its joining polygon, for every coefficient vector. -/
theorem occurrence_area_requested (outer : Fin prepared.occurrences.length)
    (physical : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length → List Topology.Polygon.Stokes.PrimitivePoint)
    {bound requested : Normalization.InverseRootPolynomial.Coordinate} (boundNN : 0 ≤ bound) (positive : 0 < requested)
    (areas : ∀ position, Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (physical position) -
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
      comparisons outer position).weighted.source.area) ≤
      Budget.Path.Aggregation.aggregationTolerance
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length bound requested *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2)
    (errors : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (physical
      position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
        sample comparisons outer position).weighted.source.total)))
        (Budget.Path.Aggregation.aggregationTolerance
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length bound requested *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))
    (leftBound : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total
      (physical position)) (bound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))
    (rightBound : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.ConjugatePathReadback.conjugateDiagonal
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
      sample comparisons outer position).weighted.source.total))
      (bound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (List.ofFn physical).flatten -
      sample.occurrenceSourceArea comparisons outer) ≤ requested *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := open Data.Rat in by
  have estimate :=
    Connection.CommonBasisRequest.Sampled.occurrence_physical_source_area_bound
    sample comparisons outer physical
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Budget.Path.Aggregation.aggregationTolerance_positive _ boundNN
      positive).le (Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))))
    (Fraction.Order.Arithmetic.mul_nonneg_direct boundNN (Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun
      row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))) areas errors leftBound rightBound
  exact estimate.trans (Budget.Path.Aggregation.aggregationTolerance_area_scaled _ boundNN positive
    (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))

/-- A single positive local tolerance pays the complete component area,
including its joining polygon, for every coefficient vector. -/
theorem component_area_requested (periodStage : Nat)
    (physical : Fin prepared.occurrences.length → List Topology.Polygon.Stokes.PrimitivePoint)
    {bound requested : Normalization.InverseRootPolynomial.Coordinate} (boundNN : 0 ≤ bound) (positive : 0 < requested)
    (areas : ∀ position, Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (physical position) -
      sample.occurrenceSourceArea comparisons position) ≤
      Budget.Path.Aggregation.aggregationTolerance prepared.occurrences.length bound requested *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) ^ 2)
    (errors : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (physical
      position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal (sample.occurrenceSourceTotal comparisons position)))
        (Budget.Path.Aggregation.aggregationTolerance prepared.occurrences.length bound requested *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))
    (leftBound : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total
      (physical position)) (bound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))
    (rightBound : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.ConjugatePathReadback.conjugateDiagonal (sample.occurrenceSourceTotal comparisons position))
      (bound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (List.ofFn physical).flatten -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
      comparisons periodStage) ≤ requested * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2
      := open Data.Rat in by
  have estimate :=
    OccurrenceAssembly.CommonBasisRequest.Sampled.occurrences_source_area_bound
    sample comparisons periodStage physical
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Budget.Path.Aggregation.aggregationTolerance_positive _ boundNN
      positive).le (Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row))))
    (Fraction.Order.Arithmetic.mul_nonneg_direct boundNN (Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun
      row => Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))) areas errors leftBound rightBound
  exact estimate.trans (Budget.Path.Aggregation.aggregationTolerance_area_scaled _ boundNN positive
    (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))

/-- Paying an occurrence's area tolerance also supplies the endpoint
accuracy required by the next assembly level. -/
theorem occurrence_total_requested (outer : Fin prepared.occurrences.length)
    (physical : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length → List Topology.Polygon.Stokes.PrimitivePoint)
    {bound requested : Normalization.InverseRootPolynomial.Coordinate} (boundNN : 0 ≤ bound) (positive : 0 < requested)
    (errors : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (physical
      position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
        sample comparisons outer position).weighted.source.total))
        (Budget.Path.Aggregation.aggregationTolerance
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length
          bound requested * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (List.ofFn
      physical).flatten).sub
      (Path.ConjugatePathReadback.conjugateDiagonal (sample.occurrenceSourceTotal comparisons outer)))
        (requested * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := open Data.Rat in by
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled.occurrence_total_error
    sample comparisons outer physical
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Budget.Path.Aggregation.aggregationTolerance_positive _ boundNN
      positive).le (Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))) errors
  have paid := Budget.Path.Aggregation.aggregationTolerance_total_scaled
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length
    boundNN positive (Algebra.FiniteSum.Rational.Order.weight_sum_nonnegative _ (fun row =>
      Data.Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  exact ⟨estimate.1.trans paid, estimate.2.trans paid⟩

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedAggregation
