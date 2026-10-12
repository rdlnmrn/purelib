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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Budget.Path.Aggregation
public import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedAggregation
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
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib.Riemann

public section

/-! Compute the two-level parent/occurrence request before taking physical samples. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

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

/-- A finite maximum pays every occurrence's squared-count magnitude loss. -/
@[expose] def componentMagnitude (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program) (parentBound : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum (fun occurrence :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
    regular domains differential =>
    (occurrence.compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2)
      prepared.occurrences * parentBound

/-- The geometry-based component magnitude is nonnegative whenever the parent magnitude is nonnegative. -/
theorem componentMagnitude_nonnegative {parentBound : Normalization.InverseRootPolynomial.Coordinate} (boundNN : 0 ≤
  parentBound) :
    0 ≤
      componentMagnitude
      prepared parentBound :=
  open Data.Rat in Fraction.Order.Arithmetic.mul_nonneg_direct
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _) boundNN

/-- The squared parent-count loss of each retained occurrence is bounded by the common component magnitude. -/
theorem occurrenceMagnitude_le (outer : Fin prepared.occurrences.length)
    {parentBound : Normalization.InverseRootPolynomial.Coordinate} (boundNN : 0 ≤ parentBound) :
    ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * parentBound ≤

        componentMagnitude
        prepared parentBound :=
  open Data.Rat in Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.le_maximum _ (List.getElem_mem outer.isLt))
    boundNN

/-- Target for each occurrence, followed by the target for each of its parents.
Both depend only on the retained geometry, a magnitude bound and the request. -/
@[expose] def occurrenceTarget (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program) (parentBound requested : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  Budget.Path.Aggregation.aggregationTolerance prepared.occurrences.length
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
    prepared parentBound) requested

/-- Compute the parentwise tolerance that pays the requested occurrence tolerance at its original parent count. -/
@[expose] def parentTarget (prepared :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
  regular domains program) (outer : Fin prepared.occurrences.length)
    (parentBound requested : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  Budget.Path.Aggregation.aggregationTolerance
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length
    parentBound
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.occurrenceTarget
      prepared parentBound requested)

/-- A positive component request and nonnegative parent magnitude give a positive occurrence tolerance. -/
theorem occurrenceTarget_positive {parentBound requested : Normalization.InverseRootPolynomial.Coordinate}
    (boundNN : 0 ≤ parentBound) (positive : 0 < requested) :
    0 <
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.occurrenceTarget
      prepared parentBound requested :=
  Budget.Path.Aggregation.aggregationTolerance_positive _
    (componentMagnitude_nonnegative
    boundNN) positive

/-- The two-level request assigns a positive tolerance to every original occurrence parent. -/
theorem parentTarget_positive (outer : Fin prepared.occurrences.length) {parentBound requested :
  Normalization.InverseRootPolynomial.Coordinate}
    (boundNN : 0 ≤ parentBound) (positive : 0 < requested) :
    0 < Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
      prepared outer parentBound requested :=
  Budget.Path.Aggregation.aggregationTolerance_positive _ boundNN
    (occurrenceTarget_positive
    boundNN positive)

/-- Each computed parent tolerance is capped by one. -/
theorem parentTarget_le_one (outer : Fin prepared.occurrences.length) (parentBound requested :
  Normalization.InverseRootPolynomial.Coordinate) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
      prepared outer parentBound requested ≤ 1 :=
  Budget.Path.Aggregation.aggregationTolerance_le_one ..

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)

/-- Instantiate this with the source-ordered physical runs. The computed parent
target pays internal areas, cross-parent joins, and cross-occurrence joins. -/
theorem hierarchical_area_requested (periodStage : Nat)
    (physical : (outer : Fin prepared.occurrences.length) →
      Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length → List Topology.Polygon.Stokes.PrimitivePoint)
    {parentBound requested : Normalization.InverseRootPolynomial.Coordinate} (boundNN : 0 ≤ parentBound) (positive : 0 <
      requested)
    (areas : ∀ outer position, Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (physical outer
      position) -
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer position).weighted.source.area) ≤
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
          prepared outer parentBound requested * (Readings.PreparedObservationCoercivity.coefficientNormSq
          coefficients) ^ 2)
    (errors : ∀ outer position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total
      (physical outer position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
        sample comparisons outer position).weighted.source.total))
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
          prepared outer parentBound requested * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))
    (leftBound : ∀ outer position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total
      (physical outer position))
      (parentBound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients))
    (rightBound : ∀ outer position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.ConjugatePathReadback.conjugateDiagonal
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer position).weighted.source.total)
        (parentBound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (List.ofFn (fun outer => (List.ofFn (physical
      outer)).flatten)).flatten -
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonSourceArea.CommonBasisRequest.Sampled.sourceAreaAt sample
        comparisons periodStage) ≤ requested * (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2
        := open Algebra in open Data.Rat in by
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  apply
    RequestedAggregation.CommonBasisRequest.Sampled.component_area_requested
    sample comparisons periodStage
    (fun outer => (List.ofFn (physical outer)).flatten)
      (componentMagnitude_nonnegative
      boundNN) positive
  · intro outer
    exact
      RequestedAggregation.CommonBasisRequest.Sampled.occurrence_area_requested
      sample comparisons outer (physical outer) boundNN

        (occurrenceTarget_positive
        boundNN positive) (areas outer) (errors outer) (leftBound outer) (rightBound outer)
  · intro outer
    exact
      RequestedAggregation.CommonBasisRequest.Sampled.occurrence_total_requested
      sample comparisons outer (physical outer) boundNN

        (occurrenceTarget_positive
        boundNN positive) (errors outer)
  · intro outer
    have estimate :=
      Connection.CommonBasisRequest.Sampled.occurrence_physical_total_bound
      outer (physical outer)
      (Fraction.Order.Arithmetic.mul_nonneg_direct boundNN massNN) (leftBound outer)
    have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (occurrenceMagnitude_le
      outer boundNN) massNN
    have rearrange : ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
        (parentBound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
      (((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * parentBound)
        *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by ring1
    exact ⟨estimate.1.trans (rearrange.trans_le paid), estimate.2.trans (rearrange.trans_le paid)⟩
  · intro outer
    have estimate := sample.occurrence_source_total_bound comparisons outer
      (Fraction.Order.Arithmetic.mul_nonneg_direct boundNN massNN) (rightBound outer)
    have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
      (occurrenceMagnitude_le
      outer boundNN) massNN
    have rearrange : ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 *
        (parentBound * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) =
      (((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * parentBound)
        *
        Readings.PreparedObservationCoercivity.coefficientNormSq coefficients := by ring1
    exact ⟨estimate.1.trans (rearrange.trans_le paid), estimate.2.trans (rearrange.trans_le paid)⟩

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
