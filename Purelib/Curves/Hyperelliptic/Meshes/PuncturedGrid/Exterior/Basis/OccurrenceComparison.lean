module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OrderedRunComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedPaths
import Purelib.Integration.Path.ConjugateBlockComparison
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentGrouping
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseRunTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns
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

/-! Pay the complete occurrence polygon, including cross-parent joining wedges. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection

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

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  (outer : Fin prepared.occurrences.length)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest in
/-- The local source polygon uses the already selected acquisitions in retained
parent order. Its joining area is included in this scalar path area. -/
@[expose] def occurrenceSourcePath : List Normalization.InverseRootPolynomial.Gaussian :=
  (List.ofFn (fun position :
    Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length =>
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer position).weighted.values.map Prod.fst)).flatten

/-- Read the area of the complete retained source polygon, including all wedges joining its original parent paths. -/
@[expose] def occurrenceSourceArea : Normalization.InverseRootPolynomial.Gaussian :=
  Path.IncrementArea.pathArea (sample.occurrenceSourcePath comparisons outer)

/-- Total displacement of the retained local polygon, used by the joins
between occurrences. It need not vanish. -/
@[expose] def occurrenceSourceTotal : Normalization.InverseRootPolynomial.Gaussian :=
  Data.Gaussian.Norm.Sum.Basic.gaussianSum (sample.occurrenceSourcePath comparisons outer)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest in
/-- Assemble the physical/source comparisons on the retained parent order.
The endpoint hypotheses pay all cross-parent wedges in the complete polygon. -/
theorem occurrence_physical_source_area_bound
    (physical : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length → List Topology.Polygon.Stokes.PrimitivePoint)
    {areaError totalError bound : Normalization.InverseRootPolynomial.Coordinate} (totalNN : 0 ≤ totalError) (boundNN :
      0 ≤ bound)
    (areas : ∀ position, Data.Gaussian.Norm.Basic.normSq
      (Path.PairedIncrementArea.area (physical position) -
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
          sample comparisons outer position).weighted.source.area) ≤ areaError)
    (errors : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (physical
      position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
          sample comparisons outer position).weighted.source.total)) totalError)
    (leftBound : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total
      (physical position)) bound)
    (rightBound : ∀ position, Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
      (Path.ConjugatePathReadback.conjugateDiagonal
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer position).weighted.source.total) bound) :
    Data.Gaussian.Norm.Basic.normSq
      (Path.PairedIncrementArea.area (List.ofFn physical).flatten -
        sample.occurrenceSourceArea comparisons outer) ≤
      2 * (((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * areaError +
        16 * ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^4 * totalError
          * bound) := by
  have estimate := Path.ConjugateBlockComparison.conjugate_blocks_area_difference_bound
    (List.ofFn (fun position => (physical position,
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer position).weighted.values.map Prod.fst))) totalNN boundNN
    (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      rw [← (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
        sample comparisons outer position).weighted.source.area_eq]
      exact areas position)
    (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      rw [← (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
        sample comparisons outer position).weighted.source.total_eq]
      exact errors position)
    (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact leftBound position)
    (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      rw [← (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
        sample comparisons outer position).weighted.source.total_eq]
      exact rightBound position)
  rw [Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.length_ofFn] at estimate
  exact estimate

variable {faceIndex : Nat}
  (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
  (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns retained inputs outer
    data coefficients)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest
/-- Uniform paid run budgets control the complete forward occurrence polygon. -/
theorem ordered_forward_source_area_bound
    (chains : ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
      run.fragments 0 1)
    {areaError totalError bound : Normalization.InverseRootPolynomial.Coordinate} (totalNN : 0 ≤ totalError) (boundNN :
      0 ≤ bound)
    (areaPaid : ∀ position,
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun sample
      comparisons outer data (ordered.runAt position)
      (chains _ (ordered.runAt_mem position))).error * (Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) ^ 2 ≤ areaError)
    (totalPaid : ∀ position,
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun sample
      comparisons outer data (ordered.runAt position)
      (chains _ (ordered.runAt_mem position))).totalError * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients ≤ totalError)
    (physicalPaid : ∀ position, 2 *
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun sample
      comparisons outer data (ordered.runAt position)
      (chains _ (ordered.runAt_mem position))).totalError +
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
          position).sources) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤ bound)
    (sourcePaid : ∀ position,
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
      position).sources *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (List.ofFn ordered.physical).flatten -
      sample.occurrenceSourceArea comparisons outer) ≤
      2 * (((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * areaError +
        16 * ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^4 *
          totalError * bound) := by
  apply sample.occurrence_physical_source_area_bound comparisons outer ordered.physical totalNN boundNN
  · intro position
    exact
      (OrderedRunComparison.CommonBasisRequest.Sampled.ordered_forward_area
      sample comparisons outer data ordered position chains).trans (areaPaid position)
  · intro position
    have estimate :=
      OrderedRunComparison.CommonBasisRequest.Sampled.ordered_forward_total
      sample comparisons outer data ordered position chains
    exact ⟨estimate.1.trans (totalPaid position), estimate.2.trans (totalPaid position)⟩
  · intro position
    have estimate :=
      OrderedRunComparison.CommonBasisRequest.Sampled.ordered_forward_bounded
      sample comparisons outer data ordered position chains
    exact ⟨estimate.1.trans (physicalPaid position), estimate.2.trans (physicalPaid position)⟩
  · intro position
    have estimate :=
      OrderedRunComparison.CommonBasisRequest.Sampled.ordered_source_bounded
      sample comparisons outer position
    exact ⟨estimate.1.trans (sourcePaid position), estimate.2.trans (sourcePaid position)⟩

/-- Uniform paid run budgets control the complete reverse occurrence polygon. -/
theorem ordered_reverse_source_area_bound
    (chains : ∀ run ∈ ordered.runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain run.fragments 1 0)
    {areaError totalError bound : Normalization.InverseRootPolynomial.Coordinate} (totalNN : 0 ≤ totalError) (boundNN :
      0 ≤ bound)
    (areaPaid : ∀ position,
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun
      sample comparisons outer data (ordered.runAt position)
      (chains _ (ordered.runAt_mem position))).error * (Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) ^ 2 ≤ areaError)
    (totalPaid : ∀ position,
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun
      sample comparisons outer data (ordered.runAt position)
      (chains _ (ordered.runAt_mem position))).totalError * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients ≤ totalError)
    (physicalPaid : ∀ position, 2 *
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun
      sample comparisons outer data (ordered.runAt position)
      (chains _ (ordered.runAt_mem position))).totalError +
        Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
          position).sources) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤ bound)
    (sourcePaid : ∀ position,
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
      position).sources *
      Readings.PreparedObservationCoercivity.coefficientNormSq coefficients ≤ bound) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (List.ofFn (fun position =>
      Path.PairedAreaReversal.reverseIncrements (ordered.physical position))).flatten -
      sample.occurrenceSourceArea comparisons outer) ≤
      2 * (((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2 * areaError +
        16 * ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^4 *
          totalError * bound) := by
  apply sample.occurrence_physical_source_area_bound comparisons outer (fun position =>
    Path.PairedAreaReversal.reverseIncrements (ordered.physical position)) totalNN boundNN
  · intro position
    exact
      (OrderedRunComparison.CommonBasisRequest.Sampled.ordered_reverse_area
      sample comparisons outer data ordered position chains).trans (areaPaid position)
  · intro position
    have estimate :=
      OrderedRunComparison.CommonBasisRequest.Sampled.ordered_reverse_total
      sample comparisons outer data ordered position chains
    exact ⟨estimate.1.trans (totalPaid position), estimate.2.trans (totalPaid position)⟩
  · intro position
    have estimate :=
      OrderedRunComparison.CommonBasisRequest.Sampled.ordered_reverse_bounded
      sample comparisons outer data ordered position chains
    exact ⟨estimate.1.trans (physicalPaid position), estimate.2.trans (physicalPaid position)⟩
  · intro position
    have estimate :=
      OrderedRunComparison.CommonBasisRequest.Sampled.ordered_source_bounded
      sample comparisons outer position
    exact ⟨estimate.1.trans (sourcePaid position), estimate.2.trans (sourcePaid position)⟩

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
