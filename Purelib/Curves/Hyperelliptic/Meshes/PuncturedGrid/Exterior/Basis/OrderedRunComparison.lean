module
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedAreaReversal
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OrientedReverseRuns
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

open Purelib

open Purelib.Riemann

@[expose] public section
/-! Compare source-indexed physical groups with the exact selected parent summaries. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OrderedRunComparison

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
  (outer : Fin prepared.occurrences.length) {faceIndex : Nat}
  (data : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FragmentQueries.RowData
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences outer) faceIndex)
  (ordered : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceOrderedRuns.ParentOrderedRuns retained inputs outer
    data coefficients)
  (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
    outer).compared.entered.cache.parents.length)

/-- The physical block's source summary is read at its actual retained
position. Repeated equal parent payloads cannot redirect the acquisition. -/
theorem ordered_forward_area
    (chains : ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
      run.fragments 0 1) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (ordered.physical position) -
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer position).weighted.source.area) ≤
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun sample
      comparisons outer data (ordered.runAt position)
      (chains _ (ordered.runAt_mem position))).error * (Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun_area sample
    comparisons outer data (ordered.runAt position)
    (chains _ (ordered.runAt_mem position))
  have selected := congrArg (fun parent =>
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
    comparisons outer parent).weighted.source.area)
    (ordered.runAt_parent position)
  rw [selected] at estimate
  exact estimate

/-- The source-ordered physical run retains the original forward total bound at its selected parent position. -/
theorem ordered_forward_total
    (chains : ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
      run.fragments 0 1) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (ordered.physical
      position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
          sample comparisons outer position).weighted.source.total))
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun sample
        comparisons outer data (ordered.runAt position)
        (chains _ (ordered.runAt_mem position))).totalError * Readings.PreparedObservationCoercivity.coefficientNormSq
          coefficients) := by
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun_total sample
    comparisons outer data (ordered.runAt position)
    (chains _ (ordered.runAt_mem position))
  have selected := congrArg (fun parent =>
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
    comparisons outer parent).weighted.source.total)
    (ordered.runAt_parent position)
  rw [selected] at estimate
  exact estimate

/-- The reversed source-ordered run retains its paid area comparison with the original source polygon. -/
theorem ordered_reverse_area
    (chains : ∀ run ∈ ordered.runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain run.fragments 1 0) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area (Path.PairedAreaReversal.reverseIncrements
      (ordered.physical position)) -
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer position).weighted.source.area) ≤
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun sample
      comparisons outer data (ordered.runAt position)
      (chains _ (ordered.runAt_mem position))).error * (Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients)^2 := by
  have estimate :=
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun sample
    comparisons outer data (ordered.runAt position)
    (chains _ (ordered.runAt_mem position))).oriented_area
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer (ordered.runAt position).parent).weighted
  have selected := congrArg (fun parent =>
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
    comparisons outer parent).weighted.source.area)
    (ordered.runAt_parent position)
  rw [selected] at estimate
  exact estimate

/-- The reversed physical run retains the original total bound at its selected source-parent position. -/
theorem ordered_reverse_total
    (chains : ∀ run ∈ ordered.runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain run.fragments 1 0) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total
      (Path.PairedAreaReversal.reverseIncrements (ordered.physical position))).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
          sample comparisons outer position).weighted.source.total))
      ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun
        sample comparisons outer data (ordered.runAt position)
        (chains _ (ordered.runAt_mem position))).totalError * Readings.PreparedObservationCoercivity.coefficientNormSq
          coefficients) := by
  have estimate :=
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun sample
    comparisons outer data (ordered.runAt position)
    (chains _ (ordered.runAt_mem position))).oriented_total
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer (ordered.runAt position).parent).weighted
  have selected := congrArg (fun parent =>
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
    comparisons outer parent).weighted.source.total)
    (ordered.runAt_parent position)
  rw [selected] at estimate
  exact estimate

/-- Source-position magnitude bounds retain the physical endpoint error. -/
theorem ordered_forward_bounded
    (chains : ∀ run ∈ ordered.runs, Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceChains.SourceChain
      run.fragments 0 1) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total (ordered.physical position))
      (2 * ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun
        sample comparisons outer data (ordered.runAt position)
        (chains _ (ordered.runAt_mem position))).totalError +
          Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
            position).sources) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have estimate :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedRun_bounded sample
    comparisons outer data (ordered.runAt position)
    (chains _ (ordered.runAt_mem position))
  have selected := congrArg (fun parent =>
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer parent).sources)
    (ordered.runAt_parent position)
  rw [selected] at estimate
  exact estimate

/-- Every fragment in a reversed source-ordered run retains its original coefficient-weighted endpoint bound. -/
theorem ordered_reverse_bounded
    (chains : ∀ run ∈ ordered.runs,
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ReverseSourceChains.ReverseSourceChain run.fragments 1 0) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total
      (Path.PairedAreaReversal.reverseIncrements (ordered.physical position)))
      (2 *
        ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun
        sample comparisons outer data (ordered.runAt position)
        (chains _ (ordered.runAt_mem position))).totalError +
          Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
            (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
            position).sources) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have estimate :=
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SelectedRuns.CommonBasisRequest.Sampled.selectedReverseRun sample
    comparisons outer data (ordered.runAt position)
    (chains _ (ordered.runAt_mem position))).oriented_bounded
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer (ordered.runAt position).parent).weighted
  have selected := congrArg (fun parent =>
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer parent).sources)
    (ordered.runAt_parent position)
  rw [selected] at estimate
  exact estimate

/-- This cached source bound does not depend on a physical fragmentation. -/
theorem ordered_source_bounded :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.ConjugatePathReadback.conjugateDiagonal
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
        comparisons outer position).weighted.source.total)
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
        position).sources * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :=
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceRuns.SourceRun.cached_source_bounded
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
    comparisons outer position).weighted

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OrderedRunComparison
