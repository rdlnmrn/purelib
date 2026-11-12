module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.ConjugateBlockComparison
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceComparison
import Purelib.Integration.Path.ConjugateBlockTotals
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

open Purelib.Riemann.Readings.PrimitiveAreaBounds

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Carry whole-occurrence endpoint errors and magnitudes into the global joins. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection

open Purelib.Riemann.Normalization

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential : Differentials.Basic.Differential genus}
  {collar : Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {program : PeriodPrograms.ExteriorProgram lifted differential} {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
    regular domains program}

variable {bounds : Charts.Reciprocal.ReciprocalPaddedInverse.UniformBounds regular.padded}
  {retained : Preparation.CommonBasisPreparation prepared}
  {basis : Charts.Reciprocal.ReciprocalPaddedBasisBounds.BasisBounds bounds}
  {target coefficientTarget : InverseRootPolynomial.Coordinate} {coverFloor floor index minimum stage
    energyFloor radialDepth : Nat}
  {box : Rational.Box} {capSample : Charts.Reciprocal.Cap.Primitives.Sample cap
    differential index box}
  {polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box}

namespace CommonBasisRequest

variable {request : Preparation.CommonBasisRequest retained basis
  target coefficientTarget coverFloor floor}
  {plans : request.Plans capSample polynomials minimum} {inputs : retained.Inputs index}
  {readings : Charts.Reciprocal.Disk.Basis.CommonParentPlans.Readings retained.anchors retained.sources
    request.schedule.bank plans inputs stage}

variable {fans : FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled

variable (sample : Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  (outer : Fin prepared.occurrences.length)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest in
/-- Uniform parentwise total errors bound the complete physical/source occurrence displacement error by the squared
parent count.

The comparison retains each original prepared source total and both conjugate coordinates. -/
theorem occurrence_total_error
    (physical : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length → List Topology.Polygon.Stokes.PrimitivePoint)
    {error : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ error)
    (errors : ∀ position, PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (physical
      position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Sampled.parentPrepared
          sample comparisons outer position).weighted.source.total)) error) :
    PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (List.ofFn
      physical).flatten).sub
      (Path.ConjugatePathReadback.conjugateDiagonal (sample.occurrenceSourceTotal comparisons outer)))
        (((ParentIndices.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length : InverseRootPolynomial.Coordinate)^2 * error) :=
          by
  have estimate := Path.ConjugateBlockTotals.conjugate_blocks_total_difference_bound
    (List.ofFn (fun position => (physical position,
      (Sampled.parentPrepared sample
        comparisons outer position).weighted.values.map Prod.fst))) nonnegative (by
        intro pair member
        obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
        rw [←
          (Sampled.parentPrepared
          sample comparisons outer position).weighted.source.total_eq]
        exact errors position)
  rw [Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.length_ofFn] at estimate
  exact estimate

/-- A uniform bound on each physical parent total bounds the complete occurrence total by the squared parent count. -/
theorem occurrence_physical_total_bound
    (physical : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length → List Topology.Polygon.Stokes.PrimitivePoint)
    {bound : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ bound)
    (bounded : ∀ position, PrimitivePoint.Bounded (Path.PairedIncrementArea.total (physical
      position)) bound) :
    PrimitivePoint.Bounded (Path.PairedIncrementArea.total (List.ofFn physical).flatten)
      (((ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length : InverseRootPolynomial.Coordinate)^2 * bound) := by
  have estimate := Path.ConjugateBlockTotals.blocks_total_bounded (List.ofFn physical) nonnegative (by
    intro block member
    obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
    exact bounded position)
  rw [Data.List.OfFn.Basic.length_ofFn] at estimate
  exact estimate

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest in
/-- A uniform bound on each retained source-parent total bounds the complete source occurrence displacement by the
squared parent count. -/
theorem occurrence_source_total_bound {bound : InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ bound)
    (bounded : ∀ position, PrimitivePoint.Bounded
      (Path.ConjugatePathReadback.conjugateDiagonal
      (Sampled.parentPrepared sample
        comparisons outer position).weighted.source.total) bound) :
    PrimitivePoint.Bounded (Path.ConjugatePathReadback.conjugateDiagonal
      (sample.occurrenceSourceTotal comparisons outer))
      (((ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length : InverseRootPolynomial.Coordinate)^2 * bound) :=
        open Purelib.Data in by
  have estimate := Path.PairedIncrementArea.total_bound nonnegative
    (values := List.ofFn (fun position => Path.ConjugatePathReadback.conjugateDiagonal
      (Sampled.parentPrepared sample
        comparisons outer position).weighted.source.total)) (by
        intro value member
        obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
        exact bounded position)
    (count := (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length)
    (by rw [List.OfFn.Basic.length_ofFn])
  have totals := List.OfFn.Basic.ofFn_congr (fun position =>
    (Sampled.parentPrepared sample
      comparisons outer position).weighted.source.total_eq)
  change List.ofFn (fun position =>
    (Sampled.parentPrepared sample
    comparisons outer position).weighted.source.total) =
    List.ofFn (fun position => Gaussian.Norm.Sum.Basic.gaussianSum
      ((Sampled.parentPrepared
        sample comparisons outer position).weighted.values.map Prod.fst)) at totals
  have mapped := congrArg (List.map Path.ConjugatePathReadback.conjugateDiagonal) totals
  rw [List.OfFn.Basic.map_ofFn, List.OfFn.Basic.map_ofFn] at mapped
  simp only [Function.comp_def] at mapped
  rw [mapped] at estimate
  have readback := Path.ConjugateBlockComparison.conjugateDiagonal_total
    (List.ofFn (fun position => Gaussian.Norm.Sum.Basic.gaussianSum
      ((Sampled.parentPrepared
        sample comparisons outer position).weighted.values.map Prod.fst)))
  rw [List.OfFn.Basic.map_ofFn] at readback
  simp only [Function.comp_def] at readback
  rw [readback] at estimate
  have summed := Path.IncrementArea.sum_flatten
    (List.ofFn (fun position =>
      (Sampled.parentPrepared sample
      comparisons outer position).weighted.values.map Prod.fst))
  rw [List.OfFn.Basic.map_ofFn] at summed
  simp only [Function.comp_def] at summed
  rw [← summed] at estimate
  exact estimate

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
