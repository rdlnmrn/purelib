module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.OfFn.Basic
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRootTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds
import Purelib.Integration.Path.ConjugateBlockTotals
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Dependent
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
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRootTotals.CommonBasisRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest

open Purelib.Curves

open Purelib.Data

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Accumulate parent root displacements and errors in each retained occurrence. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRootTotals

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest.Sampled
  (rootParentError rootParentError_nonnegative rootParentMagnitude rootParentMagnitude_nonnegative parent_root_bounded
    physical_parent_root_uniform_error)

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

variable {fans : Connection.CommonBasisRequest.FanPreparation request
  plans inputs readings energyFloor}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus}

namespace Sampled
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian)

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)

/-- Parent displacements remain in the acquired root chart. -/
def occurrenceRootPath (outer : Fin prepared.occurrences.length) : List Gaussian :=
  List.ofFn (fun position =>
    Sampled.parentRootTotal sample
    outer position)

/-- Sum the original parent displacements in their acquired root chart for one retained occurrence. -/
def occurrenceRootTotal (outer : Fin prepared.occurrences.length) : Gaussian :=
  Gaussian.Norm.Sum.Basic.gaussianSum
    (occurrenceRootPath
    sample outer)

/-- The parent restoration errors accumulate only with the finite parent count. -/
theorem physical_occurrence_root_error {requested : InverseRootPolynomial.Coordinate} (positive : 0 <
  requested)
    (runs :
      PhysicalComponentComparison.CommonBasisRequest.Sampled.PreparedPhysicalRows
      sample comparisons banks
      (SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
      retained inputs) requested)
    (outer : Fin prepared.occurrences.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (List.ofFn
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
      banks outer)).flatten).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (occurrenceRootTotal
        sample outer)))
        (((ParentIndices.occurrenceAt prepared.occurrences
          outer).compared.entered.cache.parents.length : InverseRootPolynomial.Coordinate)^2 *
          (Sampled.rootParentError
            (request := request) requested * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)) :=
            open Purelib.Algebra in open Purelib.Data.Rat in by
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have estimate := Path.ConjugateBlockTotals.conjugate_blocks_total_difference_bound
    (List.ofFn (fun position =>
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
      banks outer position,
      [Sampled.parentRootTotal
      sample outer position])))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Sampled.rootParentError_nonnegative
      positive.le) massNN) (by
      intro pair member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      simpa only
        [PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths,
        Gaussian.Norm.Sum.Basic.gaussianSum, add_zero] using

          Sampled.physical_parent_root_uniform_error
          sample comparisons banks positive runs outer position)
  rw [List.OfFn.Basic.map_ofFn, List.OfFn.Basic.map_ofFn, List.OfFn.Basic.length_ofFn] at estimate
  change Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (List.ofFn
    (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
    banks outer)).flatten).sub
    (Path.ConjugatePathReadback.conjugateDiagonal (Gaussian.Norm.Sum.Basic.gaussianSum
      (List.ofFn (fun position =>
        [Sampled.parentRootTotal
        sample outer position])).flatten))) _ at estimate
  rw [Path.IncrementArea.sum_flatten, List.OfFn.Basic.map_ofFn] at estimate
  have readback := List.OfFn.Basic.ofFn_congr (fun position =>
    (show Gaussian.Norm.Sum.Basic.gaussianSum
      [Sampled.parentRootTotal
      sample outer position] =
      Sampled.parentRootTotal
        sample outer position from add_zero _))
  change List.ofFn (fun position => Gaussian.Norm.Sum.Basic.gaussianSum
    [Sampled.parentRootTotal
    sample outer position]) =
    Sampled.occurrenceRootPath
      sample outer at readback
  simp only [Function.comp_def] at estimate
  rw [readback] at estimate
  exact estimate

include comparisons in
/-- The root total bound is independent of the number of refined increments. -/
theorem occurrence_root_bounded (outer : Fin prepared.occurrences.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.ConjugatePathReadback.conjugateDiagonal
      (occurrenceRootTotal
      sample outer))
      (((ParentIndices.occurrenceAt prepared.occurrences
        outer).compared.entered.cache.parents.length : InverseRootPolynomial.Coordinate)^2 *

          (Sampled.rootParentMagnitude
          (request := request) (inputs := inputs) * Readings.PreparedObservationCoercivity.coefficientNormSq
          coefficients)) := open Algebra in open Rat in by
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have bound := Path.IncrementArea.sum_bound_of_length
    (values :=
      occurrenceRootPath
      sample outer)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs)) massNN)
    (by
      intro value member
      obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      rw [Gaussian.Norm.Basic.normSq_eq_canonical]
      exact
        (Sampled.parent_root_bounded
        sample comparisons outer position).2)
    (count := (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length)
    (by
        rw [occurrenceRootPath, List.OfFn.Basic.length_ofFn])
  constructor
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact (Gaussian.Norm.Basic.normSq_conj _).trans_le bound
  · rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact bound

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRootTotals
