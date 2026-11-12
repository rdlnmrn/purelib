module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.Rat.Fraction.Field
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Integration.Path.PairedIncrementComparison
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRootTotals
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentJoins
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
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
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRootTotals.CommonBasisRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison.CommonBasisRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Compare physical occurrence joining polygons with retained root polygons. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningComparison

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest.Sampled
  (rootParentError rootParentError_nonnegative rootParentMagnitude rootParentMagnitude_nonnegative
    parentMagnitude_le_root parent_root_bounded physical_parent_root_uniform_error)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.OccurrenceRootTotals.CommonBasisRequest.Sampled
  (occurrenceRootTotal physical_occurrence_root_error occurrence_root_bounded)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled
  (componentMagnitude componentMagnitude_nonnegative occurrenceMagnitude_le parentTarget_le_one)

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

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)

variable {requested : InverseRootPolynomial.Coordinate} (positive : 0 < requested)
  (runs :
    Sampled.PreparedPhysicalRows
    sample comparisons banks
    (SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
    retained inputs) requested)

/-- The finite sum of squared Gaussian coefficient norms is nonnegative. -/
private theorem mass_nonnegative : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
  open Purelib.Algebra in FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Normalization.InverseRootPolynomial.Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))

include comparisons positive runs in
/-- Each physical occurrence endpoint differs from its retained root endpoint by the uniform component-scaled
restoration bound. -/
theorem physical_root_join_error (outer : Fin prepared.occurrences.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total (List.ofFn
      (Sampled.physicalPaths
      banks outer)).flatten).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Sampled.occurrenceRootTotal
        sample outer)))

          (Sampled.componentMagnitude
          prepared
          (Sampled.rootParentError
          (request := request) requested) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have error :=
    Sampled.physical_occurrence_root_error
    sample comparisons banks positive runs outer
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct

      (Sampled.occurrenceMagnitude_le
      outer
      (Sampled.rootParentError_nonnegative
      (request := request) positive.le))
    (Sampled.mass_nonnegative
      (coefficients := coefficients))
  rw [Fraction.Field.mul_assoc] at paid
  exact ⟨error.1.trans paid, error.2.trans paid⟩

include comparisons in
/-- Each retained root endpoint obeys the common component-scaled magnitude bound. -/
theorem root_join_bounded (outer : Fin prepared.occurrences.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.ConjugatePathReadback.conjugateDiagonal
      (Sampled.occurrenceRootTotal
      sample outer))

        (Sampled.componentMagnitude
        prepared
        (Sampled.rootParentMagnitude
        (request := request) (inputs := inputs)) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) := by
  have bound :=
    Sampled.occurrence_root_bounded
    sample comparisons outer
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct

      (Sampled.occurrenceMagnitude_le
      outer
      (Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs)))
    (Sampled.mass_nonnegative
      (coefficients := coefficients))
  rw [Fraction.Field.mul_assoc] at paid
  exact ⟨bound.1.trans paid, bound.2.trans paid⟩

include comparisons runs in
/-- Each original physical occurrence endpoint obeys the same component-scaled root magnitude bound. -/
theorem physical_root_join_bounded (outer : Fin prepared.occurrences.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total (List.ofFn
      (Sampled.physicalPaths
      banks outer)).flatten)

        (Sampled.componentMagnitude
        prepared
        (Sampled.rootParentMagnitude
        (request := request) (inputs := inputs)) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) := by
  have bound :=
    Connection.CommonBasisRequest.Sampled.occurrence_physical_total_bound
    outer
    (Sampled.physicalPaths
    banks outer)
    (Arithmetic.mul_nonneg_direct
      (Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs))

        (mass_nonnegative
        (coefficients := coefficients))) (by
        intro position
        have localBound :=
          PreparedPhysicalBounds.PhysicalRunBank.PreparedRun.total_bounded_requested
          ((runs.get outer).get position)
            (Sampled.parentTarget_le_one
            outer
            (SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
            retained inputs) requested)
        have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct
          ((SourceMagnitude.CommonBasisRequest.Sampled.runMagnitude_le
            retained inputs outer position).trans

              (Sampled.parentMagnitude_le_root
              (request := request) (inputs := inputs)))

            (mass_nonnegative
            (coefficients := coefficients))
        exact ⟨localBound.1.trans paid, localBound.2.trans paid⟩)
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct

      (Sampled.occurrenceMagnitude_le
      outer
      (Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs)))
    (Sampled.mass_nonnegative
      (coefficients := coefficients))
  rw [Fraction.Field.mul_assoc] at paid
  exact ⟨bound.1.trans paid, bound.2.trans paid⟩

include comparisons positive runs in
/-- Compare the actual occurrence joining polygon with retained root totals. -/
theorem physical_root_joining_area_error :
    Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (List.ofFn (fun outer => Path.PairedIncrementArea.total (List.ofFn
        (Sampled.physicalPaths
        banks outer)).flatten)) -
      Path.PairedIncrementArea.area (List.ofFn (fun outer =>
        Path.ConjugatePathReadback.conjugateDiagonal
          (Sampled.occurrenceRootTotal
          sample outer)))) ≤
      16 * (prepared.occurrences.length : InverseRootPolynomial.Coordinate)^4 *

          Sampled.componentMagnitude
          prepared
          (Sampled.rootParentError
          (request := request) requested) *

          Sampled.componentMagnitude
          prepared
          (Sampled.rootParentMagnitude
          (request := request) (inputs := inputs)) *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have estimate := Path.PairedIncrementComparison.area_difference_bound
    (List.ofFn (fun outer =>
      (Path.PairedIncrementArea.total (List.ofFn
        (Sampled.physicalPaths
        banks outer)).flatten,
        Path.ConjugatePathReadback.conjugateDiagonal
          (Sampled.occurrenceRootTotal
          sample outer))))
    (Arithmetic.mul_nonneg_direct
      (Sampled.componentMagnitude_nonnegative
      (Sampled.rootParentError_nonnegative
      (request := request) positive.le))

        (mass_nonnegative
        (coefficients := coefficients)))
    (Arithmetic.mul_nonneg_direct
      (Sampled.componentMagnitude_nonnegative
      (Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs)))

        (mass_nonnegative
        (coefficients := coefficients)))
    (by
      intro pair member
      obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact
        physical_root_join_error
        sample comparisons banks positive runs outer)
    (by
      intro pair member
      obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact
        physical_root_join_bounded
        sample comparisons banks runs outer)
    (by
      intro pair member
      obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp member
      exact
        root_join_bounded
        sample comparisons outer)
  rw [List.OfFn.Basic.map_ofFn, List.OfFn.Basic.map_ofFn, List.OfFn.Basic.length_ofFn] at estimate
  exact estimate.trans_eq (by ring1)

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningComparison
