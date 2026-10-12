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

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)

variable {requested : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 < requested)
  (runs :
    PhysicalComponentComparison.CommonBasisRequest.Sampled.PreparedPhysicalRows
    sample comparisons banks
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
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
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
      banks outer)).flatten).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (OccurrenceRootTotals.CommonBasisRequest.Sampled.occurrenceRootTotal
        sample outer)))

          (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
          prepared
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest.Sampled.rootParentError
          (request := request) requested) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := by
  have error :=
    OccurrenceRootTotals.CommonBasisRequest.Sampled.physical_occurrence_root_error
    sample comparisons banks positive runs outer
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct

      (HierarchicalRequest.CommonBasisRequest.Sampled.occurrenceMagnitude_le
      outer
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentError_nonnegative
      (request := request) positive.le))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningComparison.CommonBasisRequest.Sampled.mass_nonnegative
      (coefficients := coefficients))
  rw [Fraction.Field.mul_assoc] at paid
  exact ⟨error.1.trans paid, error.2.trans paid⟩

include comparisons in
/-- Each retained root endpoint obeys the common component-scaled magnitude bound. -/
theorem root_join_bounded (outer : Fin prepared.occurrences.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.ConjugatePathReadback.conjugateDiagonal
      (OccurrenceRootTotals.CommonBasisRequest.Sampled.occurrenceRootTotal
      sample outer))

        (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
        prepared
        (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude
        (request := request) (inputs := inputs)) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) := by
  have bound :=
    OccurrenceRootTotals.CommonBasisRequest.Sampled.occurrence_root_bounded
    sample comparisons outer
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct

      (HierarchicalRequest.CommonBasisRequest.Sampled.occurrenceMagnitude_le
      outer
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs)))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningComparison.CommonBasisRequest.Sampled.mass_nonnegative
      (coefficients := coefficients))
  rw [Fraction.Field.mul_assoc] at paid
  exact ⟨bound.1.trans paid, bound.2.trans paid⟩

include comparisons runs in
/-- Each original physical occurrence endpoint obeys the same component-scaled root magnitude bound. -/
theorem physical_root_join_bounded (outer : Fin prepared.occurrences.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total (List.ofFn
      (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
      banks outer)).flatten)

        (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
        prepared
        (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude
        (request := request) (inputs := inputs)) * Readings.PreparedObservationCoercivity.coefficientNormSq
        coefficients) := by
  have bound :=
    Connection.CommonBasisRequest.Sampled.occurrence_physical_total_bound
    outer
    (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
    banks outer)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs))

        (mass_nonnegative
        (coefficients := coefficients))) (by
        intro position
        have localBound :=
          PreparedPhysicalBounds.PhysicalRunBank.PreparedRun.total_bounded_requested
          ((runs.get outer).get position)
            (HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget_le_one
            outer
            (SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
            retained inputs) requested)
        have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.runMagnitude_le
            retained inputs outer position).trans

              (RootParentBounds.CommonBasisRequest.Sampled.parentMagnitude_le_root
              (request := request) (inputs := inputs)))

            (mass_nonnegative
            (coefficients := coefficients))
        exact ⟨localBound.1.trans paid, localBound.2.trans paid⟩)
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct

      (HierarchicalRequest.CommonBasisRequest.Sampled.occurrenceMagnitude_le
      outer
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs)))
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningComparison.CommonBasisRequest.Sampled.mass_nonnegative
      (coefficients := coefficients))
  rw [Fraction.Field.mul_assoc] at paid
  exact ⟨bound.1.trans paid, bound.2.trans paid⟩

include comparisons positive runs in
/-- Compare the actual occurrence joining polygon with retained root totals. -/
theorem physical_root_joining_area_error :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area
      (List.ofFn (fun outer => Path.PairedIncrementArea.total (List.ofFn
        (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
        banks outer)).flatten)) -
      Path.PairedIncrementArea.area (List.ofFn (fun outer =>
        Path.ConjugatePathReadback.conjugateDiagonal
          (OccurrenceRootTotals.CommonBasisRequest.Sampled.occurrenceRootTotal
          sample outer)))) ≤
      16 * (prepared.occurrences.length : Normalization.InverseRootPolynomial.Coordinate)^4 *

          HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
          prepared
          (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest.Sampled.rootParentError
          (request := request) requested) *

          HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
          prepared
          (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude
          (request := request) (inputs := inputs)) *
        (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 := by
  have estimate := Path.PairedIncrementComparison.area_difference_bound
    (List.ofFn (fun outer =>
      (Path.PairedIncrementArea.total (List.ofFn
        (PhysicalComponentComparison.CommonBasisRequest.Sampled.physicalPaths
        banks outer)).flatten,
        Path.ConjugatePathReadback.conjugateDiagonal
          (OccurrenceRootTotals.CommonBasisRequest.Sampled.occurrenceRootTotal
          sample outer))))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentError_nonnegative
      (request := request) positive.le))

        (mass_nonnegative
        (coefficients := coefficients)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude_nonnegative
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
  rw [Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.map_ofFn, Data.List.OfFn.Basic.length_ofFn] at estimate
  exact estimate.trans_eq (by ring1)

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningComparison
