module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRootTotals
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
import Purelib.Data.Vector.Dependent
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

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Compare physical parent totals with their retained root-chart displacements. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRootTotals

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

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)

/-- Compose two Gaussian squared-error bounds with the factor-two loss for the sum of their residuals. -/
private theorem scalar_error_trans {first middle last : Normalization.InverseRootPolynomial.Gaussian} {before after :
  Normalization.InverseRootPolynomial.Coordinate}
    (left : Data.Gaussian.Norm.Basic.normSq (first - middle) ≤ before) (right :
      Data.Gaussian.Norm.Basic.normSq (middle - last) ≤ after) :
    Data.Gaussian.Norm.Basic.normSq (first - last) ≤ 2 * (before + after) := open Purelib.Data.Rat in
      by
  have bound := (Gaussian.Norm.Bounds.normSq_add_le_two (first - middle) (middle - last)).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct left right)
      (by decide))
  rw [show first - middle + (middle - last) = first - last by ring1] at bound
  exact bound

/-- The actual run and its root endpoints share the selected source summary.
This pays both comparison steps without replacing the odd root coordinate. -/
theorem physical_parent_root_error (outer : Fin prepared.occurrences.length)
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length)
    {localTarget : Normalization.InverseRootPolynomial.Coordinate}
    (run : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PreparedPhysicalRuns.PhysicalRunBank.PreparedRun (banks.get
      outer).bank position
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
      comparisons outer position) localTarget) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total ((banks.get
      outer).bank.physical position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRootTotals.CommonBasisRequest.Sampled.parentRootTotal
        sample outer position)))
        (2 * (localTarget / 4 + 34 * request.allocation.allowance^2) *
          Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := open Purelib.Data.Rat in by
  have source :=
    ParentRootTotals.CommonBasisRequest.Sampled.parent_source_root_error
    sample comparisons outer position
  have canonicalBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Data.Gaussian.Norm.Basic.normSq point ≤ limit) :
      Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have oldBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Gaussian.Basic.Canonical.normSq point ≤ limit) :
      Data.Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Fraction.Order.Basic.LessEqual _ _ at h ⊢
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have root : Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.ConjugatePathReadback.conjugateDiagonal
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
    comparisons outer position).weighted.source.total).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRootTotals.CommonBasisRequest.Sampled.parentRootTotal
        sample outer position)))
        (34 * request.allocation.allowance^2 * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :=
          by
    rw [← Path.ConjugatePathReadback.conjugateDiagonal_sub]
    exact ⟨canonicalBound ((Gaussian.Norm.Basic.normSq_conj _).trans_le source), canonicalBound source⟩
  have physical :=
    PreparedPhysicalBounds.PhysicalRunBank.PreparedRun.total_quarter_requested
    run
  constructor
  · apply canonicalBound
    exact
      (scalar_error_trans
      (oldBound physical.1) (oldBound root.1)).trans_eq (by ring1)
  · apply canonicalBound
    exact
      (scalar_error_trans
      (oldBound physical.2) (oldBound root.2)).trans_eq (by ring1)

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRootTotals
