module
import Purelib.Algebra.Field.ExplicitField
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.FiniteSum.Rational.Order
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRootTotals
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalComponentComparison
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
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRootTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootRequestBudget
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRootTotals.CommonBasisRequest

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Uniform error and magnitude bounds for retained root-chart parent displacements. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled
  (parentMagnitude parentMagnitude_nonnegative source_uniform_bounded)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled
  (parentTarget)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentRootTotals.CommonBasisRequest.Sampled
  (parentRootTotal parent_source_root_error)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRootTotals.CommonBasisRequest.Sampled
  (physical_parent_root_error)
open
  PhysicalComponentComparison.CommonBasisRequest.Sampled
  (PreparedPhysicalRows)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootRequestBudget.CommonBasisRequest.Sampled
  (parentTarget_le_requested)

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
  {target coefficientTarget : Coordinate} {coverFloor floor index minimum stage
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

/-- A coefficient-independent bound for the actual root displacements. -/
def rootParentMagnitude : Coordinate :=
  2 * (Sampled.parentMagnitude
    retained inputs + 34 * request.allocation.allowance^2)

/-- The source-restored root-parent magnitude bound is nonnegative. -/
theorem rootParentMagnitude_nonnegative :
    0 ≤
      Sampled.rootParentMagnitude
      (request := request) (inputs := inputs) :=
  Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg
    (Sampled.parentMagnitude_nonnegative
    retained inputs)
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Arithmetic.sq_nonneg_direct _)))

/-- The root-parent magnitude ceiling bounds the original source-parent magnitude. -/
theorem parentMagnitude_le_root :
    Sampled.parentMagnitude
      retained inputs ≤
      Sampled.rootParentMagnitude
      (request := request) (inputs := inputs) := by
  have step :
    Sampled.parentMagnitude
    retained inputs ≤
    Sampled.parentMagnitude
    retained inputs +
      (Sampled.parentMagnitude
        retained inputs + 68 * request.allocation.allowance^2) :=
    le_add_of_nonneg_right (add_nonneg
      (Sampled.parentMagnitude_nonnegative
      retained inputs)
      (Arithmetic.mul_nonneg_direct (by decide +kernel) (Arithmetic.sq_nonneg_direct _)))
  exact step.trans_eq (by
    unfold rootParentMagnitude;
    ring1)

include comparisons in
/-- Source-to-root restoration preserves a uniform homogeneous magnitude. -/
theorem parent_root_bounded (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.ConjugatePathReadback.conjugateDiagonal
      (Sampled.parentRootTotal
      sample outer position))
      (Sampled.rootParentMagnitude
        (request := request) (inputs := inputs) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)
        := by
  have source :=
    (Sampled.source_uniform_bounded
    sample comparisons outer position).2
  have error :=
    Sampled.parent_source_root_error
    sample comparisons outer position
  have oldBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Gaussian.Basic.Canonical.normSq point ≤ limit) :
      Gaussian.Norm.Basic.normSq point ≤ limit := by
    change Basic.LessEqual _ _ at h ⊢
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have canonicalBound {point : Gaussian.Basic.Canonical} {limit : Fraction.Rational}
      (h : Gaussian.Norm.Basic.normSq point ≤ limit) :
      Gaussian.Basic.Canonical.normSq point ≤ limit := by
    change Basic.LessEqual _ _ at h ⊢
    rw [← Gaussian.Norm.Basic.normSq_eq_canonical]
    exact h
  have restored := (Gaussian.Norm.Bounds.normSq_sub_le_two
    (ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
      comparisons outer position).weighted.source.total
    ((ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
      comparisons outer position).weighted.source.total -
      Sampled.parentRootTotal
      sample outer position)).trans
      (Arithmetic.mul_le_mul_of_nonneg_left_direct (Arithmetic.add_le_add_direct (oldBound
        source) error) (by decide +kernel))
  rw [show (ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
    sample comparisons outer position).weighted.source.total -
      ((ParentPrepared.CommonBasisRequest.Sampled.parentPrepared
        sample comparisons outer position).weighted.source.total -
        Sampled.parentRootTotal
        sample outer position) =
      Sampled.parentRootTotal
        sample outer position by ring1] at restored
  have bound : Gaussian.Norm.Basic.normSq
    (Sampled.parentRootTotal
    sample outer position) ≤
      Sampled.rootParentMagnitude
        (request := request) (inputs := inputs) * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients
        :=
    restored.trans_eq (by
      unfold rootParentMagnitude;
      ring1)
  exact ⟨canonicalBound ((Gaussian.Norm.Basic.normSq_conj _).trans_le bound), canonicalBound bound⟩

/-- The two independently paid endpoint errors are retained explicitly. -/
def rootParentError (requested : Coordinate) : Coordinate :=
  2 * (requested / 4 + 34 * request.allocation.allowance^2)

/-- The combined root-parent endpoint error is nonnegative for a nonnegative requested tolerance. -/
theorem rootParentError_nonnegative {requested : Coordinate} (nonnegative : 0 ≤
  requested) :
    0 ≤ Sampled.rootParentError
      (request := request) requested :=
  Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg (Field.div_nonneg_direct
    nonnegative (by decide +kernel))
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Arithmetic.sq_nonneg_direct _)))

/-- Every original physical parent endpoint satisfies the uniform root-restoration error bound.

The positive component target pays the parent tolerance, while the retained source allocation contributes its separate
squared-error term. -/
theorem physical_parent_root_uniform_error {requested : Coordinate} (positive : 0 <
  requested)
    (runs :
      PreparedPhysicalRows
      sample comparisons banks
      (Sampled.parentMagnitude
      retained inputs) requested)
    (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded ((Path.PairedIncrementArea.total ((banks.get
      outer).bank.physical position)).sub
      (Path.ConjugatePathReadback.conjugateDiagonal
        (Sampled.parentRootTotal
        sample outer position)))
        (Sampled.rootParentError
          (request := request) requested * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) :=
          open Purelib.Algebra.Field in open Purelib.Algebra in by
  have bound :=
    PhysicalRootTotals.CommonBasisRequest.Sampled.physical_parent_root_error
    sample comparisons banks outer position ((runs.get outer).get position)
  have targetLe :=
    RootRequestBudget.CommonBasisRequest.Sampled.parentTarget_le_requested
    outer
    (Sampled.parentMagnitude_nonnegative
    retained inputs) positive
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have quarterLe :
    HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
    prepared outer
    (Sampled.parentMagnitude
    retained inputs) requested / 4 ≤ requested / 4 := by
    simpa only [ExplicitField.div_eq_mul_inv] using Arithmetic.mul_le_mul_of_nonneg_right_direct targetLe
      (by decide +kernel : (0 : Coordinate) ≤ (4 :
      Coordinate)⁻¹)
  have paid := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct quarterLe (show 34 * request.allocation.allowance^2 ≤ 34 *
        request.allocation.allowance^2 from le_rfl)) (by
            decide : (0 : Coordinate) ≤ 2)) massNN
  exact ⟨bound.1.trans paid, bound.2.trans paid⟩

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds
