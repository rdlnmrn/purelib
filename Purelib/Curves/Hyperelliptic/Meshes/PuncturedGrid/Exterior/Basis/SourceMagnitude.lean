module
import Purelib.Data.List.Flatten
import Purelib.Data.List.Membership
import Purelib.Data.List.OfFn.Basic
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
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentPrepared
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RequestedRuns
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RunTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Budget.Path.Aggregation
import Purelib.Integration.Path.ConjugatePathReadback
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Riemann.Readings.PrimitiveAreaBounds
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.CertifiedRunMagnitudes
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
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
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Riemann

public section

/-! Derive the parent magnitude and run requests from the retained source bank. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude

open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)

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

open Purelib.Integration.Budget.Path.Aggregation (aggregationTolerance aggregationTolerance_positive
  aggregationTolerance_area_scaled aggregationTolerance_total_scaled)

open Purelib.Data.Rat.Fraction.Compatibility

/-- The scalar slopes belong to the exact retained source inputs. -/
@[expose] def sourceSlopes (retained :
  Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index) : List Coordinate :=
  (List.ofFn (fun outer : Fin prepared.occurrences.length => List.ofFn (fun position =>
    BasisSourceCovers.primitiveSlope
      (ParentInputs.parentInput retained inputs outer
      position).sources))).flatten

/-- Valid before physical acquisition, because all run targets are capped by one. -/
@[expose] def parentMagnitude (retained :
  Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index) : Coordinate :=
  2 * (1 + PairedFragmentBlocks.maximum id
    (Sampled.sourceSlopes retained
    inputs))

/-- The parent magnitude computed from the finite retained source slopes is nonnegative. -/
theorem parentMagnitude_nonnegative (retained :
  Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index) :
    0 ≤ Sampled.parentMagnitude
      retained inputs :=
  open Purelib.Data.Rat in Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative _ _))

/-- Each original source-parent slope is bounded by the maximum of the retained source-slope list. -/
private theorem sourceSlope_le (retained :
  Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index)
    (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    BasisSourceCovers.primitiveSlope
      (ParentInputs.parentInput retained inputs outer
      position).sources ≤ PairedFragmentBlocks.maximum id
      (Sampled.sourceSlopes
      retained inputs) := by
  apply PairedFragmentBlocks.le_maximum id
  exact Data.List.mem_flatten_of_mem (Data.List.OfFn.Basic.mem_ofFn.mpr ⟨outer, rfl⟩) (Data.List.OfFn.Basic.mem_ofFn.mpr
    ⟨position, rfl⟩)

/-- Each original source-parent run magnitude is bounded by the common pre-acquisition parent magnitude. -/
theorem runMagnitude_le (retained : Preparation.CommonBasisPreparation
  prepared) (inputs : retained.Inputs index)
    (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    2 * (1 + BasisSourceCovers.primitiveSlope
      (ParentInputs.parentInput retained inputs outer
      position).sources) ≤
      Sampled.parentMagnitude
      retained inputs :=
  open Purelib.Data.Rat in Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct le_rfl
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.sourceSlope_le
    retained inputs outer position)) (by decide)

/-- Every original source-parent slope is bounded by the common parent magnitude. -/
theorem sourceMagnitude_le (retained :
  Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index)
    (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    BasisSourceCovers.primitiveSlope
      (ParentInputs.parentInput retained inputs outer
      position).sources ≤
      Sampled.parentMagnitude
      retained inputs := by
  have slopeNN :=
    BasisSourceCovers.primitiveSlope_nonnegative
    (ParentInputs.parentInput retained inputs outer position).sources
  have step : BasisSourceCovers.primitiveSlope
    (ParentInputs.parentInput retained inputs outer position).sources
    ≤
      BasisSourceCovers.primitiveSlope
        (ParentInputs.parentInput retained inputs outer
        position).sources +
        (2 + BasisSourceCovers.primitiveSlope
          (ParentInputs.parentInput retained inputs outer
          position).sources) :=
    le_add_of_nonneg_right (add_nonneg (by decide) slopeNN)
  have rearrange : BasisSourceCovers.primitiveSlope
    (ParentInputs.parentInput retained inputs outer position).sources
    +
      (2 + BasisSourceCovers.primitiveSlope
        (ParentInputs.parentInput retained inputs outer
        position).sources) =
    2 * (1 + BasisSourceCovers.primitiveSlope
      (ParentInputs.parentInput retained inputs outer
      position).sources) := by ring1
  exact (step.trans_eq rearrange).trans
    (Sampled.runMagnitude_le
    retained inputs outer position)

/-- The prepared source total at each original parent position satisfies the common coefficient-weighted magnitude
bound. -/
theorem source_uniform_bounded (sample :
  Connection.CommonBasisRequest.Sampled fans coefficients radialDepth)
  (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
    (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.ConjugatePathReadback.conjugateDiagonal
      (ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
      comparisons outer position).weighted.source.total)
      (Sampled.parentMagnitude
        retained inputs * Readings.PreparedObservationCoercivity.coefficientNormSq coefficients) := open Algebra
        in open Data in open Data.Rat in by
  have bounded := SourceRuns.SourceRun.cached_source_bounded
    (ParentPrepared.CommonBasisRequest.Sampled.parentPrepared sample
    comparisons outer position).weighted
  have massNN : 0 ≤ Readings.PreparedObservationCoercivity.coefficientNormSq coefficients :=
    FiniteSum.Fin.sumFin_zero.symm.trans_le
    (FiniteSum.Rational.Order.Positivity.sumFin_mono (fun _ : Fin genus => (0 :
      Coordinate)) _
      (fun row => Gaussian.Basic.Canonical.normSq_nonneg (coefficients row)))
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Sampled.sourceMagnitude_le
    retained inputs outer position) massNN
  exact ⟨bounded.1.trans paid, bounded.2.trans paid⟩

/-- Build each actual source-owned run request from a component target.
Fragment counts and the minimum depth are supplied by the retained geometry. -/
@[expose] def parentRunRequest (retained :
  Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index)
    (outer : Fin prepared.occurrences.length)
    (position : Fin (ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length)
    (fragmentCount : Nat) (requested : Coordinate) (positive : 0 < requested)
      (minimum : Nat) :
    RequestedRuns.RunRequest
      (ParentIndices.occurrenceAt prepared.occurrences outer)
      (ParentInputs.parentInput retained inputs outer
        position).sources fragmentCount
      (HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
        prepared outer
        (Sampled.parentMagnitude
        retained inputs) requested) minimum :=
  RequestedRuns.RunRequest.build _ _ fragmentCount _

      (HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget_positive
      outer
      (parentMagnitude_nonnegative
      retained inputs) positive) minimum

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
