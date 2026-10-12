module
import Purelib.Data.List.OfFn.Basic
import Purelib.Data.List.Membership
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonParentPlans
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedBasisBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Connection
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Budget.Path.Aggregation
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SelectedSlopeBound
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
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
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank

open Purelib.Curves

open Purelib.Geometry

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-! A fixed parent magnitude from the original covers, before numerical acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FixedSourceMagnitude

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

/-- Fixed before the numerical index, common-parent request, or physical mesh. -/
def fixedParentMagnitude (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) : Coordinate :=
  2 * (1 +
    Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
    retained.anchors retained.sources)

/-- The magnitude ceiling computed from the fixed retained source bank is nonnegative. -/
theorem fixedParentMagnitude_nonnegative (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) :
    0 ≤
      fixedParentMagnitude
      retained :=
  open Purelib.Data.Rat in Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg (by decide)

      (Samples.weightedSourceSlopeMaximum_nonnegative
      retained.anchors retained.sources))

/-- Every source slope in a retained parent input is bounded by the fixed source-bank magnitude. -/
theorem parentInput_slope_le_fixed (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index)
    (outer : Fin prepared.occurrences.length)
    (position : Fin (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.occurrenceAt prepared.occurrences
      outer).compared.entered.cache.parents.length) :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentInputs.parentInput retained inputs outer
      position).sources ≤

        Charts.Reciprocal.Disk.Basis.WeightedResampling.BasisCommonParentBank.Samples.weightedSourceSlopeMaximum
        retained.anchors retained.sources := by
  exact (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SelectedSlopeBound.SelectedInput.transport_slope
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex_read prepared outer position)
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.NumericalSelection.NumericalBank.select retained.anchors
      retained.sources inputs
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.ParentIndices.parentIndex prepared outer position))).trans_le
    (Hyperelliptic.Charts.Reciprocal.Disk.Basis.SelectedSlopeBound.NumericalBank.select_slope_le retained.anchors
      retained.sources inputs _)

/-- A finite maximum is bounded by a nonnegative ceiling that bounds each member. -/
private theorem maximum_le (values : List Normalization.InverseRootPolynomial.Coordinate) {bound :
  Normalization.InverseRootPolynomial.Coordinate} (nonnegative : 0 ≤ bound)
    (bounded : ∀ value ∈ values, value ≤ bound) :
      Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum id values ≤ bound := by
  induction values with
  | nil => exact nonnegative
  | cons first rest ih =>
      exact Fraction.Order.Basic.max_le (bounded first (List.mem_cons_self ..))
        (ih (fun value member => bounded value (List.mem_cons_of_mem first member)))

/-- A bound on every entry of every original block also bounds every entry of the flattened list. -/
private theorem flatten_bounded (blocks : List (List Normalization.InverseRootPolynomial.Coordinate)) {bound :
  Normalization.InverseRootPolynomial.Coordinate}
    (bounded : ∀ block ∈ blocks, ∀ value ∈ block, value ≤ bound) :
    ∀ value ∈ blocks.flatten, value ≤ bound := by
  induction blocks with
  | nil => intro value member; cases member
  | cons first rest ih =>
      intro value member
      rcases Data.List.Membership.mem_append.mp member with here | later
      · exact bounded first (List.mem_cons_self ..) value here
      · exact ih (fun block present => bounded block (List.mem_cons_of_mem first present)) value later

/-- Refining the numerical input index does not increase this fixed ceiling. -/
theorem parentMagnitude_le_fixed (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) (inputs :
  retained.Inputs index) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.SourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude
      retained inputs ≤
      fixedParentMagnitude
      retained := open Purelib.Data.Rat in by
  apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct _ (by
      decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  apply Fraction.Order.Arithmetic.add_le_add_direct le_rfl
  apply Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FixedSourceMagnitude.CommonBasisRequest.Sampled.maximum_le _
    (Samples.weightedSourceSlopeMaximum_nonnegative
    retained.anchors retained.sources)
  apply
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FixedSourceMagnitude.CommonBasisRequest.Sampled.flatten_bounded
  intro block present value inside
  obtain ⟨outer, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp present
  obtain ⟨position, rfl⟩ := Data.List.OfFn.Basic.mem_ofFn.mp inside
  exact
    parentInput_slope_le_fixed
    retained inputs outer position

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FixedSourceMagnitude
