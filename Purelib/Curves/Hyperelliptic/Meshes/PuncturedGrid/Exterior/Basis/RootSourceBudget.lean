module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningBudget
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.FixedSourceMagnitude
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Integration.Budget.Trace.Family
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathParentCaches
import Purelib.Riemann.Periods.PreparedGridPeriodPrograms
import Purelib.Riemann.RootContinuation.PreparedGridRootClosure
import Purelib.Tactic.Ring

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest

open Purelib.Data.Rat.Fraction.Order

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Pay retained root restoration before numerical and physical acquisition. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget

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

open Purelib.Data.Rat.Fraction.Compatibility

variable (sample : Connection.CommonBasisRequest.Sampled fans
  coefficients radialDepth) (comparisons :
  CommonPreparedComparison.CommonBasisRequest.Sampled.PreparedComparisons
  sample)
  {faceIndex : Nat} (banks : PhysicalRunEntries
    retained inputs coefficients faceIndex)

/-- A positive weighted allowance is no greater than its target when the weight is nonnegative. -/
private theorem allowance_le_target {weight target : Coordinate} (weightNN : 0 ≤
  weight) (positive : 0 < target) :
    Rational.Budget.Weighted.allowance target weight ≤ target := by
  have denominatorPositive : 0 < weight + 1 := Arithmetic.add_pos_of_nonneg_of_pos_direct weightNN (by
    decide)
  have allowanceNN := (Rational.Budget.Weighted.allowance_positive positive weightNN).le
  have bound := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show 1 ≤ weight + 1 from (Fraction.zero_add (1 : Coordinate)).symm.trans_le
      (Arithmetic.add_le_add_direct weightNN (Basic.le_refl _))) allowanceNN
  rw [Fraction.Field.mul_one_direct] at bound
  exact bound.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')

/-- The retained source allocation is bounded by the positive original source target. -/
theorem sourceAllowance_le_target (positive : 0 < target) : request.allocation.allowance ≤ target := by
  rw [request.allocation.allowance_eq]
  exact (Basic.min_le_right ..).trans
    (Sampled.allowance_le_target
    (Arithmetic.mul_nonneg_direct (by decide) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
      positive)

/-- The root displacement ceiling depends only on the original covers. -/
def fixedRootMagnitude (retained : Preparation.CommonBasisPreparation
  prepared) : Coordinate :=
  2 *
    (FixedSourceMagnitude.CommonBasisRequest.Sampled.fixedParentMagnitude
    retained + 34)

/-- The root-displacement ceiling computed from the fixed original covers is nonnegative. -/
theorem fixedRootMagnitude_nonnegative (retained :
  Preparation.CommonBasisPreparation prepared) :
    0 ≤ Sampled.fixedRootMagnitude
      retained :=
  Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (FixedSourceMagnitude.CommonBasisRequest.Sampled.fixedParentMagnitude_nonnegative
    retained) (by decide +kernel))

/-- For a positive source target capped by one, the retained root magnitude fits the fixed original-cover ceiling. -/
theorem rootParentMagnitude_le_fixed (positive : 0 < target) (small : target ≤ 1) :
    RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude
      (request := request) (inputs := inputs) ≤
      Sampled.fixedRootMagnitude
      retained := by
  have square := Arithmetic.pow_le_pow_direct request.allocation.positive.le
    ((sourceAllowance_le_target
    positive).trans small) 2
  have scaled := Arithmetic.mul_le_mul_of_nonneg_left_direct square (by
      decide +kernel : (0 : Coordinate) ≤ 34)
  have scaled' : 34 * request.allocation.allowance^2 ≤ 34 := scaled.trans_eq (by ring1)
  exact Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct
      (FixedSourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude_le_fixed
      retained inputs) scaled') (by decide)

/-- Coefficient- and index-independent weight for all root-restoration errors. -/
def fixedRootSourceWeight (retained :
  Preparation.CommonBasisPreparation prepared) : Coordinate :=
  (16 * (prepared.occurrences.length : Coordinate)^4 *
    Sampled.componentMagnitude
    prepared 1 *
    Sampled.componentMagnitude
      prepared
      (Sampled.fixedRootMagnitude
      retained)) * 68

/-- The coefficient-independent source-restoration weight computed on the original covers is nonnegative. -/
theorem fixedRootSourceWeight_nonnegative (retained :
  Preparation.CommonBasisPreparation prepared) :
    0 ≤
      fixedRootSourceWeight
      retained :=
  Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))

      (Sampled.componentMagnitude_nonnegative
      (by decide)))

      (Sampled.componentMagnitude_nonnegative
      (fixedRootMagnitude_nonnegative
      retained))) (by decide +kernel)

/-- The source error decays quadratically in the original requested target,
with a weight fixed before any numerical or physical refinement. -/
theorem rootSourceCost_le_target (positive : 0 < target) (small : target ≤ 1) :
    RootJoiningBudget.CommonBasisRequest.Sampled.rootSourceCost
      (request := request) (inputs := inputs) ≤
      fixedRootSourceWeight
      retained * target^2 := by
  have componentLe := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (rootParentMagnitude_le_fixed
    (request := request) (inputs := inputs) positive small)
    (PairedFragmentBlocks.maximum_nonnegative
      (fun occurrence :
        SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
        regular domains differential =>
        (occurrence.compared.entered.cache.parents.length : Coordinate)^2)
          prepared.occurrences)
  have firstNN : 0 ≤ 16 * (prepared.occurrences.length : Coordinate)^4 *
    Sampled.componentMagnitude
    prepared 1 :=
    Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
        (Sampled.componentMagnitude_nonnegative
        (by decide))
  have factorLe := Arithmetic.mul_le_mul_of_nonneg_left_direct componentLe firstNN
  have sourceLe := Arithmetic.mul_le_mul_of_nonneg_right_direct factorLe
    (Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
      Coordinate) ≤ 68) (Arithmetic.sq_nonneg_direct
      request.allocation.allowance))
  have square := Arithmetic.pow_le_pow_direct request.allocation.positive.le
    (sourceAllowance_le_target
    positive) 2
  have paid := Arithmetic.mul_le_mul_of_nonneg_left_direct square
    (fixedRootSourceWeight_nonnegative
    retained)
  exact sourceLe.trans ((show
    (16 * (prepared.occurrences.length : Coordinate)^4 *
      Sampled.componentMagnitude
      prepared 1 *

        Sampled.componentMagnitude
        prepared
        (fixedRootMagnitude
        retained)) * (68 * request.allocation.allowance^2) =

        fixedRootSourceWeight
        retained * request.allocation.allowance^2 by
        unfold
          fixedRootSourceWeight;
          ring1).trans_le paid)

/-- An arbitrarily small root budget is paid by a target chosen on the fixed covers. -/
def rootSourceTarget (retained : Preparation.CommonBasisPreparation
  prepared) (rootAllowance : Coordinate) : Coordinate :=
  min 1 (Rational.Budget.Weighted.allowance (8 * rootAllowance^2)
    (Sampled.fixedRootSourceWeight
    retained))

/-- A positive root allowance gives a positive fixed-cover source target. -/
theorem rootSourceTarget_positive (retained :
  Preparation.CommonBasisPreparation prepared) {rootAllowance :
  Coordinate}
    (positive : 0 < rootAllowance) : 0 <
      Sampled.rootSourceTarget
      retained rootAllowance :=
  Basic.lt_min (by decide) (Rational.Budget.Weighted.allowance_positive
    (Arithmetic.mul_pos_direct (by decide) (Arithmetic.pow_pos_direct positive 2))
      (fixedRootSourceWeight_nonnegative
      retained))

/-- A positive source target below the fixed-cover ceiling pays the retained source-restoration cost. -/
theorem rootSourceCost_paid {rootAllowance : Coordinate} (positive : 0 < target)
    (targetPaid : target ≤
      Sampled.rootSourceTarget
      retained rootAllowance) :
    RootJoiningBudget.CommonBasisRequest.Sampled.rootSourceCost
      (request := request) (inputs := inputs) ≤ 8 * rootAllowance^2 := by
  have small : target ≤ 1 := targetPaid.trans (Basic.min_le_left ..)
  have square : target^2 ≤ target :=
    (show target^2 = target * target by ring1).trans_le
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct small positive.le).trans_eq
        (Fraction.Field.mul_one_direct _))
  have allowanceLe := square.trans (targetPaid.trans (Basic.min_le_right ..))
  exact
    (rootSourceCost_le_target
    positive small).trans
    ((Arithmetic.mul_le_mul_of_nonneg_left_direct allowanceLe
      (fixedRootSourceWeight_nonnegative
      retained)).trans
      (Rational.Budget.Weighted.mul_allowance_le
        (Arithmetic.mul_nonneg_direct (by decide) (Arithmetic.sq_nonneg_direct
          rootAllowance))
          (fixedRootSourceWeight_nonnegative
          retained)))

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget
