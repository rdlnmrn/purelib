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

/-- A positive weighted allowance is no greater than its target when the weight is nonnegative. -/
private theorem allowance_le_target {weight target : Normalization.InverseRootPolynomial.Coordinate} (weightNN : 0 ≤
  weight) (positive : 0 < target) :
    Rational.Budget.Weighted.allowance target weight ≤ target := by
  have denominatorPositive : 0 < weight + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct weightNN (by
    decide)
  have allowanceNN := (Rational.Budget.Weighted.allowance_positive positive weightNN).le
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show 1 ≤ weight + 1 from (Fraction.zero_add (1 : Normalization.InverseRootPolynomial.Coordinate)).symm.trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct weightNN (Fraction.Order.Basic.le_refl _))) allowanceNN
  rw [Fraction.Field.mul_one_direct] at bound
  exact bound.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')

/-- The retained source allocation is bounded by the positive original source target. -/
theorem sourceAllowance_le_target (positive : 0 < target) : request.allocation.allowance ≤ target := by
  rw [request.allocation.allowance_eq]
  exact (Fraction.Order.Basic.min_le_right ..).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.allowance_le_target
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)))
      positive)

/-- The root displacement ceiling depends only on the original covers. -/
def fixedRootMagnitude (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) : Coordinate :=
  2 *
    (FixedSourceMagnitude.CommonBasisRequest.Sampled.fixedParentMagnitude
    retained + 34)

/-- The root-displacement ceiling computed from the fixed original covers is nonnegative. -/
theorem fixedRootMagnitude_nonnegative (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) :
    0 ≤ Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.fixedRootMagnitude
      retained :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (FixedSourceMagnitude.CommonBasisRequest.Sampled.fixedParentMagnitude_nonnegative
    retained) (by decide +kernel))

/-- For a positive source target capped by one, the retained root magnitude fits the fixed original-cover ceiling. -/
theorem rootParentMagnitude_le_fixed (positive : 0 < target) (small : target ≤ 1) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude
      (request := request) (inputs := inputs) ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.fixedRootMagnitude
      retained := by
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct request.allocation.positive.le
    ((sourceAllowance_le_target
    positive).trans small) 2
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square (by
      decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 34)
  have scaled' : 34 * request.allocation.allowance^2 ≤ 34 := scaled.trans_eq (by ring1)
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct
      (FixedSourceMagnitude.CommonBasisRequest.Sampled.parentMagnitude_le_fixed
      retained inputs) scaled') (by decide)

/-- Coefficient- and index-independent weight for all root-restoration errors. -/
def fixedRootSourceWeight (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) : Coordinate :=
  (16 * (prepared.occurrences.length : Normalization.InverseRootPolynomial.Coordinate)^4 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
    prepared 1 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
      prepared
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.fixedRootMagnitude
      retained)) * 68

/-- The coefficient-independent source-restoration weight computed on the original covers is nonnegative. -/
theorem fixedRootSourceWeight_nonnegative (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) :
    0 ≤
      fixedRootSourceWeight
      retained :=
  Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (Fraction.Order.Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))

      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      (by decide)))

      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      (fixedRootMagnitude_nonnegative
      retained))) (by decide +kernel)

/-- The source error decays quadratically in the original requested target,
with a weight fixed before any numerical or physical refinement. -/
theorem rootSourceCost_le_target (positive : 0 < target) (small : target ≤ 1) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningBudget.CommonBasisRequest.Sampled.rootSourceCost
      (request := request) (inputs := inputs) ≤
      fixedRootSourceWeight
      retained * target^2 := by
  have componentLe := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (rootParentMagnitude_le_fixed
    (request := request) (inputs := inputs) positive small)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.maximum_nonnegative
      (fun occurrence :
        SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfaceOccurrence
        regular domains differential =>
        (occurrence.compared.entered.cache.parents.length : Normalization.InverseRootPolynomial.Coordinate)^2)
          prepared.occurrences)
  have firstNN : 0 ≤ 16 * (prepared.occurrences.length : Normalization.InverseRootPolynomial.Coordinate)^4 *
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
    prepared 1 :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))
        (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
        (by decide))
  have factorLe := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct componentLe firstNN
  have sourceLe := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct factorLe
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel : (0 :
      Normalization.InverseRootPolynomial.Coordinate) ≤ 68) (Fraction.Order.Arithmetic.sq_nonneg_direct
      request.allocation.allowance))
  have square := Fraction.Order.Arithmetic.pow_le_pow_direct request.allocation.positive.le
    (sourceAllowance_le_target
    positive) 2
  have paid := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct square
    (fixedRootSourceWeight_nonnegative
    retained)
  exact sourceLe.trans ((show
    (16 * (prepared.occurrences.length : Normalization.InverseRootPolynomial.Coordinate)^4 *
      HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
      prepared 1 *

        HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
        prepared
        (fixedRootMagnitude
        retained)) * (68 * request.allocation.allowance^2) =

        fixedRootSourceWeight
        retained * request.allocation.allowance^2 by
        unfold
          fixedRootSourceWeight;
          ring1).trans_le paid)

/-- An arbitrarily small root budget is paid by a target chosen on the fixed covers. -/
def rootSourceTarget (retained : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation
  prepared) (rootAllowance : Normalization.InverseRootPolynomial.Coordinate) : Coordinate :=
  min 1 (Rational.Budget.Weighted.allowance (8 * rootAllowance^2)
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.fixedRootSourceWeight
    retained))

/-- A positive root allowance gives a positive fixed-cover source target. -/
theorem rootSourceTarget_positive (retained :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation.CommonBasisPreparation prepared) {rootAllowance :
  Normalization.InverseRootPolynomial.Coordinate}
    (positive : 0 < rootAllowance) : 0 <
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.rootSourceTarget
      retained rootAllowance :=
  Fraction.Order.Basic.lt_min (by decide) (Rational.Budget.Weighted.allowance_positive
    (Fraction.Order.Arithmetic.mul_pos_direct (by decide) (Fraction.Order.Arithmetic.pow_pos_direct positive 2))
      (fixedRootSourceWeight_nonnegative
      retained))

/-- A positive source target below the fixed-cover ceiling pays the retained source-restoration cost. -/
theorem rootSourceCost_paid {rootAllowance : Normalization.InverseRootPolynomial.Coordinate} (positive : 0 < target)
    (targetPaid : target ≤
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget.CommonBasisRequest.Sampled.rootSourceTarget
      retained rootAllowance) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningBudget.CommonBasisRequest.Sampled.rootSourceCost
      (request := request) (inputs := inputs) ≤ 8 * rootAllowance^2 := by
  have small : target ≤ 1 := targetPaid.trans (Fraction.Order.Basic.min_le_left ..)
  have square : target^2 ≤ target :=
    (show target^2 = target * target by ring1).trans_le
      ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small positive.le).trans_eq
        (Fraction.Field.mul_one_direct _))
  have allowanceLe := square.trans (targetPaid.trans (Fraction.Order.Basic.min_le_right ..))
  exact
    (rootSourceCost_le_target
    positive small).trans
    ((Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct allowanceLe
      (fixedRootSourceWeight_nonnegative
      retained)).trans
      (Rational.Budget.Weighted.mul_allowance_le
        (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (Fraction.Order.Arithmetic.sq_nonneg_direct
          rootAllowance))
          (fixedRootSourceWeight_nonnegative
          retained)))

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootSourceBudget
