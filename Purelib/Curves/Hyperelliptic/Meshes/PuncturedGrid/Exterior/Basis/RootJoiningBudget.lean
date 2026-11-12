module
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
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
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.PhysicalRunEntries
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.Preparation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootParentBounds
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CommonPreparedComparison
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootBoundaryEnergy.CommonBasisRequest

open Purelib.Data.Rat.Fraction.Order

open Purelib.Curves

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

@[expose] public section

/-! Pay the root joining comparison with a computed physical target. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningBudget

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

/-- Separate the physical request from the already acquired source allowance. -/
def rootJoiningFactor : Coordinate :=
  16 * (prepared.occurrences.length : Coordinate)^4 *
    HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
    prepared 1 *
    HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
      prepared
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude
      (request := request) (inputs := inputs))

/-- The coefficient-independent factor multiplying the physical and source-restoration errors is nonnegative. -/
theorem rootJoiningFactor_nonnegative :
    0 ≤ Sampled.rootJoiningFactor
      (request := request) (inputs := inputs) :=
  Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct (by decide +kernel) (Arithmetic.pow_nonneg_direct
      (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)) 4))

      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      (by decide)))

      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      (RootParentBounds.CommonBasisRequest.Sampled.rootParentMagnitude_nonnegative
      (request := request) (inputs := inputs)))

/-- Compute the part of the root-polygon error caused by the retained source-restoration allowance. -/
def rootSourceCost : Coordinate :=
  Sampled.rootJoiningFactor
    (request := request) (inputs := inputs) * (68 * request.allocation.allowance^2)

/-- Source restoration is a separate cost; refining physical runs alone does
not make it disappear. -/
theorem rootJoiningCost_split (requested : Coordinate) :
    Sampled.rootJoiningCost
      (request := request) (inputs := inputs) requested =
      Sampled.rootJoiningFactor
        (request := request) (inputs := inputs) * requested / 2 +
        Sampled.rootSourceCost
          (request := request) (inputs := inputs) := by
  unfold Sampled.rootSourceCost
    Sampled.rootJoiningCost
    Sampled.rootJoiningFactor
    HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude
    RootParentBounds.CommonBasisRequest.Sampled.rootParentError
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  rw [show (2 : Coordinate)⁻¹ = 2 * (4 :
    Coordinate)⁻¹ by decide +kernel]
  ring1

/-- Choose a positive physical target that fits both the physical energy budget and half the root-polygon budget.

The finite minimum uses the original source-dependent root factor plus one as a positive denominator. The
source-restoration cost remains a separate obligation. -/
def rootPhysicalTarget (physicalAllowance rootAllowance : Coordinate) : Coordinate
  :=
  min (16 * physicalAllowance^2)
    (16 * rootAllowance^2 /
      (Sampled.rootJoiningFactor
      (request := request) (inputs := inputs) + 1))

/-- Positive physical and root allowances give a positive computed physical target. -/
theorem rootPhysicalTarget_positive {physicalAllowance rootAllowance : Coordinate}
    (physicalPositive : 0 < physicalAllowance) (rootPositive : 0 < rootAllowance) :
    0 <
      Sampled.rootPhysicalTarget
      (request := request) (inputs := inputs) physicalAllowance rootAllowance := by
  have physicalSquare : 0 < physicalAllowance^2 := by
    simpa only [pow_two] using Arithmetic.mul_pos_direct physicalPositive physicalPositive
  have rootSquare : 0 < rootAllowance^2 := by
    simpa only [pow_two] using Arithmetic.mul_pos_direct rootPositive rootPositive
  exact Basic.lt_min (Arithmetic.mul_pos_direct (by decide) physicalSquare)
    (Field.div_pos_direct (Arithmetic.mul_pos_direct (by decide) rootSquare)
      (Arithmetic.add_pos_of_nonneg_of_pos_direct
        (rootJoiningFactor_nonnegative
        (request := request) (inputs := inputs)) (by decide)))

/-- The computed physical target fits the squared physical energy allowance. -/
theorem rootPhysicalTarget_physical_paid (physicalAllowance rootAllowance :
  Coordinate) :
    Sampled.rootPhysicalTarget
      (request := request) (inputs := inputs) physicalAllowance rootAllowance ≤ 16 * physicalAllowance^2 :=
  Basic.min_le_left ..

/-- Half the root budget pays the physical request; the other half pays the
retained source-restoration cost. -/
theorem rootPhysicalTarget_root_paid {physicalAllowance rootAllowance : Coordinate}
    (physicalPositive : 0 < physicalAllowance) (rootPositive : 0 < rootAllowance)
    (sourcePaid :
      Sampled.rootSourceCost
      (request := request) (inputs := inputs) ≤ 8 * rootAllowance ^ 2) :
    Sampled.rootJoiningCost
      (request := request) (inputs := inputs)
      (Sampled.rootPhysicalTarget
        (request := request) (inputs := inputs) physicalAllowance rootAllowance) ≤ 16 * rootAllowance^2 := by
  let factor :=
    Sampled.rootJoiningFactor
    (request := request) (inputs := inputs)
  let requested :=
    Sampled.rootPhysicalTarget
    (request := request) (inputs := inputs) physicalAllowance rootAllowance
  have factorNN : 0 ≤ factor :=
    rootJoiningFactor_nonnegative
  have denominatorPositive : 0 < factor + 1 := Arithmetic.add_pos_of_nonneg_of_pos_direct factorNN (by
    decide)
  have requestedPositive : 0 < requested :=
    rootPhysicalTarget_positive
    physicalPositive rootPositive
  have requestedLe : requested ≤ 16 * rootAllowance^2 / (factor + 1) := Basic.min_le_right ..
  have product := Arithmetic.mul_le_mul_of_nonneg_right_direct requestedLe denominatorPositive.le
  rw [Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne'] at product
  have smaller := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show factor ≤ factor + 1 from
      (Fraction.zero_add factor).symm.trans_le
        ((Arithmetic.add_le_add_right_direct
          (show (0 : Coordinate) ≤ 1 by decide) factor).trans_eq
          (Fraction.add_comm 1 factor))) requestedPositive.le
  have total : factor * requested ≤ 16 * rootAllowance^2 :=
    (show factor * requested = requested * factor by ring1).trans_le (smaller.trans product)
  have half := Arithmetic.mul_le_mul_of_nonneg_right_direct total (by decide : (0 :
    Coordinate) ≤ (2 : Coordinate)⁻¹)
  have paid := Arithmetic.add_le_add_direct half sourcePaid
  rw
    [rootJoiningCost_split]
  exact (show
    Sampled.rootJoiningFactor
    (request := request) (inputs := inputs) * requested / 2 +
    Sampled.rootSourceCost
      (request := request) (inputs := inputs) =
    factor * requested * (2 : Coordinate)⁻¹ +
      Sampled.rootSourceCost
      (request := request) (inputs := inputs) by
      rw [Fraction.Field.div_eq_mul_inv_direct]).trans_le (paid.trans_eq (by
        calc
          16 * rootAllowance^2 * (2 : Coordinate)⁻¹ + 8 * rootAllowance^2 =
            (16 * (2 : Coordinate)⁻¹ + 8) * rootAllowance^2 := by ring1
          _ = 16 * rootAllowance^2 := congrArg (fun scalar => scalar * rootAllowance^2)
            (by decide +kernel)))

/-- A later common request may decrease the physical target without increasing
any retained root-polygon cost. -/
theorem rootJoiningCost_mono {first last : Coordinate} (order : first ≤ last) :
    Sampled.rootJoiningCost
      (request := request) (inputs := inputs) first ≤
      Sampled.rootJoiningCost
        (request := request) (inputs := inputs) last := by
  rw
    [rootJoiningCost_split,
    rootJoiningCost_split]
  simp only [Fraction.Field.div_eq_mul_inv_direct]
  exact Arithmetic.add_le_add_right_direct (Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct order
      (rootJoiningFactor_nonnegative
      (request := request) (inputs := inputs)))
    (by decide : (0 : Coordinate) ≤ (2 :
      Coordinate)⁻¹)) _

/-- Any physical target below the computed target fits the root budget when the retained source-restoration cost is
paid. -/
theorem rootJoiningCost_paid_of_target_le {physicalAllowance rootAllowance requested :
  Coordinate}
    (physicalPositive : 0 < physicalAllowance) (rootPositive : 0 < rootAllowance)
    (sourcePaid :
      Sampled.rootSourceCost
      (request := request) (inputs := inputs) ≤ 8 * rootAllowance ^ 2)
    (targetPaid : requested ≤
      Sampled.rootPhysicalTarget
      (request := request) (inputs := inputs) physicalAllowance rootAllowance) :
    Sampled.rootJoiningCost
      (request := request) (inputs := inputs) requested ≤ 16 * rootAllowance^2 :=
  (Sampled.rootJoiningCost_mono
    targetPaid).trans
    (rootPhysicalTarget_root_paid
    physicalPositive rootPositive sourcePaid)

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootJoiningBudget
