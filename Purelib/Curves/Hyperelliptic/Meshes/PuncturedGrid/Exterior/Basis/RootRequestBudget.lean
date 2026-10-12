module
import Purelib.LinearAlgebra.Gaussian.Energy
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
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces

open Purelib.Curves

open Purelib.Geometry

open Purelib.Integration

open Purelib

open Purelib.Data.Rat

open Purelib.Riemann

@[expose] public section

/-! Bound the retained parent targets by the requested component tolerance. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootRequestBudget

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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled
  (componentMagnitude_nonnegative occurrenceTarget_positive parentTarget)

/-- The local fragment tolerance does not exceed its positive target when its magnitude bound is nonnegative. -/
private theorem local_tolerance_le_target (count : Nat) {bound target : Normalization.InverseRootPolynomial.Coordinate}
    (boundNN : 0 ≤ bound) (positive : 0 < target) :
    Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance count bound
      target ≤ target := open Purelib.Data.Rat in by
  let cost := 2 * ((count : Normalization.InverseRootPolynomial.Coordinate)^2 + 16 * (count :
    Normalization.InverseRootPolynomial.Coordinate)^4 * bound)
  have costNN : 0 ≤ cost := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Fraction.Order.Arithmetic.sq_nonneg_direct _)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      (Fraction.Order.Arithmetic.pow_nonneg_direct (Fraction.Cast.Order.natCast_le_direct (Nat.zero_le count)) 4))
      boundNN))
  have tolerancePositive :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedFragmentBlocks.fragmentLocalTolerance_positive count boundNN
    positive
  have denominatorPositive : 0 < cost + 1 := Fraction.Order.Arithmetic.add_pos_of_nonneg_of_pos_direct costNN (by
    decide)
  have multiplied := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (show 1 ≤ cost + 1 from
    (Fraction.zero_add (1 : Normalization.InverseRootPolynomial.Coordinate)).symm.trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct costNN (Fraction.Order.Basic.le_refl _))) tolerancePositive.le
  rw [Fraction.Field.mul_one_direct] at multiplied
  exact multiplied.trans_eq (Fraction.Field.div_mul_cancel_of_ne _ _ denominatorPositive.ne')

/-- The unit cap does not prevent choosing arbitrarily small component errors. -/
theorem aggregationTolerance_le_target (count : Nat) {bound target : Normalization.InverseRootPolynomial.Coordinate}
    (boundNN : 0 ≤ bound) (positive : 0 < target) :
    Budget.Path.Aggregation.aggregationTolerance count bound target ≤ target :=
  (Fraction.Order.Basic.min_le_right ..).trans
    (local_tolerance_le_target
    count boundNN positive)

/-- Both levels of the finite request hierarchy respect the original target. -/
theorem parentTarget_le_requested (outer : Fin prepared.occurrences.length) {parentBound requested :
  Normalization.InverseRootPolynomial.Coordinate}
    (boundNN : 0 ≤ parentBound) (positive : 0 < requested) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.HierarchicalRequest.CommonBasisRequest.Sampled.parentTarget
      prepared outer parentBound requested ≤ requested :=

    (aggregationTolerance_le_target
    _ boundNN
    (HierarchicalRequest.CommonBasisRequest.Sampled.occurrenceTarget_positive
    boundNN positive)).trans

      (aggregationTolerance_le_target
      _
      (HierarchicalRequest.CommonBasisRequest.Sampled.componentMagnitude_nonnegative
      boundNN) positive)

end Sampled
end CommonBasisRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Basis.RootRequestBudget
