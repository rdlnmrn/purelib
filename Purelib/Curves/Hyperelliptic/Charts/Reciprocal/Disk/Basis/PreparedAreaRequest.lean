module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedWeightedPairs
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedPathReadback
import Mathlib.Algebra.Ring.Defs
import Mathlib.Order.Defs.LinearOrder
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveRequest
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Path.IncrementArea
import Purelib.Tactic.Ring

open Purelib.Approximation

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib

open Purelib.Riemann

public section

/-! Select the polynomial and common-interval tolerances before sampling,
paying the complete prepared-integral/pullback area discrepancy. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility

variable {cover : Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {target :
  Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

variable {minimum : Nat} {common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers
  minimum}

set_option genInjectivity false in
/-- A paid homogeneous area request for one retained finite primitive combination.

It retains the original common primitive request, half allowance and source target together with the exact scalar
payment inequality. -/
structure BasisPreparedAreaRequest (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap)
    (common : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum) (allowance
      coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (floor : Nat) where
  /-- The cached half allowance. -/ half : Normalization.InverseRootPolynomial.Coordinate
  /-- The half allowance is exactly half the requested allowance. -/ half_eq : half = allowance / 2
  /-- The original source approximation target. -/ sourceTarget : Normalization.InverseRootPolynomial.Coordinate
  /-- The source target is the minimum of one and the weighted allowance determined by the retained primitive slope and
    half allowance. -/ sourceTarget_eq : sourceTarget = min 1
    (Rational.Budget.Weighted.allowance (half^2) (32 *
      (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers + 1)))
  /-- The original prepared common primitive request with its coefficient targets and supplied stage floor. -/ request :
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest regular common half
    sourceTarget coefficientTarget floor
  /-- The retained source and area error terms are paid by the square of the requested allowance. -/ paid : 2 * (32 *
    sourceTarget * (Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope
    covers + sourceTarget) + half^2) ≤ allowance^2

constructive_injectivity BasisPreparedAreaRequest

namespace BasisPreparedAreaRequest

/-- Prepare the original common primitive request and certify its homogeneous area payment using the retained primitive
slope. -/
@[expose] def build (regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap) (common :
  Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum)
    (allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate) (positive : 0 < allowance)
      (coefficientPositive : 0 < coefficientTarget)
    (floor : Nat) : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest.BasisPreparedAreaRequest regular
      common allowance coefficientTarget floor := by
  let half := allowance / 2
  have halfPositive : 0 < half := Fraction.Order.Field.div_pos_direct positive (by decide)
  let slope := Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope covers
  have slopeNonnegative : 0 ≤ slope :=
    Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds.BasisSourceCovers.primitiveSlope_nonnegative covers
  let weight := 32 * (slope + 1)
  have weightNonnegative : 0 ≤ weight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) (add_nonneg
    slopeNonnegative (by decide))
  let sourceTarget := min 1 (Rational.Budget.Weighted.allowance (half^2) weight)
  have sourcePositive : 0 < sourceTarget := Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
    (Rational.Budget.Weighted.allowance_positive (Fraction.Order.Arithmetic.pow_pos_direct halfPositive 2)
      weightNonnegative)
  have small : sourceTarget ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have bound := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Arithmetic.add_le_add_direct
    (le_rfl : slope ≤ slope) small)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (by
        decide +kernel : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 32) sourcePositive.le)
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show sourceTarget ≤ Rational.Budget.Weighted.allowance (half^2) weight from
      Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _ _) weightNonnegative).trans
      (Rational.Budget.Weighted.mul_allowance_le (Fraction.Order.Arithmetic.sq_nonneg_direct half) weightNonnegative)
  have sourcePaid : 32 * sourceTarget * (slope + sourceTarget) ≤ half^2 :=
    bound.trans ((show 32 * sourceTarget * (slope + 1) = weight * sourceTarget by ring1).trans_le paid)
  let request := Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedCommonRequest.BasisPreparedCommonRequest.build
    regular common half sourceTarget coefficientTarget
    halfPositive sourcePositive coefficientPositive floor
  refine ⟨half, rfl, sourceTarget, rfl, request, ?_⟩
  have combined := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Fraction.Order.Arithmetic.add_le_add_direct sourcePaid (le_rfl : half^2 ≤ half^2))
    (by decide : (0 : Normalization.InverseRootPolynomial.Coordinate) ≤ 2)
  exact combined.trans_eq (calc
    2 * (half^2 + half^2) = (half * 2)^2 := by ring1
    _ = allowance^2 := by rw [Fraction.Field.div_mul_cancel_of_ne allowance 2 (by decide)])

variable {allowance coefficientTarget : Normalization.InverseRootPolynomial.Coordinate}
  {polynomials : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
    {originals : Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index}
  {cells : Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers index}
    {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The bound is homogeneous and uses the actual cached summaries on both sides. -/
theorem bounded (budget : Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest.BasisPreparedAreaRequest
  regular common allowance coefficientTarget floor)
    (acquired : budget.request.Acquisition polynomials originals cells coefficients depth)
    {pairs :
      Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedChildPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs
      acquired} (weighted :
      PreparedWeightedPairs.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted
      pairs) :
    Data.Gaussian.Norm.Basic.normSq (weighted.integral.area - acquired.area.pullback.area) ≤ allowance^2 *
      (Readings.PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=

    (PreparedPathReadback.BasisPreparedCommonRequest.Acquisition.ChildPairs.Weighted.integral_pullback_bound
    weighted).trans (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct budget.paid
    (Fraction.Order.Arithmetic.sq_nonneg_direct _))

end BasisPreparedAreaRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.PreparedAreaRequest
