module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.LinearAlgebra.Gaussian.Energy
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Integration.Path.IncrementArea
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.PreparedObservationCoercivity
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.LinearOrder
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring
meta import Mathlib.Tactic.Linter.Lint

open Purelib

open Purelib.Approximation.Rational.Budget

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveBounds

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveParentArea.CommonPrimitivePlans

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Data.Rat

open Purelib.Integration.Path

open Purelib.LinearAlgebra.Gaussian.Energy

open Purelib.Riemann.Normalization

open Purelib.Riemann.Readings

public section

/-! A requested parent-area allowance selects every primitive threshold
before sampling and certifies the cached complete path discrepancy. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover Cell)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalRootChannels (RootModel)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_sub sumFin_congr)
open Purelib.Riemann.Readings.PreparedObservationCoercivity (coefficientNormSq)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations (BasisSourceCovers BasisSourceLocations)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover (BasisCommonCover BasisCommonInterval)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition (CommonPrimitivePlans)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveAcquisition.CommonPrimitivePlans (Blocks)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy (RegularBasisPolynomials)

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {covers :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceCovers parent}
  {index : Nat} {box : Purelib.Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples (DyadicSample)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {cover : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover.Cover data} {target :
  Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {floor : Nat}

variable {minimum : Nat} {common :
  Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonCover.BasisCommonCover cover covers minimum}

set_option genInjectivity false in
/-- A paid common-interval primitive schedule controlling the complete original source/pullback area discrepancy.

The shared slope, interval count and squared allowance fix one tolerance before the original chart and source reading
stages are chosen. -/
structure CommonPrimitiveRequest (regular : RegularBounds.Data cap)
    (common : CommonCover.BasisCommonCover cover covers minimum) (allowance : InverseRootPolynomial.Coordinate) (floor :
      Nat) where
  /-- The cached primitive slope bound of the original basis source covers. -/ slope : InverseRootPolynomial.Coordinate
  /-- The retained slope is exactly the original source-cover primitive bound. -/ slope_eq : slope =
    BasisSourceCovers.primitiveSlope covers
  /-- The cached complete interval-count and slope area perturbation weight. -/ weight :
    InverseRootPolynomial.Coordinate
  /-- The cached weight is exactly the original quadratic and fourth-power interval-count expression. -/ weight_eq :
    weight = 2 * (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * (144 * slope + 160) +
    64 * (common.intervals.length : InverseRootPolynomial.Coordinate)^4 * (slope + 1)
  /-- The retained common primitive-reading tolerance. -/ tolerance : InverseRootPolynomial.Coordinate
  /-- The tolerance is the smaller of one and the weighted allowance for the requested squared error. -/ tolerance_eq :
    tolerance = min 1 (Weighted.allowance (allowance^2) weight)
  /-- The retained common tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- The full original interval perturbation expression is bounded by the requested squared allowance. -/ paid : 2 *
    (common.intervals.length : InverseRootPolynomial.Coordinate)^2 * tolerance *
      (144 * BasisSourceCovers.primitiveSlope covers + 160 * tolerance) +
    64 * (common.intervals.length : InverseRootPolynomial.Coordinate)^4 * tolerance * (BasisSourceCovers.primitiveSlope
      covers + tolerance) ≤ allowance^2
  /-- All original common-interval chart and source plans at the retained tolerance and floor. -/ plans :
    CommonPrimitiveAcquisition.CommonPrimitivePlans regular tolerance floor common.intervals
  /-- The cached stage paying the original complete plan bank. -/ index : Nat
  /-- The retained request stage equals the actual original plan stage. -/ index_eq : index = plans.stage

constructive_injectivity CommonPrimitiveRequest

namespace CommonPrimitiveRequest

/-- Choose the common tolerance from the original slope and interval count, prepare every retained primitive plan and
certify the full area allowance. -/
@[expose] def build (regular : RegularBounds.Data cap) (common : CommonCover.BasisCommonCover cover covers minimum)
    (allowance : InverseRootPolynomial.Coordinate) (positive : 0 < allowance) (floor : Nat) :
      CommonPrimitiveRequest regular common
      allowance floor := by
  let slope := BasisSourceCovers.primitiveSlope covers
  have slopeNonnegative : 0 ≤ slope := BasisSourceCovers.primitiveSlope_nonnegative covers
  let count : Coordinate := common.intervals.length
  have countNonnegative : 0 ≤ count := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  let firstWeight := 2 * count^2
  let lastWeight := 64 * count^4
  have firstNonnegative : 0 ≤ firstWeight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
    (Fraction.Order.Arithmetic.sq_nonneg_direct count)
  have lastNonnegative : 0 ≤ lastWeight := Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Fraction.Order.Arithmetic.pow_nonneg_direct countNonnegative 4)
  let weight := firstWeight * (144 * slope + 160) + lastWeight * (slope + 1)
  have weightNonnegative : 0 ≤ weight := add_nonneg
    (Fraction.Order.Arithmetic.mul_nonneg_direct firstNonnegative (add_nonneg
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) slopeNonnegative) (by decide +kernel)))
    (Fraction.Order.Arithmetic.mul_nonneg_direct lastNonnegative (add_nonneg slopeNonnegative (by decide)))
  have squarePositive := Fraction.Order.Arithmetic.pow_pos_direct positive 2
  let tolerance := min 1 (Weighted.allowance (allowance^2) weight)
  have tolerancePositive : 0 < tolerance := Purelib.Data.Rat.Fraction.Order.Basic.lt_min (by decide)
    (Weighted.allowance_positive squarePositive weightNonnegative)
  have small : tolerance ≤ 1 := Purelib.Data.Rat.Fraction.Order.Basic.min_le_left _ _
  have firstLe : 144 * slope + 160 * tolerance ≤ 144 * slope + 160 := by
    have le := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
        decide +kernel : (0 : InverseRootPolynomial.Coordinate) ≤ 160)
    rw [Fraction.Field.mul_one_direct] at le
    exact Fraction.Order.Arithmetic.add_le_add_direct le_rfl le
  have lastLe : slope + tolerance ≤ slope + 1 := Fraction.Order.Arithmetic.add_le_add_direct le_rfl small
  have estimate := Fraction.Order.Arithmetic.add_le_add_direct
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct firstLe (Fraction.Order.Arithmetic.mul_nonneg_direct
      firstNonnegative tolerancePositive.le))
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct lastLe (Fraction.Order.Arithmetic.mul_nonneg_direct
      lastNonnegative tolerancePositive.le))
  have paid := (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show tolerance ≤ Weighted.allowance (allowance^2) weight from Purelib.Data.Rat.Fraction.Order.Basic.min_le_right _
      _) weightNonnegative).trans
      (Weighted.mul_allowance_le squarePositive.le weightNonnegative)
  let plans := CommonPrimitivePlans.build regular tolerance tolerancePositive floor common.intervals
  refine ⟨slope, rfl, weight, rfl, tolerance, rfl, tolerancePositive, ?_, plans, plans.stage, rfl⟩
  exact estimate.trans ((show firstWeight * tolerance * (144 * slope + 160) + lastWeight * tolerance * (slope + 1) =
    weight * tolerance by ring1).trans_le paid)

variable {allowance : Purelib.Riemann.Normalization.InverseRootPolynomial.Coordinate} {polynomials :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBasisEnergy.RegularBasisPolynomials cap index box}
  {originals :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.CommonPrimitiveSamples.BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis.SourceLocations.BasisSourceLocations.SampleBank covers
    index}
  {coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus} {depth : Nat}

/-- The original requested numerical floor is no greater than the retained request stage. -/
theorem floor_le (request :
  CommonPrimitiveRequest regular common
  allowance floor) : floor ≤ request.index :=
  request.plans.floor_le.trans_eq request.index_eq.symm

/-- The actual retained common-interval source and pullback blocks on the original polynomials, sample banks,
coefficients and depth. -/
@[expose] def AcquiredBlocks (request :
  CommonPrimitiveRequest regular common
  allowance floor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) :=
  CommonPrimitivePlans.Blocks regular polynomials originals cells coefficients depth request.plans

/-- The original complete source/pullback area discrepancy obeys the requested squared allowance with its homogeneous
coefficient-norm factor. -/
theorem bounded (request :
  CommonPrimitiveRequest regular common
  allowance floor)
    (blocks : request.AcquiredBlocks polynomials originals cells coefficients depth) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (blocks.paths.map Prod.fst).flatten -
      IncrementArea.pathArea (blocks.paths.map Prod.snd).flatten) ≤ allowance^2 *
        (PreparedObservationCoercivity.coefficientNormSq coefficients)^2 :=
  (Blocks.area_bound blocks request.positive.le).trans
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct request.paid
      (Fraction.Order.Arithmetic.sq_nonneg_direct _))

set_option genInjectivity false in
/-- The certificate retains both complete path summaries and the paid error; it does not infer closure or equality of
independently chosen origins. -/
structure Acquisition (request :
  CommonPrimitiveRequest regular common
  allowance floor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) where
  /-- The actual original acquired common-interval block bank. -/ blocks : request.AcquiredBlocks polynomials originals
    cells coefficients depth
  /-- The cached summary of the complete original source path. -/ source : IncrementArea.Summary (blocks.paths.map
    Prod.fst).flatten
  /-- The cached summary of the complete original pullback path. -/ pullback : IncrementArea.Summary (blocks.paths.map
    Prod.snd).flatten
  /-- The cached signed area discrepancy of the two retained complete paths. -/ difference :
    InverseRootPolynomial.Gaussian
  /-- The retained discrepancy is the source summary area minus the pullback summary area. -/ difference_eq : difference
    = source.area - pullback.area
  /-- The cached actual area discrepancy satisfies the original paid homogeneous squared allowance. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq difference ≤ allowance^2 * (PreparedObservationCoercivity.coefficientNormSq
    coefficients)^2

constructive_injectivity Acquisition

/-- Acquire the original common-interval blocks once and retain both complete path summaries with their paid homogeneous
discrepancy bound. -/
@[expose] def acquire (request :
  CommonPrimitiveRequest regular common
  allowance floor)
    (polynomials : CapBasisEnergy.RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : LinearAlgebra.Gaussian.Energy.GaussianVector genus) (depth : Nat) (later : request.index ≤ index) :
    Acquisition request
      polynomials originals cells coefficients depth := by
  let blocks := request.plans.acquire polynomials originals cells coefficients depth (request.index_eq.symm.trans_le
    later)
  let source := blocks.sourceSummary
  let pullback := blocks.pullbackSummary
  have bound := request.bounded blocks
  rw [← source.area_eq, ← pullback.area_eq] at bound
  exact ⟨blocks, source, pullback, source.area - pullback.area, rfl, bound⟩

end CommonPrimitiveRequest
end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.Basis
