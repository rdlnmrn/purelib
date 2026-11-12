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

open Purelib.Data.Rat.Fraction.Order

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

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent} {data :
    UniformReciprocalModels.Data patch count}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : RegularBounds.Data cap} {covers :
    BasisSourceCovers parent}
  {index : Nat} {box : Geometry.Rational.Box}

open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin_zero sumFin_mul_right)

open Purelib.Integration.Path.Dyadic.DyadicPrimitivePathSamples (DyadicSample)
open Purelib.Integration.Path.Dyadic.DyadicPrimitivePaths (dyadicIncrements_sub_constant pathArea_dyadicIncrements)
open Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon (dyadicArea)

variable {cover : Cover data} {target :
  Coordinate} {floor : Nat}

variable {minimum : Nat} {common :
  BasisCommonCover cover covers minimum}

set_option genInjectivity false in
/-- A paid common-interval primitive schedule controlling the complete original source/pullback area discrepancy.

The shared slope, interval count and squared allowance fix one tolerance before the original chart and source reading
stages are chosen. -/
structure CommonPrimitiveRequest (regular : RegularBounds.Data cap)
    (common : BasisCommonCover cover covers minimum) (allowance : Coordinate) (floor :
      Nat) where
  /-- The cached primitive slope bound of the original basis source covers. -/ slope : Coordinate
  /-- The retained slope is exactly the original source-cover primitive bound. -/ slope_eq : slope =
    BasisSourceCovers.primitiveSlope covers
  /-- The cached complete interval-count and slope area perturbation weight. -/ weight :
    Coordinate
  /-- The cached weight is exactly the original quadratic and fourth-power interval-count expression. -/ weight_eq :
    weight = 2 * (common.intervals.length : Coordinate)^2 * (144 * slope + 160) +
    64 * (common.intervals.length : Coordinate)^4 * (slope + 1)
  /-- The retained common primitive-reading tolerance. -/ tolerance : Coordinate
  /-- The tolerance is the smaller of one and the weighted allowance for the requested squared error. -/ tolerance_eq :
    tolerance = min 1 (Weighted.allowance (allowance^2) weight)
  /-- The retained common tolerance is strictly positive. -/ positive : 0 < tolerance
  /-- The full original interval perturbation expression is bounded by the requested squared allowance. -/ paid : 2 *
    (common.intervals.length : Coordinate)^2 * tolerance *
      (144 * BasisSourceCovers.primitiveSlope covers + 160 * tolerance) +
    64 * (common.intervals.length : Coordinate)^4 * tolerance * (BasisSourceCovers.primitiveSlope
      covers + tolerance) ≤ allowance^2
  /-- All original common-interval chart and source plans at the retained tolerance and floor. -/ plans :
    CommonPrimitivePlans regular tolerance floor common.intervals
  /-- The cached stage paying the original complete plan bank. -/ index : Nat
  /-- The retained request stage equals the actual original plan stage. -/ index_eq : index = plans.stage

constructive_injectivity CommonPrimitiveRequest

namespace CommonPrimitiveRequest

/-- Choose the common tolerance from the original slope and interval count, prepare every retained primitive plan and
certify the full area allowance. -/
@[expose] def build (regular : RegularBounds.Data cap) (common : BasisCommonCover cover covers minimum)
    (allowance : Coordinate) (positive : 0 < allowance) (floor : Nat) :
      CommonPrimitiveRequest regular common
      allowance floor := by
  let slope := BasisSourceCovers.primitiveSlope covers
  have slopeNonnegative : 0 ≤ slope := BasisSourceCovers.primitiveSlope_nonnegative covers
  let count : Coordinate := common.intervals.length
  have countNonnegative : 0 ≤ count := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _)
  let firstWeight := 2 * count^2
  let lastWeight := 64 * count^4
  have firstNonnegative : 0 ≤ firstWeight := Arithmetic.mul_nonneg_direct (by decide)
    (Arithmetic.sq_nonneg_direct count)
  have lastNonnegative : 0 ≤ lastWeight := Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.pow_nonneg_direct countNonnegative 4)
  let weight := firstWeight * (144 * slope + 160) + lastWeight * (slope + 1)
  have weightNonnegative : 0 ≤ weight := add_nonneg
    (Arithmetic.mul_nonneg_direct firstNonnegative (add_nonneg
      (Arithmetic.mul_nonneg_direct (by decide +kernel) slopeNonnegative) (by decide +kernel)))
    (Arithmetic.mul_nonneg_direct lastNonnegative (add_nonneg slopeNonnegative (by decide)))
  have squarePositive := Arithmetic.pow_pos_direct positive 2
  let tolerance := min 1 (Weighted.allowance (allowance^2) weight)
  have tolerancePositive : 0 < tolerance := Basic.lt_min (by decide)
    (Weighted.allowance_positive squarePositive weightNonnegative)
  have small : tolerance ≤ 1 := Basic.min_le_left _ _
  have firstLe : 144 * slope + 160 * tolerance ≤ 144 * slope + 160 := by
    have le := Arithmetic.mul_le_mul_of_nonneg_left_direct small (by
        decide +kernel : (0 : Coordinate) ≤ 160)
    rw [Fraction.Field.mul_one_direct] at le
    exact Arithmetic.add_le_add_direct le_rfl le
  have lastLe : slope + tolerance ≤ slope + 1 := Arithmetic.add_le_add_direct le_rfl small
  have estimate := Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct firstLe (Arithmetic.mul_nonneg_direct
      firstNonnegative tolerancePositive.le))
    (Arithmetic.mul_le_mul_of_nonneg_left_direct lastLe (Arithmetic.mul_nonneg_direct
      lastNonnegative tolerancePositive.le))
  have paid := (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (show tolerance ≤ Weighted.allowance (allowance^2) weight from Basic.min_le_right _
      _) weightNonnegative).trans
      (Weighted.mul_allowance_le squarePositive.le weightNonnegative)
  let plans := CommonPrimitivePlans.build regular tolerance tolerancePositive floor common.intervals
  refine ⟨slope, rfl, weight, rfl, tolerance, rfl, tolerancePositive, ?_, plans, plans.stage, rfl⟩
  exact estimate.trans ((show firstWeight * tolerance * (144 * slope + 160) + lastWeight * tolerance * (slope + 1) =
    weight * tolerance by ring1).trans_le paid)

variable {allowance : Coordinate} {polynomials :
  RegularBasisPolynomials cap index box}
  {originals :
    BasisSourceLocations.PrimitiveBank
    covers index} {cells :
    BasisSourceLocations.SampleBank covers
    index}
  {coefficients : GaussianVector genus} {depth : Nat}

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
    (polynomials : RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : GaussianVector genus) (depth : Nat) :=
  Blocks regular polynomials originals cells coefficients depth request.plans

/-- The original complete source/pullback area discrepancy obeys the requested squared allowance with its homogeneous
coefficient-norm factor. -/
theorem bounded (request :
  CommonPrimitiveRequest regular common
  allowance floor)
    (blocks : request.AcquiredBlocks polynomials originals cells coefficients depth) :
    Data.Gaussian.Norm.Basic.normSq (IncrementArea.pathArea (blocks.paths.map Prod.fst).flatten -
      IncrementArea.pathArea (blocks.paths.map Prod.snd).flatten) ≤ allowance^2 *
        (coefficientNormSq coefficients)^2 :=
  (Blocks.area_bound blocks request.positive.le).trans
    (Arithmetic.mul_le_mul_of_nonneg_right_direct request.paid
      (Arithmetic.sq_nonneg_direct _))

set_option genInjectivity false in
/-- The certificate retains both complete path summaries and the paid error; it does not infer closure or equality of
independently chosen origins. -/
structure Acquisition (request :
  CommonPrimitiveRequest regular common
  allowance floor)
    (polynomials : RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : GaussianVector genus) (depth : Nat) where
  /-- The actual original acquired common-interval block bank. -/ blocks : request.AcquiredBlocks polynomials originals
    cells coefficients depth
  /-- The cached summary of the complete original source path. -/ source : IncrementArea.Summary (blocks.paths.map
    Prod.fst).flatten
  /-- The cached summary of the complete original pullback path. -/ pullback : IncrementArea.Summary (blocks.paths.map
    Prod.snd).flatten
  /-- The cached signed area discrepancy of the two retained complete paths. -/ difference :
    Gaussian
  /-- The retained discrepancy is the source summary area minus the pullback summary area. -/ difference_eq : difference
    = source.area - pullback.area
  /-- The cached actual area discrepancy satisfies the original paid homogeneous squared allowance. -/ bounded :
    Data.Gaussian.Norm.Basic.normSq difference ≤ allowance^2 * (coefficientNormSq
    coefficients)^2

constructive_injectivity Acquisition

/-- Acquire the original common-interval blocks once and retain both complete path summaries with their paid homogeneous
discrepancy bound. -/
@[expose] def acquire (request :
  CommonPrimitiveRequest regular common
  allowance floor)
    (polynomials : RegularBasisPolynomials cap index box)
    (originals : BasisSourceLocations.PrimitiveBank covers index) (cells : BasisSourceLocations.SampleBank covers index)
    (coefficients : GaussianVector genus) (depth : Nat) (later : request.index ≤ index) :
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
