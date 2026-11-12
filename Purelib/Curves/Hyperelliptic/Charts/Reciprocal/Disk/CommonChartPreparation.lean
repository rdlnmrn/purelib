module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Data.Vector.Dependent
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Normalization.ReciprocalDiskCommonSourceCharts
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Data.Rat.Fraction.Order

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPaddedInverse

open Purelib.Data.Rat

open Purelib.Data.Vector

open Purelib.Riemann.Normalization

@[expose] public section

/-! Depth-independent comparison data for an entire retained common cover. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Coordinate)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels (Data)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cover)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCommonCover (CommonCover)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CoordinatePolynomial (CoordinateBounds)
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_succ)
variable {genus count otherCount : Nat} {curve : HyperellipticCurve genus}
  {differential other : Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {parent : Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : PreparedPatch parent}
  {otherPatch : PreparedPatch
    (recastCenteredEdge other parent)}
  {data : Data patch count} {otherData :
    Data otherPatch otherCount}
  {cover : Cover data} {otherCover :
    Cover otherData}
  (regular : RegularBounds.Data cap) (common :
    CommonCover cover otherCover)

/-- Read an original common-cover interval with its retained finite-index bound. -/
def IntervalAt (i : Fin common.intervals.length) := common.intervals[i.val]'i.isLt

set_option genInjectivity false in
/-- The two original cell comparisons and intrinsic coordinate bounds at one retained common-cover interval. -/
structure ChartPreparationAt (i : Fin common.intervals.length) where
  /-- The original first covered cell's retained regular comparison. -/ first : ArcSamples.Data regular
    (IntervalAt common i).first.cell
  /-- The original second covered cell's retained regular comparison. -/ second : ArcSamples.Data regular
    (IntervalAt common i).second.cell
  /-- The intrinsic reciprocal-coordinate bounds for this exact first retained cell. -/ coordinates :
    CoordinateBounds first

constructive_injectivity ChartPreparationAt

/-- A dependent vector of preparations indexed by the original common-cover intervals. -/
def ChartPreparations := DependentVector
  (ChartPreparationAt regular common)

/-- Combine the original interval coordinate slopes and common arc bound into the retained full-cover error scale. -/
def chartGeometricScale (arcScale : Coordinate) (entries :
  ChartPreparations regular common) : Coordinate :=
  (common.intervals.length : Coordinate) * sumFin (fun i => 4 * arcScale *
    ((entries.get i).coordinates.slope + 4)^2)

set_option genInjectivity false in
/-- Cached depth-independent chart comparisons for an original common cover.

The entries retain both source cells, a shared padded coefficient bound and the exact finite geometric scale, without
selecting any sampling stage. -/
structure ChartPreparation where
  /-- The cached comparison preparation at every original common-cover interval. -/ entries :
    ChartPreparations regular common
  /-- The retained padded inverse bounds shared by both original differentials. -/ bounds :
    UniformBounds regular.padded
  /-- The cached common squared coefficient ceiling for the two original cap primitives. -/ arcScale :
    Coordinate
  /-- The arc ceiling is sixteen times the square of the larger original coefficient bound. -/ arcScale_eq : arcScale =
    16 * (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other))^2
  /-- The cached full-cover geometric discrepancy scale. -/ scale : Coordinate
  /-- The scale is exactly the original interval-count weighted sum of retained coordinate ceilings. -/ scale_eq : scale
    = chartGeometricScale regular common arcScale
    entries
  /-- The retained full-cover geometric scale is nonnegative. -/ nonnegative : 0 ≤ scale

constructive_injectivity ChartPreparation

/-- A finite sum of nonnegative original rational entries is nonnegative. -/
private theorem sum_nonnegative {n : Nat} (values : Fin n → Coordinate) (bounded : ∀ i, 0 ≤ values
  i) : 0 ≤ sumFin values := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [sumFin_succ]; exact add_nonneg (bounded 0) (ih _ (fun i => bounded i.succ))

/-- A finite sum of nonnegative original rational entries is nonnegative. -/
theorem sum_nonnegative_for_chart {n : Nat} (values : Fin n → Coordinate) (bounded : ∀ i, 0 ≤
  values i) : 0 ≤ sumFin values := by
  induction n with
  | zero => exact le_rfl
  | succ n ih => rw [sumFin_succ]; exact add_nonneg (bounded 0) (ih _ (fun i => bounded i.succ))

/-- No dyadic vertices or polynomial sampling stage is chosen here. -/
def ChartPreparation.build : ChartPreparation regular
  common := by
  let entries : ChartPreparations regular common :=
    DependentVector.ofFn (fun i =>
    let first := ArcSamples.Data.build regular
      (IntervalAt common i).first.cell
    let second := ArcSamples.Data.build regular
      (IntervalAt common i).second.cell
    ⟨first, second, CoordinateBounds.build first⟩)
  let bounds := UniformBounds.build regular.padded
  let arcScale := 16 * (max (bounds.coefficientUpper differential) (bounds.coefficientUpper other))^2
  have arcNonnegative : 0 ≤ arcScale := Arithmetic.mul_nonneg_direct (by decide +kernel)
    (Arithmetic.sq_nonneg_direct _)
  let scale := chartGeometricScale regular common
    arcScale entries
  have nonnegative : 0 ≤ scale := Arithmetic.mul_nonneg_direct (Fraction.Cast.Order.natCast_le_direct
    (Nat.zero_le _))
    (sum_nonnegative_for_chart _ (fun _ =>
      Arithmetic.mul_nonneg_direct (Arithmetic.mul_nonneg_direct (by decide)
      arcNonnegative) (Arithmetic.sq_nonneg_direct _)))
  exact ⟨entries, bounds, arcScale, rfl, scale, rfl, nonnegative⟩

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.CommonChartPreparation
