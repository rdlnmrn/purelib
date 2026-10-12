module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcSamples
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.InverseRootPolynomial
public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ArcArea
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalBoundaryArea
import Init.Prelude
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalPrimitiveRibbon
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic

public section

/-!
# One retained cap comparison bank for a complete reciprocal parent

Prepare every original reciprocal cell once, sharing the global cap data.
The finite maximum and parent-wide integral/area scales are cached before
choosing a refinement index. Later evaluations consume the existing source
and reciprocal area records instead of rebuilding their primitive paths.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank

open Purelib

open Purelib.Approximation.Rational

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk

open Purelib.Data.Rat

open Purelib.Riemann.Branches

open Purelib.Riemann.Normalization

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Gaussian Coordinate)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalCover (Cell Cells)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (ParameterEdge)
open Purelib.Data.Gaussian.Basic.Canonical

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {differential :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {parent : Purelib.Riemann.Integration.PreparedSubdivisionModelCore.CenteredEdge curve differential}
  {patch : Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility.PreparedPatch parent} {data :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.UniformReciprocalModels.Data patch count}
  {regular : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap}

set_option genInjectivity false in
/-- The original reciprocal cells' retained cap comparison data in source-parent order.

Every entry shares the original global regular cap preparation and preserves its exact covered parameter edge. -/
inductive Bank (regular : RegularBounds.Data cap) (data : UniformReciprocalModels.Data patch count) :
    List ClearSheetContinuation.Subdivision.ParameterEdge → Type
  /-- The empty original reciprocal edge list retains no cell comparisons. -/ | nil :
    Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data []
  /-- Retain the original covered cell's comparison data and the matching original parameter-edge tail. -/ | cons {edge
    : ClearSheetContinuation.Subdivision.ParameterEdge} {remaining : List
    ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
      (head : ArcSamples.Data regular cell) (tail : Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank
        regular data remaining) :
      Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data (edge :: remaining)

constructive_injectivity Bank

namespace Bank

/-- Prepare each original covered reciprocal cell once using the same retained global cap data. -/
@[expose] def build (regular : RegularBounds.Data cap) : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge}
  →
    UniformReciprocalCover.Cells data edges → Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data
      edges
  | _, .nil => .nil
  | _, .cons head tail => .cons (ArcSamples.Data.build regular head)
    (Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank.build regular tail)

/-- Take the maximum of the retained cell comparison scales.

The empty spine contributes zero; each cell contributes its cached scale
before the recursively retained tail maximum. -/
@[expose] def maximum : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} →
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges → InverseRootPolynomial.Coordinate
  | _, .nil => 0
  | _, .cons head tail => max head.scale tail.maximum

/-- Every original comparison entry in the retained bank satisfies the supplied common scale ceiling. -/
@[expose] def Bounded : {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} →
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges → InverseRootPolynomial.Coordinate →
  Prop
  | _, .nil, _ => True
  | _, .cons head tail, upper => head.scale ≤ upper ∧ tail.Bounded upper

/-- An upper bound for all retained original cell scales remains valid at a larger ceiling. -/
theorem bounded_mono {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (bank :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges) {small large :
  InverseRootPolynomial.Coordinate}
    (bounded : bank.Bounded small) (order : small ≤ large) : bank.Bounded large := by
  induction bank with
  | nil => trivial
  | cons head tail ih => exact ⟨bounded.1.trans order, ih bounded.2⟩

/-- The retained bank's maximum comparison scale is nonnegative.

Every cell scale is nonnegative, and the empty bank contributes zero. -/
theorem maximum_nonnegative {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (bank :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges) : 0 ≤ bank.maximum := by
  cases bank with
  | nil => exact le_rfl
  | cons head tail => exact head.scale_nonnegative.trans (Fraction.Order.Basic.le_max_left _ _)

/-- The retained finite maximum bounds every cell comparison scale.

The head bound and the transported tail bounds certify the complete
dependent comparison spine. -/
theorem maximum_bounded {edges : List ClearSheetContinuation.Subdivision.ParameterEdge} (bank :
  Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Bank regular data edges) : bank.Bounded bank.maximum := by
  induction bank with
  | nil => trivial
  | cons head tail ih =>
    exact ⟨Fraction.Order.Basic.le_max_left _ _, tail.bounded_mono ih (Fraction.Order.Basic.le_max_right _ _)⟩

end Bank

set_option genInjectivity false in
/-- Fixed whole-parent integral, arc-area and boundary-area comparison scales.

The original source slope and common cell scale remain cached before choosing any later refinement stage. -/
structure Budget (data : UniformReciprocalModels.Data patch count) where
  /-- The retained common ceiling on the original cell comparison scales. -/ scale : InverseRootPolynomial.Coordinate
  /-- The retained common comparison scale is nonnegative. -/ nonnegative : 0 ≤ scale
  /-- The cached original source parent movement slope. -/ slope : InverseRootPolynomial.Coordinate
  /-- The cached slope is exactly the original source model's slope. -/ slope_eq : slope = data.sourceSlope
  /-- The cached full inverse-arc area comparison scale. -/ areaScale : InverseRootPolynomial.Coordinate
  /-- The area scale keeps the original common comparison scale and source slope factors. -/ areaScale_eq : areaScale =
    scale * (144 * slope + 160 * scale)
  /-- The cached full boundary-area comparison scale including endpoint contributions. -/ boundaryAreaScale :
    InverseRootPolynomial.Coordinate
  /-- The boundary-area scale combines twice the original arc scale and its retained endpoint correction cost. -/
    boundaryAreaScale_eq : boundaryAreaScale = 2 * areaScale + 64 * scale * (slope + scale)

constructive_injectivity Budget

namespace Budget

/-- Cache the original common cell scale, source slope and complete parent area comparison costs. -/
@[expose] def build (data : UniformReciprocalModels.Data patch count) (scale : InverseRootPolynomial.Coordinate)
  (nonnegative : 0 ≤ scale) : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Budget data :=
  let slope := data.sourceSlope
  let areaScale := scale * (144 * slope + 160 * scale)
  ⟨scale, nonnegative, slope, rfl, areaScale, rfl, 2 * areaScale + 64 * scale * (slope + scale), rfl⟩

/-- The cached original source slope is nonnegative. -/
theorem slope_nonnegative (budget : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Budget data) : 0 ≤
  budget.slope := by
  rw [budget.slope_eq]
  exact data.sourceSlope_nonnegative

/-- The retained whole-parent arc-area comparison scale is nonnegative. -/
theorem areaScale_nonnegative (budget : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Budget data) : 0 ≤
  budget.areaScale := by
  rw [budget.areaScale_eq]
  exact Fraction.Order.Arithmetic.mul_nonneg_direct budget.nonnegative
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) budget.slope_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) budget.nonnegative))

/-- The retained whole-parent boundary-area scale is nonnegative. -/
theorem boundaryAreaScale_nonnegative (budget : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Budget data) : 0
  ≤ budget.boundaryAreaScale := by
  rw [budget.boundaryAreaScale_eq]
  exact add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) budget.areaScale_nonnegative)
    (Fraction.Order.Arithmetic.mul_nonneg_direct
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) budget.nonnegative)
      (add_nonneg budget.slope_nonnegative budget.nonnegative))

/-- Every original cell bounded by the retained common scale has its area scale bounded by the cached parent budget. -/
theorem areaScale_le (budget : Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank.Budget data) {edge :
  ClearSheetContinuation.Subdivision.ParameterEdge} {cell : UniformReciprocalCover.Cell data edge}
    (comparison : ArcSamples.Data regular cell) (bounded : comparison.scale ≤ budget.scale) :
    ArcArea.Data.areaScale comparison ≤ budget.areaScale := by
  rw [ArcArea.Data.areaScale, budget.areaScale_eq, budget.slope_eq]
  exact Fraction.Order.Arithmetic.mul_le_mul_direct bounded
    (add_le_add le_rfl (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct bounded (by decide +kernel)))
    (add_nonneg (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) data.sourceSlope_nonnegative)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide +kernel) comparison.scale_nonnegative)) budget.nonnegative

end Budget

/-- Increasing the original scale increases its quarter-radius bound at every fixed finite stage. -/
theorem quarterRadius_mono {first last : InverseRootPolynomial.Coordinate} (order : first ≤ last) (index : Nat) :
    Geometric.Basic.quarterRadius first index ≤ Geometric.Basic.quarterRadius last index := by
  rw [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide : (0 : InverseRootPolynomial.Coordinate) ≤ 1 / 4) _)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.ParentBank
