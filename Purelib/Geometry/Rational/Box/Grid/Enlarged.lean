module
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
public import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
public import Purelib.Data.Rat.Grid.Index
public import Purelib.Data.Rat.Rounding.Floor
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Bounds.Diameter
import Purelib.Geometry.Rational.Box.Dimensions

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Order.Monoid.Unbundled.Basic
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Basic
import Mathlib.Order.Defs.PartialOrder
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data.Rat

open Purelib.Data.Rat.Grid

open Purelib.Data.Rat.Rounding

open Purelib.Geometry

open Purelib.Geometry.Rational.Box.Bounds

/-!
# Enlarged rational grid cells

Ambient widths and the positive retained mesh determine finite interval
counts. The original lower-left anchor selects a cell covering a small box.
-/

namespace Purelib.Geometry.Rational.Box.Grid.Enlarged

/-- The natural ceiling of the ambient horizontal width divided by the chosen mesh side. -/
@[expose] public def horizontalIntervals (ambient : Rational.Box) (side : Fraction.Rational) : Nat :=
  Floor.ceilNat (ambient.widthX / side)

/-- The natural ceiling of the ambient vertical width divided by the chosen mesh side. -/
@[expose] public def verticalIntervals (ambient : Rational.Box) (side : Fraction.Rational) : Nat :=
  Floor.ceilNat (ambient.widthY / side)

/-- The computed horizontal interval count covers the ambient width.

A positive mesh side allows scaling the canonical ceiling bound. The same
ambient width and chosen side determine the retained natural count. -/
public theorem widthX_le_intervals_mul
    (ambient : Rational.Box) {side : Fraction.Rational} (sidePositive : 0 < side) :
    ambient.widthX ≤ (Geometry.Rational.Box.Grid.Enlarged.horizontalIntervals ambient side : Nat) * side := by
  have quotientNonnegative : 0 ≤ ambient.widthX / side :=
    Fraction.Order.Arithmetic.mul_nonneg_direct ambient.widthX_nonneg
      (Fraction.Order.Field.inv_pos_direct sidePositive).le
  have ceiling := Floor.le_natCast_ceilNat_of_nonneg
    quotientNonnegative
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    ceiling sidePositive.le
  calc
    ambient.widthX = (ambient.widthX / side) * side :=
      (Fraction.Field.div_mul_cancel_of_ne ambient.widthX side
        (ne_of_gt sidePositive)).symm
    _ ≤ (Geometry.Rational.Box.Grid.Enlarged.horizontalIntervals ambient side : Nat) * side := scaled

/-- The computed vertical interval count covers the ambient height.

A positive mesh side allows scaling the canonical ceiling bound. The same
ambient height and chosen side determine the retained natural count. -/
public theorem widthY_le_intervals_mul
    (ambient : Rational.Box) {side : Fraction.Rational} (sidePositive : 0 < side) :
    ambient.widthY ≤ (Geometry.Rational.Box.Grid.Enlarged.verticalIntervals ambient side : Nat) * side := by
  have quotientNonnegative : 0 ≤ ambient.widthY / side :=
    Fraction.Order.Arithmetic.mul_nonneg_direct ambient.widthY_nonneg
      (Fraction.Order.Field.inv_pos_direct sidePositive).le
  have ceiling := Floor.le_natCast_ceilNat_of_nonneg
    quotientNonnegative
  have scaled := Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    ceiling sidePositive.le
  calc
    ambient.widthY = (ambient.widthY / side) * side :=
      (Fraction.Field.div_mul_cancel_of_ne ambient.widthY side
        (ne_of_gt sidePositive)).symm
    _ ≤ (Geometry.Rational.Box.Grid.Enlarged.verticalIntervals ambient side : Nat) * side := scaled

/-- Enlarge the retained grid cell toward increasing coordinates by one side.

The same ambient lower endpoints and bounded grid indices determine all four
endpoints. A nonnegative side certifies their order, including a zero side. -/
@[expose] public def enlargedCell
    (ambient : Rational.Box) (side : Fraction.Rational) (sideNonnegative : 0 ≤ side)
    (i : Fin (Geometry.Rational.Box.Grid.Enlarged.horizontalIntervals ambient side + 1))
    (j : Fin (Geometry.Rational.Box.Grid.Enlarged.verticalIntervals ambient side + 1)) : Rational.Box
      where
  xLower := ambient.xLower + (i.val : Nat) * side
  xUpper := ambient.xLower + ((i.val : Nat) + 1) * side + side
  yLower := ambient.yLower + (j.val : Nat) * side
  yUpper := ambient.yLower + ((j.val : Nat) + 1) * side + side
  x_valid := by
    calc
      ambient.xLower + (i.val : Nat) * side ≤
          ambient.xLower + ((i.val : Nat) + 1) * side := by
        apply add_le_add_right
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        · exact Fraction.Cast.Order.natCast_le_direct
            (m := i.val) (n := i.val + 1) (Nat.le_add_right i.val 1)
        · exact sideNonnegative
      _ ≤ ambient.xLower + ((i.val : Nat) + 1) * side + side :=
        le_add_of_nonneg_right sideNonnegative
  y_valid := by
    calc
      ambient.yLower + (j.val : Nat) * side ≤
          ambient.yLower + ((j.val : Nat) + 1) * side := by
        apply add_le_add_right
        apply Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
        · exact Fraction.Cast.Order.natCast_le_direct
            (m := j.val) (n := j.val + 1) (Nat.le_add_right j.val 1)
        · exact sideNonnegative
      _ ≤ ambient.yLower + ((j.val : Nat) + 1) * side + side :=
        le_add_of_nonneg_right sideNonnegative

/-- An enlarged grid cell has squared diagonal eight times the squared side.

Each coordinate interval spans two copies of the original mesh side. The
identity retains the ambient endpoints and the two original bounded indices. -/
public theorem enlargedCell_diagonalSq
    (ambient : Rational.Box) (side : Fraction.Rational) (sideNonnegative : 0 ≤ side)
    (i : Fin (Geometry.Rational.Box.Grid.Enlarged.horizontalIntervals ambient side + 1))
    (j : Fin (Geometry.Rational.Box.Grid.Enlarged.verticalIntervals ambient side + 1)) :
    (Geometry.Rational.Box.Grid.Enlarged.enlargedCell ambient side sideNonnegative i j).diagonalSq =
      8 * side ^ 2 := by
  dsimp only [Geometry.Rational.Box.Grid.Enlarged.enlargedCell, Rational.Box.diagonalSq]
  ring1

/-- A subbox with diagonal at most one mesh side fits inside the enlarged cell selected by its lower-left anchor.

The positive mesh and retained ambient refinement bound both grid indices and provide the coordinatewise inclusion
certificate. -/
public theorem box_refines_anchor_enlargedCell
    {ambient box : Rational.Box} {side : Fraction.Rational} (sidePositive : 0 < side)
    (refines : box.Refines ambient)
    (diagonal : box.diagonalSq ≤ side ^ 2) :
    let i := Index.coordinateIndex ambient.xLower side box.anchor.re
      (Geometry.Rational.Box.Grid.Enlarged.horizontalIntervals ambient side)
    let j := Index.coordinateIndex ambient.yLower side box.anchor.im
      (Geometry.Rational.Box.Grid.Enlarged.verticalIntervals ambient side)
    box.Refines (Geometry.Rational.Box.Grid.Enlarged.enlargedCell ambient side sidePositive.le i j) := by
  let horizontal := Geometry.Rational.Box.Grid.Enlarged.horizontalIntervals ambient side
  let vertical := Geometry.Rational.Box.Grid.Enlarged.verticalIntervals ambient side
  let i := Index.coordinateIndex ambient.xLower side box.anchor.re horizontal
  let j := Index.coordinateIndex ambient.yLower side box.anchor.im vertical
  have anchorAmbient : ambient.Contains box.anchor :=
    refines.contains box.contains_anchor
  have horizontalCover : box.anchor.re ≤
      ambient.xLower + (horizontal : Nat) * side := by
    calc
      box.anchor.re ≤ ambient.xUpper := anchorAmbient.2.1
      _ = ambient.xLower + ambient.widthX := by
        dsimp only [Rational.Box.widthX]
        ring1
      _ ≤ ambient.xLower + (horizontal : Nat) * side :=
        add_le_add_right (Geometry.Rational.Box.Grid.Enlarged.widthX_le_intervals_mul ambient sidePositive)
          ambient.xLower
  have verticalCover : box.anchor.im ≤
      ambient.yLower + (vertical : Nat) * side := by
    calc
      box.anchor.im ≤ ambient.yUpper := anchorAmbient.2.2.2
      _ = ambient.yLower + ambient.widthY := by
        dsimp only [Rational.Box.widthY]
        ring1
      _ ≤ ambient.yLower + (vertical : Nat) * side :=
        add_le_add_right (Geometry.Rational.Box.Grid.Enlarged.widthY_le_intervals_mul ambient sidePositive)
          ambient.yLower
  have horizontalMembership := Index.coordinateIndex_mem sidePositive horizontal
    anchorAmbient.1 horizontalCover
  have verticalMembership := Index.coordinateIndex_mem sidePositive vertical
    anchorAmbient.2.2.1 verticalCover
  have widths := Diameter.widths_le_of_diagonal sidePositive.le diagonal
  constructor
  · exact horizontalMembership.1
  constructor
  · calc
      box.xUpper = box.xLower + box.widthX := by
        dsimp only [Rational.Box.widthX]
        ring1
      _ ≤ (ambient.xLower + ((i.val : Nat) + 1) * side) + side :=
        add_le_add horizontalMembership.2 widths.1
  constructor
  · exact verticalMembership.1
  · calc
      box.yUpper = box.yLower + box.widthY := by
        dsimp only [Rational.Box.widthY]
        ring1
      _ ≤ (ambient.yLower + ((j.val : Nat) + 1) * side) + side :=
        add_le_add verticalMembership.2 widths.2

end Purelib.Geometry.Rational.Box.Grid.Enlarged
