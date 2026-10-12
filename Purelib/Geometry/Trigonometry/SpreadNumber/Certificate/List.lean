module

public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.List.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

/-!
# Divine Proportions, Examples 2.2--2.5

The source describes square, spread, and square-spread numbers by counting an
entire finite field.  This project does not enumerate an ambient carrier.
Instead, the displayed tables are retained as explicit finite witness rows:
every listed entry carries the root which certifies it, the list is proved
duplicate-free, and its displayed length is checked by the kernel.

Exercise 2.3 is represented by the finite algebra behind the usual count.  A
square-spread value is exactly the first-coordinate square of a point on the
unit circle.  Away from the two boundary values, a supplied pair of roots
gives the four independent sign choices.  The final formulas for primes of
the forms `4l+1` and `4l+3` are finite natural-number calculations; no finite
cardinal, carrier enumeration, or selected square root is introduced.
-/

@[expose] public section

namespace Purelib.Geometry.Trigonometry.SpreadNumber.Certificate.List

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

section

set_option genInjectivity false in
/-- A proposed spread value with an explicit candidate square witness.

The record retains the value and root; a table certificate separately checks that the residual vanishes. -/
structure SpreadRow (R : Type*) where
  /-- The proposed spread value. -/ value : R
  /-- The displayed candidate square root of `value*(1-value)`. -/ root : R

constructive_injectivity SpreadRow

set_option genInjectivity false in
/-- A proposed square-spread value with its two explicit candidate roots.

The roots witness the value and its spread radicand when the associated residual pair vanishes. -/
structure SquareSpreadRow (R : Type*) where
  /-- The proposed square-spread value. -/ value : R
  /-- The displayed candidate square root of the value. -/ squareRoot : R
  /-- The displayed candidate square root of `value*(1-value)`. -/ spreadRoot : R

constructive_injectivity SquareSpreadRow

/-- The difference between the spread radicand and its proposed witness square. -/
def spreadResidual {R : Type*} [One R] [Sub R] [Mul
  R] [Pow R Nat]
    (row : SpreadRow R) : R :=
  row.value * (1 - row.value) - row.root ^ 2

/-- The two residuals checking the value square and the spread-radicand square. -/
def squareSpreadResidual {R : Type*} [One R] [Sub R]
  [Mul R] [Pow R Nat]
    (row : SquareSpreadRow R) : R × R :=
  (row.value - row.squareRoot ^ 2,
    row.value * (1 - row.value) - row.spreadRoot ^ 2)

/-- A displayed spread table with an explicit witness in each row. -/
def SpreadTableCertified {R : Type*}
    [Zero R] [One R] [Sub R] [Mul R] [Pow R Nat] [DecidableEq R]
    (rows : List (SpreadRow R)) (values : List R) (count : Nat) :
      Prop :=
  List.map Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadRow.value rows = values ∧
    List.map spreadResidual rows = List.replicate rows.length 0 ∧
    values.Nodup ∧ values.length = count

/-- A displayed square-spread table with both roots explicit. -/
def SquareSpreadTableCertified {R : Type*}
    [Zero R] [One R] [Sub R] [Mul R] [Pow R Nat] [DecidableEq R]
    (rows : List (SquareSpreadRow R)) (values : List R) (count :
      Nat) : Prop :=
  List.map Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadRow.value rows = values ∧
    List.map squareSpreadResidual rows =
      List.replicate rows.length (0, 0) ∧
    values.Nodup ∧ values.length = count

end

end Purelib.Geometry.Trigonometry.SpreadNumber.Certificate.List

end
