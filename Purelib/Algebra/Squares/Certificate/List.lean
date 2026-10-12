module

public import Purelib.Algebra.Field.ExplicitField

import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Algebra.Field

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

namespace Purelib.Algebra.Squares.Certificate.List

variable {K : Type*} [ExplicitField K]

section SquareSpreadTables

set_option genInjectivity false in
/-- A proposed square value with its displayed root.

This data record contains no correctness proof; its residual or a certified table checks the proposed relation. -/
structure SquareRow (R : Type*) where
  /-- The proposed square value. -/ value : R
  /-- A proposed root, whose square is checked separately against the value. -/ root : R

constructive_injectivity SquareRow

open Purelib.Algebra.Squares.Certificate.List in
/-- Subtract a proposed root square from its displayed value. -/
def squareResidual {R : Type*} [Sub R] [Pow R Nat]
    (row : SquareRow R) : R :=
  row.value - row.root ^ 2

open Purelib.Algebra.Squares.Certificate.List in
open Purelib.Algebra.Squares in
/-- Certify a finite table of distinct square values and its displayed size.

The value projection must equal the supplied list, every row residual must be zero, and the value list must be
duplicate-free with the supplied length. -/
def SquareTableCertified {R : Type*}
    [Zero R] [Sub R] [Pow R Nat] [DecidableEq R]
    (rows : List (SquareRow R)) (values : List R) (count : Nat) : Prop :=
  List.map SquareRow.value rows = values ∧
    List.map squareResidual rows = List.replicate rows.length 0 ∧
    values.Nodup ∧ values.length = count

end SquareSpreadTables

end Purelib.Algebra.Squares.Certificate.List

end
