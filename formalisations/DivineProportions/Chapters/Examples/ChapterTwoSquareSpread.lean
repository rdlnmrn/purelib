module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Squares.Certificate.List
public import Purelib.Geometry.Trigonometry.SpreadNumber.Certificate.List
public import Purelib.Algebra.Field.Finite.Eleven
public import Purelib.Algebra.Field.Finite.Nineteen
public import Purelib.Algebra.Field.Finite.Seven
public import Purelib.Algebra.Field.Finite.Thirteen
public import Purelib.Algebra.Field.Finite.Three

public import Purelib.Algebra.Field.Finite.Five
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.GroupWithZero.Nat

open Purelib.Algebra.Field

open Purelib

section
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

namespace formalisations.DivineProportions.Chapters.Examples.ChapterTwoSquareSpread

variable {K : Type*} [ExplicitField K]

namespace SquareSpreadTables
namespace FieldThree

/-- Explicit square witness rows for [0, 1] modulo three.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareRows : List (Algebra.Squares.Certificate.List.SquareRow Finite.Three.Element) := [⟨0, 0⟩, ⟨1, 1⟩]
/-- Explicit spread witness rows for [0, 1, 2] modulo three.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def spreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadRow Finite.Three.Element) := [⟨0, 0⟩,
  ⟨1, 0⟩, ⟨2, 1⟩]
/-- Explicit square-spread witness rows for [0, 1] modulo three.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareSpreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadRow Finite.Three.Element)
  :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩]

/-- The square table modulo three certifies [0, 1] with 2 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_2 : Algebra.Squares.Certificate.List.SquareTableCertified squareRows [0, 1] 2 := by
  unfold Algebra.Squares.Certificate.List.SquareTableCertified squareRows
    Algebra.Squares.Certificate.List.squareResidual
  decide
/-- The spread table modulo three certifies [0, 1, 2] with 3 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_4 : Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows [0, 1, 2] 3 :=
  by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.spreadResidual
  decide
/-- The square-spread table modulo three certifies [0, 1] with 2 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_5 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows [0, 1] 2 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.squareSpreadResidual
  decide

end FieldThree

namespace FieldFive

/-- Explicit square witness rows for [0, 1, 4] modulo five.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareRows : List (Algebra.Squares.Certificate.List.SquareRow Finite.Five.Element) := [⟨0, 0⟩, ⟨1, 1⟩, ⟨4, 2⟩]
/-- Explicit spread witness rows for [0, 1, 3] modulo five.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def spreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadRow Finite.Five.Element) := [⟨0, 0⟩,
  ⟨1, 0⟩, ⟨3, 2⟩]

/-- The source prints `4` in this table, but its own preceding tables give
`Squares={0,1,4}` and `Spreads={0,1,3}`.  The intersection is `[0,1]`. -/
def squareSpreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadRow Finite.Five.Element) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩]

/-- The square table modulo five certifies [0, 1, 4] with 3 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_2 : Algebra.Squares.Certificate.List.SquareTableCertified squareRows [0, 1, 4] 3 := by
  unfold Algebra.Squares.Certificate.List.SquareTableCertified squareRows
    Algebra.Squares.Certificate.List.squareResidual
  decide
/-- The spread table modulo five certifies [0, 1, 3] with 3 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_4 : Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows [0, 1, 3] 3 :=
  by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.spreadResidual
  decide
/-- The square-spread table modulo five certifies [0, 1] with 2 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_5_corrected :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows [0, 1] 2 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.squareSpreadResidual
  decide

/-- The direct arithmetic discrepancy behind the correction: for the printed
candidate `4`, the spread radicand is `3`, not one of the displayed squares
`0`, `1`, and `4`. -/
theorem printed_four_radicand :
    (4 : Finite.Five.Element) * (1 - 4) = 3 ∧ (3 : Finite.Five.Element) ≠ 0 ∧ (3 : Finite.Five.Element) ≠ 1 ∧ (3 :
      Finite.Five.Element) ≠ 4 := by
  decide

end FieldFive

namespace FieldSeven

/-- Explicit square witness rows for [0, 1, 2, 4] modulo seven.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareRows : List (Algebra.Squares.Certificate.List.SquareRow Finite.Seven.Element) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨4, 2⟩]
/-- Explicit spread witness rows for [0, 1, 3, 4, 5] modulo seven.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def spreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadRow Finite.Seven.Element) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨3, 1⟩, ⟨4, 3⟩, ⟨5, 1⟩]
/-- Explicit square-spread witness rows for [0, 1, 4] modulo seven.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareSpreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadRow Finite.Seven.Element)
  :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨4, 2, 3⟩]

/-- The square table modulo seven certifies [0, 1, 2, 4] with 4 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_2 : Algebra.Squares.Certificate.List.SquareTableCertified squareRows [0, 1, 2, 4] 4 := by
  unfold Algebra.Squares.Certificate.List.SquareTableCertified squareRows
    Algebra.Squares.Certificate.List.squareResidual
  decide
/-- The spread table modulo seven certifies [0, 1, 3, 4, 5] with 5 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_4 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows [0, 1, 3, 4, 5] 5 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.spreadResidual
  decide
/-- The square-spread table modulo seven certifies [0, 1, 4] with 3 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_5 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows [0, 1, 4] 3 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.squareSpreadResidual
  decide

end FieldSeven

namespace FieldEleven

/-- Explicit square witness rows for [0, 1, 3, 4, 5, 9] modulo eleven.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareRows : List (Algebra.Squares.Certificate.List.SquareRow Finite.Eleven.Element) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨3, 5⟩, ⟨4, 2⟩, ⟨5, 4⟩, ⟨9, 3⟩]
/-- Explicit spread witness rows for [0, 1, 2, 3, 6, 9, 10] modulo eleven.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def spreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadRow Finite.Eleven.Element) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨6, 5⟩, ⟨9, 4⟩, ⟨10, 3⟩]
/-- Explicit square-spread witness rows for [0, 1, 3, 9] modulo eleven.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareSpreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadRow Finite.Eleven.Element)
  :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨3, 5, 4⟩, ⟨9, 3, 4⟩]

/-- The square table modulo eleven certifies [0, 1, 3, 4, 5, 9] with 6 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_2 :
    Algebra.Squares.Certificate.List.SquareTableCertified squareRows [0, 1, 3, 4, 5, 9] 6 := by
  unfold Algebra.Squares.Certificate.List.SquareTableCertified squareRows
    Algebra.Squares.Certificate.List.squareResidual
  decide
/-- The spread table modulo eleven certifies [0, 1, 2, 3, 6, 9, 10] with 7 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_4 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows [0, 1, 2, 3, 6, 9, 10] 7 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.spreadResidual
  decide
/-- The square-spread table modulo eleven certifies [0, 1, 3, 9] with 4 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_5 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows [0, 1, 3, 9] 4 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.squareSpreadResidual
  decide

end FieldEleven

namespace FieldThirteen

/-- Explicit square witness rows for [0, 1, 3, 4, 9, 10, 12] modulo thirteen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareRows : List (Algebra.Squares.Certificate.List.SquareRow Finite.Thirteen.Element) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨3, 4⟩, ⟨4, 2⟩, ⟨9, 3⟩, ⟨10, 6⟩, ⟨12, 5⟩]
/-- Explicit spread witness rows for [0, 1, 4, 6, 7, 8, 10] modulo thirteen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def spreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadRow Finite.Thirteen.Element) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨4, 1⟩, ⟨6, 3⟩, ⟨7, 6⟩, ⟨8, 3⟩, ⟨10, 1⟩]
/-- Explicit square-spread witness rows for [0, 1, 4, 10] modulo thirteen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareSpreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadRow
  Finite.Thirteen.Element) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨4, 2, 1⟩, ⟨10, 6, 1⟩]

/-- The square table modulo thirteen certifies [0, 1, 3, 4, 9, 10, 12] with 7 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_2 :
    Algebra.Squares.Certificate.List.SquareTableCertified squareRows [0, 1, 3, 4, 9, 10, 12] 7 := by
  unfold Algebra.Squares.Certificate.List.SquareTableCertified squareRows
    Algebra.Squares.Certificate.List.squareResidual
  decide
/-- The spread table modulo thirteen certifies [0, 1, 4, 6, 7, 8, 10] with 7 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_4 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows [0, 1, 4, 6, 7, 8, 10] 7 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.spreadResidual
  decide
/-- The square-spread table modulo thirteen certifies [0, 1, 4, 10] with 4 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_5 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows [0, 1, 4, 10] 4 :=
      by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.squareSpreadResidual
  decide

end FieldThirteen

namespace FieldSeventeen

/-- The seventeen displayed residue labels; no field instance or carrier
classification is installed. -/
abbrev F := Fin 17

/-- Seventeen is nonzero, providing the modulus certificate for the displayed residue labels. -/
instance instNeZeroSeventeen : NeZero 17 := ⟨by decide⟩

/-- Explicit square witness rows for [0, 1, 2, 4, 8, 9, 13, 15, 16] modulo seventeen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareRows : List (Algebra.Squares.Certificate.List.SquareRow F) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 6⟩, ⟨4, 2⟩, ⟨8, 5⟩, ⟨9, 3⟩, ⟨13, 8⟩,
    ⟨15, 7⟩, ⟨16, 4⟩]
/-- Explicit spread witness rows for [0, 1, 2, 6, 7, 9, 11, 12, 16] modulo seventeen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def spreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadRow F) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 7⟩, ⟨6, 2⟩, ⟨7, 3⟩, ⟨9, 8⟩, ⟨11, 3⟩,
    ⟨12, 2⟩, ⟨16, 7⟩]
/-- Explicit square-spread witness rows for [0, 1, 2, 9, 16] modulo seventeen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareSpreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadRow F) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨2, 6, 7⟩, ⟨9, 3, 8⟩, ⟨16, 4, 7⟩]

/-- The square table modulo seventeen certifies [0, 1, 2, 4, 8, 9, 13, 15, 16] with 9 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_2 :
    Algebra.Squares.Certificate.List.SquareTableCertified squareRows [0, 1, 2, 4, 8, 9, 13, 15, 16] 9 := by
  unfold Algebra.Squares.Certificate.List.SquareTableCertified squareRows
    Algebra.Squares.Certificate.List.squareResidual
  decide
/-- The spread table modulo seventeen certifies [0, 1, 2, 6, 7, 9, 11, 12, 16] with 9 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_4 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows [0, 1, 2, 6, 7, 9, 11, 12, 16] 9
      := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.spreadResidual
  decide
/-- The square-spread table modulo seventeen certifies [0, 1, 2, 9, 16] with 5 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_5 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows [0, 1, 2, 9, 16] 5
      := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.squareSpreadResidual
  decide

end FieldSeventeen

namespace FieldNineteen

/-- Explicit square witness rows for [0, 1, 4, 5, 6, 7, 9, 11, 16, 17] modulo nineteen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareRows : List (Algebra.Squares.Certificate.List.SquareRow Finite.Nineteen.Element) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨5, 9⟩, ⟨6, 5⟩, ⟨7, 8⟩, ⟨9, 3⟩,
    ⟨11, 7⟩, ⟨16, 4⟩, ⟨17, 6⟩]
/-- Explicit spread witness rows for [0, 1, 2, 4, 8, 9, 10, 11, 12, 16, 18] modulo nineteen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def spreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadRow Finite.Nineteen.Element) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 6⟩, ⟨4, 8⟩, ⟨8, 1⟩, ⟨9, 2⟩, ⟨10, 9⟩,
    ⟨11, 2⟩, ⟨12, 1⟩, ⟨16, 8⟩, ⟨18, 6⟩]
/-- Explicit square-spread witness rows for [0, 1, 4, 9, 11, 16] modulo nineteen.

Each row retains its displayed root witness; the list makes no carrier-enumeration claim. -/
def squareSpreadRows : List (Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadRow
  Finite.Nineteen.Element) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨4, 2, 8⟩, ⟨9, 3, 2⟩, ⟨11, 7, 2⟩,
    ⟨16, 4, 8⟩]

/-- The square table modulo nineteen certifies [0, 1, 4, 5, 6, 7, 9, 11, 16, 17] with 10 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_2 :
    Algebra.Squares.Certificate.List.SquareTableCertified squareRows [0, 1, 4, 5, 6, 7, 9, 11, 16, 17] 10 := by
  unfold Algebra.Squares.Certificate.List.SquareTableCertified squareRows
    Algebra.Squares.Certificate.List.squareResidual
  decide
/-- The spread table modulo nineteen certifies [0, 1, 2, 4, 8, 9, 10, 11, 12, 16, 18] with 11 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_4 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows [0, 1, 2, 4, 8, 9, 10, 11, 12,
      16, 18] 11 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SpreadTableCertified spreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.spreadResidual
  decide
/-- The square-spread table modulo nineteen certifies [0, 1, 4, 9, 11, 16] with 6 distinct entries.

Kernel evaluation checks the retained root equations, duplicate-freeness and the displayed length. -/
theorem example_2_5 :
    Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows [0, 1, 4, 9, 11, 16]
      6 := by
  unfold Geometry.Trigonometry.SpreadNumber.Certificate.List.SquareSpreadTableCertified squareSpreadRows
    Geometry.Trigonometry.SpreadNumber.Certificate.List.squareSpreadResidual
  decide

end FieldNineteen
end SquareSpreadTables

end formalisations.DivineProportions.Chapters.Examples.ChapterTwoSquareSpread

end

end
