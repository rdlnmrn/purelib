module

public import Purelib.Data.Presentation
public import Purelib.Data.Gaussian.Basic

namespace Purelib.Data.Gaussian.Presentation

open Purelib.Data.Rat.Fraction
open Purelib.Data.Gaussian.Basic

/-- A Gaussian coordinate display is an ordered pair of canonical rationals. -/
public abbrev Code := Rational × Rational

/-- Every typed pair of canonical rational coordinates is admissible. -/
@[expose] public def Valid (_ : Code) : Prop := True

/-- A typed coordinate pair carries all the evidence needed for admission. -/
@[expose] public def recognize (code : Code) : Decidable (Valid code) :=
  .isTrue True.intro

/-- A coordinate pair with its trivial admission certificate. -/
public abbrev Display := {code : Code // Valid code}

/-- Read the coordinates into the original Gaussian rational owner. -/
@[expose] public def read (display : Display) : Canonical :=
  ⟨display.val.1, display.val.2⟩

/-- Quote the retained real and imaginary coordinates of a Gaussian rational. -/
@[expose] public def quote (value : Canonical) : Display :=
  ⟨(value.re, value.im), True.intro⟩

/-- Two admissible coordinate displays are equal when both coordinates agree. -/
@[expose] public def Same (left right : Display) : Prop := left.val = right.val

/-- Compare the retained rational coordinates by their original equality decisions. -/
@[expose] public def compare (left right : Display) : Decidable (Same left right) :=
  inferInstanceAs (Decidable (left.val = right.val))

/-- Reading the quoted coordinates recovers the original Gaussian rational. -/
public theorem read_quote (value : Canonical) : read (quote value) = value := by
  cases value
  rfl

/-- Quoting a read display recovers its original coordinate pair. -/
public theorem quote_read (display : Display) : quote (read display) = display := by
  cases display with
  | mk code _ =>
    cases code
    rfl

/-- Coordinate equality agrees exactly with equality of original Gaussian rationals. -/
public theorem same_iff_read_eq (left right : Display) : Same left right ↔ read left = read right := by
  constructor
  · intro same
    cases left with
    | mk left _ =>
      cases right with
      | mk right _ =>
        cases same
        rfl
  · intro same
    exact congrArg (fun value : Canonical => (value.re, value.im)) same

/-!
## Gaussian rational coordinates

The typed input is an ordered pair of canonical rational coordinates. All such
pairs are admitted; recognition of raw fraction displays remains a separate
operation. `compare` uses the existing rational equality decisions on both
coordinates. `same_iff_read_eq` identifies this equality with the original
`Canonical` equality, while `read_quote` and `quote_read` give both round trips.
The pair decisions terminate through the original finite rational decisions;
proof-system, construction-admission and runtime accounts remain separate.
-/
/-- The explicit coordinate presentation of original Gaussian rationals. -/
@[expose] public def coordinates : Purelib.Data.Presentation Code where
  Valid := Valid
  recognize := recognize
  Same := Same
  compare := compare
  same_laws := ⟨fun _ => rfl, fun h => h.symm, fun h k => h.trans k⟩

end Purelib.Data.Gaussian.Presentation
