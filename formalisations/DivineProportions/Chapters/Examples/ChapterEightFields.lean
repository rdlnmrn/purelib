module
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Geometry.Trigonometry.Spread.Number.Basic
import Purelib.Polynomial.Recurrence.Spread.Basic
public import Purelib.Polynomial.Recurrence.Spread.Orbit.Basic
import Purelib.Polynomial.Recurrence.Spread.Period
public import Purelib.Algebra.Field.Finite.Nineteen
public import Purelib.Algebra.Field.Finite.Seven
public import Purelib.Algebra.Field.Finite.Thirteen

public import Purelib.Algebra.Field.Finite.Five

section
@[expose] public section

/-!
# Divine Proportions, Chapter 8 finite-field examples

Every table and orbit below is an executable bounded calculation in an
explicit finite carrier.  Periodicity at arbitrary requested indices is then
deduced from two checked recurrence seeds.
-/

namespace formalisations.DivineProportions.Chapters.Examples.ChapterEightFields

namespace ChapterEightFiniteFieldExamples

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]
namespace ExampleEightOne

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Trigonometry.Spread.Number
/-- Every spread number in the field of 13 elements belongs to the displayed residue list. -/
private theorem classified_of_spread_number (value : Thirteen.Element)
    (spreadNumber : Basic.IsSpreadNumber value) :
    value = 0 ∨ value = 1 ∨ value = 4 ∨ value = 6 ∨
      value = 7 ∨ value = 8 ∨ value = 10 := by
  rcases spreadNumber with ⟨root, square⟩
  decide +revert

/-- The spread numbers modulo 13 are exactly 0, 1, 4, 6, 7, 8 and 10.

Each listed residue has an explicit square witness, and the finite calculation excludes every other residue. -/
theorem spread_number_classification (value : Thirteen.Element) :
    Basic.IsSpreadNumber value ↔
      value = 0 ∨ value = 1 ∨ value = 4 ∨ value = 6 ∨
        value = 7 ∨ value = 8 ∨ value = 10 := by
  constructor
  · exact classified_of_spread_number value
  · intro classified
    rcases classified with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨6, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨1, by decide⟩

end

open Purelib.Algebra.Field.Finite
open Purelib.Polynomial.Recurrence.Spread.Orbit
/-- The spread orbit of 6 modulo 13 has order twelve. -/
theorem six_has_order_twelve : Basic.HasSpreadOrder (6 : Thirteen.Element) 12 := by
  unfold Basic.HasSpreadOrder
  decide

/-- The displayed list is the exact spread-orbit prefix of 6 modulo 13. -/
theorem six_sequence :
    Basic.spreadOrbitPrefix 12 (6 : Thirteen.Element) =
      [0, 6, 10, 7, 4, 8, 1, 8, 4, 7, 10, 6] := by
  decide

/-- The spread orbit of 10 modulo 13 has order six. -/
theorem ten_has_order_six : Basic.HasSpreadOrder (10 : Thirteen.Element) 6 := by
  unfold Basic.HasSpreadOrder
  decide

/-- The displayed list is the exact spread-orbit prefix of 10 modulo 13. -/
theorem ten_sequence :
    Basic.spreadOrbitPrefix 6 (10 : Thirteen.Element) = [0, 10, 4, 1, 4, 10] := by
  decide

end ExampleEightOne

namespace ExampleEightTwo

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Trigonometry.Spread.Number
/-- Every spread number in the field of 19 elements belongs to the displayed residue list. -/
private theorem classified_of_spread_number (value : Nineteen.Element)
    (spreadNumber : Basic.IsSpreadNumber value) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 4 ∨
      value = 8 ∨ value = 9 ∨ value = 10 ∨ value = 11 ∨
      value = 12 ∨ value = 16 ∨ value = 18 := by
  rcases spreadNumber with ⟨root, square⟩
  decide +revert

/-- The spread numbers modulo 19 are exactly 0, 1, 2, 4, 8, 9, 10, 11, 12, 16 and 18.

Each listed residue has an explicit square witness, and the finite calculation excludes every other residue. -/
theorem spread_number_classification (value : Nineteen.Element) :
    Basic.IsSpreadNumber value ↔
      value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 4 ∨
        value = 8 ∨ value = 9 ∨ value = 10 ∨ value = 11 ∨
        value = 12 ∨ value = 16 ∨ value = 18 := by
  constructor
  · exact classified_of_spread_number value
  · intro classified
    rcases classified with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨6, by decide⟩
    · exact ⟨8, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨9, by decide⟩
    · exact ⟨2, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨8, by decide⟩
    · exact ⟨6, by decide⟩

end

open Purelib.Algebra.Field.Finite
open Purelib.Polynomial.Recurrence.Spread.Orbit
/-- The spread orbit of 8 modulo 19 has order twenty. -/
theorem eight_has_order_twenty : Basic.HasSpreadOrder (8 : Nineteen.Element) 20 := by
  unfold Basic.HasSpreadOrder
  decide

/-- The displayed list is the exact spread-orbit prefix of 8 modulo 19. -/
theorem eight_sequence :
    Basic.spreadOrbitPrefix 20 (8 : Nineteen.Element) =
      [0, 8, 4, 2, 9, 10, 11, 18, 16, 12, 1, 12, 16, 18, 11, 10, 9, 2, 4, 8] := by
  decide

/-- The spread orbit of 4 modulo 19 has order ten. -/
theorem four_has_order_ten : Basic.HasSpreadOrder (4 : Nineteen.Element) 10 := by
  unfold Basic.HasSpreadOrder
  decide

/-- The displayed list is the exact spread-orbit prefix of 4 modulo 19. -/
theorem four_sequence :
    Basic.spreadOrbitPrefix 10 (4 : Nineteen.Element) =
      [0, 4, 9, 11, 16, 1, 16, 11, 9, 4] := by
  decide

/-- The spread orbit of 9 modulo 19 has order five. -/
theorem nine_has_order_five : Basic.HasSpreadOrder (9 : Nineteen.Element) 5 := by
  unfold Basic.HasSpreadOrder
  decide

/-- The displayed list is the exact spread-orbit prefix of 9 modulo 19. -/
theorem nine_sequence :
    Basic.spreadOrbitPrefix 5 (9 : Nineteen.Element) = [0, 9, 16, 16, 9] := by
  decide

end ExampleEightTwo

namespace ExampleEightThree

open Purelib.Algebra.Field.Finite in
open Purelib.Polynomial.Recurrence.Spread in
/-- The first 13 spread-polynomial rows evaluated at every residue modulo 5.

Rows retain the recurrence index and columns follow the executable finite carrier enumeration. -/
def table : List (List Five.Element) :=
  List.ofFn (fun index : Fin 13 =>
    List.ofFn (fun value : Five.Element => Basic.spreadPolynomial index.1 value))

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Trigonometry.Spread.Number
/-- Every spread number in the field of 5 elements belongs to the displayed residue list. -/
private theorem classified_of_spread_number (value : Five.Element)
    (spreadNumber : Basic.IsSpreadNumber value) :
    value = 0 ∨ value = 1 ∨ value = 3 := by
  rcases spreadNumber with ⟨root, square⟩
  decide +revert

/-- The spread numbers modulo 5 are exactly 0, 1 and 3.

Each listed residue has an explicit square witness, and the finite calculation excludes every other residue. -/
theorem spread_number_classification (value : Five.Element) :
    Basic.IsSpreadNumber value ↔ value = 0 ∨ value = 1 ∨ value = 3 := by
  constructor
  · exact classified_of_spread_number value
  · intro classified
    rcases classified with rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨2, by decide⟩

end

/-- The spread-polynomial table modulo 5 equals the complete displayed rows. -/
theorem table_value : table =
    [[0, 0, 0, 0, 0],
     [0, 1, 2, 3, 4],
     [0, 0, 2, 1, 2],
     [0, 1, 0, 3, 1],
     [0, 0, 2, 0, 2],
     [0, 1, 2, 3, 4],
     [0, 0, 0, 1, 0],
     [0, 1, 2, 3, 4],
     [0, 0, 2, 0, 2],
     [0, 1, 0, 3, 1],
     [0, 0, 2, 1, 2],
     [0, 1, 2, 3, 4],
     [0, 0, 0, 0, 0]] := by
  decide

open Purelib.Algebra.Field.Finite in
open Purelib.Polynomial.Recurrence.Spread in
/-- Every spread-polynomial sequence modulo 5 repeats after twelve indices. -/
theorem period_twelve (index : Nat) (value : Five.Element) :
    Basic.spreadPolynomial (index + 12) value = Basic.spreadPolynomial index value := by
  apply Period.spreadPolynomial_period 12 value
  · decide +revert
  · decide +revert

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Trigonometry.Spread.Number in
open Purelib.Polynomial.Recurrence.Spread in
/-- A spread-number input modulo 5 has period four.

The classified input residues supply the two recurrence seeds for every natural index. -/
theorem spread_number_period_four
    (index : Nat) (value : Five.Element) (spreadNumber : Basic.IsSpreadNumber value) :
    Basic.spreadPolynomial (index + 4) value = Basic.spreadPolynomial index value := by
  have zeroSeed : Basic.spreadPolynomial 4 value = 0 := by
    rcases (spread_number_classification value).1 spreadNumber with
      valueZero | valueOne | valueThree
    · rw [valueZero]
      decide
    · rw [valueOne]
      decide
    · rw [valueThree]
      decide
  have oneSeed : Basic.spreadPolynomial (4 + 1) value = value := by
    rcases (spread_number_classification value).1 spreadNumber with
      valueZero | valueOne | valueThree
    · rw [valueZero]
      decide
    · rw [valueOne]
      decide
    · rw [valueThree]
      decide
  exact Period.spreadPolynomial_period 4 value zeroSeed oneSeed index

end ExampleEightThree

namespace ExampleEightFour

open Purelib.Algebra.Field.Finite in
open Purelib.Polynomial.Recurrence.Spread in
/-- The first 26 spread-polynomial rows evaluated at every residue modulo 7.

Rows retain the recurrence index and columns follow the executable finite carrier enumeration. -/
def table : List (List Seven.Element) :=
  List.ofFn (fun index : Fin 26 =>
    List.ofFn (fun value : Seven.Element => Basic.spreadPolynomial index.1 value))

section
open Purelib.Algebra.Field.Finite
open Purelib.Geometry.Trigonometry.Spread.Number
/-- Every spread number in the field of 7 elements belongs to the displayed residue list. -/
private theorem classified_of_spread_number (value : Seven.Element)
    (spreadNumber : Basic.IsSpreadNumber value) :
    value = 0 ∨ value = 1 ∨ value = 3 ∨ value = 4 ∨ value = 5 := by
  rcases spreadNumber with ⟨root, square⟩
  decide +revert

/-- The spread numbers modulo 7 are exactly 0, 1, 3, 4 and 5.

Each listed residue has an explicit square witness, and the finite calculation excludes every other residue. -/
theorem spread_number_classification (value : Seven.Element) :
    Basic.IsSpreadNumber value ↔
      value = 0 ∨ value = 1 ∨ value = 3 ∨ value = 4 ∨ value = 5 := by
  constructor
  · exact classified_of_spread_number value
  · intro classified
    rcases classified with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨1, by decide⟩
    · exact ⟨3, by decide⟩
    · exact ⟨1, by decide⟩

end

/-- The spread-polynomial table modulo 7 equals the complete displayed rows. -/
theorem table_value : table =
    [[0, 0, 0, 0, 0, 0, 0],
     [0, 1, 2, 3, 4, 5, 6],
     [0, 0, 6, 4, 1, 4, 6],
     [0, 1, 1, 5, 4, 3, 0],
     [0, 0, 6, 1, 0, 1, 6],
     [0, 1, 2, 5, 4, 3, 6],
     [0, 0, 0, 4, 1, 4, 0],
     [0, 1, 2, 3, 4, 5, 6],
     [0, 0, 6, 0, 0, 0, 6],
     [0, 1, 1, 3, 4, 5, 0],
     [0, 0, 6, 4, 1, 4, 6],
     [0, 1, 2, 5, 4, 3, 6],
     [0, 0, 0, 1, 0, 1, 0],
     [0, 1, 2, 5, 4, 3, 6],
     [0, 0, 6, 4, 1, 4, 6],
     [0, 1, 1, 3, 4, 5, 0],
     [0, 0, 6, 0, 0, 0, 6],
     [0, 1, 2, 3, 4, 5, 6],
     [0, 0, 0, 4, 1, 4, 0],
     [0, 1, 2, 5, 4, 3, 6],
     [0, 0, 6, 1, 0, 1, 6],
     [0, 1, 1, 5, 4, 3, 0],
     [0, 0, 6, 4, 1, 4, 6],
     [0, 1, 2, 3, 4, 5, 6],
     [0, 0, 0, 0, 0, 0, 0],
     [0, 1, 2, 3, 4, 5, 6]] := by
  decide

open Purelib.Algebra.Field.Finite in
open Purelib.Polynomial.Recurrence.Spread in
/-- Every spread-polynomial sequence modulo 7 repeats after twenty four indices. -/
theorem period_twenty_four (index : Nat) (value : Seven.Element) :
    Basic.spreadPolynomial (index + 24) value = Basic.spreadPolynomial index value := by
  apply Period.spreadPolynomial_period 24 value
  · decide +revert
  · decide +revert

open Purelib.Algebra.Field.Finite in
open Purelib.Geometry.Trigonometry.Spread.Number in
open Purelib.Polynomial.Recurrence.Spread in
/-- A spread-number input modulo 7 has period eight.

The classified input residues supply the two recurrence seeds for every natural index. -/
theorem spread_number_period_eight
    (index : Nat) (value : Seven.Element) (spreadNumber : Basic.IsSpreadNumber value) :
    Basic.spreadPolynomial (index + 8) value = Basic.spreadPolynomial index value := by
  have zeroSeed : Basic.spreadPolynomial 8 value = 0 := by
    rcases (spread_number_classification value).1 spreadNumber with
      valueZero | valueOne | valueThree | valueFour | valueFive
    · rw [valueZero]
      decide
    · rw [valueOne]
      decide
    · rw [valueThree]
      decide
    · rw [valueFour]
      decide
    · rw [valueFive]
      decide
  have oneSeed : Basic.spreadPolynomial (8 + 1) value = value := by
    rcases (spread_number_classification value).1 spreadNumber with
      valueZero | valueOne | valueThree | valueFour | valueFive
    · rw [valueZero]
      decide
    · rw [valueOne]
      decide
    · rw [valueThree]
      decide
    · rw [valueFour]
      decide
    · rw [valueFive]
      decide
  exact Period.spreadPolynomial_period 8 value zeroSeed oneSeed index

end ExampleEightFour

end ChapterEightFiniteFieldExamples

end formalisations.DivineProportions.Chapters.Examples.ChapterEightFields

end
