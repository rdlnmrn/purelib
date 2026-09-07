import DivineProportions.Trigonometry.SpreadPolynomial
import DivineProportions.Trigonometry.SpreadNumbers
import DivineProportions.Algebra.FieldFive
import DivineProportions.Algebra.FieldSeven
import DivineProportions.Algebra.FieldThirteen
import DivineProportions.Algebra.FieldNineteen

/-!
# Divine Proportions, Chapter 8 finite-field examples

Every table and orbit below is an executable bounded calculation in an
explicit finite carrier.  Periodicity at arbitrary requested indices is then
deduced from two checked recurrence seeds.
-/

namespace DivineProportions

namespace ChapterEightFiniteFieldExamples

variable {K : Type*} [RFAP.ExplicitField K]

/-- The requested finite prefix `[S₀(s),…,Sₙ₋₁(s)]`. -/
def spreadOrbitPrefix (length : Nat) (value : K) : List K :=
  List.ofFn (fun index : Fin length => spreadPolynomial index.1 value)

/-- `value` has the displayed least positive zero index.  Minimality is a
bounded check over exactly the preceding positive indices. -/
def HasSpreadOrder (value : K) (order : Nat) : Prop :=
  spreadPolynomial order value = 0 ∧
    ∀ index : Fin (order - 1),
      spreadPolynomial (index.1 + 1) value ≠ 0

namespace ExampleEightOne

abbrev F₁₃ := FieldThirteen.Element

private theorem classified_of_spread_number (value : F₁₃)
    (spreadNumber : IsSpreadNumber value) :
    value = 0 ∨ value = 1 ∨ value = 4 ∨ value = 6 ∨
      value = 7 ∨ value = 8 ∨ value = 10 := by
  rcases spreadNumber with ⟨root, square⟩
  decide +revert

theorem spread_number_classification (value : F₁₃) :
    IsSpreadNumber value ↔
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

theorem six_has_order_twelve : HasSpreadOrder (6 : F₁₃) 12 := by
  unfold HasSpreadOrder
  decide

theorem six_sequence :
    spreadOrbitPrefix 12 (6 : F₁₃) =
      [0, 6, 10, 7, 4, 8, 1, 8, 4, 7, 10, 6] := by
  decide

theorem ten_has_order_six : HasSpreadOrder (10 : F₁₃) 6 := by
  unfold HasSpreadOrder
  decide

theorem ten_sequence :
    spreadOrbitPrefix 6 (10 : F₁₃) = [0, 10, 4, 1, 4, 10] := by
  decide

end ExampleEightOne

namespace ExampleEightTwo

abbrev F₁₉ := FieldNineteen.Element

private theorem classified_of_spread_number (value : F₁₉)
    (spreadNumber : IsSpreadNumber value) :
    value = 0 ∨ value = 1 ∨ value = 2 ∨ value = 4 ∨
      value = 8 ∨ value = 9 ∨ value = 10 ∨ value = 11 ∨
      value = 12 ∨ value = 16 ∨ value = 18 := by
  rcases spreadNumber with ⟨root, square⟩
  decide +revert

theorem spread_number_classification (value : F₁₉) :
    IsSpreadNumber value ↔
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

theorem eight_has_order_twenty : HasSpreadOrder (8 : F₁₉) 20 := by
  unfold HasSpreadOrder
  decide

theorem eight_sequence :
    spreadOrbitPrefix 20 (8 : F₁₉) =
      [0, 8, 4, 2, 9, 10, 11, 18, 16, 12, 1, 12, 16, 18, 11, 10, 9, 2, 4, 8] := by
  decide

theorem four_has_order_ten : HasSpreadOrder (4 : F₁₉) 10 := by
  unfold HasSpreadOrder
  decide

theorem four_sequence :
    spreadOrbitPrefix 10 (4 : F₁₉) =
      [0, 4, 9, 11, 16, 1, 16, 11, 9, 4] := by
  decide

theorem nine_has_order_five : HasSpreadOrder (9 : F₁₉) 5 := by
  unfold HasSpreadOrder
  decide

theorem nine_sequence :
    spreadOrbitPrefix 5 (9 : F₁₉) = [0, 9, 16, 16, 9] := by
  decide

end ExampleEightTwo

namespace ExampleEightThree

abbrev F₅ := FieldFive.Element

def table : List (List F₅) :=
  List.ofFn (fun index : Fin 13 =>
    List.ofFn (fun value : F₅ => spreadPolynomial index.1 value))

private theorem classified_of_spread_number (value : F₅)
    (spreadNumber : IsSpreadNumber value) :
    value = 0 ∨ value = 1 ∨ value = 3 := by
  rcases spreadNumber with ⟨root, square⟩
  decide +revert

theorem spread_number_classification (value : F₅) :
    IsSpreadNumber value ↔ value = 0 ∨ value = 1 ∨ value = 3 := by
  constructor
  · exact classified_of_spread_number value
  · intro classified
    rcases classified with rfl | rfl | rfl
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨2, by decide⟩

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

theorem period_twelve (index : Nat) (value : F₅) :
    spreadPolynomial (index + 12) value = spreadPolynomial index value := by
  apply spreadPolynomial_period 12 value
  · decide +revert
  · decide +revert

theorem spread_number_period_four
    (index : Nat) (value : F₅) (spreadNumber : IsSpreadNumber value) :
    spreadPolynomial (index + 4) value = spreadPolynomial index value := by
  have zeroSeed : spreadPolynomial 4 value = 0 := by
    rcases (spread_number_classification value).1 spreadNumber with
      valueZero | valueOne | valueThree
    · rw [valueZero]
      decide
    · rw [valueOne]
      decide
    · rw [valueThree]
      decide
  have oneSeed : spreadPolynomial (4 + 1) value = value := by
    rcases (spread_number_classification value).1 spreadNumber with
      valueZero | valueOne | valueThree
    · rw [valueZero]
      decide
    · rw [valueOne]
      decide
    · rw [valueThree]
      decide
  exact spreadPolynomial_period 4 value zeroSeed oneSeed index

end ExampleEightThree

namespace ExampleEightFour

abbrev F₇ := FieldSeven.Element

def table : List (List F₇) :=
  List.ofFn (fun index : Fin 26 =>
    List.ofFn (fun value : F₇ => spreadPolynomial index.1 value))

private theorem classified_of_spread_number (value : F₇)
    (spreadNumber : IsSpreadNumber value) :
    value = 0 ∨ value = 1 ∨ value = 3 ∨ value = 4 ∨ value = 5 := by
  rcases spreadNumber with ⟨root, square⟩
  decide +revert

theorem spread_number_classification (value : F₇) :
    IsSpreadNumber value ↔
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

theorem period_twenty_four (index : Nat) (value : F₇) :
    spreadPolynomial (index + 24) value = spreadPolynomial index value := by
  apply spreadPolynomial_period 24 value
  · decide +revert
  · decide +revert

theorem spread_number_period_eight
    (index : Nat) (value : F₇) (spreadNumber : IsSpreadNumber value) :
    spreadPolynomial (index + 8) value = spreadPolynomial index value := by
  have zeroSeed : spreadPolynomial 8 value = 0 := by
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
  have oneSeed : spreadPolynomial (8 + 1) value = value := by
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
  exact spreadPolynomial_period 8 value zeroSeed oneSeed index

end ExampleEightFour

end ChapterEightFiniteFieldExamples

end DivineProportions
