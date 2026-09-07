import mathlib.Tactic.QuotientFreeOmega
import DivineProportions.Trigonometry.SpreadNumbers
import DivineProportions.Algebra.FieldThree
import DivineProportions.Algebra.FieldFive
import DivineProportions.Algebra.FieldSeven
import DivineProportions.Algebra.FieldEleven
import DivineProportions.Algebra.FieldThirteen
import DivineProportions.Algebra.FieldNineteen
import mathlib.RFAP.ConstructiveFraction

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

namespace DivineProportions

variable {K : Type*} [RFAP.ExplicitField K]

/-- A square number with its root retained existentially. -/
def IsSquareNumber (value : K) : Prop :=
  ∃ root : K, value = root ^ 2

/-- A number which is both square and spread. -/
def IsSquareSpreadNumber (value : K) : Prop :=
  IsSquareNumber value ∧ IsSpreadNumber value

/-- The fibre over `value` of the first-coordinate-square map on the unit
circle. -/
def HasUnitCircleLift (value : K) : Prop :=
  ∃ first second : K,
    value = first ^ 2 ∧ first ^ 2 + second ^ 2 = 1

/-- A constructive square-spread value is precisely a value with a unit-circle
lift.  When the first root is nonzero, the second coordinate is computed as
`spreadRoot / squareRoot`; the zero case has the explicit lift `(0,1)`. -/
theorem squareSpread_iff_unitCircleLift [DecidableEq K] (value : K) :
    IsSquareSpreadNumber value ↔ HasUnitCircleLift value := by
  constructor
  · rintro ⟨⟨first, valueSquare⟩, ⟨spreadRoot, spreadSquare⟩⟩
    by_cases firstZero : first = 0
    · refine ⟨0, 1, ?_, ?_⟩
      · calc
          value = first ^ 2 := valueSquare
          _ = 0 := by rw [firstZero]; ring1
          _ = (0 : K) ^ 2 := by ring1
      · ring1
    · let second := spreadRoot / first
      have firstCancel : first * first⁻¹ = (1 : K) :=
        RFAP.ExplicitField.mul_inv_cancel first firstZero
      have spreadEquation :
          first ^ 2 * (1 - first ^ 2) = spreadRoot ^ 2 := by
        calc
          first ^ 2 * (1 - first ^ 2) = value * (1 - value) := by
            rw [valueSquare]
          _ = spreadRoot ^ 2 := spreadSquare
      have secondSquare : second ^ 2 = 1 - first ^ 2 := by
        simp only [second, RFAP.ExplicitField.div_eq_mul_inv]
        calc
          (spreadRoot * first⁻¹) ^ 2 =
              spreadRoot ^ 2 * first⁻¹ ^ 2 := by ring1
          _ = first ^ 2 * (1 - first ^ 2) * first⁻¹ ^ 2 := by
            rw [← spreadEquation]
          _ = (1 - first ^ 2) * (first * first⁻¹) ^ 2 := by ring1
          _ = 1 - first ^ 2 := by rw [firstCancel]; ring1
      exact ⟨first, second, valueSquare, by rw [secondSquare]; ring1⟩
  · rintro ⟨first, second, valueSquare, circleEquation⟩
    constructor
    · exact ⟨first, valueSquare⟩
    · refine ⟨first * second, ?_⟩
      calc
        value * (1 - value) =
            first ^ 2 * (1 - first ^ 2) := by rw [valueSquare]
        _ = first ^ 2 * second ^ 2 := by
          have secondSquare : second ^ 2 = 1 - first ^ 2 := by
            calc
              second ^ 2 = (first ^ 2 + second ^ 2) - first ^ 2 := by ring1
              _ = 1 - first ^ 2 := by rw [circleEquation]
          rw [secondSquare]
        _ = (first * second) ^ 2 := by ring1

/-- Equality of two squares has the two explicit sign alternatives. -/
theorem eq_or_eq_neg_of_sq_eq_sq [DecidableEq K]
    {left right : K} (squaresEqual : left ^ 2 = right ^ 2) :
    left = right ∨ left = -right := by
  have productZero : (left - right) * (left + right) = 0 := by
    calc
      (left - right) * (left + right) = left ^ 2 - right ^ 2 := by ring1
      _ = 0 := by rw [squaresEqual]; ring1
  by_cases firstFactorZero : left - right = 0
  · exact Or.inl (sub_eq_zero.mp firstFactorZero)
  · have secondFactorZero : left + right = 0 := by
      by_cases secondFactorNonzero : left + right = 0
      · exact secondFactorNonzero
      · exact False.elim
          ((RFAP.ExplicitField.mul_ne_zero firstFactorZero
            secondFactorNonzero) productZero)
    exact Or.inr (eq_neg_of_add_eq_zero_left secondFactorZero)

/-- A supplied pair of roots bounds every unit-circle lift by the four finite
sign choices.  This is the fibre calculation used in Exercise 2.3. -/
theorem unitCircleLift_sign_choices [DecidableEq K]
    (value firstRoot secondRoot first second : K)
    (valueSquare : value = firstRoot ^ 2)
    (complementSquare : 1 - value = secondRoot ^ 2)
    (liftValue : value = first ^ 2)
    (liftCircle : first ^ 2 + second ^ 2 = 1) :
    (first = firstRoot ∨ first = -firstRoot) ∧
      (second = secondRoot ∨ second = -secondRoot) := by
  have firstSquares : first ^ 2 = firstRoot ^ 2 := by
    calc
      first ^ 2 = value := liftValue.symm
      _ = firstRoot ^ 2 := valueSquare
  have secondSquareValue : second ^ 2 = 1 - value := by
    calc
      second ^ 2 = (first ^ 2 + second ^ 2) - first ^ 2 := by ring1
      _ = 1 - first ^ 2 := by rw [liftCircle]
      _ = 1 - value := by rw [← liftValue]
  exact ⟨eq_or_eq_neg_of_sq_eq_sq firstSquares,
    eq_or_eq_neg_of_sq_eq_sq (secondSquareValue.trans complementSquare)⟩

/-- The four sign choices obtained from two supplied roots really are
unit-circle lifts. -/
theorem four_unitCircle_lifts
    (value firstRoot secondRoot : K)
    (valueSquare : value = firstRoot ^ 2)
    (complementSquare : 1 - value = secondRoot ^ 2) :
    firstRoot ^ 2 + secondRoot ^ 2 = 1 ∧
      (-firstRoot) ^ 2 + secondRoot ^ 2 = 1 ∧
      firstRoot ^ 2 + (-secondRoot) ^ 2 = 1 ∧
      (-firstRoot) ^ 2 + (-secondRoot) ^ 2 = 1 := by
  have base : firstRoot ^ 2 + secondRoot ^ 2 = 1 := by
    calc
      firstRoot ^ 2 + secondRoot ^ 2 = value + (1 - value) := by
        rw [← valueSquare, ← complementSquare]
      _ = 1 := by ring1
  exact ⟨base,
    calc
      (-firstRoot) ^ 2 + secondRoot ^ 2 =
          firstRoot ^ 2 + secondRoot ^ 2 := by ring1
      _ = 1 := base,
    calc
      firstRoot ^ 2 + (-secondRoot) ^ 2 =
          firstRoot ^ 2 + secondRoot ^ 2 := by ring1
      _ = 1 := base,
    calc
      (-firstRoot) ^ 2 + (-secondRoot) ^ 2 =
          firstRoot ^ 2 + secondRoot ^ 2 := by ring1
      _ = 1 := base⟩

private theorem ne_neg_self_of_nonzero
    (value : K) (twoNonzero : (2 : K) ≠ 0) (valueNonzero : value ≠ 0) :
    value ≠ -value := by
  intro equalNegative
  have doubledZero : (2 : K) * value = 0 := by
    calc
      (2 : K) * value = value + value := by ring1
      _ = -value + value := congrArg (fun entry => entry + value)
        equalNegative
      _ = 0 := by ring1
  exact (RFAP.ExplicitField.mul_ne_zero twoNonzero valueNonzero) doubledZero

/-- Away from the boundary values, and outside characteristic two, the four
sign choices are four distinct finite pairs. -/
theorem four_sign_pairs_nodup
    (firstRoot secondRoot : K) (twoNonzero : (2 : K) ≠ 0)
    (firstNonzero : firstRoot ≠ 0) (secondNonzero : secondRoot ≠ 0) :
    [ (firstRoot, secondRoot), (-firstRoot, secondRoot),
      (firstRoot, -secondRoot), (-firstRoot, -secondRoot) ].Nodup := by
  have firstNotNegative :=
    ne_neg_self_of_nonzero firstRoot twoNonzero firstNonzero
  have secondNotNegative :=
    ne_neg_self_of_nonzero secondRoot twoNonzero secondNonzero
  simp [firstNotNegative, secondNotNegative]

namespace ExampleTwoThree

abbrev Rational := RFAP.ConstructiveFraction.Rational

/-- The constructive half of Example 2.3: a displayed square root certifies
nonnegativity in the rational/decimal order. -/
theorem squareNumber_nonnegative
    (value : Rational) (square : IsSquareNumber value) : 0 ≤ value := by
  rcases square with ⟨root, valueSquare⟩
  rw [valueSquare]
  exact RFAP.ConstructiveFraction.sq_nonneg_direct root

/-- A rational spread-number witness forces the value into the unit interval.
The converse over the source's decimal field requires square-root closure;
over constructive rationals it is correctly retained as explicit witness
data rather than a selected root. -/
theorem spreadNumber_mem_unitInterval
    (value : Rational) (spreadNumber : IsSpreadNumber value) :
    0 ≤ value ∧ value ≤ 1 := by
  rcases spreadNumber with ⟨root, spreadSquare⟩
  have productNonnegative : 0 ≤ value * (1 - value) := by
    rw [spreadSquare]
    exact RFAP.ConstructiveFraction.sq_nonneg_direct root
  constructor
  · rcases lt_trichotomy value 0 with valueNegative | valueZero |
        valuePositive
    · have onePositive : (0 : Rational) < 1 := by decide
      have valueLessOne : value < 1 := valueNegative.trans onePositive
      have complementPositive :=
        RFAP.ConstructiveFraction.sub_pos_direct valueLessOne
      have productNegative :=
        RFAP.ConstructiveFraction.mul_neg_of_neg_of_pos_direct valueNegative
          complementPositive
      exact False.elim ((not_lt_of_ge productNonnegative) productNegative)
    · rw [valueZero]
    · exact RFAP.ConstructiveFraction.le_of_lt_direct valuePositive
  · rcases lt_trichotomy value 1 with valueLess | valueOne | valueGreater
    · exact RFAP.ConstructiveFraction.le_of_lt_direct valueLess
    · exact valueOne.le
    · have valuePositive : (0 : Rational) < value :=
        (by decide : (0 : Rational) < 1).trans valueGreater
      have complementNegative :=
        RFAP.ConstructiveFraction.sub_neg_direct valueGreater
      have productNegative :=
        RFAP.ConstructiveFraction.mul_neg_of_pos_of_neg_direct valuePositive
          complementNegative
      exact False.elim ((not_lt_of_ge productNonnegative) productNegative)

/-- Example 2.3 with the analytic root-existence clause made explicit: if a
value and its complement carry square roots, it is a spread number in
`[0,1]`. -/
theorem example_2_3
    (value firstRoot secondRoot : Rational)
    (valueSquare : value = firstRoot ^ 2)
    (complementSquare : 1 - value = secondRoot ^ 2) :
    IsSquareSpreadNumber value ∧ 0 ≤ value ∧ value ≤ 1 := by
  have lift : HasUnitCircleLift value := by
    refine ⟨firstRoot, secondRoot, valueSquare, ?_⟩
    calc
      firstRoot ^ 2 + secondRoot ^ 2 = value + (1 - value) := by
        rw [← valueSquare, ← complementSquare]
      _ = 1 := by ring1
  have squareSpread := (squareSpread_iff_unitCircleLift value).2 lift
  exact ⟨squareSpread,
    spreadNumber_mem_unitInterval value squareSpread.2⟩

end ExampleTwoThree

namespace FiniteSquareSpreadTables

/-- One finite square-witness row. -/
structure SquareRow (R : Type*) where
  value : R
  root : R

/-- One finite spread-witness row. -/
structure SpreadRow (R : Type*) where
  value : R
  root : R

/-- One finite square-spread witness row. -/
structure SquareSpreadRow (R : Type*) where
  value : R
  squareRoot : R
  spreadRoot : R

def squareResidual {R : Type*} [Sub R] [Pow R Nat]
    (row : SquareRow R) : R :=
  row.value - row.root ^ 2

def spreadResidual {R : Type*} [One R] [Sub R] [Mul R] [Pow R Nat]
    (row : SpreadRow R) : R :=
  row.value * (1 - row.value) - row.root ^ 2

def squareSpreadResidual {R : Type*} [One R] [Sub R] [Mul R] [Pow R Nat]
    (row : SquareSpreadRow R) : R × R :=
  (row.value - row.squareRoot ^ 2,
    row.value * (1 - row.value) - row.spreadRoot ^ 2)

/-- A displayed square table consists of distinct values, one checked root per
value, and the printed finite length. -/
def SquareTableCertified {R : Type*}
    [Zero R] [Sub R] [Pow R Nat] [DecidableEq R]
    (rows : List (SquareRow R)) (values : List R) (count : Nat) : Prop :=
  List.map SquareRow.value rows = values ∧
    List.map squareResidual rows = List.replicate rows.length 0 ∧
    values.Nodup ∧ values.length = count

/-- A displayed spread table with an explicit witness in each row. -/
def SpreadTableCertified {R : Type*}
    [Zero R] [One R] [Sub R] [Mul R] [Pow R Nat] [DecidableEq R]
    (rows : List (SpreadRow R)) (values : List R) (count : Nat) : Prop :=
  List.map SpreadRow.value rows = values ∧
    List.map spreadResidual rows = List.replicate rows.length 0 ∧
    values.Nodup ∧ values.length = count

/-- A displayed square-spread table with both roots explicit. -/
def SquareSpreadTableCertified {R : Type*}
    [Zero R] [One R] [Sub R] [Mul R] [Pow R Nat] [DecidableEq R]
    (rows : List (SquareSpreadRow R)) (values : List R) (count : Nat) : Prop :=
  List.map SquareSpreadRow.value rows = values ∧
    List.map squareSpreadResidual rows =
      List.replicate rows.length (0, 0) ∧
    values.Nodup ∧ values.length = count

namespace FieldThree

abbrev F := DivineProportions.FieldThree.Element

def squareRows : List (SquareRow F) := [⟨0, 0⟩, ⟨1, 1⟩]
def spreadRows : List (SpreadRow F) := [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩]
def squareSpreadRows : List (SquareSpreadRow F) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩]

theorem example_2_2 : SquareTableCertified squareRows [0, 1] 2 := by
  unfold SquareTableCertified squareRows squareResidual
  decide
theorem example_2_4 : SpreadTableCertified spreadRows [0, 1, 2] 3 := by
  unfold SpreadTableCertified spreadRows spreadResidual
  decide
theorem example_2_5 :
    SquareSpreadTableCertified squareSpreadRows [0, 1] 2 := by
  unfold SquareSpreadTableCertified squareSpreadRows squareSpreadResidual
  decide

end FieldThree

namespace FieldFive

abbrev F := DivineProportions.FieldFive.Element

def squareRows : List (SquareRow F) := [⟨0, 0⟩, ⟨1, 1⟩, ⟨4, 2⟩]
def spreadRows : List (SpreadRow F) := [⟨0, 0⟩, ⟨1, 0⟩, ⟨3, 2⟩]

/-- The source prints `4` in this table, but its own preceding tables give
`Squares={0,1,4}` and `Spreads={0,1,3}`.  The intersection is `[0,1]`. -/
def squareSpreadRows : List (SquareSpreadRow F) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩]

theorem example_2_2 : SquareTableCertified squareRows [0, 1, 4] 3 := by
  unfold SquareTableCertified squareRows squareResidual
  decide
theorem example_2_4 : SpreadTableCertified spreadRows [0, 1, 3] 3 := by
  unfold SpreadTableCertified spreadRows spreadResidual
  decide
theorem example_2_5_corrected :
    SquareSpreadTableCertified squareSpreadRows [0, 1] 2 := by
  unfold SquareSpreadTableCertified squareSpreadRows squareSpreadResidual
  decide

/-- The direct arithmetic discrepancy behind the correction: for the printed
candidate `4`, the spread radicand is `3`, not one of the displayed squares
`0`, `1`, and `4`. -/
theorem printed_four_radicand :
    (4 : F) * (1 - 4) = 3 ∧ (3 : F) ≠ 0 ∧ (3 : F) ≠ 1 ∧ (3 : F) ≠ 4 := by
  decide

end FieldFive

namespace FieldSeven

abbrev F := DivineProportions.FieldSeven.Element

def squareRows : List (SquareRow F) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 3⟩, ⟨4, 2⟩]
def spreadRows : List (SpreadRow F) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨3, 1⟩, ⟨4, 3⟩, ⟨5, 1⟩]
def squareSpreadRows : List (SquareSpreadRow F) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨4, 2, 3⟩]

theorem example_2_2 : SquareTableCertified squareRows [0, 1, 2, 4] 4 := by
  unfold SquareTableCertified squareRows squareResidual
  decide
theorem example_2_4 :
    SpreadTableCertified spreadRows [0, 1, 3, 4, 5] 5 := by
  unfold SpreadTableCertified spreadRows spreadResidual
  decide
theorem example_2_5 :
    SquareSpreadTableCertified squareSpreadRows [0, 1, 4] 3 := by
  unfold SquareSpreadTableCertified squareSpreadRows squareSpreadResidual
  decide

end FieldSeven

namespace FieldEleven

abbrev F := DivineProportions.FieldEleven.Element

def squareRows : List (SquareRow F) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨3, 5⟩, ⟨4, 2⟩, ⟨5, 4⟩, ⟨9, 3⟩]
def spreadRows : List (SpreadRow F) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 3⟩, ⟨3, 4⟩, ⟨6, 5⟩, ⟨9, 4⟩, ⟨10, 3⟩]
def squareSpreadRows : List (SquareSpreadRow F) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨3, 5, 4⟩, ⟨9, 3, 4⟩]

theorem example_2_2 :
    SquareTableCertified squareRows [0, 1, 3, 4, 5, 9] 6 := by
  unfold SquareTableCertified squareRows squareResidual
  decide
theorem example_2_4 :
    SpreadTableCertified spreadRows [0, 1, 2, 3, 6, 9, 10] 7 := by
  unfold SpreadTableCertified spreadRows spreadResidual
  decide
theorem example_2_5 :
    SquareSpreadTableCertified squareSpreadRows [0, 1, 3, 9] 4 := by
  unfold SquareSpreadTableCertified squareSpreadRows squareSpreadResidual
  decide

end FieldEleven

namespace FieldThirteen

abbrev F := DivineProportions.FieldThirteen.Element

def squareRows : List (SquareRow F) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨3, 4⟩, ⟨4, 2⟩, ⟨9, 3⟩, ⟨10, 6⟩, ⟨12, 5⟩]
def spreadRows : List (SpreadRow F) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨4, 1⟩, ⟨6, 3⟩, ⟨7, 6⟩, ⟨8, 3⟩, ⟨10, 1⟩]
def squareSpreadRows : List (SquareSpreadRow F) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨4, 2, 1⟩, ⟨10, 6, 1⟩]

theorem example_2_2 :
    SquareTableCertified squareRows [0, 1, 3, 4, 9, 10, 12] 7 := by
  unfold SquareTableCertified squareRows squareResidual
  decide
theorem example_2_4 :
    SpreadTableCertified spreadRows [0, 1, 4, 6, 7, 8, 10] 7 := by
  unfold SpreadTableCertified spreadRows spreadResidual
  decide
theorem example_2_5 :
    SquareSpreadTableCertified squareSpreadRows [0, 1, 4, 10] 4 := by
  unfold SquareSpreadTableCertified squareSpreadRows squareSpreadResidual
  decide

end FieldThirteen

namespace FieldSeventeen

/-- The seventeen displayed residue labels; no field instance or carrier
classification is installed. -/
abbrev F := Fin 17

instance instNeZeroSeventeen : NeZero 17 := ⟨by decide⟩

def squareRows : List (SquareRow F) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨2, 6⟩, ⟨4, 2⟩, ⟨8, 5⟩, ⟨9, 3⟩, ⟨13, 8⟩,
    ⟨15, 7⟩, ⟨16, 4⟩]
def spreadRows : List (SpreadRow F) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 7⟩, ⟨6, 2⟩, ⟨7, 3⟩, ⟨9, 8⟩, ⟨11, 3⟩,
    ⟨12, 2⟩, ⟨16, 7⟩]
def squareSpreadRows : List (SquareSpreadRow F) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨2, 6, 7⟩, ⟨9, 3, 8⟩, ⟨16, 4, 7⟩]

theorem example_2_2 :
    SquareTableCertified squareRows [0, 1, 2, 4, 8, 9, 13, 15, 16] 9 := by
  unfold SquareTableCertified squareRows squareResidual
  decide
theorem example_2_4 :
    SpreadTableCertified spreadRows [0, 1, 2, 6, 7, 9, 11, 12, 16] 9 := by
  unfold SpreadTableCertified spreadRows spreadResidual
  decide
theorem example_2_5 :
    SquareSpreadTableCertified squareSpreadRows [0, 1, 2, 9, 16] 5 := by
  unfold SquareSpreadTableCertified squareSpreadRows squareSpreadResidual
  decide

end FieldSeventeen

namespace FieldNineteen

abbrev F := DivineProportions.FieldNineteen.Element

def squareRows : List (SquareRow F) :=
  [⟨0, 0⟩, ⟨1, 1⟩, ⟨4, 2⟩, ⟨5, 9⟩, ⟨6, 5⟩, ⟨7, 8⟩, ⟨9, 3⟩,
    ⟨11, 7⟩, ⟨16, 4⟩, ⟨17, 6⟩]
def spreadRows : List (SpreadRow F) :=
  [⟨0, 0⟩, ⟨1, 0⟩, ⟨2, 6⟩, ⟨4, 8⟩, ⟨8, 1⟩, ⟨9, 2⟩, ⟨10, 9⟩,
    ⟨11, 2⟩, ⟨12, 1⟩, ⟨16, 8⟩, ⟨18, 6⟩]
def squareSpreadRows : List (SquareSpreadRow F) :=
  [⟨0, 0, 0⟩, ⟨1, 1, 0⟩, ⟨4, 2, 8⟩, ⟨9, 3, 2⟩, ⟨11, 7, 2⟩,
    ⟨16, 4, 8⟩]

theorem example_2_2 :
    SquareTableCertified squareRows [0, 1, 4, 5, 6, 7, 9, 11, 16, 17] 10 := by
  unfold SquareTableCertified squareRows squareResidual
  decide
theorem example_2_4 :
    SpreadTableCertified spreadRows [0, 1, 2, 4, 8, 9, 10, 11, 12, 16, 18] 11 := by
  unfold SpreadTableCertified spreadRows spreadResidual
  decide
theorem example_2_5 :
    SquareSpreadTableCertified squareSpreadRows [0, 1, 4, 9, 11, 16] 6 := by
  unfold SquareSpreadTableCertified squareSpreadRows squareSpreadResidual
  decide

end FieldNineteen

/-- Exercise 2.3, arithmetic branch `p=4l+1`: the square-spread count is
`l+1=(p+3)/4` once the finite unit-circle accounting is supplied. -/
theorem exercise_2_3_four_mul_add_one (l : Nat) :
    (4 * l + 1 + 3) / 4 = l + 1 := by omega0

/-- Exercise 2.3, arithmetic branch `p=4l+3`: the square-spread count is
`l+2=(p+5)/4` once the finite unit-circle accounting is supplied. -/
theorem exercise_2_3_four_mul_add_three (l : Nat) :
    (4 * l + 3 + 5) / 4 = l + 2 := by omega0

end FiniteSquareSpreadTables

end DivineProportions
