module

public import Init.Data.ToString.Basic
public import Purelib.Data.Nat.BitWidth
import Purelib.Data.Nat.Division
import Purelib.Data.Nat.Remainder
import Purelib.Tactic.QuotientFreeOmega
-- Fuel agreement reduces the original digit recursion and Nat.repr bodies.
import all Init.Data.Repr

namespace Purelib.Data.Nat.Decimal

/-- Every displayed binary power is positive. -/
private theorem twoPower_positive (width : Nat) : 0 < 2 ^ width := by
  induction width with
  | zero => exact Nat.zero_lt_succ 0
  | succ width ih =>
      rewrite [Nat.pow_succ]
      exact Nat.mul_pos ih (Nat.zero_lt_succ 1)

/-- A decimal quotient falls below the preceding displayed binary ceiling. -/
private theorem quotientBelow {width value : Nat} (bound : value < 2 ^ (width + 1)) :
    value / 10 < 2 ^ width := by
  have positive := twoPower_positive width
  have predecessor : (2 ^ width - 1) + 1 = 2 ^ width :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt positive)
  have expanded : value < 2 * 2 ^ width := by
    rewrite [Nat.pow_succ, Nat.mul_comm] at bound
    exact bound
  have large : value < 10 * ((2 ^ width - 1) + 1) := by
    rewrite [predecessor]
    exact Nat.lt_of_lt_of_le expanded (Nat.mul_le_mul_right (2 ^ width) (by decide +kernel))
  exact Nat.lt_of_le_of_lt (Division.div_le_of_lt_mul_succ large)
    (Nat.sub_lt positive (Nat.zero_lt_succ 0))

/-- Binary-width fuel reproduces the complete original decimal digit recursion.

The original input, accumulator and sufficient original counter remain on the
right. Each nonterminal decimal quotient fits the preceding binary ceiling,
so the shortened counter never changes a digit or the stopping branch.
-/
public theorem digits_binaryFuel_eq (width fuel value : Nat) (digits : List Char)
    (bound : value < 2 ^ width) (enough : value < fuel) :
    Nat.toDigitsCore 10 (width + 1) value digits = Nat.toDigitsCore 10 fuel value digits := by
  induction width generalizing fuel value digits with
  | zero =>
      have zeroValue : value = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
      cases zeroValue
      cases fuel with
      | zero => exact (Nat.not_lt_zero 0 enough).elim
      | succ fuel => rfl
  | succ width ih =>
      cases fuel with
      | zero => exact (Nat.not_lt_zero value enough).elim
      | succ fuel =>
          change
            (if value / 10 = 0 then Nat.digitChar (value % 10) :: digits else
              Nat.toDigitsCore 10 (width + 1) (value / 10) (Nat.digitChar (value % 10) :: digits)) =
            (if value / 10 = 0 then Nat.digitChar (value % 10) :: digits else
              Nat.toDigitsCore 10 fuel (value / 10) (Nat.digitChar (value % 10) :: digits))
          by_cases stopped : value / 10 = 0
          · rewrite [if_pos stopped, if_pos stopped]
            rfl
          · rewrite [if_neg stopped, if_neg stopped]
            have valuePositive : 0 < value := by
              cases value with
              | zero => exact (stopped rfl).elim
              | succ value => exact Nat.zero_lt_succ value
            have smaller := Division.div_lt_self valuePositive (by decide +kernel : 1 < 10)
            exact ih fuel (value / 10) _ (quotientBelow bound)
              (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ enough))

/-- Decimal division lowers a retained power-of-ten ceiling by one digit. -/
private theorem decimalQuotientBelow {width value : Nat}
    (bound : value < 10 ^ (width + 1)) : value / 10 < 10 ^ width := by
  have positive : 0 < 10 ^ width := Nat.pow_pos (by decide +kernel)
  have predecessor : (10 ^ width - 1) + 1 = 10 ^ width :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt positive)
  have large : value < 10 * ((10 ^ width - 1) + 1) := by
    rewrite [predecessor]
    rewrite [Nat.pow_succ, Nat.mul_comm] at bound
    exact bound
  exact Nat.lt_of_le_of_lt (Division.div_le_of_lt_mul_succ large)
    (Nat.sub_lt positive (Nat.zero_lt_succ 0))

/-- Binary ceilings make every sufficiently long original digit counter agree. -/
private theorem binaryFuelAgreement (width first second value : Nat) (digits : List Char)
    (bound : value < 2 ^ width) (firstEnough : width < first) (secondEnough : width < second) :
    Nat.toDigitsCore 10 first value digits = Nat.toDigitsCore 10 second value digits := by
  induction width generalizing first second value digits with
  | zero =>
      have zeroValue : value = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
      cases zeroValue
      cases first with
      | zero => exact (Nat.not_lt_zero 0 firstEnough).elim
      | succ first =>
          cases second with
          | zero => exact (Nat.not_lt_zero 0 secondEnough).elim
          | succ second => rfl
  | succ width ih =>
      cases first with
      | zero => exact (Nat.not_lt_zero _ firstEnough).elim
      | succ first =>
          cases second with
          | zero => exact (Nat.not_lt_zero _ secondEnough).elim
          | succ second =>
              change
                (if value / 10 = 0 then Nat.digitChar (value % 10) :: digits else
                  Nat.toDigitsCore 10 first (value / 10) (Nat.digitChar (value % 10) :: digits)) =
                (if value / 10 = 0 then Nat.digitChar (value % 10) :: digits else
                  Nat.toDigitsCore 10 second (value / 10) (Nat.digitChar (value % 10) :: digits))
              by_cases stopped : value / 10 = 0
              · rewrite [if_pos stopped, if_pos stopped]
                rfl
              · rewrite [if_neg stopped, if_neg stopped]
                exact ih first second _ _ (quotientBelow bound)
                  (Nat.lt_of_succ_lt_succ firstEnough) (Nat.lt_of_succ_lt_succ secondEnough)

/-- Both sufficiently long counters retain the same complete original decimal digits. -/
private theorem decimalFuelAgreement (width first second value : Nat) (digits : List Char)
    (bound : value < 10 ^ width) (firstEnough : width < first) (secondEnough : width < second) :
    Nat.toDigitsCore 10 first value digits = Nat.toDigitsCore 10 second value digits := by
  induction width generalizing first second value digits with
  | zero =>
      have zeroValue : value = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
      cases zeroValue
      cases first with
      | zero => exact (Nat.not_lt_zero 0 firstEnough).elim
      | succ first =>
          cases second with
          | zero => exact (Nat.not_lt_zero 0 secondEnough).elim
          | succ second => rfl
  | succ width ih =>
      cases first with
      | zero => exact (Nat.not_lt_zero _ firstEnough).elim
      | succ first =>
          cases second with
          | zero => exact (Nat.not_lt_zero _ secondEnough).elim
          | succ second =>
              change
                (if value / 10 = 0 then Nat.digitChar (value % 10) :: digits else
                  Nat.toDigitsCore 10 first (value / 10) (Nat.digitChar (value % 10) :: digits)) =
                (if value / 10 = 0 then Nat.digitChar (value % 10) :: digits else
                  Nat.toDigitsCore 10 second (value / 10) (Nat.digitChar (value % 10) :: digits))
              by_cases stopped : value / 10 = 0
              · rewrite [if_pos stopped, if_pos stopped]
                rfl
              · rewrite [if_neg stopped, if_neg stopped]
                exact ih first second _ _ (decimalQuotientBelow bound)
                  (Nat.lt_of_succ_lt_succ firstEnough) (Nat.lt_of_succ_lt_succ secondEnough)

/-- Retain exactly the requested number of decimal places, including leading zero places. -/
@[expose] public def places : Nat → Nat → List Char → List Char
  | 0, _, digits => digits
  | count + 1, value, digits =>
      places count (value / 10) (Nat.digitChar (value % 10) :: digits)

/-- A retained positive leading keeps all requested low decimal places before original continuation. -/
private theorem originalPlaces (count fuel leading remainder : Nat) (digits : List Char)
    (leadingPositive : 0 < leading) (remainderBound : remainder < 10 ^ count) :
    Nat.toDigitsCore 10 (count + fuel) (10 ^ count * leading + remainder) digits =
      Nat.toDigitsCore 10 fuel leading (places count remainder digits) := by
  induction count generalizing fuel leading remainder digits with
  | zero =>
      have zeroRemainder : remainder = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ remainderBound)
      cases zeroRemainder
      rewrite [Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add]
      rfl
  | succ count ih =>
      have decomposition : 10 ^ (count + 1) * leading + remainder =
          10 * (10 ^ count * leading) + remainder := by
        rewrite [Nat.pow_succ, Nat.mul_comm (10 ^ count) 10, Nat.mul_assoc]
        rfl
      have quotient : (10 ^ (count + 1) * leading + remainder) / 10 =
          10 ^ count * leading + remainder / 10 := by
        rewrite [decomposition]
        exact Division.mul_add_div (by decide +kernel : 0 < 10) _ _
      have lastPlace : (10 ^ (count + 1) * leading + remainder) % 10 = remainder % 10 := by
        rewrite [decomposition]
        exact Remainder.mul_add_mod 10 _ _
      have quotientPositive : 0 < 10 ^ count * leading + remainder / 10 :=
        Nat.lt_of_lt_of_le (Nat.mul_pos (Nat.pow_pos (by decide +kernel)) leadingPositive)
          (Nat.le_add_right _ _)
      have fuelShape : count + 1 + fuel = (count + fuel) + 1 := by omega0
      rewrite [fuelShape]
      change
        (if (10 ^ (count + 1) * leading + remainder) / 10 = 0 then
          Nat.digitChar ((10 ^ (count + 1) * leading + remainder) % 10) :: digits else
          Nat.toDigitsCore 10 (count + fuel) ((10 ^ (count + 1) * leading + remainder) / 10)
            (Nat.digitChar ((10 ^ (count + 1) * leading + remainder) % 10) :: digits)) = _
      rewrite [quotient, lastPlace, if_neg (Nat.ne_of_gt quotientPositive)]
      exact ih fuel leading (remainder / 10) _ leadingPositive (decimalQuotientBelow remainderBound)

/-- A nine-place quotient falls below the preceding retained binary ceiling. -/
private theorem chunkQuotientBelow {width value : Nat} (bound : value < 2 ^ (width + 1)) :
    value / 1000000000 < 2 ^ width := by
  have positive := twoPower_positive width
  have predecessor : (2 ^ width - 1) + 1 = 2 ^ width :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt positive)
  have expanded : value < 2 * 2 ^ width := by
    rewrite [Nat.pow_succ, Nat.mul_comm] at bound
    exact bound
  have large : value < 1000000000 * ((2 ^ width - 1) + 1) := by
    rewrite [predecessor]
    exact Nat.lt_of_lt_of_le expanded
      (Nat.mul_le_mul_right (2 ^ width) (by decide +kernel))
  exact Nat.lt_of_le_of_lt (Division.div_le_of_lt_mul_succ large)
    (Nat.sub_lt positive (Nat.zero_lt_succ 0))

/-- Render retained nine-digit chunks, caching the original large quotient and remainder once per chunk. -/
@[expose] public def groupedDigits : Nat → Nat → List Char → List Char
  | 0, value, digits => Nat.toDigitsCore 10 1 value digits
  | fuel + 1, value, digits =>
      let quotient := value / 1000000000
      let remainder := value % 1000000000
      if quotient = 0 then Nat.toDigitsCore 10 10 remainder digits else
        groupedDigits fuel quotient (places 9 remainder digits)

/-- Grouped division retains the complete original digit list under the original binary ceiling. -/
public theorem groupedDigits_eq (width value : Nat) (digits : List Char)
    (bound : value < 2 ^ width) :
    groupedDigits width value digits = Nat.toDigitsCore 10 (9 * width + 1) value digits := by
  induction width generalizing value digits with
  | zero =>
      have zeroValue : value = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ bound)
      cases zeroValue
      rfl
  | succ width ih =>
      let quotient := value / 1000000000
      let remainder := value % 1000000000
      have remainderBound : remainder < 1000000000 := Nat.mod_lt value (by decide +kernel)
      have decomposition : value = 1000000000 * quotient + remainder := by
        exact (Division.mod_add_div value 1000000000).symm.trans
          (Nat.add_comm _ _)
      change (if quotient = 0 then Nat.toDigitsCore 10 10 remainder digits else
        groupedDigits width quotient (places 9 remainder digits)) = _
      by_cases stopped : quotient = 0
      · rewrite [if_pos stopped]
        have valueEq : value = remainder := by
          rewrite [decomposition, stopped, Nat.mul_zero, Nat.zero_add]
          rfl
        rewrite [valueEq]
        apply decimalFuelAgreement 9 10 (9 * (width + 1) + 1) remainder digits
        · exact remainderBound
        · decide +kernel
        · omega0
      · rewrite [if_neg stopped, ih quotient _ (chunkQuotientBelow bound)]
        have leadingPositive : 0 < quotient := Nat.zero_lt_of_ne_zero stopped
        have groupedFuel : 9 * (width + 1) + 1 = 9 + (9 * width + 1) := by omega0
        rewrite [groupedFuel, decomposition]
        exact (originalPlaces 9 (9 * width + 1) quotient remainder digits leadingPositive
          remainderBound).symm

/-- Cache squared decimal divisors from highest to lowest for half-width recursion.

Each supplied power is retained once before squaring. Both rendering children
consume the same original list tail, rather than rebuilding their divisors.
-/
@[expose] public def halfPowers : Nat → Nat → Nat → List Nat
  | 0, _, _ => []
  | fuel + 1, value, power =>
      if value < power then [] else halfPowers fuel value (power * power) ++ [power]

/-- Render all low-half places, preserving zero padding at every retained split.

The empty table emits nine places. A table of squared decimal powers splits
both quotient and remainder at the same retained half-width before continuing
on its original tail. The exposed body supports ordinary-import reduction.
-/
@[expose] public def fixedHalves : List Nat → Nat → List Char → List Char
  | [], value, digits => places 9 value digits
  | power :: remaining, value, digits =>
      let quotient := value / power
      let remainder := value % power
      fixedHalves remaining quotient (fixedHalves remaining remainder digits)

/-- Render the leading half without zeros and every lower half at its retained width.

Unused high halves are omitted only along the leading path. Every lower half
uses the retained fixed-width program, including all its required zero places.
-/
@[expose] public def balancedDigits : List Nat → Nat → List Char → List Char
  | [], value, digits => Nat.toDigitsCore 10 10 value digits
  | power :: remaining, value, digits =>
      let quotient := value / power
      let remainder := value % power
      if quotient = 0 then balancedDigits remaining remainder digits else
        balancedDigits remaining quotient (fixedHalves remaining remainder digits)

/-- Render a natural using retained squared powers and fixed-width lower halves.

The original small-value branch remains unchanged. Each lower half keeps its
complete fixed-width padding; `repr_eq` retains the original string
record for every input.
-/
@[expose] public def repr (value : Nat) : _root_.String :=
  if value < USize.size then Nat.repr value else
    let powers := halfPowers (BitWidth.natWidth value) value 1000000000
    _root_.String.ofList (balancedDigits powers value [])

/-- A cached divisor list retains exactly its doubled fixed decimal widths.

The nine-place leaf is doubled by each retained power-of-ten divisor. This
proof-only shape keeps its actual list and width as correctness indices.
-/
private inductive PowerShape : Nat → List Nat → Prop
  /-- The original nine-place leaf. -/
  | base : PowerShape 9 []
  /-- One retained divisor joins two equal fixed-width halves. -/
  | step {width : Nat} {powers : List Nat} : PowerShape width powers →
      PowerShape (width + width) (10 ^ width :: powers)

/-- Every retained half-width divisor is at least two.

The nine-place leaf has this bound, and each successive squaring preserves it.
-/
private theorem PowerShape.two_le_power {width : Nat} {powers : List Nat}
    (shape : PowerShape width powers) : 2 ≤ 10 ^ width := by
  induction shape with
  | base => decide +kernel
  | @step width powers shape ih =>
      have positive : 1 ≤ 10 ^ width := Nat.le_trans (by decide +kernel : 1 ≤ 2) ih
      have growth := Nat.mul_le_mul_left (10 ^ width) positive
      rewrite [Nat.mul_one] at growth
      rewrite [Nat.pow_add]
      exact Nat.le_trans ih growth

/-- Fixed decimal places split at the original retained power without losing zero padding.

The low remainder is below its displayed power. The leading value may be zero,
so the equality also preserves fixed-width padding in all lower halves.
-/
private theorem splitPlaces (count fuel leading remainder : Nat) (digits : List Char)
    (remainderBound : remainder < 10 ^ count) :
    places (count + fuel) (10 ^ count * leading + remainder) digits =
      places fuel leading (places count remainder digits) := by
  induction count generalizing fuel leading remainder digits with
  | zero =>
      have zeroRemainder : remainder = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ remainderBound)
      cases zeroRemainder
      rewrite [Nat.pow_zero, Nat.one_mul, Nat.add_zero, Nat.zero_add]
      rfl
  | succ count ih =>
      have decomposition : 10 ^ (count + 1) * leading + remainder =
          10 * (10 ^ count * leading) + remainder := by
        rewrite [Nat.pow_succ, Nat.mul_comm (10 ^ count) 10, Nat.mul_assoc]
        rfl
      have quotient : (10 ^ (count + 1) * leading + remainder) / 10 =
          10 ^ count * leading + remainder / 10 := by
        rewrite [decomposition]
        exact Division.mul_add_div (by decide +kernel : 0 < 10) _ _
      have lastPlace : (10 ^ (count + 1) * leading + remainder) % 10 = remainder % 10 := by
        rewrite [decomposition]
        exact Remainder.mul_add_mod 10 _ _
      have fuelShape : count + 1 + fuel = (count + fuel) + 1 := by omega0
      rewrite [fuelShape]
      change places (count + fuel) ((10 ^ (count + 1) * leading + remainder) / 10)
        (Nat.digitChar ((10 ^ (count + 1) * leading + remainder) % 10) :: digits) =
          places fuel leading (places count (remainder / 10) (Nat.digitChar (remainder % 10) :: digits))
      rewrite [quotient, lastPlace]
      exact ih fuel leading (remainder / 10) _ (decimalQuotientBelow remainderBound)

/-- The cached fixed-half program retains every original decimal place for all bounded inputs.

The exact table shape and its power-of-ten ceiling bound the retained input;
the original trailing accumulator remains unchanged.
-/
private theorem fixedHalves_eq {width : Nat} {powers : List Nat} (shape : PowerShape width powers)
    (value : Nat) (digits : List Char) (bound : value < 10 ^ width) :
    fixedHalves powers value digits = places width value digits := by
  induction shape generalizing value digits with
  | base => rfl
  | @step width powers shape ih =>
      have productBound : value < 10 ^ width * 10 ^ width := by
        rewrite [Nat.pow_add] at bound
        exact bound
      have quotientBound : value / 10 ^ width < 10 ^ width := Division.div_lt_of_lt_mul productBound
      have remainderBound : value % 10 ^ width < 10 ^ width :=
        Nat.mod_lt value (Nat.pow_pos (by decide +kernel))
      have decomposition : value = 10 ^ width * (value / 10 ^ width) + value % 10 ^ width :=
        (Division.mod_add_div value (10 ^ width)).symm.trans (Nat.add_comm _ _)
      change fixedHalves powers (value / 10 ^ width)
        (fixedHalves powers (value % 10 ^ width) digits) = _
      rewrite [ih _ digits remainderBound, ih _ _ quotientBound]
      exact ((splitPlaces width width (value / 10 ^ width) (value % 10 ^ width) digits remainderBound).symm).trans
        (congrArg (fun current => places (width + width) current digits) decomposition.symm)

/-- Leading-half rendering agrees with the original sufficient decimal counter at every cached width.

The bound refers to the same cached table width. The original counter is that
width plus one, and the equality retains its complete trailing accumulator.
-/
private theorem balancedDigits_eq {width : Nat} {powers : List Nat} (shape : PowerShape width powers)
    (value : Nat) (digits : List Char) (bound : value < 10 ^ width) :
    balancedDigits powers value digits = Nat.toDigitsCore 10 (width + 1) value digits := by
  induction shape generalizing value digits with
  | base => rfl
  | @step width powers shape ih =>
      have productBound : value < 10 ^ width * 10 ^ width := by
        rewrite [Nat.pow_add] at bound
        exact bound
      let quotient := value / 10 ^ width
      let remainder := value % 10 ^ width
      have quotientBound : quotient < 10 ^ width := Division.div_lt_of_lt_mul productBound
      have remainderBound : remainder < 10 ^ width := Nat.mod_lt value (Nat.pow_pos (by decide +kernel))
      have decomposition : value = 10 ^ width * quotient + remainder :=
        (Division.mod_add_div value (10 ^ width)).symm.trans (Nat.add_comm _ _)
      change (if quotient = 0 then balancedDigits powers remainder digits else
        balancedDigits powers quotient (fixedHalves powers remainder digits)) = _
      by_cases stopped : quotient = 0
      · rewrite [if_pos stopped, ih remainder digits remainderBound]
        have same : value = remainder := by
          rewrite [decomposition, stopped, Nat.mul_zero, Nat.zero_add]
          rfl
        rewrite [same]
        exact decimalFuelAgreement width (width + 1) (width + width + 1) remainder digits
          remainderBound (Nat.lt_succ_self _) (by omega0)
      · rewrite [if_neg stopped, fixedHalves_eq shape remainder digits remainderBound,
          ih quotient _ quotientBound]
        have original := originalPlaces width (width + 1) quotient remainder digits
          (Nat.zero_lt_of_ne_zero stopped) remainderBound
        have fuelShape : width + (width + 1) = width + width + 1 := by omega0
        rewrite [fuelShape] at original
        exact original.symm.trans
          (congrArg (fun current => Nat.toDigitsCore 10 (width + width + 1) current digits) decomposition.symm)

/-- Growing the retained divisor table yields an actual sufficient fixed width before fuel is exhausted.

The initial decimal divisor compensates for each binary fuel decrement by
squaring. The completed original table therefore has an actual power-of-ten
ceiling above the supplied value, without a separately recomputed divisor list.
-/
private theorem halfPowers_shape (fuel value width : Nat) (lower : List Nat)
    (shape : PowerShape width lower) (bound : value < 10 ^ width * 2 ^ fuel) :
    ∃ finalWidth, PowerShape finalWidth (halfPowers fuel value (10 ^ width) ++ lower) ∧
      value < 10 ^ finalWidth := by
  induction fuel generalizing width lower with
  | zero =>
      refine ⟨width, shape, ?_⟩
      rewrite [Nat.pow_zero, Nat.mul_one] at bound
      exact bound
  | succ fuel ih =>
      by_cases finished : value < 10 ^ width
      · refine ⟨width, ?_, finished⟩
        change PowerShape width ((if value < 10 ^ width then [] else
          halfPowers fuel value (10 ^ width * 10 ^ width) ++ [10 ^ width]) ++ lower)
        rewrite [if_pos finished]
        exact shape
      · have growth : 10 ^ width * 2 ^ (fuel + 1) ≤ (10 ^ width * 10 ^ width) * 2 ^ fuel := by
          have scaled := Nat.mul_le_mul_right (2 ^ fuel)
            (Nat.mul_le_mul_left (10 ^ width) shape.two_le_power)
          have same : 10 ^ width * 2 ^ (fuel + 1) = (10 ^ width * 2) * 2 ^ fuel := by
            rewrite [Nat.pow_succ, Nat.mul_comm (2 ^ fuel) 2, Nat.mul_assoc]
            rfl
          exact Nat.le_trans (Nat.le_of_eq same) scaled
        have nextBound : value < 10 ^ (width + width) * 2 ^ fuel := by
          rewrite [Nat.pow_add]
          exact Nat.lt_of_lt_of_le bound growth
        obtain ⟨finalWidth, finalShape, finalBound⟩ :=
          ih (width + width) (10 ^ width :: lower) (PowerShape.step shape) nextBound
        refine ⟨finalWidth, ?_, finalBound⟩
        change PowerShape finalWidth ((if value < 10 ^ width then [] else
          halfPowers fuel value (10 ^ width * 10 ^ width) ++ [10 ^ width]) ++ lower)
        rewrite [if_neg finished, List.append_assoc]
        rewrite [Nat.pow_add] at finalShape
        exact finalShape

/-- Every original digit counter longer than its value returns the same complete digits.

A nonterminal decimal quotient is smaller than the original value, so both
retained counters remain sufficient until the same first zero quotient.
-/
private theorem originalFuelAgreement (first second value : Nat) (digits : List Char)
    (firstEnough : value < first) (secondEnough : value < second) :
    Nat.toDigitsCore 10 first value digits = Nat.toDigitsCore 10 second value digits := by
  induction first generalizing second value digits with
  | zero => exact (Nat.not_lt_zero value firstEnough).elim
  | succ first ih =>
      cases second with
      | zero => exact (Nat.not_lt_zero value secondEnough).elim
      | succ second =>
          change (if value / 10 = 0 then Nat.digitChar (value % 10) :: digits else
            Nat.toDigitsCore 10 first (value / 10) (Nat.digitChar (value % 10) :: digits)) =
              (if value / 10 = 0 then Nat.digitChar (value % 10) :: digits else
                Nat.toDigitsCore 10 second (value / 10) (Nat.digitChar (value % 10) :: digits))
          by_cases stopped : value / 10 = 0
          · rewrite [if_pos stopped, if_pos stopped]
            rfl
          · rewrite [if_neg stopped, if_neg stopped]
            have positive : 0 < value := by
              cases value with
              | zero => exact (stopped rfl).elim
              | succ value => exact Nat.zero_lt_succ value
            have smaller := Division.div_lt_self positive (by decide +kernel : 1 < 10)
            exact ih second _ _ (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ firstEnough))
              (Nat.lt_of_lt_of_le smaller (Nat.le_of_lt_succ secondEnough))

/-- Any sufficient decimal-width counter returns the complete original digit list.

The decimal ceiling covers short width counters. Counters above the value
agree through the original value-fuel recursion, including all leading cases.
-/
private theorem decimalDigits_eq_original (width value : Nat) (digits : List Char)
    (bound : value < 10 ^ width) :
    Nat.toDigitsCore 10 (width + 1) value digits = Nat.toDigitsCore 10 (value + 1) value digits := by
  by_cases short : value < width
  · exact originalFuelAgreement _ _ value digits (Nat.lt_trans short (Nat.lt_succ_self width)) (Nat.lt_succ_self value)
  · exact decimalFuelAgreement width (width + 1) (value + 1) value digits bound (Nat.lt_succ_self width)
      (Nat.lt_succ_of_le (Nat.le_of_not_gt short))

/-- Balanced rendering returns the complete original string record for every natural input.

The small branch is unchanged. The large branch consumes its actual certified
power table and the complete original digit accumulator, including zero padding.
-/
public theorem repr_eq (value : Nat) : repr value = Nat.repr value := by
  unfold repr
  split
  · rfl
  · have initialBound : value < 10 ^ 9 * 2 ^ BitWidth.natWidth value :=
      Nat.lt_of_lt_of_le (BitWidth.lt_two_pow_natWidth value) (by
        have positive : 1 ≤ 10 ^ 9 := by decide +kernel
        have multiplied := Nat.mul_le_mul_right (2 ^ BitWidth.natWidth value) positive
        rewrite [Nat.one_mul] at multiplied
        exact multiplied)
    obtain ⟨width, shape, bound⟩ := halfPowers_shape (BitWidth.natWidth value) value 9 []
      PowerShape.base initialBound
    rewrite [List.append_nil] at shape
    change PowerShape width (halfPowers (BitWidth.natWidth value) value 1000000000) at shape
    change _root_.String.ofList (balancedDigits
      (halfPowers (BitWidth.natWidth value) value 1000000000) value []) =
        _root_.String.ofList (Nat.toDigitsCore 10 (value + 1) value [])
    exact congrArg _root_.String.ofList ((balancedDigits_eq shape value [] bound).trans
      (decimalDigits_eq_original width value [] bound))

/-- Rendering preserves the complete shortened-fuel string, including its original small-value branch. -/
public theorem repr_eq_binaryFuel (value : Nat) :
    repr value = if value < USize.size then Nat.repr value else
      _root_.String.ofList (Nat.toDigitsCore 10 (BitWidth.natWidth value + 1) value []) := by
  rewrite [repr_eq]
  split
  · rfl
  · change _root_.String.ofList (Nat.toDigitsCore 10 (value + 1) value []) =
      _root_.String.ofList (Nat.toDigitsCore 10 (BitWidth.natWidth value + 1) value [])
    exact congrArg _root_.String.ofList
      (digits_binaryFuel_eq (BitWidth.natWidth value) (value + 1) value []
        (BitWidth.lt_two_pow_natWidth value) (Nat.lt_succ_self value)).symm

/-- Balanced rendering preserves every complete original UTF-8 byte array. -/
public theorem repr_bytes (value : Nat) : (repr value).toByteArray = (Nat.repr value).toByteArray :=
  congrArg _root_.String.toByteArray (repr_eq value)

end Purelib.Data.Nat.Decimal
