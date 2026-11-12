module
public import Purelib.Data.Rat.Rounding.Floor.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Parity
import Purelib.Data.List.Nodup
import Purelib.Data.List.Range.Nodup
import Purelib.Data.List.Range.Basic
import Purelib.Data.List.Map
import Purelib.Tactic.Ring

/-!
# Exact rational reciprocal step

Each positive rational query evaluates the original reciprocal, integer floor
and parity. The origin and nonpositive queries return zero. No real-name
comparison, infinite list or limiting computation is used.
-/

public section

namespace Purelib.Integration.Step.Reciprocal

open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction.Order

/-- Evaluate the parity of the exact reciprocal floor at a rational point.

At positive inputs the integer floor is nonnegative, so its natural readback
and remainder modulo two give the original floor parity. Nonpositive inputs
return zero; in particular the retained origin value is zero. -/
@[expose] def value (point : Fraction.Rational) : Fraction.Rational :=
  if 0 < point then ((Rounding.Floor.floor (1 / point)).toNat % 2 : Nat) else 0

/-- The origin has the retained exact value zero. -/
theorem value_zero : value 0 = 0 := by
  unfold value
  rw [if_neg (by decide : ¬ (0 : Fraction.Rational) < 0)]

/-- Every rational evaluation lies in the exact closed range from zero to one. -/
theorem value_range (point : Fraction.Rational) : 0 ≤ value point ∧ value point ≤ 1 := by
  unfold value
  split
  · have bound : (Rounding.Floor.floor (1 / point)).toNat % 2 ≤ 1 :=
      Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
    exact ⟨Fraction.Cast.Order.natCast_le_direct (Nat.zero_le _), Fraction.Cast.Order.natCast_le_direct bound⟩
  · exact ⟨Fraction.Order.Basic.le_refl _, by decide⟩

/-- The reciprocal floor of a positive rational is a nonnegative integer. -/
theorem floor_nonnegative (point : Fraction.Rational) (positive : 0 < point) :
    0 ≤ Rounding.Floor.floor (1 / point) := by
  apply (Rounding.Floor.intCast_le_iff_floor 0 (1 / point)).mp
  exact (Fraction.Order.Field.div_pos_direct (by decide) positive).le

/-- At a positive point the natural readback is exactly the integer floor parity. -/
theorem value_eq_integer_parity (point : Fraction.Rational) (positive : 0 < point) :
    value point = ((Rounding.Floor.floor (1 / point) % 2 : Int) : Fraction.Rational) := by
  unfold value
  rw [if_pos positive]
  have nonnegative := floor_nonnegative point positive
  cases floorEq : Rounding.Floor.floor (1 / point) with
  | ofNat number =>
      rw [Fraction.Cast.natCast_eq_fromInt, Fraction.Cast.intCast_eq_fromInt]
      rfl
  | negSucc number =>
      rw [floorEq] at nonnegative
      cases nonnegative

/-- A known natural reciprocal floor gives the exact retained parity reading. -/
theorem value_of_floor (point : Fraction.Rational) (positive : 0 < point) (index : Nat)
    (floor_eq : Rounding.Floor.floor (1 / point) = (index : Int)) :
    value point = ((index % 2 : Nat) : Fraction.Rational) := by
  unfold value
  rw [if_pos positive, floor_eq]
  rfl

/-- The original floor of a natural rational cast is exactly that natural integer. -/
theorem floor_natCast (index : Nat) : Rounding.Floor.floor (index : Fraction.Rational) = (index : Int) := by
  apply Rounding.Floor.Bounds.floor_eq_of_bounds (index : Int) (index : Fraction.Rational)
  · rw [← Fraction.Cast.natCast_eq_fromInt index]
  · have next := Fraction.Cast.Order.natCast_lt_direct (Nat.lt_succ_self index)
    rw [Fraction.Cast.natCast_eq_fromInt (index + 1)] at next
    exact next

/-- A positive natural reciprocal is read with the parity of its exact cut index. -/
theorem value_at_reciprocal (index : Nat) (positive : 0 < index) :
    value (1 / (index : Fraction.Rational)) = ((index % 2 : Nat) : Fraction.Rational) := by
  have castPositive : 0 < (index : Fraction.Rational) := Fraction.Cast.Order.natCast_pos_direct positive
  have pointPositive : 0 < 1 / (index : Fraction.Rational) :=
    Fraction.Order.Field.div_pos_direct (by decide) castPositive
  have reciprocal : 1 / (1 / (index : Fraction.Rational)) = (index : Fraction.Rational) := by
    apply Fraction.Field.mul_right_cancel_of_ne pointPositive.ne'
    calc
      (1 / (1 / (index : Fraction.Rational))) * (1 / (index : Fraction.Rational)) = 1 :=
        Fraction.Field.div_mul_cancel_of_ne 1 _ pointPositive.ne'
      _ = (index : Fraction.Rational) * (1 / (index : Fraction.Rational)) := by
        rw [Fraction.Field.mul_comm, Fraction.Field.div_mul_cancel_of_ne 1 _ castPositive.ne']
  apply value_of_floor _ pointPositive index
  rw [reciprocal]
  exact floor_natCast index

/-- Reciprocal displacement is no greater than displacement above one.

The exact cross-product identity gives the difference as `(upper - lower)`
divided by the product of the original positive denominators. -/
private theorem reciprocal_displacement {lower upper : Fraction.Rational}
    (lowerBound : 1 ≤ lower) (ordered : lower ≤ upper) :
    1 / lower - 1 / upper ≤ upper - lower := by
  have upperBound : 1 ≤ upper := lowerBound.trans ordered
  have lowerPositive : 0 < lower := (by decide : (0 : Fraction.Rational) < 1).trans_le lowerBound
  have upperPositive : 0 < upper := (by decide : (0 : Fraction.Rational) < 1).trans_le upperBound
  have productBound : 1 ≤ lower * upper := by
    have scaled := Arithmetic.mul_le_mul_direct lowerBound upperBound
      (by decide : (0 : Fraction.Rational) ≤ 1) lowerPositive.le
    simpa only [Fraction.Field.one_mul] using scaled
  rw [Fraction.Field.div_sub_div_direct 1 lower 1 upper lowerPositive.ne' upperPositive.ne']
  rw [Fraction.Field.one_mul, Fraction.Field.one_mul]
  exact Fraction.Order.Field.divide_le_self (Arithmetic.sub_nonneg_direct ordered) productBound

/-- Strictly increasing positive denominators strictly decrease their reciprocals. -/
private theorem reciprocal_lt {lower upper : Fraction.Rational}
    (lowerPositive : 0 < lower) (ordered : lower < upper) :
    1 / upper < 1 / lower := by
  have upperPositive := lowerPositive.trans ordered
  apply Arithmetic.lt_of_sub_pos_direct
  rw [Fraction.Field.div_sub_div_direct 1 lower 1 upper lowerPositive.ne' upperPositive.ne']
  rw [Fraction.Field.one_mul, Fraction.Field.one_mul]
  exact Fraction.Order.Field.div_pos_direct (Arithmetic.sub_pos_direct ordered)
    (Arithmetic.mul_pos_direct lowerPositive upperPositive)

/-- A positive denominator is recovered exactly by taking two reciprocals. -/
private theorem reciprocal_reciprocal {denominator : Fraction.Rational} (positive : 0 < denominator) :
    1 / (1 / denominator) = denominator := by
  have inversePositive : 0 < 1 / denominator := Fraction.Order.Field.div_pos_direct (by decide) positive
  apply Fraction.Field.mul_right_cancel_of_ne inversePositive.ne'
  calc
    (1 / (1 / denominator)) * (1 / denominator) = 1 :=
      Fraction.Field.div_mul_cancel_of_ne 1 _ inversePositive.ne'
    _ = denominator * (1 / denominator) := by
      rw [Fraction.Field.mul_comm, Fraction.Field.div_mul_cancel_of_ne 1 _ positive.ne']

/-- Natural lower and successor bounds identify the original rational floor. -/
private theorem floor_between_nat (index : Nat) (number : Fraction.Rational)
    (lower : (index : Fraction.Rational) ≤ number)
    (upper : number < ((index + 1 : Nat) : Fraction.Rational)) :
    Rounding.Floor.floor number = (index : Int) := by
  apply Rounding.Floor.Bounds.floor_eq_of_bounds
  · rwa [← Fraction.Cast.natCast_eq_fromInt index]
  · rw [Fraction.Cast.natCast_eq_fromInt (index + 1)] at upper
    exact upper

/-- Every reciprocal cut from one half onward has opposite rational side readings.

For any positive neighborhood radius, both witnesses are inside the unit
interval, strictly on opposite sides of the exact cut and less than the
requested distance from it. Their original evaluations are zero and one in
one order or the other. The cut itself uses the floor's lower endpoint. -/
theorem jump_witnesses (index : Nat) (radius : Fraction.Rational) (radiusPositive : 0 < radius) :
    ∃ left right : Fraction.Rational,
      0 < left ∧ right ≤ 1 ∧
      left < 1 / ((index + 2 : Nat) : Fraction.Rational) ∧
      1 / ((index + 2 : Nat) : Fraction.Rational) < right ∧
      1 / ((index + 2 : Nat) : Fraction.Rational) - left < radius ∧
      right - 1 / ((index + 2 : Nat) : Fraction.Rational) < radius ∧
      ((value left = 0 ∧ value right = 1) ∨ (value left = 1 ∧ value right = 0)) := by
  let shift : Fraction.Rational := min (1 / 2) (radius / 2)
  have shiftPositive : 0 < shift := Fraction.Order.Basic.lt_min (by decide)
    (Fraction.Order.Field.div_pos_direct radiusPositive (by decide))
  have shiftLtOne : shift < 1 :=
    (Fraction.Order.Basic.min_le_left (1 / 2 : Fraction.Rational) (radius / 2)).trans_lt (by decide)
  have shiftLtRadius : shift < radius :=
    (Fraction.Order.Basic.min_le_right (1 / 2 : Fraction.Rational) (radius / 2)).trans_lt
      (Fraction.Order.Field.half_lt_self radiusPositive)
  let base : Fraction.Rational := (index : Fraction.Rational) + 1
  let cut : Fraction.Rational := base + 1
  let leftDenominator : Fraction.Rational := cut + shift
  let rightDenominator : Fraction.Rational := cut - shift
  have baseBound : 1 ≤ base := by
    have nonnegative := Fraction.Cast.Order.natCast_le_direct (Nat.zero_le index)
    change (0 : Fraction.Rational) ≤ (index : Fraction.Rational) at nonnegative
    have bound := Arithmetic.add_le_add_right_direct nonnegative 1
    rw [Fraction.Field.zero_add] at bound
    exact bound
  have baseLessRight : base < rightDenominator := by
    have positive := Arithmetic.sub_pos_direct shiftLtOne
    have bound := Arithmetic.add_lt_add_left_direct positive base
    rw [show base + 0 = base by ring1] at bound
    have identity : base + (1 - shift) = rightDenominator := by dsimp [rightDenominator, cut]; ring1
    rw [identity] at bound
    exact bound
  have rightLessCut : rightDenominator < cut := by
    have bound := Arithmetic.sub_lt_sub_left_direct shiftPositive cut
    rw [show cut - 0 = cut by ring1] at bound
    exact bound
  have cutLessLeft : cut < leftDenominator := by
    have bound := Arithmetic.add_lt_add_left_direct shiftPositive cut
    rw [show cut + 0 = cut by ring1] at bound
    exact bound
  have leftLessSuccessor : leftDenominator < cut + 1 :=
    Arithmetic.add_lt_add_left_direct shiftLtOne cut
  have rightBound : 1 ≤ rightDenominator := baseBound.trans baseLessRight.le
  have cutBound : 1 ≤ cut := rightBound.trans rightLessCut.le
  have leftBound : 1 ≤ leftDenominator := cutBound.trans cutLessLeft.le
  have rightPositive : 0 < rightDenominator := (by decide : (0 : Fraction.Rational) < 1).trans_le rightBound
  have cutPositive : 0 < cut := (by decide : (0 : Fraction.Rational) < 1).trans_le cutBound
  have leftPositive : 0 < leftDenominator := (by decide : (0 : Fraction.Rational) < 1).trans_le leftBound
  have cutEq : cut = ((index + 2 : Nat) : Fraction.Rational) := by
    dsimp [cut, base]
    rw [Fraction.Cast.natCast_add_direct]
    ring1
  have baseEq : base = ((index + 1 : Nat) : Fraction.Rational) := by
    dsimp [base]
    rw [Fraction.Cast.natCast_add_direct]
    rw [show ((1 : Nat) : Fraction.Rational) = 1 by decide]
  have nextEq : cut + 1 = ((index + 2 + 1 : Nat) : Fraction.Rational) := by
    rw [cutEq, Fraction.Cast.natCast_add_direct (index + 2) 1]
    rw [show ((1 : Nat) : Fraction.Rational) = 1 by decide]
  have rightFloor : Rounding.Floor.floor rightDenominator = ((index + 1 : Nat) : Int) := by
    apply floor_between_nat (index + 1) rightDenominator
    · rw [← baseEq]
      exact baseLessRight.le
    · rw [← cutEq]
      exact rightLessCut
  have leftFloor : Rounding.Floor.floor leftDenominator = ((index + 2 : Nat) : Int) := by
    apply floor_between_nat (index + 2) leftDenominator
    · rw [← cutEq]
      exact cutLessLeft.le
    · rw [← nextEq]
      exact leftLessSuccessor
  have leftReading : value (1 / leftDenominator) = (((index + 2) % 2 : Nat) : Fraction.Rational) := by
    apply value_of_floor _ (Fraction.Order.Field.div_pos_direct (by decide) leftPositive)
    rw [reciprocal_reciprocal leftPositive]
    exact leftFloor
  have rightReading : value (1 / rightDenominator) = (((index + 1) % 2 : Nat) : Fraction.Rational) := by
    apply value_of_floor _ (Fraction.Order.Field.div_pos_direct (by decide) rightPositive)
    rw [reciprocal_reciprocal rightPositive]
    exact rightFloor
  refine ⟨1 / leftDenominator, 1 / rightDenominator,
    Fraction.Order.Field.div_pos_direct (by decide) leftPositive, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · apply (Fraction.Order.Field.div_le_iff_pos rightPositive).mpr
    rw [Fraction.Field.one_mul]
    exact rightBound
  · rw [← cutEq]
    exact reciprocal_lt cutPositive cutLessLeft
  · rw [← cutEq]
    exact reciprocal_lt rightPositive rightLessCut
  · rw [← cutEq]
    have displacement := reciprocal_displacement cutBound cutLessLeft.le
    have identity : leftDenominator - cut = shift := by dsimp [leftDenominator]; ring1
    rw [identity] at displacement
    exact displacement.trans_lt shiftLtRadius
  · rw [← cutEq]
    have displacement := reciprocal_displacement rightBound rightLessCut.le
    have identity : cut - rightDenominator = shift := by dsimp [rightDenominator]; ring1
    rw [identity] at displacement
    exact displacement.trans_lt shiftLtRadius
  · cases Purelib.Data.Nat.Parity.consecutive (index + 1) with
    | inl even =>
        right
        rw [leftReading, rightReading, even.1, even.2]
        exact ⟨rfl, rfl⟩
    | inr odd =>
        left
        rw [leftReading, rightReading, odd.1, odd.2]
        exact ⟨rfl, rfl⟩

/-- The exact reciprocal cut indexed from one half. -/
@[expose] def cut (index : Nat) : Fraction.Rational :=
  1 / ((index + 2 : Nat) : Fraction.Rational)

/-- Different natural indices have different exact reciprocal cuts. -/
theorem cut_injective : Function.Injective cut := by
  intro first second equal
  have firstPositive : 0 < ((first + 2 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ _)
  have secondPositive : 0 < ((second + 2 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ _)
  have reciprocalEqual := congrArg (fun point : Fraction.Rational => 1 / point) equal
  change 1 / (1 / ((first + 2 : Nat) : Fraction.Rational)) =
    1 / (1 / ((second + 2 : Nat) : Fraction.Rational)) at reciprocalEqual
  rw [reciprocal_reciprocal firstPositive, reciprocal_reciprocal secondPositive] at reciprocalEqual
  exact Nat.add_right_cancel (Fraction.Cast.Order.natCast_injective_direct reciprocalEqual)

/-- Enumerate exactly the requested finite number of reciprocal cuts. -/
@[expose] def cuts (count : Nat) : List Fraction.Rational := (List.range count).map cut

/-- The enumerated cut list retains the requested length and has no repetitions. -/
theorem cuts_distinct (count : Nat) : (cuts count).length = count ∧ (cuts count).Nodup := by
  constructor
  · rw [cuts, Purelib.Data.List.Map.length_map, Purelib.Data.List.Range.Basic.length_range]
  · exact Purelib.Data.List.Nodup.nodup_map_of_injective cut_injective
      (Purelib.Data.List.Range.Nodup.range_nodup count)

/-- Every retained finite cut has opposite readings in each positive rational neighborhood. -/
theorem cuts_witnesses (count : Nat) (point : Fraction.Rational) (member : point ∈ cuts count)
    (radius : Fraction.Rational) (radiusPositive : 0 < radius) :
    ∃ left right : Fraction.Rational,
      0 < left ∧ right ≤ 1 ∧ left < point ∧ point < right ∧
      point - left < radius ∧ right - point < radius ∧
      ((value left = 0 ∧ value right = 1) ∨ (value left = 1 ∧ value right = 0)) := by
  obtain ⟨index, _, equal⟩ := Purelib.Data.List.Map.mem_map.mp member
  rw [← equal]
  exact jump_witnesses index radius radiusPositive

/-- Compute a finite reciprocal cut count from a rational integration tolerance.

The extra two ensure the count is at least two, including coarse requests.
The original exact reciprocal-ceiling operation chooses the count directly. -/
@[expose] def tailCount (tolerance : Fraction.Rational) : Nat :=
  Rounding.Floor.ceilNat (1 / (tolerance / 2)) + 2

/-- The computed tail count is at least two for every rational request. -/
theorem tailCount_ge_two (tolerance : Fraction.Rational) : 2 ≤ tailCount tolerance :=
  Nat.le_add_left 2 _

/-- The reciprocal tail chosen for a positive request costs less than half the request. -/
theorem tail_width_lt (tolerance : Fraction.Rational) (positive : 0 < tolerance) :
    1 / ((tailCount tolerance : Nat) : Fraction.Rational) < tolerance / 2 := by
  have halfPositive : 0 < tolerance / 2 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let ceiling := Rounding.Floor.ceilNat (1 / (tolerance / 2))
  have lowerPositive : 0 < ((ceiling + 1 : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_pos_direct (Nat.zero_lt_succ _)
  have countOrder : ((ceiling + 1 : Nat) : Fraction.Rational) ≤
      ((tailCount tolerance : Nat) : Fraction.Rational) :=
    Fraction.Cast.Order.natCast_le_direct (Nat.add_le_add_left (by decide : 1 ≤ 2) ceiling)
  have smaller := Fraction.Order.Field.div_le_div_of_nonneg_left_direct
    (by decide : (0 : Fraction.Rational) ≤ 1) lowerPositive countOrder
  exact smaller.trans_lt (Rounding.Floor.Bounds.reciprocal_ceilNat_lt (tolerance / 2) halfPositive)

end Purelib.Integration.Step.Reciprocal

end
