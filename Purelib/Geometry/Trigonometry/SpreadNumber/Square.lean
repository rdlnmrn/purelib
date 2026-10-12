module
public import Purelib.Data.Nat.Order
public import Purelib.Algebra.Group.Negation
import Purelib.Data.List.Membership
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Squares.Basic
import Purelib.Algebra.Squares.Equality
public import Purelib.Geometry.Trigonometry.Spread.Number.Basic

import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Algebra.Group.Basic
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Algebra.Squares

open Purelib.Geometry.Trigonometry.Spread

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

public section

namespace Purelib.Geometry.Trigonometry.SpreadNumber.Square

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

attribute [local instance 2000] Group.Negation.subNegZeroMonoid

/-- A number which is both square and spread. -/
@[expose] def IsSquareSpreadNumber (value : K) : Prop :=
  Squares.Basic.IsSquareNumber value ∧ Number.Basic.IsSpreadNumber value

/-- The fibre over `value` of the first-coordinate-square map on the unit circle. -/
@[expose] def HasUnitCircleLift (value : K) : Prop :=
  ∃ first second : K,
    value = first ^ 2 ∧ first ^ 2 + second ^ 2 = 1

/-- A constructive square-spread value is precisely a value with a unit-circle lift. When the first root is nonzero, the
second coordinate is computed as `spreadRoot / squareRoot`; the zero case has the explicit lift `(0,1)`. -/
theorem squareSpread_iff_unitCircleLift [DecidableEq K] (value : K) :
    Geometry.Trigonometry.SpreadNumber.Square.IsSquareSpreadNumber value ↔
      Geometry.Trigonometry.SpreadNumber.Square.HasUnitCircleLift value := by
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
        Algebra.Field.ExplicitField.mul_inv_cancel first firstZero
      have spreadEquation :
          first ^ 2 * (1 - first ^ 2) = spreadRoot ^ 2 := by
        calc
          first ^ 2 * (1 - first ^ 2) = value * (1 - value) := by
            rw [valueSquare]
          _ = spreadRoot ^ 2 := spreadSquare
      have secondSquare : second ^ 2 = 1 - first ^ 2 := by
        simp only [second, Algebra.Field.ExplicitField.div_eq_mul_inv]
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

/-- A supplied pair of roots bounds every unit-circle lift by the four finite sign choices. This is the fibre
calculation used in Exercise 2.3. -/
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
  exact ⟨Equality.eq_or_eq_neg_of_sq_eq_sq firstSquares,
    Equality.eq_or_eq_neg_of_sq_eq_sq (secondSquareValue.trans complementSquare)⟩

/-- The four sign choices obtained from two supplied roots really are unit-circle lifts. -/
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

/-- A nonzero scalar differs from its negative when two is nonzero. -/
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
  exact (Algebra.Field.ExplicitField.mul_ne_zero twoNonzero valueNonzero) doubledZero

/-- Away from the boundary values, and outside characteristic two, the four sign choices are four distinct finite pairs.
-/
theorem four_sign_pairs_nodup
    (firstRoot secondRoot : K) (twoNonzero : (2 : K) ≠ 0)
    (firstNonzero : firstRoot ≠ 0) (secondNonzero : secondRoot ≠ 0) :
    [ (firstRoot, secondRoot), (-firstRoot, secondRoot),
      (firstRoot, -secondRoot), (-firstRoot, -secondRoot) ].Nodup := by
  have firstNotNegative :=
    Geometry.Trigonometry.SpreadNumber.Square.ne_neg_self_of_nonzero firstRoot twoNonzero firstNonzero
  have secondNotNegative :=
    Geometry.Trigonometry.SpreadNumber.Square.ne_neg_self_of_nonzero secondRoot twoNonzero secondNonzero
  change List.Pairwise (fun left right : K × K => left ≠ right)
    [(firstRoot, secondRoot), (-firstRoot, secondRoot),
      (firstRoot, -secondRoot), (-firstRoot, -secondRoot)]
  constructor
  · intro pair member equal
    rcases Data.List.Membership.mem_cons.mp member with same | member
    · exact firstNotNegative (congrArg Prod.fst (equal.trans same))
    rcases Data.List.Membership.mem_cons.mp member with same | member
    · exact secondNotNegative (congrArg Prod.snd (equal.trans same))
    rcases Data.List.Membership.mem_cons.mp member with same | member
    · exact firstNotNegative (congrArg Prod.fst (equal.trans same))
    · exact List.not_mem_nil member
  constructor
  · intro pair member equal
    rcases Data.List.Membership.mem_cons.mp member with same | member
    · exact firstNotNegative (congrArg Prod.fst (equal.trans same)).symm
    rcases Data.List.Membership.mem_cons.mp member with same | member
    · exact secondNotNegative (congrArg Prod.snd (equal.trans same))
    · exact List.not_mem_nil member
  constructor
  · intro pair member equal
    rcases Data.List.Membership.mem_cons.mp member with same | member
    · exact firstNotNegative (congrArg Prod.fst (equal.trans same))
    · exact List.not_mem_nil member
  constructor
  · intro pair member
    exact False.elim (List.not_mem_nil member)
  · exact List.Pairwise.nil

end Purelib.Geometry.Trigonometry.SpreadNumber.Square

end
