module
import Purelib.Algebra.Field.Characteristic.Nonzero
import Purelib.Geometry.Plane.Line.Spread.Realization
import Purelib.Geometry.Stars.Regular.OrderThree.Construction
import Purelib.Algebra.Field.Cancellation
import Purelib.Algebra.Field.ExplicitField
public import Purelib.Algebra.Field.Squares
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Spread
import Purelib.Geometry.Plane.Line.Spread.Consecutive
public import Purelib.Geometry.Stars.Regular.OrderThree.Basic
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Logic.Nontrivial.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra.Field

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Line.Spread

open Purelib.Geometry.Stars.Regular

open Purelib.Geometry.Stars.Regular.OrderThree

section
@[expose] public section

/-!
# Divine Proportions, Theorem 95: regular stars of order three

The three-line star is finite data.  Its cyclic rule stores the three
reflection-lineation equations explicitly, and mutual nonparallelism replaces
any appeal to a global collection of lines.
-/

namespace Purelib.Geometry.Stars.Regular.OrderThree.Classification

variable {K : Type*} [ExplicitField K]

/-- Theorem 95 (Order three star): a regular three-star exists exactly when `3` is a nonzero square. Characteristic two
is excluded explicitly because the source construction then has null mirror lines. -/
theorem order_three_star [Nontrivial K] [DecidableEq K]
    (twoNonzero : (2 : K) ≠ 0) :
    Nonempty (OrderThree.Basic.RegularThreeStar K) ↔ Squares.IsNonzeroSquare (3 : K) := by
  constructor
  · rintro ⟨star⟩
    let s := Spread.spread star.line₀ star.line₁
      star.line₀NonNull star.line₁NonNull
    have sNonzero : s ≠ 0 := by
      intro sZero
      apply star.line₀Line₁Nonparallel
      exact (Spread.spread_eq_zero_iff_parallel star.line₀ star.line₁
        star.line₀NonNull star.line₁NonNull).1 sZero
    have firstEquality := star.spread₀₁_eq_spread₁₂
    have secondEquality := star.spread₁₂_eq_spread₂₀
    have alternatives := Consecutive.three_equal_spreads
      star.line₀ star.line₁ star.line₂ star.line₀
      star.line₀NonNull star.line₁NonNull star.line₂NonNull star.line₀NonNull
      firstEquality secondEquality (by
        intro parallel
        apply star.line₂Line₀Nonparallel
        exact Plane.Line.parallel_symm parallel)
    have selfZero :
        Spread.spread star.line₀ star.line₀ star.line₀NonNull star.line₀NonNull = 0 :=
      (Spread.spread_eq_zero_iff_parallel star.line₀ star.line₀
        star.line₀NonNull star.line₀NonNull).2
        (Plane.Line.parallel_refl star.line₀)
    change
      Spread.spread star.line₀ star.line₀ star.line₀NonNull star.line₀NonNull = s ∨
        Spread.spread star.line₀ star.line₀ star.line₀NonNull star.line₀NonNull =
          s * (3 - 4 * s) ^ 2 at alternatives
    rw [selfZero] at alternatives
    have factorSquareZero : (3 - 4 * s) ^ 2 = 0 := by
      rcases alternatives with zeroEqualsS | productZero
      · exact False.elim (sNonzero zeroEqualsS.symm)
      · by_cases squareZero : (3 - 4 * s) ^ 2 = 0
        · exact squareZero
        · exact False.elim
            ((ExplicitField.mul_ne_zero sNonzero squareZero)
              productZero.symm)
    have factorZero := (fun {K : Type _} [ExplicitField K] [DecidableEq K] (value : K) (squareZero
      : value ^ 2 = 0) => (Purelib.Algebra.Field.Squares.eq_zero_of_square_eq_zero (K := K) value squareZero : value =
      0)) (3 - 4 * s) factorSquareZero
    have fourS : (4 : K) * s = 3 := by
      calc
        (4 : K) * s = 3 - (3 - 4 * s) := by ring1
        _ = 3 := by rw [factorZero]; ring1
    have fourNonzero := Characteristic.Nonzero.four_ne_zero twoNonzero
    have threeNonzero : (3 : K) ≠ 0 := by
      intro threeZero
      apply (ExplicitField.mul_ne_zero fourNonzero sNonzero)
      calc
        (4 : K) * s = 3 := fourS
        _ = 0 := threeZero
    rcases Realization.spread_isSpreadNumber star.line₀ star.line₁
        star.line₀NonNull star.line₁NonNull with ⟨root, rootSquare⟩
    have fourComplement : (4 : K) * (1 - s) = 1 := by
      calc
        (4 : K) * (1 - s) = 4 - 4 * s := by ring1
        _ = 1 := by rw [fourS]; ring1
    have threeSquare : (3 : K) = (4 * root) ^ 2 := by
      calc
        (3 : K) = (4 * s) * (4 * (1 - s)) := by
          rw [fourS, fourComplement]
          ring1
        _ = 16 * (s * (1 - s)) := by ring1
        _ = 16 * root ^ 2 := by rw [rootSquare]
        _ = (4 * root) ^ 2 := by ring1
    have rootNonzero : (4 : K) * root ≠ 0 := by
      intro rootZero
      apply threeNonzero
      calc
        (3 : K) = (4 * root) ^ 2 := threeSquare
        _ = 0 := by rw [rootZero]; ring1
    exact ⟨4 * root, rootNonzero, threeSquare⟩
  · rintro ⟨root, rootNonzero, threeSquare⟩
    exact ⟨Construction.orderThreeStar root rootNonzero threeSquare twoNonzero⟩
end Purelib.Geometry.Stars.Regular.OrderThree.Classification

end
