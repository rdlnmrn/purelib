module

public import Purelib.Algebra.Semiring.Nat
public import Purelib.Algebra.Ring.Int
import Purelib.Data.Int.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Retained four-square representations and Euler multiplication

The representation retains four original natural roots and their indexed
square-sum certificate. Euler multiplication computes its original four
signed integer products, then retains their original natural magnitudes.
-/

open Purelib.Data.Int

namespace Purelib.NumberTheory.FourSquares.Basic

@[expose] public section

set_option genInjectivity false in
/-- Four displayed natural square roots represent the indexed natural value.

The retained roots use the original natural power operation. Their defining
equation identifies their four squares with the same original target index. -/
structure Representation (value : Nat) where
  /-- The retained first natural square root. -/ first : Nat
  /-- The retained second natural square root. -/ second : Nat
  /-- The retained third natural square root. -/ third : Nat
  /-- The retained fourth natural square root. -/ fourth : Nat
  /-- The four retained natural squares sum to the original target value. -/ equation : first ^ 2 + second ^ 2 + third ^
    2 + fourth ^ 2 = value

constructive_injectivity Representation

end

/-- Multiply two checked four-square representations by the original Euler products.

The four signed integer products retain their displayed order and signs.
Their natural magnitudes form the output roots, and direct scalar cast and
square transports certify the original product of the two target indices. -/
@[expose] public def Representation.multiply {leftValue rightValue : Nat}
    (left : Representation leftValue) (right : Representation rightValue) :
    Representation (leftValue * rightValue) := by
  let firstProduct : Int :=
    (left.first : Int) * right.first -
      (left.second : Int) * right.second -
      (left.third : Int) * right.third -
      (left.fourth : Int) * right.fourth
  let secondProduct : Int :=
    (left.first : Int) * right.second +
      (left.second : Int) * right.first +
      (left.third : Int) * right.fourth -
      (left.fourth : Int) * right.third
  let thirdProduct : Int :=
    (left.first : Int) * right.third -
      (left.second : Int) * right.fourth +
      (left.third : Int) * right.first +
      (left.fourth : Int) * right.second
  let fourthProduct : Int :=
    (left.first : Int) * right.fourth +
      (left.second : Int) * right.third -
      (left.third : Int) * right.second +
      (left.fourth : Int) * right.first
  have leftCast :
      (left.first : Int) ^ 2 + (left.second : Int) ^ 2 +
          (left.third : Int) ^ 2 + (left.fourth : Int) ^ 2 =
        (leftValue : Int) := by
    exact congrArg (fun value : Nat => (value : Int)) left.equation
  have rightCast :
      (right.first : Int) ^ 2 + (right.second : Int) ^ 2 +
          (right.third : Int) ^ 2 + (right.fourth : Int) ^ 2 =
        (rightValue : Int) := by
    exact congrArg (fun value : Nat => (value : Int)) right.equation
  have productNorm :
      firstProduct ^ 2 + secondProduct ^ 2 +
          thirdProduct ^ 2 + fourthProduct ^ 2 =
        (leftValue : Int) * (rightValue : Int) := by
    calc
      firstProduct ^ 2 + secondProduct ^ 2 +
            thirdProduct ^ 2 + fourthProduct ^ 2 =
          ((left.first : Int) ^ 2 + (left.second : Int) ^ 2 +
            (left.third : Int) ^ 2 + (left.fourth : Int) ^ 2) *
          ((right.first : Int) ^ 2 + (right.second : Int) ^ 2 +
            (right.third : Int) ^ 2 + (right.fourth : Int) ^ 2) := by
        unfold firstProduct secondProduct thirdProduct fourthProduct
        ring1
      _ = (leftValue : Int) * (rightValue : Int) := by
        rw [leftCast, rightCast]
  have naturalProductNorm :
      firstProduct.natAbs ^ 2 + secondProduct.natAbs ^ 2 +
          thirdProduct.natAbs ^ 2 + fourthProduct.natAbs ^ 2 =
        leftValue * rightValue := by
    apply Int.ofNat.inj
    change (firstProduct.natAbs : Int) ^ 2 + (secondProduct.natAbs : Int) ^ 2 +
        (thirdProduct.natAbs : Int) ^ 2 + (fourthProduct.natAbs : Int) ^ 2 =
      (leftValue : Int) * (rightValue : Int)
    have firstSquare := Arithmetic.natAbs_pow_two firstProduct
    have secondSquare := Arithmetic.natAbs_pow_two secondProduct
    have thirdSquare := Arithmetic.natAbs_pow_two thirdProduct
    have fourthSquare := Arithmetic.natAbs_pow_two fourthProduct
    exact (congrArg₂ (fun left right : Int => left + right)
      (congrArg₂ (fun left right : Int => left + right)
        (congrArg₂ (fun left right : Int => left + right) firstSquare secondSquare)
        thirdSquare) fourthSquare).trans productNorm
  exact
    ⟨firstProduct.natAbs, secondProduct.natAbs, thirdProduct.natAbs,
      fourthProduct.natAbs, naturalProductNorm⟩

end Purelib.NumberTheory.FourSquares.Basic
