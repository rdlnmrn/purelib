module

import Purelib.Polynomial.Laurent.Toeplitz.Product
import Purelib.System.IO

/-!
# Actual recurrence boundary indices of normalized Laurent products

Each input and its actual product receive their own automatic comparison.
Original pole cancellation, repeated roots, retained margins and guarded
evaluations are checked together with the three actual recurrence defects.
-/

namespace TestPurelib.Polynomial.Laurent.Toeplitz.Product

open Purelib
open Purelib.Polynomial.Laurent
open Basic (LaurentPolynomial)
open Purelib.RationalFunctions.Curve.Canonical.Circle

/-- Check three independently constructed actual recurrence ledgers and their original product data. -/
private def check (left right : LaurentPolynomial) (leftDepth rightDepth : Nat)
    (leftIndex rightIndex : Int) (extra pole inside : Nat) : IO Unit := do
  match left.prepare, right.prepare with
  | .normalized leftResult, .normalized rightResult =>
      let leftBoundary := Boundary.prepare leftResult.polynomial leftDepth
      let rightBoundary := Boundary.prepare rightResult.polynomial rightDepth
      match leftBoundary.2, rightBoundary.2 with
      | .clear leftClearance, .clear rightClearance =>
          let first := Toeplitz.Comparison.prepare leftResult leftBoundary.1.paths leftClearance
          let second := Toeplitz.Comparison.prepare rightResult rightBoundary.1.paths rightClearance
          let product := Arithmetic.multiply left right
          let comparison := Toeplitz.Product.Comparison.prepare product first second
          let target := comparison.result
          unless first.index == leftIndex && second.index == rightIndex &&
              target.index == leftIndex + rightIndex && target.index == first.index + second.index &&
              target.circle.reading.winding == -(leftIndex + rightIndex) &&
              comparison.circle.extraShift == extra && comparison.circle.normalized.poleOrder == pole &&
              target.circle.polynomial.inventory.insideCount == inside do
            throw (IO.userError "actual product recurrence ledgers lost their index or pole/zero compensation")
          unless comparison.circle.margin.bound == first.circle.polynomial.margin.toCertificate.bound *
              second.circle.polynomial.margin.toCertificate.bound do
            throw (IO.userError "actual product recurrence comparison lost the original margin payment")
          for parameter in ([-1, 0, 1] : List Data.Rat.Fraction.Rational) do
            let point := (circle 1).point parameter
            unless product.eval point == left.eval point * right.eval point &&
                comparison.circle.normalized.polynomial.eval point /
                  target.circle.paths.denominator.eval point == product.eval point do
              throw (IO.userError "actual product recurrence comparison lost original guarded evaluation")
      | _, _ => throw (IO.userError "a product input lacked its expected finite whole-boundary clearance")
  | _, _ => throw (IO.userError "a nonzero product input returned a zero-symbol obstruction")

/-- Run cancelling powers, mixed monomials, repeated inside roots and nonreal constant products. -/
public def run : IO Unit := do
  check ⟨[⟨1, .negative 0⟩]⟩ ⟨[⟨1, .nonnegative 1⟩]⟩ 0 3 1 (-1) 1 0 0
  check ⟨[⟨1, .nonnegative 3⟩]⟩ ⟨[⟨1, .negative 1⟩]⟩ 8 0 (-3) 2 2 0 1
  check ⟨[⟨1, .nonnegative 1⟩, ⟨-(1 / 2), .nonnegative 0⟩]⟩
    ⟨[⟨1, .nonnegative 1⟩, ⟨-(1 / 2), .nonnegative 0⟩]⟩ 5 5 (-1) (-1) 0 0 2
  check ⟨[⟨⟨1, 1⟩, .nonnegative 0⟩]⟩ ⟨[⟨⟨1, -1⟩, .negative 0⟩]⟩ 0 0 0 1 0 1 0

end TestPurelib.Polynomial.Laurent.Toeplitz.Product
