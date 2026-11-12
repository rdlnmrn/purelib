module

import Purelib.Polynomial.Laurent.Circle.Product
import Purelib.System.IO

/-!
# Original Laurent product comparison construction chains

Actual cancelled and mixed monomial products retain their original guarded
inputs and the extra polynomializing shift. Repeated interior roots exercise
the separate multiplicity inventories and independently computed readings.
-/

namespace TestPurelib.Polynomial.Laurent.Circle.Product

open Purelib
open Polynomial.Laurent.Basic (LaurentPolynomial)
open Polynomial.Laurent.Normalization (Normalized)
open Polynomial.Laurent
open RationalFunctions.Curve.Canonical.Circle

/-- Every actual product comparison has additive independent winding and signed index. -/
private theorem constructed_winding {left right : LaurentPolynomial}
    {leftResult : Normalized left} {rightResult : Normalized right}
    {leftPaths : Boundary.Substitutions leftResult.polynomial}
    {rightPaths : Boundary.Substitutions rightResult.polynomial}
    {leftClearance : Boundary.Clearance leftPaths} {rightClearance : Boundary.Clearance rightPaths}
    (leftComparison : Circle.Comparison leftResult leftPaths leftClearance)
    (rightComparison : Circle.Comparison rightResult rightPaths rightClearance)
    (product : Arithmetic.Product left right) :
    let result := Circle.Product.Comparison.prepare product leftComparison rightComparison
    result.result.reading.winding = leftComparison.reading.winding + rightComparison.reading.winding :=
  (Circle.Product.Comparison.prepare product leftComparison rightComparison).winding_add

/-- Cancelling displayed exponents still preserves the two original input guards at zero. -/
private theorem cancelled_guard :
    ¬(Arithmetic.multiply (⟨[⟨1, .negative 0⟩]⟩ : LaurentPolynomial)
      (⟨[⟨1, .nonnegative 1⟩]⟩ : LaurentPolynomial)).DefinedAt 0 := by
  intro defined
  exact defined.1 ⟨1, .negative 0⟩ List.mem_cons_self (by decide) rfl

/-- Check the actual product construction, retained payment and independent inventory/phase comparisons. -/
private def check (left right : LaurentPolynomial) (leftDepth rightDepth : Nat)
    (leftWinding rightWinding : Int) (extra pole inside : Nat) : IO Unit := do
  match left.prepare, right.prepare with
  | .normalized leftResult, .normalized rightResult =>
      let leftBoundary := Boundary.prepare leftResult.polynomial leftDepth
      let rightBoundary := Boundary.prepare rightResult.polynomial rightDepth
      match leftBoundary.2, rightBoundary.2 with
      | .clear leftClearance, .clear rightClearance =>
          let leftComparison := Circle.Comparison.prepare leftResult leftBoundary.1.paths leftClearance
          let rightComparison := Circle.Comparison.prepare rightResult rightBoundary.1.paths rightClearance
          let product := Arithmetic.multiply left right
          let result := Circle.Product.Comparison.prepare product leftComparison rightComparison
          unless leftComparison.reading.winding == leftWinding && rightComparison.reading.winding == rightWinding &&
              result.result.reading.winding == leftWinding + rightWinding && result.extraShift == extra &&
              result.normalized.poleOrder == pole && result.result.polynomial.inventory.insideCount == inside do
            throw (IO.userError "Laurent product lost independent winding, multiplicity or pole compensation")
          unless result.margin.bound == leftComparison.polynomial.margin.toCertificate.bound *
                rightComparison.polynomial.margin.toCertificate.bound &&
              result.result.polynomial.reading.winding + (result.extraShift : Int) ==
                leftComparison.polynomial.reading.winding + rightComparison.polynomial.reading.winding &&
              (result.normalized.poleOrder : Int) - (result.result.polynomial.inventory.insideCount : Int) ==
                ((leftResult.poleOrder : Int) - (leftComparison.polynomial.inventory.insideCount : Int)) +
                  ((rightResult.poleOrder : Int) - (rightComparison.polynomial.inventory.insideCount : Int)) do
            throw (IO.userError "actual product index lost its original margin or compensated zero-root balance")
          for parameter in ([-1, 0, 1] : List Data.Rat.Fraction.Rational) do
            let point := (circle 1).point parameter
            unless product.eval point == left.eval point * right.eval point &&
                result.normalized.polynomial.eval point / result.result.paths.denominator.eval point ==
                  product.eval point do
              throw (IO.userError "actual product evaluation lost its same original guarded factors")
      | _, _ => throw (IO.userError "a nonvanishing product input failed its original finite clearance fixture")
  | _, _ => throw (IO.userError "a nonzero product input returned the original zero obstruction")

/-- Run exact pole cancellation, mixed powers, repeated interior roots, and nonreal constant products. -/
public def run : IO Unit := do
  check ⟨[⟨1, .negative 0⟩]⟩ ⟨[⟨1, .nonnegative 1⟩]⟩ 0 3 (-1) 1 1 0 0
  check ⟨[⟨1, .nonnegative 3⟩]⟩ ⟨[⟨1, .negative 1⟩]⟩ 8 0 3 (-2) 2 0 1
  check ⟨[⟨1, .nonnegative 1⟩, ⟨-(1 / 2), .nonnegative 0⟩]⟩
    ⟨[⟨1, .nonnegative 1⟩, ⟨-(1 / 2), .nonnegative 0⟩]⟩ 5 5 1 1 0 0 2
  check ⟨[⟨⟨1, 1⟩, .nonnegative 0⟩]⟩ ⟨[⟨⟨1, -1⟩, .negative 0⟩]⟩ 0 0 0 (-1) 0 1 0

end TestPurelib.Polynomial.Laurent.Circle.Product
