module

import Purelib.Polynomial.Laurent.Toeplitz.Transport
import Purelib.System.IO

/-!
# Actual transformed-symbol recurrence ledgers

Each original symbol and its conjugate, exponent reverse and adjoint receive
their own automatically computed recurrence normal form. Independent winding,
minimal support, repeated roots and actual target evaluations remain checked.
-/

namespace TestPurelib.Polynomial.Laurent.Toeplitz.Transport

open Purelib
open Purelib.Polynomial.Laurent
open Basic (LaurentPolynomial)
open Normalization (Normalized)
open Circle.Transport (Orientation)
open Purelib.RationalFunctions.Curve.Canonical.Circle

/-- Check one actual transformed recurrence ledger and the original target's support and boundary values. -/
private def checkTarget {source target : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    {original : Toeplitz.Comparison normalized paths clearance} {orientation : Orientation}
    (comparison : Toeplitz.Transport.Comparison original target orientation)
    (expected : Int) (pole zeroCount inside : Nat) : IO Unit := do
  let retained := comparison.circle
  let result := comparison.result
  unless result.index == expected && result.circle.reading.winding == -expected &&
      retained.normalized.poleOrder == pole && retained.normalized.zeroMultiplicity == zeroCount &&
      result.circle.polynomial.inventory.insideCount == inside &&
      retained.margin.bound == original.circle.polynomial.margin.toCertificate.bound &&
      decide (retained.symbol = target) do
    throw (IO.userError "actual transformed recurrence ledger lost its defect, source or support")
  for parameter in ([-1, 0, 1] : List Data.Rat.Fraction.Rational) do
    let point := (circle 1).point parameter
    unless retained.normalized.polynomial.eval point / result.circle.paths.denominator.eval point ==
        target.eval point do
      throw (IO.userError "actual transformed recurrence ledger lost original guarded evaluation")

/-- Run all three actual target constructions from one retained original scalar comparison. -/
private def check (source : LaurentPolynomial) (depth : Nat) (expected : Int)
    (sourcePole sourceZero sourceInside reversePole reverseZero reverseInside : Nat) : IO Unit := do
  match source.prepare with
  | .zero _ => throw (IO.userError "a nonzero transport input returned a zero-symbol obstruction")
  | .normalized normalized =>
      let boundary := Boundary.prepare normalized.polynomial depth
      match boundary.2 with
      | .clear clearance =>
          let original := Toeplitz.Comparison.prepare normalized boundary.1.paths clearance
          unless original.index == expected && normalized.poleOrder == sourcePole &&
              normalized.zeroMultiplicity == sourceZero &&
              original.circle.polynomial.inventory.insideCount == sourceInside do
            throw (IO.userError "an original recurrence transport fixture lost its expected sign or multiplicity")
          let conjugated := Toeplitz.Transport.Comparison.conjugate original
          let reversed := Toeplitz.Transport.Comparison.reverse original
          let adjoint := Toeplitz.Transport.Comparison.adjoint original
          have _ := conjugated.circle.conjugate_locations
          have _ := reversed.circle.reverse_locations
          have _ := adjoint.circle.adjoint_locations
          let sourceInventory := original.circle.polynomial.inventory
          let conjugateInventory := conjugated.circle.result.polynomial.inventory
          unless conjugateInventory.insideCount == sourceInventory.insideCount &&
              conjugateInventory.outsideCount == sourceInventory.outsideCount do
            throw (IO.userError "conjugation lost an actual original radial inventory count")
          let reverseInventory := reversed.circle.result.polynomial.inventory
          let adjointInventory := adjoint.circle.result.polynomial.inventory
          unless reverseInventory.insideCount ==
                sourceInventory.outsideCount + reversed.circle.normalized.zeroMultiplicity &&
              reverseInventory.outsideCount + normalized.zeroMultiplicity == sourceInventory.insideCount &&
              adjointInventory.insideCount ==
                sourceInventory.outsideCount + adjoint.circle.normalized.zeroMultiplicity &&
              adjointInventory.outsideCount + normalized.zeroMultiplicity == sourceInventory.insideCount do
            throw (IO.userError "reversal or adjoint lost actual zero-corrected radial inventory exchange")
          checkTarget conjugated expected sourcePole sourceZero sourceInside
          checkTarget reversed (-expected) reversePole reverseZero reverseInside
          checkTarget adjoint (-expected) reversePole reverseZero reverseInside
      | _ => throw (IO.userError "a transport input lacked its expected finite whole-boundary clearance")

/-- Run seven original sources and twenty-one actual conjugate, reversed and adjoint recurrence ledgers. -/
public def run : IO Unit := do
  check ⟨[⟨1, .nonnegative 1⟩]⟩ 3 (-1) 0 1 1 1 0 0
  check ⟨[⟨1, .negative 0⟩]⟩ 0 1 1 0 0 0 1 1
  check ⟨[⟨1, .nonnegative 3⟩]⟩ 8 (-3) 0 3 3 3 0 0
  check ⟨[⟨1, .negative 1⟩]⟩ 0 2 2 0 0 0 2 2
  check ⟨[⟨1, .nonnegative 0⟩, ⟨0, .nonnegative 6⟩]⟩ 0 0 0 0 0 0 0 0
  check ⟨[⟨1, .nonnegative 2⟩, ⟨-1, .nonnegative 1⟩, ⟨1/4, .nonnegative 0⟩]⟩ 8 (-2) 0 0 2 2 0 0
  check ⟨[⟨⟨2, 1⟩, .nonnegative 1⟩, ⟨⟨-1/4, -3/4⟩, .nonnegative 0⟩]⟩ 8 (-1) 0 0 1 1 0 0

end TestPurelib.Polynomial.Laurent.Toeplitz.Transport
