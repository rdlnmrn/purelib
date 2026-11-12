module

import Purelib.Polynomial.Laurent.Circle.Transport
import Purelib.System.IO
import Purelib.Tactic.Ring

/-!
# Actual Laurent winding transport construction chains

The original source comparison and all three independently computed target
comparisons run on signed monomials, zero-root blocks, repeated roots,
nonreal coefficients and a retained implicit-zero domain guard.
-/

namespace TestPurelib.Polynomial.Laurent.Circle.Transport

open Purelib
open Polynomial.Laurent.Basic (LaurentPolynomial)
open Polynomial.Laurent.Normalization (Normalized)
open Polynomial.Laurent
open Polynomial.Laurent.Circle
open Polynomial.Laurent.Circle.Transport
open RationalFunctions.Curve.Canonical.Circle

/-- Every actual coefficient-conjugate constructor preserves its independently computed winding. -/
private theorem conjugate_reading {source : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    (original : Circle.Comparison normalized paths clearance) :
    (Transport.Comparison.conjugate original).result.reading.winding = original.reading.winding := by
  have relation := (Transport.Comparison.conjugate original).winding_eq
  change _ = 1 * _ at relation
  exact relation.trans (by ring1)

/-- Every actual exponent-reversed constructor negates its independently computed winding. -/
private theorem reverse_reading {source : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    (original : Circle.Comparison normalized paths clearance) :
    (Transport.Comparison.reverse original).result.reading.winding = -original.reading.winding := by
  have relation := (Transport.Comparison.reverse original).winding_eq
  change _ = (-1) * _ at relation
  exact relation.trans (by ring1)

/-- Every actual adjoint constructor negates its independently computed winding. -/
private theorem adjoint_reading {source : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    (original : Circle.Comparison normalized paths clearance) :
    (Transport.Comparison.adjoint original).result.reading.winding = -original.reading.winding := by
  have relation := (Transport.Comparison.adjoint original).winding_eq
  change _ = (-1) * _ at relation
  exact relation.trans (by ring1)

/-- A reversed implicit zero term still retains the original nonzero-input guard. -/
private theorem reversed_zero_guard :
    ¬(⟨[⟨1, .nonnegative 0⟩, ⟨0, .nonnegative 6⟩]⟩ : LaurentPolynomial).reverse.DefinedAt 0 := by
  intro defined
  exact defined ⟨0, .negative 5⟩ (List.Mem.tail _ (List.Mem.head _)) (by decide +kernel) rfl

/-- Check actual cached target values, quantitative payment and original unit-circle evaluation readbacks. -/
private def checkTarget {source target : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} {clearance : Boundary.Clearance paths}
    {original : Circle.Comparison normalized paths clearance} {orientation : Orientation}
    (retained : Transport.Comparison original target orientation)
    (expected : Int) (pole zeroCount inside : Nat) : IO Unit := do
  unless retained.result.reading.winding == expected && retained.normalized.poleOrder == pole &&
      retained.normalized.zeroMultiplicity == zeroCount && retained.result.polynomial.inventory.insideCount == inside &&
      retained.margin.bound == original.polynomial.margin.toCertificate.bound && decide (retained.symbol = target) do
    throw (IO.userError "actual Laurent transport lost independent winding, source ownership or zero/pole payment")
  unless (retained.normalized.poleOrder : Int) - (retained.result.polynomial.inventory.insideCount : Int) ==
      -expected do
    throw (IO.userError "actual Laurent transport lost the independently read pole-minus-inside index")
  for parameter in ([-1, 0, 1] : List Data.Rat.Fraction.Rational) do
    let point := (circle 1).point parameter
    unless retained.normalized.polynomial.eval point / retained.result.paths.denominator.eval point ==
        target.eval point do
      throw (IO.userError "actual Laurent transport lost its same original guarded evaluation")

/-- Run the actual source and three original target constructors against independent expected multiplicities. -/
private def check (source : LaurentPolynomial) (depth : Nat) (expected : Int)
    (sourcePole sourceZero sourceInside reversePole reverseZero reverseInside : Nat) : IO Unit := do
  match source.prepare with
  | .zero _ => throw (IO.userError "a nonzero Laurent transport fixture returned the original zero obstruction")
  | .normalized normalized =>
      let boundary := Boundary.prepare normalized.polynomial depth
      match boundary.2 with
      | .clear clearance =>
          let original := Circle.Comparison.prepare normalized boundary.1.paths clearance
          unless original.reading.winding == expected && normalized.poleOrder == sourcePole &&
              normalized.zeroMultiplicity == sourceZero && original.polynomial.inventory.insideCount == sourceInside do
            throw (IO.userError "the original Laurent transport fixture lost its independent sign or multiplicity")
          checkTarget (Transport.Comparison.conjugate original) expected sourcePole sourceZero sourceInside
          checkTarget (Transport.Comparison.reverse original) (-expected) reversePole reverseZero reverseInside
          checkTarget (Transport.Comparison.adjoint original) (-expected) reversePole reverseZero reverseInside
      | _ => throw (IO.userError "a nonvanishing Laurent transport fixture failed its original finite clearance")

/-- Run original monomial signs, nonminimal zero terms, repeated roots and nonreal coefficients. -/
public def run : IO Unit := do
  System.IO.println "Laurent transport: z"
  check ⟨[⟨1, .nonnegative 1⟩]⟩ 3 1 0 1 1 1 0 0
  System.IO.println "Laurent transport: z inverse"
  check ⟨[⟨1, .negative 0⟩]⟩ 0 (-1) 1 0 0 0 1 1
  System.IO.println "Laurent transport: triple zero"
  check ⟨[⟨1, .nonnegative 3⟩]⟩ 8 3 0 3 3 3 0 0
  System.IO.println "Laurent transport: double pole"
  check ⟨[⟨1, .negative 1⟩]⟩ 0 (-2) 2 0 0 0 2 2
  System.IO.println "Laurent transport: retained zero-term guard"
  check ⟨[⟨1, .nonnegative 0⟩, ⟨0, .nonnegative 6⟩]⟩ 0 0 0 0 0 0 0 0
  System.IO.println "Laurent transport: repeated inside root"
  check ⟨[⟨1, .nonnegative 2⟩, ⟨-1, .nonnegative 1⟩, ⟨1/4, .nonnegative 0⟩]⟩ 8 2 0 0 2 2 0 0
  System.IO.println "Laurent transport: nonreal root and leading coefficient"
  check ⟨[⟨⟨2, 1⟩, .nonnegative 1⟩, ⟨⟨-1/4, -3/4⟩, .nonnegative 0⟩]⟩ 8 1 0 0 1 1 0 0

end TestPurelib.Polynomial.Laurent.Circle.Transport
