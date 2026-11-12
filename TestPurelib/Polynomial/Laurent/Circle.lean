module

public import Purelib.Polynomial.Laurent.Circle
import Purelib.System.IO

/-!
# Original Laurent circle winding construction chains

The actual normalization, complete chart preparation, independent quotient
phase reading and original multiplicity inventory run together. Positive and
negative monomials fix the sign, and cancelled negative terms retain their
original guards at zero.
-/

namespace TestPurelib.Polynomial.Laurent.Circle

open Purelib
open Polynomial.Laurent.Basic (LaurentPolynomial)
open Polynomial.Laurent.Normalization (Normalized)
open Polynomial.Laurent.Circle
open RationalFunctions.Curve.Canonical.Circle

/-- Every actual constructor result compares independent winding with its same retained complete inventory. -/
private theorem constructed_winding {source : LaurentPolynomial} (normalized : Normalized source)
    (paths : Boundary.Substitutions normalized.polynomial) (clearance : Boundary.Clearance paths) :
    let result := Comparison.prepare normalized paths clearance
    result.reading.winding = (result.polynomial.inventory.insideCount : Int) - (normalized.poleOrder : Int) :=
  (Comparison.prepare normalized paths clearance).winding_eq

/-- The same original guarded source value is exactly the retained quotient at every explicitly nonzero input. -/
private theorem guarded_value {source : LaurentPolynomial} {normalized : Normalized source}
    {paths : Boundary.Substitutions normalized.polynomial} (substitutions : Substitutions normalized paths)
    (point : Data.Gaussian.Basic.Canonical) (nonzero : point ≠ 0) :
    normalized.polynomial.eval point / substitutions.denominator.eval point = source.eval point :=
  substitutions.quotient_value point nonzero

/-- Original cancelling negative terms still forbid the input zero. -/
private theorem cancelled_guard :
    ¬(⟨[⟨1, .negative 0⟩, ⟨-1, .negative 0⟩, ⟨1, .nonnegative 1⟩]⟩ : LaurentPolynomial).DefinedAt 0 := by
  intro defined
  exact defined ⟨1, .negative 0⟩ List.mem_cons_self (by decide) rfl

/-- Execute the actual complete normalized source, original paths and independent winding comparison. -/
private def check (source : LaurentPolynomial) (depth : Nat) (expected : Int) : IO Unit := do
  match source.prepare with
  | .zero _ => throw (IO.userError "a nonzero Laurent fixture returned the zero-symbol obstruction")
  | .normalized normalized =>
      let boundary := Boundary.prepare normalized.polynomial depth
      match boundary.2 with
      | .clear clearance =>
          let result := Comparison.prepare normalized boundary.1.paths clearance
          unless result.reading.winding == expected &&
              (normalized.poleOrder : Int) - (result.polynomial.inventory.insideCount : Int) == -expected &&
              decide (result.paths.denominatorMargin.bound = 1) do
            throw (IO.userError "original Laurent circle winding lost its pole, inside multiplicity or orientation")
          for parameter in ([-1, 0, 1] : List Data.Rat.Fraction.Rational) do
            let point := (circle 1).point parameter
            let divisor := result.paths.denominator.eval point
            let scale := (parameter ^ 2 + 1) ^ normalized.polynomial.coeffs.length *
              (parameter ^ 2 + 1) ^ result.paths.denominator.coeffs.length * divisor.normSq
            let actual : Data.Gaussian.Basic.Canonical :=
              ⟨result.paths.quotient.primaryReal.eval parameter, result.paths.quotient.primaryImaginary.eval parameter⟩
            unless normalized.polynomial.eval point / divisor == source.eval point &&
                decide (0 < scale) && actual == (⟨scale, 0⟩ : Data.Gaussian.Basic.Canonical) * source.eval point do
              throw (IO.userError "original guarded Laurent evaluation lost its exact positive quotient direction")
      | .contact _ _ _ => throw (IO.userError "a nonvanishing Laurent fixture met the unit circle")
      | .inconclusive _ _ _ _ _ => throw (IO.userError "a Laurent fixture retained unresolved boundary cells")

/-- Run both monomial signs, exact repeated zero multiplicities, a nonreal constant and guarded cancellation. -/
public def run : IO Unit := do
  check ⟨[⟨1, .nonnegative 1⟩]⟩ 3 1
  check ⟨[⟨1, .negative 0⟩]⟩ 0 (-1)
  check ⟨[⟨1, .nonnegative 3⟩]⟩ 8 3
  check ⟨[⟨1, .negative 1⟩]⟩ 0 (-2)
  check ⟨[⟨⟨1, 1⟩, .nonnegative 0⟩]⟩ 0 0
  check ⟨[⟨1, .nonnegative 0⟩, ⟨-(1 / 2), .negative 0⟩]⟩ 5 0
  check ⟨[⟨1, .negative 0⟩, ⟨-1, .negative 0⟩, ⟨1, .nonnegative 1⟩]⟩ 3 1

end TestPurelib.Polynomial.Laurent.Circle
