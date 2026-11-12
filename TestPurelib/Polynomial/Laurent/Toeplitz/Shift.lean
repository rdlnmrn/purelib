module

import Purelib.Polynomial.Laurent.Toeplitz.Shift
import Purelib.System.IO

/-!
# Original shifted inventories and actual Laurent recurrence indices

Each nonminimal numerator receives its own original complete circle
comparison. Its extra zero roots compensate the larger polynomializing shift,
while the source retains the actual minimal-pole recurrence ledger.
-/

namespace TestPurelib.Polynomial.Laurent.Toeplitz.Shift

open Purelib
open Polynomial.Laurent
open Basic (LaurentPolynomial)
open Polynomial.Dense.Basic (DensePolynomial)
open RationalFunctions.Curve.Canonical.Circle

/-- Compare the actual original shifted root inventory with the same source's genuine recurrence defect. -/
private def check (source : LaurentPolynomial) (depth extra : Nat) (index : Int) : IO Unit := do
  match source.prepare with
  | .zero _ => throw (IO.userError "a nonminimal-shift fixture returned the zero-symbol obstruction")
  | .normalized normalized =>
      let boundary := Boundary.prepare normalized.polynomial depth
      match boundary.2 with
      | .contact _ _ _ => throw (IO.userError "a nonminimal-shift fixture met the unit circle")
      | .inconclusive _ _ _ _ _ => throw (IO.userError "a nonminimal-shift fixture lacked whole-circle clearance")
      | .clear clearance =>
          let original := Toeplitz.Comparison.prepare normalized boundary.1.paths clearance
          let polynomial := DensePolynomial.shift extra normalized.polynomial
          let paths := Boundary.Substitutions.prepare polynomial
          let margin := original.circle.polynomial.margin.toCertificate.shift extra
          let shiftedClearance := margin.onBoundary paths
          let shifted := RootIsolation.Multiplicity.Circle.Comparison.prepare paths shiftedClearance
            (DensePolynomial.normalize_shift _ _)
          have _ := original.circle.polynomial.shift_insideCount extra shifted
          have _ := original.nonminimal_index extra shifted
          have _ := normalized.nonminimal_zeroMultiplicity extra
          unless original.index == index &&
              shifted.inventory.insideCount == original.circle.polynomial.inventory.insideCount + extra &&
              shifted.inventory.outsideCount == original.circle.polynomial.inventory.outsideCount &&
              polynomial.zeroMultiplicity == normalized.zeroMultiplicity + extra &&
              margin.bound == original.circle.polynomial.margin.toCertificate.bound &&
              decide (((normalized.poleOrder + extra : Nat) : Int) -
                (shifted.inventory.insideCount : Int) = original.index) do
            throw (IO.userError "the actual nonminimal root inventory lost pole/zero compensation")
          System.IO.println s!"Toeplitz shift: added{extra} actual zero roots; original index{index}."

/-- Exercise constants, both pole signs, an interior root and an exterior root with actual added zero owners. -/
public def run : IO Unit := do
  check ⟨[⟨⟨1, 1⟩, .nonnegative 0⟩]⟩ 0 2 0
  check ⟨[⟨1, .nonnegative 1⟩]⟩ 3 2 (-1)
  check ⟨[⟨1, .negative 0⟩]⟩ 0 2 1
  check ⟨[⟨1, .nonnegative 1⟩, ⟨-(1 / 2), .nonnegative 0⟩]⟩ 5 2 (-1)
  check ⟨[⟨1, .nonnegative 1⟩, ⟨-2, .nonnegative 0⟩]⟩ 5 2 0

end TestPurelib.Polynomial.Laurent.Toeplitz.Shift
