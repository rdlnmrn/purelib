module

public import Purelib.RationalFunctions.Winding.Circle
import TestPurelib.Polynomial.Winding.Circle
import Purelib.System.IO

/-!
# Independent whole-circle quotient winding regressions

These fixtures prepare both original polynomial boundaries, construct the
actual conjugate-denominator product coordinates and execute their original
phase resolution. Signed results include negative winding and cancellation.
-/

namespace TestPurelib.RationalFunctions.Winding.Circle

open Purelib
open Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.RationalFunctions.Winding.Circle (Paths Reading raw raw_eq_sub)

/-- The actual conjugate-coordinate raw computation gives negative winding for the reciprocal coordinate. -/
private theorem reciprocal_raw
    (numeratorClearance : Boundary.Clearance
      (Boundary.Substitutions.prepare (⟨[1]⟩ : CoefficientPolynomial)))
    (denominatorClearance : Boundary.Clearance
      (Boundary.Substitutions.prepare (⟨[1, 0]⟩ : CoefficientPolynomial))) :
    raw (Paths.prepare (Boundary.Substitutions.prepare (⟨[1]⟩ : CoefficientPolynomial))
      (Boundary.Substitutions.prepare (⟨[1, 0]⟩ : CoefficientPolynomial))) = -4 := by
  rw [raw_eq_sub _ numeratorClearance denominatorClearance,
    TestPurelib.Polynomial.Winding.Circle.constant_raw, TestPurelib.Polynomial.Winding.Circle.coordinate_raw]
  rfl

/-- Every actual quotient constructor result retains exact quadrupled divisibility. -/
public theorem constructed_raw {numerator denominator : CoefficientPolynomial}
    {numeratorPaths : Boundary.Substitutions numerator} {denominatorPaths : Boundary.Substitutions denominator}
    (paths : Paths numeratorPaths denominatorPaths) (numeratorClearance : Boundary.Clearance numeratorPaths)
    (denominatorClearance : Boundary.Clearance denominatorPaths) :
    raw paths = 4 * (Reading.prepare paths numeratorClearance denominatorClearance).winding :=
  (Reading.prepare paths numeratorClearance denominatorClearance).raw_eq

/-- Run the original independent phase constructor on one actual pair of cleared boundaries. -/
private def check (numerator denominator : CoefficientPolynomial) (numeratorDepth denominatorDepth : Nat)
    (expected : Int) : IO Unit := do
  let numeratorPrepared := Boundary.prepare numerator numeratorDepth
  let denominatorPrepared := Boundary.prepare denominator denominatorDepth
  match numeratorPrepared.2, denominatorPrepared.2 with
  | .clear numeratorClearance, .clear denominatorClearance =>
      let paths := Paths.prepare numeratorPrepared.1.paths denominatorPrepared.1.paths
      let reading := Reading.prepare paths numeratorClearance denominatorClearance
      let numeratorReading := Polynomial.Winding.Circle.Reading.prepare numeratorPrepared.1.paths numeratorClearance
      let denominatorReading := Polynomial.Winding.Circle.Reading.prepare
        denominatorPrepared.1.paths denominatorClearance
      unless reading.winding == expected && raw paths == 4 * expected &&
          reading.winding == numeratorReading.winding - denominatorReading.winding do
        throw (IO.userError "independent quotient-circle winding lost its sign or product endpoint cancellation")
      for parameter in ([-1, 0, 1] : List Data.Rat.Fraction.Rational) do
        let point := (circle 1).point parameter
        let scale := (parameter ^ 2 + 1) ^ numerator.coeffs.length *
          (parameter ^ 2 + 1) ^ denominator.coeffs.length * (denominator.eval point).normSq
        let actual : Data.Gaussian.Basic.Canonical :=
          ⟨paths.primaryReal.eval parameter, paths.primaryImaginary.eval parameter⟩
        unless decide (0 < scale) && actual == (⟨scale, 0⟩ : Data.Gaussian.Basic.Canonical) *
            (numerator.eval point / denominator.eval point) do
          throw (IO.userError "cleared quotient coordinates lost their exact positive original-evaluation multiplier")
  | _, _ => throw (IO.userError "a quotient-circle fixture lacked whole-boundary polynomial clearance")

/-- Run signed reciprocal, positive coordinate and cancelled quotient construction chains. -/
public def run : IO Unit := do
  check ⟨[1]⟩ ⟨[1, 0]⟩ 0 3 (-1)
  check ⟨[1, 0]⟩ ⟨[1]⟩ 3 0 1
  check ⟨[1, 0, 0]⟩ ⟨[1, 0]⟩ 5 3 1
  check ⟨[1, 0]⟩ ⟨[1, 0, 0]⟩ 3 5 (-1)

end TestPurelib.RationalFunctions.Winding.Circle
