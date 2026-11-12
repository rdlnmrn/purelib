module

import Purelib.Polynomial.Elimination.Axis.Separated
import Purelib.Polynomial.Elimination.Separated.Replay
import Purelib.Data.Vector.Basic
meta import Purelib.Polynomial.Elimination.Axis.Separated
meta import Purelib.Polynomial.Elimination.Separated.Replay
meta import Purelib.Data.Vector.Basic

/-! # Checked numerical cofactor reconstruction and exact original fallback -/

namespace TestPurelib.Polynomial.ComputedAxisCofactors

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Polynomial.Elimination

example (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false)
    (positive : 0 < polynomial.natDegree) (parameter : Rational)
    (safe : (Elimination.Separated.Scalar.scalarEliminant polynomial).eval parameter ≠ 0) :
    (Axis.Separated.Replay.computeVertical polynomial nonzero positive parameter safe).val =
      Axis.Separated.Bezout.verticalCoprimeCertificate polynomial nonzero positive parameter safe :=
  (Axis.Separated.Replay.computeVertical polynomial nonzero positive parameter safe).property

example (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false)
    (positive : 0 < polynomial.natDegree) (parameter : Rational)
    (safe : (Axis.Separated.Eliminant.horizontalEliminant polynomial).eval parameter ≠ 0) :
    (Axis.Separated.Replay.computeHorizontal polynomial nonzero positive parameter safe).val =
      Axis.Separated.Bezout.horizontalCoprimeCertificate polynomial nonzero positive parameter safe :=
  (Axis.Separated.Replay.computeHorizontal polynomial nonzero positive parameter safe).property

/-- The original positive-degree linear polynomial used for direct successful and rejected proposals. -/
private def polynomial : CoefficientPolynomial := ⟨[1, -1]⟩

/-- The retained original coefficient table is nonzero. -/
private theorem nonzero : polynomial.isZero = false := by decide +kernel
/-- The original coefficient table has positive natural degree. -/
private theorem positive : 0 < polynomial.natDegree := by decide +kernel
/-- The displayed original vertical parameter avoids the scalar eliminant. -/
private theorem verticalSafe : (Elimination.Separated.Scalar.scalarEliminant polynomial).eval 3 ≠ 0 := by
  decide +kernel
/-- The displayed original horizontal parameter avoids the quarter-turn eliminant. -/
private theorem horizontalSafe : (Axis.Separated.Eliminant.horizontalEliminant polynomial).eval 3 ≠ 0 := by
  decide +kernel

/-- Validate computed columns, an actual rejected row equation and both exact original fallback routes. -/
private def checkComputedCofactors : IO Unit := do
  let values := Elimination.Separated.Replay.propose polynomial positive 3
  match Axis.Separated.Replay.verticalAttempt polynomial nonzero positive 3 verticalSafe values with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "computed vertical proposal did not reconstruct the original certificate")
  let zero := Data.Vector.Basic.vectorOfFn (fun _ : Fin (polynomial.natDegree + polynomial.natDegree) =>
    (0 : Data.Gaussian.Basic.Canonical))
  match Axis.Separated.Replay.verticalAttempt polynomial nonzero positive 3 verticalSafe zero with
  | .ok _ => throw (IO.userError "zero column was accepted as an original unit-column solution")
  | .error (.equation actual _ _) =>
      unless actual ⟨0, by decide +kernel⟩ = 0 do
        throw (IO.userError "rejection lost its actual failed matrix-vector product")
  let vertical := Axis.Separated.Replay.fromVerticalProposal polynomial nonzero positive 3 verticalSafe zero
  let originalVertical := Axis.Separated.Bezout.verticalCoprimeCertificate
    polynomial nonzero positive 3 verticalSafe
  unless vertical.val.left.coeffs = originalVertical.left.coeffs ∧
      vertical.val.right.coeffs = originalVertical.right.coeffs do
    throw (IO.userError "vertical fallback changed an original cofactor")
  let rotated := Dense.Gaussian.Substitution.QuarterTurn.quarterTurn polynomial
  have rotatedPositive : 0 < rotated.natDegree := by
    rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_natDegree polynomial nonzero]
    exact positive
  let horizontalValues := Elimination.Separated.Replay.propose rotated rotatedPositive 3
  match Elimination.Separated.Replay.check rotated rotatedPositive 3 horizontalValues with
  | .ok _ => pure ()
  | .error _ => throw (IO.userError "computed horizontal proposal did not solve its original quarter-turn system")
  let horizontalZero := Data.Vector.Basic.vectorOfFn
    (fun _ : Fin (rotated.natDegree + rotated.natDegree) => (0 : Data.Gaussian.Basic.Canonical))
  let horizontal := Axis.Separated.Replay.fromHorizontalProposal
    polynomial nonzero positive 3 horizontalSafe horizontalZero
  let originalHorizontal := Axis.Separated.Bezout.horizontalCoprimeCertificate
    polynomial nonzero positive 3 horizontalSafe
  unless horizontal.val.left.coeffs = originalHorizontal.left.coeffs ∧
      horizontal.val.right.coeffs = originalHorizontal.right.coeffs do
    throw (IO.userError "horizontal fallback changed an original quarter-turn cofactor")

#eval checkComputedCofactors

end TestPurelib.Polynomial.ComputedAxisCofactors
