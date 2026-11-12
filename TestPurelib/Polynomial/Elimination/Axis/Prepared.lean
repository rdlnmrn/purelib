module

import Purelib.Polynomial.Elimination.Axis.Preparation
import Purelib.Polynomial.Elimination.Separated.Bezout.Prepared
import Purelib.Polynomial.Elimination.Axis.Separated.Replay
import Purelib.Polynomial.Elimination.Separated.Replay
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Data.Vector.Basic
import Purelib.Data.Gaussian.Field
import Purelib.System.IO
import scripts.checkpoint.Integration

/-! # Complete original cofactor certificates with retained normalization and paths -/

namespace TestPurelib.Polynomial.Elimination.Axis.Prepared

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Separated.Bezout.Prepared
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open IntegrationCheckpoint
open Purelib.Polynomial.Elimination

/-- Check both complete prepared certificates and a rejected zero column at one displayed coordinate. -/
private def checkReplayAt (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false)
    (positive : 0 < polynomial.natDegree) (axes : Axis.Preparation.Prepared polynomial)
    (parameter : Rational) : IO Unit := do
  if safe : axes.vertical.eliminant.eval parameter ≠ 0 then
    let column := Separated.Replay.Column.ofPrepared (positive := positive) (parameter := parameter)
      axes.vertical (axes.vertical.scalar_ne_zero parameter safe)
    match Separated.Replay.check polynomial positive parameter column.values with
    | .error _ => throw (IO.userError "retained prepared vertical column failed its complete unit equation")
    | .ok checked =>
        let actual := checked.verticalFromPrepared axes.vertical nonzero safe
        let original := Axis.Separated.Prepared.vertical axes.vertical nonzero positive parameter safe
        unless actual.val.left = original.left && actual.val.right = original.right do
          throw (IO.userError "prepared vertical replay changed a complete cofactor table")
  else throw (IO.userError "fixed prepared vertical replay coordinate was not clear")
  let rotated := Dense.Gaussian.Substitution.QuarterTurn.quarterTurn polynomial
  have rotatedPositive : 0 < rotated.natDegree := by
    rewrite [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_natDegree polynomial nonzero]
    exact positive
  if safe : axes.horizontal.eliminant.eval parameter ≠ 0 then
    let column := Separated.Replay.Column.ofPrepared (positive := rotatedPositive) (parameter := parameter)
      axes.horizontal (axes.horizontal.scalar_ne_zero parameter safe)
    match Separated.Replay.check rotated rotatedPositive parameter column.values with
    | .error _ => throw (IO.userError "retained prepared horizontal column failed its complete unit equation")
    | .ok checked =>
        let actual := Axis.Separated.Replay.horizontalFromPrepared polynomial axes.horizontal
          nonzero positive parameter safe checked
        let original := Axis.Separated.Prepared.horizontal axes.horizontal nonzero positive parameter safe
        unless actual.val.left = original.left && actual.val.right = original.right do
          throw (IO.userError "prepared horizontal replay changed a complete cofactor table")
  else throw (IO.userError "fixed prepared horizontal replay coordinate was not clear")
  let zero := Data.Vector.Basic.vectorOfFn fun _ : Fin (polynomial.natDegree + polynomial.natDegree) =>
    (0 : Basic.Canonical)
  match Separated.Replay.check polynomial positive parameter zero with
  | .ok _ => throw (IO.userError "prepared column checker accepted a zero vector at a nonempty unit column")
  | .error _ => pure ()

/-- Check retained prepared columns and complete replay in both directions on fixed finite source matrices.

Each original two-axis preparation is computed once before its coordinates.
Quadratic, cubic and complex nonmonic sources retain their exact coefficient
tables; every returned column is independently row-checked before cofactor comparison. -/
public def checkReplay : IO Unit := do
  let sources : List (List Basic.Canonical) :=
    [[1, 0, -4], [1, 0, 0, -2], [⟨2, 1⟩, ⟨3, -2⟩, ⟨-1, 4⟩, ⟨5, -1⟩]]
  let quadratic : CoefficientPolynomial := ⟨[1, 0, -4]⟩
  let singular := Axis.Preparation.prepare quadratic (by decide +kernel)
  unless singular.vertical.eliminant.eval 2 = 0 do
    throw (IO.userError "prepared quadratic eliminant lost its actual root-coordinate obstruction")
  for coefficients in sources do
    let polynomial : CoefficientPolynomial := ⟨coefficients⟩
    if nonzero : polynomial.isZero = false then
      if positive : 0 < polynomial.natDegree then
        let axes := Axis.Preparation.prepare polynomial nonzero
        for parameter in ([3, 3 / 7, 7 / 16] : List Rational) do
          checkReplayAt polynomial nonzero positive axes parameter
      else throw (IO.userError "fixed prepared replay polynomial lost its positive degree")
    else throw (IO.userError "fixed prepared replay polynomial became zero")
  System.IO.println "retained prepared unit columns, both full cofactor tables and zero-column rejection passed"

/-- Materialize one retained original preparation before measuring either cofactor producer. -/
@[noinline] private def prepare (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false) :
    IO (Separated.Preparation.Prepared polynomial) :=
  pure (Separated.Preparation.prepare polynomial nonzero)

/-- Reproduce the original separate real-path cofactor producer on the same retained inverse. -/
private def originalLeft {p : CoefficientPolynomial} (prepared : Separated.Preparation.Prepared p)
    (positive : 0 < p.natDegree) (parameter : Rational) : Dense.Rational.Basic.CoordinatePolynomial :=
  Dense.Gaussian.Path.Components.pathReal (normalizedLeft prepared positive parameter)
    (Cast.Winding.verticalBase parameter) Constants.imaginaryUnit +
  Dense.Gaussian.Path.Components.pathReal (normalizedRight prepared positive parameter)
    (Cast.Winding.verticalBase parameter) Constants.imaginaryUnit

/-- Reproduce the original separate imaginary-path cofactor producer on the same retained inverse. -/
private def originalRight {p : CoefficientPolynomial} (prepared : Separated.Preparation.Prepared p)
    (positive : 0 < p.natDegree) (parameter : Rational) : Dense.Rational.Basic.CoordinatePolynomial :=
  Dense.Gaussian.Path.Components.pathImag (normalizedLeft prepared positive parameter)
    (Cast.Winding.verticalBase parameter) Constants.imaginaryUnit -
  Dense.Gaussian.Path.Components.pathImag (normalizedRight prepared positive parameter)
    (Cast.Winding.verticalBase parameter) Constants.imaginaryUnit

/-- Assemble the original complete certificate from its two separately produced cofactor polynomials. -/
private def original {p : CoefficientPolynomial} (prepared : Separated.Preparation.Prepared p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Rational)
    (safe : prepared.eliminant.eval parameter ≠ 0) :
    Dense.Rational.Bezout.Basic.CoprimeCertificate (Dense.Gaussian.Path.Axis.verticalPathReal p parameter)
      (Dense.Gaussian.Path.Axis.verticalPathImag p parameter) where
  left := originalLeft prepared positive parameter
  right := originalRight prepared positive parameter
  identity := (Elimination.Axis.Separated.Prepared.vertical prepared nonzero positive parameter safe).identity

/-- The cached producer retains the complete original certificate for every input, including its proof fields. -/
private theorem agreement {p : CoefficientPolynomial} (prepared : Separated.Preparation.Prepared p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Rational)
    (safe : prepared.eliminant.eval parameter ≠ 0) :
    Elimination.Axis.Separated.Prepared.vertical prepared nonzero positive parameter safe =
      original prepared nonzero positive parameter safe :=
  Dense.Rational.Bezout.Basic.coprime_eq _ _
    (Elimination.Axis.Separated.Prepared.vertical_left prepared nonzero positive parameter safe)
    (Elimination.Axis.Separated.Prepared.vertical_right prepared nonzero positive parameter safe)

/-- Force one complete certificate at an explicit original-versus-cached timing boundary. -/
@[noinline] private def produce {p : CoefficientPolynomial} (cached : Bool)
    (prepared : Separated.Preparation.Prepared p) (nonzero : p.isZero = false)
    (positive : 0 < p.natDegree) (parameter : Rational) (safe : prepared.eliminant.eval parameter ≠ 0) :
    IO (Dense.Rational.Bezout.Basic.CoprimeCertificate (Dense.Gaussian.Path.Axis.verticalPathReal p parameter)
      (Dense.Gaussian.Path.Axis.verticalPathImag p parameter)) :=
  pure (if cached then Elimination.Axis.Separated.Prepared.vertical prepared nonzero positive parameter safe
    else original prepared nonzero positive parameter safe)

/-- Compare both complete cofactor tables in both timing orders on one same retained original matrix preparation. -/
private def compare {p : CoefficientPolynomial} (prepared : Separated.Preparation.Prepared p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) (parameter : Rational) : IO Unit := do
  if safe : prepared.eliminant.eval parameter ≠ 0 then
    let start ← IO.monoNanosNow
    let original ← produce false prepared nonzero positive parameter safe
    let first ← IO.monoNanosNow
    let cached ← produce true prepared nonzero positive parameter safe
    let second ← IO.monoNanosNow
    unless original.left = cached.left && original.right = cached.right do
      throw (IO.userError "cached normalization or paths changed an original cofactor table")
    let third ← IO.monoNanosNow
    let cachedAgain ← produce true prepared nonzero positive parameter safe
    let fourth ← IO.monoNanosNow
    let originalAgain ← produce false prepared nonzero positive parameter safe
    let fifth ← IO.monoNanosNow
    unless originalAgain.left = cachedAgain.left && originalAgain.right = cachedAgain.right do
      throw (IO.userError "reverse timing changed an original cofactor table")
    System.IO.println s!"same original cofactor dimension={p.natDegree+p.natDegree}: \
      original_ns={first-start} cached_ns={second-first}; \
      reverse_cached_ns={fourth-third} reverse_original_ns={fifth-fourth}; both complete tables agree"
    (← IO.getStdout).flush
  else throw (IO.userError "cofactor benchmark coordinate is not clear on its original owner")

/-- Compare one unchanged request's same retained cofactor operands at three displayed coordinates. -/
public def profileStored (path : System.FilePath) : IO Unit := do
  let raw : Data.Json ← loadJson path
  let data : List GaussianData ← match raw.getObjValAs? (List GaussianData) "polynomial" with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let coefficients ← match data.mapM decodeGaussian with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  let polynomial : CoefficientPolynomial := ⟨coefficients⟩
  if nonzero : polynomial.isZero = false then
    if positive : 0 < polynomial.natDegree then
      let prepared ← prepare polynomial nonzero
      compare prepared nonzero positive 3
      compare prepared nonzero positive (3/7)
      compare prepared nonzero positive (7/16)

end TestPurelib.Polynomial.Elimination.Axis.Prepared
