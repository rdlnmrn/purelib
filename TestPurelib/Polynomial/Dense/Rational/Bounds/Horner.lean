module

import Purelib.Polynomial.Dense.Rational.Bounds.Horner
import Purelib.Polynomial.Elimination.Separated.Replay
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.System.IO
import scripts.checkpoint.RootRefinement

namespace TestPurelib.Polynomial.Dense.Rational.Bounds.Horner

open Purelib
open Purelib.Data.Rat
open Purelib.Polynomial.Dense.Rational
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Separated
open Purelib.Data.Gaussian
open Purelib.Geometry.Rational
open IntegrationCheckpoint

/-- Compute the original doubled Horner fold on the same retained coefficient table. -/
private def original (polynomial : Basic.CoordinatePolynomial) (interval : Interval.Bounds) : Fraction.Rational :=
  polynomial.coeffs.foldl (fun bound coefficient => 2 * (bound * interval.squareBound + coefficient ^ 2)) 0

/-- Force both same-input cofactor bounds at an explicit original-versus-direct-square timing boundary. -/
@[noinline] private def produce (cached : Bool) (left right : Basic.CoordinatePolynomial)
    (interval : Interval.Bounds) : IO Fraction.Rational :=
  pure (if cached then
    max 1 (Purelib.Polynomial.Dense.Rational.Bounds.Horner.evalSqBound left interval +
      Purelib.Polynomial.Dense.Rational.Bounds.Horner.evalSqBound right interval)
  else max 1 (original left interval + original right interval))

/-- Compare both timing orders on the same checked original column and horizontal ambient interval.

The saved column is decoded and every matrix row checked before its original
cofactor polynomials are read along the negative vertical line. Both majorant
producers consume those same tables and the retained interval `[1, 3/2]`.
-/
public def profileStored (path : System.FilePath) : IO Unit := do
  let raw : ClearanceCheckpoint.RawColumn ← loadJson path
  let coefficients ← match raw.polynomial.mapM decodeGaussian with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  let parameter ← match decodeFraction raw.parameter with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  let polynomial : CoefficientPolynomial := ⟨coefficients⟩
  if positive : 0 < polynomial.natDegree then
    let column ← match ClearanceCheckpoint.decode polynomial positive parameter raw with
      | .ok value => pure value
      | .error _ => throw (IO.userError "original Horner benchmark column failed its complete matrix check")
    let origin := Cast.Winding.verticalBase parameter
    let left := column.pathLeft origin Affine.Axis.negativeVerticalDirection
    let right := column.pathRight origin Affine.Axis.negativeVerticalDirection
    let interval : Interval.Bounds := ⟨1, 3/2, by decide⟩
    let start ← IO.monoNanosNow
    let old ← produce false left right interval
    let first ← IO.monoNanosNow
    let cached ← produce true left right interval
    let second ← IO.monoNanosNow
    unless old = cached do throw (IO.userError "direct squares changed the complete original Horner majorant")
    let third ← IO.monoNanosNow
    let cachedAgain ← produce true left right interval
    let fourth ← IO.monoNanosNow
    let oldAgain ← produce false left right interval
    let fifth ← IO.monoNanosNow
    unless oldAgain = cachedAgain do throw (IO.userError "reverse-order original Horner majorant disagrees")
    System.IO.println s!"same checked original horizontal majorant: original_ns={first-start} \
      direct_square_ns={second-first}; reverse_direct_ns={fourth-third} reverse_original_ns={fifth-fourth}; \
      both complete scalar bounds agree"
    (← IO.getStdout).flush
  else throw (IO.userError "original Horner benchmark polynomial has no positive degree")

end TestPurelib.Polynomial.Dense.Rational.Bounds.Horner
