module

import Purelib.Polynomial.Elimination.Separated.Replay
import Purelib.Polynomial.Dense.Gaussian.Path.Components
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Gaussian.Constants
import Purelib.Geometry.Rational.Affine.Axis
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.LinearAlgebra.Matrix.Multiplication.Gaussian
import Purelib.Data.Vector.Basic
import Purelib.System.IO
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.Integration

/-! # Affine path tables of checked original separated columns -/

namespace TestPurelib.Polynomial.Elimination.Separated.Replay

open Purelib
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Separated
open Purelib.Data.Gaussian
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Rational.Affine
open IntegrationCheckpoint
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.Data.Vector.Basic (vectorOfFn)

/-- Force one complete Gaussian product within a separate IO timing boundary. -/
@[noinline] private def produceProduct {count : Nat}
    (work : Unit → Data.Vector Basic.Canonical count) : IO (Data.Vector Basic.Canonical count) :=
  pure (work ())

/-- Compare every original product coordinate in both execution orders on the same retained operands. -/
private def compareProducts {count : Nat} (matrix : SquareMatrix Basic.Canonical count)
    (values : Data.Vector Basic.Canonical count) : IO Unit := do
  let start ← IO.monoNanosNow
  let original ← produceProduct fun _ => SquareMatrix.Multiplication.matrixVector matrix values
  let first ← IO.monoNanosNow
  let integers ← produceProduct fun _ => SquareMatrix.Multiplication.Gaussian.matrixVector matrix values
  let second ← IO.monoNanosNow
  unless ∀ row, original row = integers row do
    throw (IO.userError "integer accumulation changed an original product coordinate")
  let third ← IO.monoNanosNow
  let integersAgain ← produceProduct fun _ => SquareMatrix.Multiplication.Gaussian.matrixVector matrix values
  let fourth ← IO.monoNanosNow
  let originalAgain ← produceProduct fun _ => SquareMatrix.Multiplication.matrixVector matrix values
  let fifth ← IO.monoNanosNow
  unless ∀ row, originalAgain row = integersAgain row do
    throw (IO.userError "reverse timing changed an original product coordinate")
  System.IO.println s!"original matrix product: dimension={count} original_ns={first-start} \
    integer_ns={second-first}; reverse_integer_ns={fourth-third} reverse_original_ns={fifth-fourth}; \
    all complete product entries agree"
  (← IO.getStdout).flush

/-- Compare full Gaussian products on a saved polynomial, parameter and ordered column.

Only the saved scalar encodings and exact vector dimension are decoded. The
two products consume the same evaluated matrix and original column, including
when that column fails the separated unit-column equation. No root state or
column proposal is generated.
-/
public def profileProductsStored (path : System.FilePath) : IO Unit := do
  let raw : ClearanceCheckpoint.RawColumn ← loadJson path
  let coefficients ← match raw.polynomial.mapM decodeGaussian with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  let parameter ← match decodeFraction raw.parameter with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  let values ← match raw.values.mapM decodeGaussian with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  let polynomial : CoefficientPolynomial := ⟨coefficients⟩
  let count := polynomial.natDegree + polynomial.natDegree
  if size : values.length = count then
    let vector := vectorOfFn fun index : Fin count =>
      values[index.val]'(size.symm ▸ index.isLt)
    compareProducts (Replay.matrix polynomial parameter) vector
  else throw (IO.userError "saved original column dimension differs from twice its polynomial degree")

/-- Force the two original cofactor path tables at a separate measured IO boundary. -/
@[noinline] private def produce {p positive parameter} (cached : Bool) (column : Replay.Column p positive parameter)
    (direction : Basic.Canonical) :
    IO (Dense.Rational.Basic.CoordinatePolynomial × Dense.Rational.Basic.CoordinatePolynomial) :=
  pure (if cached then column.pathCofactors (Cast.Winding.verticalBase parameter) direction
    else (column.pathLeft (Cast.Winding.verticalBase parameter) direction,
      column.pathRight (Cast.Winding.verticalBase parameter) direction))

/-- Measure the original two cofactor paths on the same checked column and actual axis direction. -/
private def measure {p positive parameter} (column : Replay.Column p positive parameter)
    (horizontal : Bool) : IO Unit := do
  let direction := if horizontal then Axis.negativeVerticalDirection else Constants.imaginaryUnit
  System.IO.println s!"original column path start: dimension={p.natDegree+p.natDegree} horizontal={horizontal}"
  (← IO.getStdout).flush
  let start ← IO.monoNanosNow
  let original ← produce false column direction
  let first ← IO.monoNanosNow
  let cached ← produce true column direction
  let second ← IO.monoNanosNow
  unless original.1 = cached.1 && original.2 = cached.2 do
    throw (IO.userError "paired paths changed an original complete cofactor table")
  System.IO.println s!"same original column paths: original_ns={first-start} cached_ns={second-first} \
    left_count={cached.1.degreeCount} right_count={cached.2.degreeCount}; both complete tables agree"
  (← IO.getStdout).flush
  let third ← IO.monoNanosNow
  let cachedAgain ← produce true column direction
  let fourth ← IO.monoNanosNow
  let originalAgain ← produce false column direction
  let fifth ← IO.monoNanosNow
  unless originalAgain.1 = cachedAgain.1 && originalAgain.2 = cachedAgain.2 do
    throw (IO.userError "reverse timing changed an original complete cofactor table")
  System.IO.println s!"same original column reverse: cached_ns={fourth-third} original_ns={fifth-fourth}; \
    both complete tables agree"
  (← IO.getStdout).flush

/-- Check the exact saved column operands and profile their original affine cofactor tables.

The saved polynomial and parameter index the original full matrix equation.
The displayed direction selects its vertical or quarter-turned horizontal
callback. No column, root state or clearance majorant is regenerated.
-/
public def profileStored (path : System.FilePath) (horizontal : Bool) : IO Unit := do
  let raw : ClearanceCheckpoint.RawColumn ← loadJson path
  let coefficients ← match raw.polynomial.mapM decodeGaussian with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  let parameter ← match decodeFraction raw.parameter with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  let polynomial : CoefficientPolynomial := ⟨coefficients⟩
  if positive : 0 < polynomial.natDegree then
    System.IO.println "original saved column: decoded, checking original matrix equation"
    (← IO.getStdout).flush
    match ClearanceCheckpoint.decode polynomial positive parameter raw with
    | .error failure => throw (IO.userError s!"saved original column failed: {failure.report}")
    | .ok column => measure column horizontal
  else throw (IO.userError "saved original column has no positive degree")

end TestPurelib.Polynomial.Elimination.Separated.Replay
