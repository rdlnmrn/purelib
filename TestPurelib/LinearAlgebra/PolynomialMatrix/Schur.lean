module

import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Data.Gaussian.Field
import Purelib.System.IO
import scripts.checkpoint.Integration

/-! # Exact original Schur data with retained input caches -/

namespace TestPurelib.LinearAlgebra.PolynomialMatrix.Schur

open Purelib
open Purelib.Algebra.Field (ExplicitField)
open Purelib.LinearAlgebra renaming Matrix -> SquareMatrix
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open IntegrationCheckpoint
open Purelib.Data.Gaussian.Basic (Canonical)

/-- The original entry formula reconstructs its same tail, column and row inside every output entry. -/
private def entryFormula {K : Type*} [ExplicitField K] [DecidableEq K] {n : Nat}
    (matrix : Basic.Matrix K (n + 1)) : Basic.Matrix K n :=
  SquareMatrix.matrixOfFn fun row column =>
    Basic.head matrix * Basic.tail matrix row column - Basic.leftColumn matrix row * Basic.topRow matrix column

example {K : Type*} [ExplicitField K] [DecidableEq K] {n : Nat}
    (matrix : Basic.Matrix K (n + 1)) : Basic.schur matrix = entryFormula matrix := Basic.schur_eq matrix

/-- Compute the complete original scalar through the original entry formula at every retained dimension. -/
private def scalarFormula {K : Type*} [ExplicitField K] [DecidableEq K] :
    (n : Nat) → Basic.Matrix K n → Polynomial.Dense.Basic.DensePolynomial K
  | 0, _ => Polynomial.Dense.Basic.DensePolynomial.constant 1
  | n + 1, matrix => Basic.head matrix * scalarFormula n (entryFormula matrix)

example {K : Type*} [ExplicitField K] [DecidableEq K] (n : Nat) (matrix : Basic.Matrix K n) :
    Inverse.Scaled.Compute.scaledScalar n matrix = scalarFormula n matrix := by
  induction n with
  | zero => rfl
  | succ n inductionHypothesis =>
      exact congrArg (fun scalar => Basic.head matrix * scalar)
        ((inductionHypothesis (Basic.schur matrix)).trans
          (congrArg (scalarFormula n) (Basic.schur_eq matrix)))

/-- Force one complete original polynomial scalar producer at an explicit IO boundary. -/
@[noinline] private def produceScalar (work : Unit → Polynomial.Dense.Basic.DensePolynomial Canonical) :
    IO (Polynomial.Dense.Basic.DensePolynomial Canonical) := pure (work ())

/-- Force one original finite matrix producer at an explicit IO boundary. -/
@[noinline] private def produce {n : Nat} (work : Unit → Basic.Matrix Canonical n) : IO (Basic.Matrix Canonical n) :=
  pure (work ())

/-- Compare both entry producers in both orders on the same retained original matrix. -/
private def compare {n : Nat} (stage : Nat) (matrix : Basic.Matrix Canonical (n + 1)) :
    IO (Basic.Matrix Canonical n) := do
  let beginning ← IO.monoNanosNow
  let original ← produce (fun _ => entryFormula matrix)
  let first ← IO.monoNanosNow
  let cached ← produce (fun _ => Basic.schur matrix)
  let second ← IO.monoNanosNow
  unless ∀ row column : Fin n, original row column = cached row column do
    throw (IO.userError "retained input caches changed an original Schur entry")
  let third ← IO.monoNanosNow
  let cachedAgain ← produce (fun _ => Basic.schur matrix)
  let fourth ← IO.monoNanosNow
  let originalAgain ← produce (fun _ => entryFormula matrix)
  let fifth ← IO.monoNanosNow
  unless ∀ row column : Fin n, originalAgain row column = cachedAgain row column do
    throw (IO.userError "reverse timing changed an original Schur entry")
  Purelib.System.IO.println s!"original Schur stage={stage} dimension={n+1}: \
    original_ns={first-beginning} retained_ns={second-first}; \
    reverse_retained_ns={fourth-third} reverse_original_ns={fifth-fourth}; all entries agree"
  (← IO.getStdout).flush
  return original

/-- Carry the same completed original matrix into the next finite Schur stage without rebuilding its prefix. -/
private def stages : Nat → Nat → {n : Nat} → Basic.Matrix Canonical n → IO Unit
  | 0, _, _, _ => pure ()
  | _ + 1, _, 0, _ => pure ()
  | count + 1, stage, _ + 1, matrix => do
      let next ← compare stage matrix
      stages count (stage + 1) next

/-- Decode the same exact original coefficient field for both finite matrix interpreters. -/
private def readPolynomial (path : System.FilePath) : IO CoefficientPolynomial := do
  let raw : Data.Json ← loadJson path
  let data : List GaussianData ← match raw.getObjValAs? (List GaussianData) "polynomial" with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let coefficients ← match data.mapM decodeGaussian with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  return ⟨coefficients⟩

/-- Measure exact original polynomial matrices from a retained request without invoking root or elimination generators.

Only the original coefficient field is decoded. Three original Schur stages
retain their completed matrices and verify every entry in both timing orders;
the original request's geometric bounds, depth and target remain unchanged.
-/
public def checkStored (path : System.FilePath) : IO Unit := do
  let polynomial ← readPolynomial path
  let matrix := Polynomial.Elimination.Separated.Sylvester.separatedSylvester polynomial
  stages 3 0 matrix

/-- Compare complete scalar outputs on the same retained original coefficients, preserving every actual coefficient.

This finite scalar-only phase computes no root family, source refinement or
geometric request. The all-input identity above relates its original formula
to the same production scalar, independently of the native equality check.
-/
public def checkScalarStored (path : System.FilePath) : IO Unit := do
  let polynomial ← readPolynomial path
  let matrix := Polynomial.Elimination.Separated.Sylvester.separatedSylvester polynomial
  Purelib.System.IO.println s!"original scalar phase: original dimension={polynomial.natDegree+polynomial.natDegree}"
  (← IO.getStdout).flush
  let beginning ← IO.monoNanosNow
  let original ← produceScalar (fun _ => scalarFormula _ matrix)
  let first ← IO.monoNanosNow
  let cached ← produceScalar (fun _ => Inverse.Scaled.Compute.scaledScalar _ matrix)
  let second ← IO.monoNanosNow
  unless original = cached do throw (IO.userError "retained Schur inputs changed the complete original scalar")
  Purelib.System.IO.println s!"original scalar phase: original_ns={first-beginning} \
    retained_ns={second-first} degree={cached.natDegree}; all original coefficients agree"
  (← IO.getStdout).flush

end TestPurelib.LinearAlgebra.PolynomialMatrix.Schur
