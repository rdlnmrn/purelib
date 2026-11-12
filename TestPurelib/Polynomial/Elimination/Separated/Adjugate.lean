module

import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Adjugate
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Coefficients
import Purelib.Polynomial.Elimination.Separated.Sylvester
import Purelib.Polynomial.Dense.Gaussian.Components.Selection
import Purelib.Polynomial.Elimination.Axis.Preparation
import Purelib.Data.Gaussian.Field
import Purelib.System.IO
import Purelib.Data.Fin
import scripts.checkpoint.Integration

/-! # Checked adjugate proposals for original separated Sylvester inputs -/

namespace TestPurelib.Polynomial.Elimination.Separated.Adjugate

open Purelib
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Data.Gaussian.Basic (Canonical)
open IntegrationCheckpoint

/-- Force the complete retained proposal at a measured IO boundary. -/
@[noinline] private def produce {n : Nat} (matrix : Basic.Matrix Canonical n) :
    IO (Inverse.Scaled.Basic.ScaledInverseData Canonical n) := pure (Adjugate.compute matrix)

/-- Force both retained axis preparations before recording their completion boundary. -/
@[noinline] private def produceAxis (polynomial : CoefficientPolynomial) (nonzero : polynomial.isZero = false) :
    IO (Elimination.Axis.Preparation.Prepared polynomial) :=
  pure (Elimination.Axis.Preparation.prepare polynomial nonzero)

/-- Check every original polynomial product and the nonzero selected scalar of one retained source.

The source's actual coefficient list selects the same separated Sylvester
matrix as the original algorithm. No root, isolation or geometric request is
replaced by this matrix-only producer feasibility check.
-/
private def checkPolynomial (polynomial : CoefficientPolynomial) : IO Unit := do
  let matrix := Elimination.Separated.Sylvester.separatedSylvester polynomial
  let beginning ← IO.monoNanosNow
  let data ← produce matrix
  let produced ← IO.monoNanosNow
  match Coefficients.check matrix data with
  | .error _ => throw (IO.userError "polynomial trace proposal failed an original complete product")
  | .ok _ => pure ()
  unless data.scalar.isZero = false do throw (IO.userError "polynomial trace proposal retained a zero scalar")
  let selected := Dense.Gaussian.Components.Selection.selectedCoordinate data.scalar
  unless selected.isZero = false do throw (IO.userError "selected rational coordinate became zero")
  let checked ← IO.monoNanosNow
  System.IO.println s!"original Sylvester dimension={polynomial.natDegree+polynomial.natDegree}: \
    produce_ns={produced-beginning} checked_ns={checked-produced}; \
    Gaussian_degree={data.scalar.natDegree} selected_degree={selected.natDegree}; both complete products checked"
  (← IO.getStdout).flush
  if nonzero : polynomial.isZero = false then
    if positive : 0 < polynomial.natDegree then
      let started ← IO.monoNanosNow
      let prepared ← produceAxis polynomial nonzero
      let certificate := prepared.certificate nonzero positive
      let ready ← IO.monoNanosNow
      match prepared.vertical.construction, prepared.horizontal.construction with
      | .checked _, .checked _ => pure ()
      | _, _ => throw (IO.userError "original axis proposal did not pass both complete checks")
      if verticalSafe : certificate.vertical.eval 3 ≠ 0 then
        let cofactor := certificate.vertical_coprime 3 verticalSafe
        unless cofactor.left.eval 7 * (Dense.Gaussian.Path.Axis.verticalPathReal polynomial 3).eval 7 +
            cofactor.right.eval 7 * (Dense.Gaussian.Path.Axis.verticalPathImag polynomial 3).eval 7 = 1 do
          throw (IO.userError "retained vertical callback changed its original pointwise identity")
      else throw (IO.userError "retained vertical test coordinate was not clear")
      if horizontalSafe : certificate.horizontal.eval 3 ≠ 0 then
        let cofactor := certificate.horizontal_coprime 3 horizontalSafe
        unless cofactor.left.eval 7 * (Dense.Gaussian.Path.Axis.horizontalPathReal polynomial 3).eval 7 +
            cofactor.right.eval 7 * (Dense.Gaussian.Path.Axis.horizontalPathImag polynomial 3).eval 7 = 1 do
          throw (IO.userError "retained horizontal callback changed its original pointwise identity")
      else throw (IO.userError "retained horizontal test coordinate was not clear")
      let finished ← IO.monoNanosNow
      System.IO.println s!"actual retained axis certificate degree={prepared.degree}: \
        prepare_ns={ready-started} callbacks_ns={finished-ready}; both same-source coprime callbacks consumed"
      (← IO.getStdout).flush

/-- Inspect a typed retained failure through its original indexed construction. -/
private def checkFailure {p : CoefficientPolynomial} {data}
    (construction : Elimination.Separated.Preparation.Construction p data) : IO Nat :=
  match construction with
  | .checked _ => throw (IO.userError "invalid supplied proposal unexpectedly passed")
  | .fallback proposal (.zero _) => do
      unless proposal.scalar.isZero = true do throw (IO.userError "zero failure lost its original scalar")
      return 1
  | .fallback _ (.products (.left product identity _ _ _)) => do
      unless ∀ row column, (product row column).isZero = true do
        throw (IO.userError "failed product lost its computed original zero entries")
      letI : Decidable (∃ index, identity index index = Dense.Basic.DensePolynomial.constant 1) :=
        Data.Fin.existsDecidable _ _
      do
        unless ∃ index, identity index index = Dense.Basic.DensePolynomial.constant 1 do
          throw (IO.userError "failed product lost its original scalar target")
        return 2
  | .fallback _ (.products (.right _ _ _ _ _)) =>
      throw (IO.userError "invalid supplied proposal did not fail its first original product")

/-- Exercise both typed failed proposals and the exact original fallback on the same nonzero source. -/
private def checkFallback : IO Unit := do
  let polynomial : CoefficientPolynomial := ⟨[1, 0, -4]⟩
  have nonzero : polynomial.isZero = false := by decide +kernel
  let inverse : Basic.Matrix Canonical (polynomial.natDegree + polynomial.natDegree) := Basic.scaleIdentity 0
  let zeroProposal : Inverse.Scaled.Basic.ScaledInverseData Canonical (polynomial.natDegree + polynomial.natDegree) :=
    ⟨0, inverse⟩
  let zeroResult := Elimination.Separated.Preparation.prepareWithProposal polynomial nonzero zeroProposal
  unless (← checkFailure zeroResult.construction) = 1 do throw (IO.userError "wrong retained zero-scalar failure")
  let badProposal : Inverse.Scaled.Basic.ScaledInverseData Canonical (polynomial.natDegree + polynomial.natDegree) :=
    ⟨Dense.Basic.DensePolynomial.constant 1, inverse⟩
  let badResult := Elimination.Separated.Preparation.prepareWithProposal polynomial nonzero badProposal
  unless (← checkFailure badResult.construction) = 2 do throw (IO.userError "wrong retained complete-product failure")
  unless zeroResult.data.scalar = badResult.data.scalar do
    throw (IO.userError "typed rejection changed the original fallback scalar")
  System.IO.println "zero-scalar and complete-product failures retained; exact original fallback consumed"

/-- Check the original coefficient field from a saved request without invoking its geometric producers. -/
public def checkStored (path : System.FilePath) : IO Unit := do
  checkFallback
  let raw : Data.Json ← loadJson path
  let data : List GaussianData ← match raw.getObjValAs? (List GaussianData) "polynomial" with
    | .ok value => pure value
    | .error message => throw (IO.userError message)
  let coefficients ← match data.mapM decodeGaussian with
    | .ok value => pure value
    | .error failure => throw (IO.userError failure.message)
  checkPolynomial ⟨coefficients⟩

end TestPurelib.Polynomial.Elimination.Separated.Adjugate
