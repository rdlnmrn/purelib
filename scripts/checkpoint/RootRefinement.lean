module

import Purelib.System.FilePath
import Purelib.Data.String.Parsing

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.Int.Decimal
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Polynomial.Dense.Gaussian.Newton.Basic
public import Purelib.RootIsolation.SquareRoot.Replay.CheckedDiameterReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay
import Purelib.Data.Rat.Fraction
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Basic
import Purelib.Polynomial.Dense.Rational.SignedRemainder.Variation
import Purelib.Approximation.Gaussian.Grid.Box
import Purelib.Approximation.Gaussian.Grid.Replay
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Rounding.Floor
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Bezout
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Path.Box.Sides
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Polynomial.Dense.Rational.Basic
import Purelib.Polynomial.Dense.Rational.Pair.Path.Basic
import Purelib.Polynomial.Elimination.Axis.Band
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Elimination.Axis.Separated
public import Purelib.Polynomial.Elimination.Axis.Separated.Replay
import Purelib.Polynomial.Elimination.Separated.Replay
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.RootIsolation.Newton.Search.Iteration
import Purelib.RootIsolation.Newton.Search.Replay.Input
public import Purelib.RootIsolation.Newton.Search.Execution
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.Subdivision.Raw.Request
import Purelib.Polynomial.Dense.Rational.Division.Replay
public import Purelib.Polynomial.Dense.Rational.SignedRemainder.Replay
public import Purelib.RootIsolation.Newton.Search.Center.Replay

import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
public import Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay
public import scripts.checkpoint.RootState
import Init.Data.Int.Basic
import Init.Data.List.OfFn
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
public import Init.Control.Except
public import Init.Control.State
import Purelib.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Band.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Budget.Center
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.LinearAlgebra.Matrix.Inverse.Scaled.GaussianColumn
import Purelib.LinearAlgebra.Matrix.Multiplication
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.Polynomial.Dense.Derivative
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Path.Axis
import Purelib.Polynomial.Dense.Multiplication
import Purelib.Polynomial.Dense.Rational.Bezout.Basic
import Purelib.Polynomial.Dense.Rational.CauchyIndex.Path
import Purelib.Polynomial.Elimination.Axis.Separated.Bezout
import Purelib.Polynomial.Elimination.Separated.Bezout
import Purelib.RootIsolation.Newton.Search.Center.Basic
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.State.WindingOne.Raw
import scripts.checkpoint.Integration
import Purelib.Tactic.QuotientFreeOmega

-- Use complete constructor eliminators for the original match arms.
set_option backward.match.sparseCases false

open Purelib

open Purelib.Approximation

open Purelib.Data.Rat

open Purelib.Data.Rat.Rounding

open Purelib.Geometry

open Purelib.Polynomial

open Purelib.RootIsolation

open Purelib.Data (Json)
open scoped Purelib.Data.String
open scoped Purelib.Data.Int.Decimal
open Purelib.Data.Json (toJson)

public section

/-!
Atomic, independently checked Newton-proposal checkpoints.  The supplied
polynomial, ambient, current box and request are bound by exact decoded data;
each proposal is then checked against the preceding certified search cursor.
This restores that bounded attempt, not an unidentified period source.

The only additional dependencies are the existing finite checkpoint codecs
and Lean's IO.  No mathematical module imports this script.
-/

/-!
Atomic checkpoints for each division in the original finite winding chain.
Reload uses exact coefficient identities, never the division generator. Each
file binds both input polynomials and the saved witness. This is a new stage
beside older Newton proposal files; those files remain usable unchanged.
-/

namespace WindingCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]

open IntegrationCheckpoint
open Purelib.Polynomial.Dense.Basic.DensePolynomial
open Purelib.Polynomial.Dense.Rational.Basic renaming CoordinatePolynomial -> Dense

set_option genInjectivity false in
/-- Serialized operands and quotient/remainder witness for one original winding-chain division.

All four polynomial encodings retain their original coefficient order.
Verification checks the supplied division relation rather than recomputing
and silently selecting a different quotient or remainder. -/
structure RawStep where
  /-- The exact dividend coefficients in ascending order. -/ dividend : List FractionData
  /-- The exact divisor coefficients in ascending order. -/ divisor : List FractionData
  /-- The proposed exact quotient coefficients. -/ quotient : List FractionData
  /-- The proposed exact remainder coefficients. -/ remainder : List FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawStep

/-- Encode each exact rational coefficient of a dense polynomial. -/
@[expose] def polynomialData (p : Dense.Rational.Basic.CoordinatePolynomial) : List FractionData := p.coeffs.map
  fractionData

/-- Decode a finite coefficient list into a dense rational polynomial. -/
@[expose] def decodePolynomial (data : List FractionData) : Except InvalidData Dense := do
  return ⟨← data.mapM decodeFraction⟩

/-- Serialize both original division operands and the saved quotient/remainder witness. -/
@[expose] def encode (p q : Dense.Rational.Basic.CoordinatePolynomial) (witness :
  Dense.Rational.Division.Replay.Witness) :
  RawStep :=
  ⟨polynomialData p, polynomialData q, polynomialData witness.quotient,
    polynomialData witness.remainder⟩

set_option genInjectivity false in
/-- A scalar, operand-identity or division-certificate failure for the original chain step. -/
inductive Failure (p q : Dense.Rational.Basic.CoordinatePolynomial) where
  /-- An invalid exact scalar encoding. -/ | field (failure : InvalidData)
  /-- A decoded dividend certified different from the original operand. -/ | dividend (saved :
    Dense.Rational.Basic.CoordinatePolynomial) (failed : saved ≠ p)
  /-- A decoded divisor certified different from the original operand. -/ | divisor (saved :
    Dense.Rational.Basic.CoordinatePolynomial) (failed : saved ≠ q)
  /-- A proposed division witness failing normalization, degree or exact identity checks. -/ | witness (saved :
    Dense.Rational.Division.Replay.Witness) (failure : Dense.Rational.Division.Replay.Invalid p q saved)

constructive_injectivity Failure

/-- Check a saved division against its exact original operands and nonzero divisor.

Decode all coefficients, require operand equality and verify the polynomial identity and strict remainder-degree bound.
-/
@[expose] def decode (p q : Dense.Rational.Basic.CoordinatePolynomial) (nonzero : q.isZero = false) (raw : RawStep) :
    Except (Failure p q) (Dense.Rational.Division.Replay.Step p q) := do
  let savedP ← (decodePolynomial raw.dividend).mapError .field
  let savedQ ← (decodePolynomial raw.divisor).mapError .field
  if sameP : savedP = p then
    if sameQ : savedQ = q then
      let quotient ← (decodePolynomial raw.quotient).mapError .field
      let remainder ← (decodePolynomial raw.remainder).mapError .field
      let witness : Dense.Rational.Division.Replay.Witness := ⟨quotient, remainder⟩
      (Dense.Rational.Division.Replay.check p q nonzero witness).mapError (.witness witness)
    else .error (.divisor savedQ sameQ)
  else .error (.dividend savedP sameP)

/-- Serialize the failed scalar, operand comparison or exact division condition. -/
@[expose] def Failure.report {p q : Dense.Rational.Basic.CoordinatePolynomial} : Failure p q → Json
  | .field failure => Json.mkObj [("kind", toJson failure.message)]
  | .dividend saved _ => Json.mkObj
      [("kind", toJson "dividend differs from original chain member"),
       ("saved", toJson (polynomialData saved)), ("original", toJson (polynomialData p))]
  | .divisor saved _ => Json.mkObj
      [("kind", toJson "divisor differs from original chain member"),
       ("saved", toJson (polynomialData saved)), ("original", toJson (polynomialData q))]
  | .witness saved failure =>
      let kind := match failure with
        | .normalization _ => "remainder is not normalized"
        | .degree _ => "remainder degree does not strictly decrease"
        | .identity _ _ _ => "polynomial division identity failed"
      Json.mkObj [("kind", toJson kind), ("operands", toJson (encode p q saved))]

set_option genInjectivity false in
/-- Controls for forbidding winding generation and observing completed atomic saves. -/
structure Control (m : Type → Type := IO) [Monad m] where
  /-- Require every division witness to be present already, without calling its generator. -/ savedOnly : Bool := false
  /-- Regression hook runs only after the witness is atomically saved. -/
  afterSave : m Unit := pure ()

constructive_injectivity Control

/-- Generate one original exact polynomial-division witness, emitting the generation diagnostic. -/
@[expose, noinline] def generateStep (p q : Dense.Rational.Basic.CoordinatePolynomial) :
  Dense.Rational.Division.Replay.Step p q
  :=
  dbg_trace "WINDING_DIVISION_GENERATOR_FORCED"
  Dense.Rational.Division.Replay.generate p q

/-- Restore a checked division witness or atomically save a newly generated one.

Saved-only replay retains the next exact operands when a file is missing; invalid saved data retains the failed
condition. -/
@[expose] def loadStep (control : Control m) (directory : System.FilePath) (index : Nat)
    (p q : Dense.Rational.Basic.CoordinatePolynomial) (nonzero : q.isZero = false) : m
      (Dense.Rational.Division.Replay.Step p q)
      := do
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"division-{index}.json")))
  if ← path.pathExists then
    let raw : RawStep ← loadJson path
    match decode p q nonzero raw with
    | .ok step =>
        profile directory s!"REUSED winding division {index}"
        return step
    | .error failure =>
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid.json")))) failure.report
        throw (IO.userError s!"invalid winding division {index}; violated condition and operands saved")
  if control.savedOnly then
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("missing.json")))) (Json.mkObj
      [("kind", toJson "incomplete saved winding chain; generation forbidden"),
       ("index", toJson index), ("dividend", toJson (polynomialData p)),
       ("divisor", toJson (polynomialData q)), ("remainingDegree", toJson q.degreeCount)])
    throw (IO.userError s!"missing winding division {index}; exact next operands retained")
  let step := generateStep p q
  saveJson path (encode p q step.witness)
  profile directory s!"SAVED winding division {index}"
  control.afterSave
  return step

/-- The degree bound is a proof about the original chain, independent of file contents. A saved witness cannot extend
the recursion budget. -/
@[expose] def chain (control : Control m) (directory : System.FilePath) :
    (fuel index : Nat) → (p q : Dense.Rational.Basic.CoordinatePolynomial) → q.degreeCount ≤ fuel →
      m { values : List Dense.Rational.Basic.CoordinatePolynomial // values =
        Dense.Rational.SignedRemainder.Basic.Sturm.signedRemainderChain p q }
  | 0, _, p, q, bound => do
      have zero := Dense.Basic.DensePolynomial.isZero_true_of_degreeCount_eq_zero (show q.degreeCount = 0 by omega)
      return ⟨[p], (Dense.Rational.SignedRemainder.Replay.terminal p q zero).symm⟩
  | fuel + 1, index, p, q, bound => do
      if zero : q.isZero = true then return ⟨[p], (Dense.Rational.SignedRemainder.Replay.terminal p q zero).symm⟩
      else
        have nonzero : q.isZero = false := Bool.eq_false_iff.mpr zero
        let step ← loadStep control directory index p q nonzero
        let tail ← chain control directory fuel (index + 1) q (-step.witness.remainder)
          (by have := step.small nonzero; omega)
        return ⟨p :: tail.val, step.prepend nonzero tail.val tail.property⟩

/-- Reconstruct the original doubled edge winding from its checked signed-remainder chain. -/
@[expose] def edge (control : Control m) (directory : System.FilePath) (edge :
  Dense.Rational.Pair.Path.Basic.PolynomialEdge) :
    m { value : Int // value = edge.doubledWinding } := do
  IO.FS.createDirAll directory
  let values ← chain control directory edge.realPart.degreeCount 0 edge.imagPart edge.realPart le_rfl
  return ⟨(Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 values.val edge.start : Int) -
      Dense.Rational.SignedRemainder.Variation.Sturm.endpointVariation2 values.val edge.stop, by
    rw [values.property]; rfl⟩

/-- Reconstruct the original quadrupled box winding from four ordered checked edge chains.

Save the exact polynomial, box and winding readback, with an equation to the original winding operation. -/
@[expose] def box (control : Control m) (directory : System.FilePath)
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Rational.Box) :
    m { value : Int // value = Winding.Box.Basic.quadrupledBoxWinding p box } := do
  let bottom ← edge control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("bottom"))))
    (Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yLower box.xLower box.xUpper)
  let right ← edge control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("right"))))
    (Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xUpper box.yLower box.yUpper)
  let top ← edge control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("top"))))
    (Dense.Gaussian.Path.Box.Sides.horizontalEdge p box.yUpper box.xUpper box.xLower)
  let left ← edge control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("left"))))
    (Dense.Gaussian.Path.Box.Sides.verticalEdge p box.xLower box.yUpper box.yLower)
  let value := bottom.val + right.val + top.val + left.val
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("winding-result.json")))) (Json.mkObj
    [("polynomial", toJson (p.coeffs.map gaussianData)),
     ("box", toJson (RootStateCheckpoint.boxData box)),
     ("winding", toJson value),
     ("source", toJson "reconstructed from checked original division chain")])
  profile directory s!"COMPLETE original box winding {value}"
  return ⟨value, by
    dsimp only [value]
    rw [Winding.Box.Basic.quadrupledBoxWinding_eq, bottom.property, right.property,
      top.property, left.property]⟩

end WindingCheckpoint

namespace ClearanceCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]

open IntegrationCheckpoint
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Data.Rat.Fraction (Rational)

/-- Finite vectors with the supplied carrier and retained dimension. -/
abbrev Vector (K : Type*) (n : Nat) := Data.Vector K n

set_option genInjectivity false in
/-- Serialized polynomial, axis parameter and proposed separated-Sylvester column.

The polynomial, parameter and ordered column values remain separate retained
encodings. Verification checks their exact scalar readbacks at that parameter. -/
structure RawColumn where
  /-- The original Gaussian polynomial coefficients. -/ polynomial : List GaussianData
  /-- The exact axis parameter of the evaluated matrix. -/ parameter : FractionData
  /-- The proposed finite column entries in their original order. -/ values : List GaussianData
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawColumn

set_option genInjectivity false in
/-- Controls for saved-only clearance replay and completed atomic saves. -/
structure Control (m : Type → Type := IO) [Monad m] where
  /-- Forbid generating a missing clearance column. -/ savedOnly : Bool := false
  /-- The hook invoked only after the checked column has been saved. -/ afterSave : m Unit := pure ()

constructive_injectivity Control

/-- Serialize a checked separated-Sylvester column with its original polynomial and parameter. -/
@[expose] def encode {p positive parameter} (column : Elimination.Separated.Replay.Column p positive parameter) :
  RawColumn :=
  ⟨p.coeffs.map gaussianData, fractionData parameter,
    (List.ofFn fun index => column.values index).map gaussianData⟩

set_option genInjectivity false in
/-- A scalar, polynomial-identity, dimension or matrix-equation failure for a saved column. -/
inductive Failure (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (positive : 0 <
  p.natDegree) (parameter
  : Fraction.Rational) where
  /-- A failed scalar decode or exact axis-parameter comparison. -/ | field (failure : InvalidData)
  /-- A decoded polynomial certified different from the original input. -/ | polynomial (saved :
    Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (failed : saved ≠ p)
  /-- A saved column length different from twice the polynomial degree. -/ | size (values : List
    Data.Gaussian.Basic.Canonical) (failed : values.length ≠ p.natDegree + p.natDegree)
  /-- A finite vector failing the original evaluated Sylvester equation. -/ | equation (values : Vector
    Data.Gaussian.Basic.Canonical (p.natDegree + p.natDegree))
      (failure : Elimination.Separated.Replay.Invalid p positive parameter values)

constructive_injectivity Failure

/-- Check a saved column against the original polynomial, parameter and matrix equation.

Only an exactly sized vector satisfying that equation becomes a retained clearance certificate. -/
@[expose] def decode (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (positive : 0 <
  p.natDegree)
  (parameter : Fraction.Rational)
    (raw : RawColumn) : Except (Failure p positive parameter) (Elimination.Separated.Replay.Column p positive parameter)
      := do
  let coefficients ← (raw.polynomial.mapM decodeGaussian).mapError .field
  let saved : GaussianPolynomial := ⟨coefficients⟩
  if same : saved = p then
    let savedParameter ← (decodeFraction raw.parameter).mapError .field
    if sameParameter : savedParameter = parameter then
      let values ← (raw.values.mapM decodeGaussian).mapError .field
      if size : values.length = p.natDegree + p.natDegree then
        let vector := Data.Vector.Basic.vectorOfFn fun index : Fin (p.natDegree + p.natDegree) =>
          values[index.val]'(by have := index.isLt; omega)
        (Elimination.Separated.Replay.check p positive parameter vector).mapError (.equation vector)
      else .error (.size values size)
    else .error (.field (.rationalMismatch "clearance parameter" savedParameter parameter sameParameter))
  else .error (.polynomial saved same)

/-- Serialize the exact failed field, polynomial, dimension or evaluated matrix product. -/
@[expose] def Failure.report {p positive parameter} : Failure p positive parameter → Json
  | .field failure => Json.mkObj [("kind", toJson failure.message)]
  | .polynomial saved _ => Json.mkObj
      [("kind", toJson "clearance source polynomial differs"),
       ("saved", toJson (saved.coeffs.map gaussianData)),
       ("expected", toJson (p.coeffs.map gaussianData))]
  | .size values _ => Json.mkObj
      [("kind", toJson "clearance column length differs from twice the polynomial degree"),
       ("values", toJson (values.map gaussianData)), ("expected", toJson (p.natDegree + p.natDegree))]
  | .equation values (.equation actual _ _) => Json.mkObj
      [("kind", toJson "saved column does not solve the original evaluated Sylvester equation"),
       ("values", toJson ((List.ofFn fun index => values index).map gaussianData)),
       ("actualProduct", toJson ((List.ofFn fun index => actual index).map gaussianData))]

/-- Propose the original finite separated-Sylvester column and emit the generation diagnostic. -/
@[expose, noinline] def generate (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial)
  (positive : 0 <
  p.natDegree) (parameter : Fraction.Rational) :=
  dbg_trace "CLEARANCE_COLUMN_GENERATOR_FORCED"
  Elimination.Separated.Replay.propose p positive parameter

/-- Restore a verified clearance column or check and save a fresh finite proposal.

A failed fresh equation is proposal failure, while a missing saved-only column retains the precise next request. -/
@[expose] def load (control : Control m) (directory : System.FilePath)
    (p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (positive : 0 < p.natDegree)
      (parameter :
      Fraction.Rational) :
    m (Elimination.Separated.Replay.Column p positive parameter) := do
  IO.FS.createDirAll directory
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("column.json")))
  if ← path.pathExists then
    let raw : RawColumn ← loadJson path
    match decode p positive parameter raw with
    | .ok result =>
        profile directory "REUSED original clearance column"
        return result
    | .error failure =>
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid.json")))) failure.report
        throw (IO.userError "invalid saved clearance column; failed equation and operands retained")
  if control.savedOnly then
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("missing.json")))) (Json.mkObj
      [("kind", toJson "missing original clearance column; generation forbidden"),
       ("polynomial", toJson (p.coeffs.map gaussianData)),
       ("parameter", toJson (fractionData parameter)), ("dimension", toJson (p.natDegree + p.natDegree))])
    throw (IO.userError "missing original clearance column; next request retained")
  let values := generate p positive parameter
  match Elimination.Separated.Replay.check p positive parameter values with
  | .error failure =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-generated.json"))))
        (Failure.report (.equation values failure))
      throw (IO.userError "finite clearance-column proposal failed its equation; this is not input invalidity")
  | .ok result =>
      saveJson path (encode result)
      profile directory "SAVED original clearance column"
      control.afterSave
      return result

end ClearanceCheckpoint

namespace RootRefinementCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]

open Purelib.Approximation.Gaussian.Grid.Replay (Witness)
open Purelib.RootIsolation.Newton.Search.Replay.Input (Invalid)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction renaming Rational -> Coordinate
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial

open IntegrationCheckpoint

set_option genInjectivity false in
/-- Serialized integer floors for one rounded Gaussian proposal.

The two signed integer floors retain their exact decimal representations.
Their relation to the original real and imaginary readings is checked before
using the restored rounding witness. -/
structure RawWitness where
  /-- The exact real-coordinate grid-floor integer. -/ realFloor : String
  /-- The exact imaginary-coordinate grid-floor integer. -/ imaginaryFloor : String
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawWitness

/-- Serialize both integer floors of a rounding witness. -/
@[expose] def encode (witness : Gaussian.Grid.Replay.Witness) : RawWitness :=
  ⟨toString witness.realFloor, toString witness.imaginaryFloor⟩

/-- Decode the two signed grid-floor integers, retaining invalid syntax. -/
@[expose] def decode (raw : RawWitness) : Except InvalidData Witness := do
  let some real := (Purelib.Data.String.toInt? raw.realFloor)
    | .error (.syntax s!"invalid real floor {raw.realFloor}")
  let some imaginary := (Purelib.Data.String.toInt? raw.imaginaryFloor)
    | .error (.syntax s!"invalid imaginary floor {raw.imaginaryFloor}")
  return ⟨real, imaginary⟩

/-- Serialize a violated grid, floor bound or exact Newton product identity. -/
@[expose] def invalidReport : Invalid → Json
  | .nonpositiveGrid value _ => Json.mkObj
      [("kind", toJson "nonpositive grid"), ("grid", toJson (fractionData value))]
  | .lower imaginary value spacing integer _ => Json.mkObj
      [("kind", toJson "floor lower bound violated"), ("imaginary", toJson imaginary),
       ("value", toJson (fractionData value)), ("grid", toJson (fractionData spacing)),
       ("integer", toJson (toString integer))]
  | .upper imaginary value spacing integer _ => Json.mkObj
      [("kind", toJson "floor strict upper bound violated"), ("imaginary", toJson imaginary),
       ("value", toJson (fractionData value)), ("grid", toJson (fractionData spacing)),
       ("integer", toJson (toString integer))]
  | .newton center next derivative value _ => Json.mkObj
      [("kind", toJson "Newton product identity violated"),
       ("center", toJson (gaussianData center)), ("next", toJson (gaussianData next)),
       ("derivative", toJson (gaussianData derivative)), ("value", toJson (gaussianData value))]

set_option genInjectivity false in
/-- Counts of newly generated and reused rounding and Newton proposal stages.

The counters retain separate generated and reused outcomes. Constructor
defaults initialize absent construction arguments; decoding still requires
every nonoptional serialized field. -/
structure Counts where
  /-- The number of rounding stages generated and saved in this run. -/ generatedRounding : Nat := 0
  /-- The number of saved rounding stages reused in this run. -/ reusedRounding : Nat := 0
  /-- The number of Newton stages generated and saved in this run. -/ generatedNewton : Nat := 0
  /-- The number of saved Newton stages reused in this run. -/ reusedNewton : Nat := 0
deriving Json.ToJson, Json.FromJson

constructive_injectivity Counts

set_option genInjectivity false in
/-- Replay policy and interruption hook for the exact finite proposal stages.

Counter state is threaded separately through `Execution`, retaining updated
counts with both successful results and structured IO errors. -/
structure Control where
  /-- Forbid invoking a completed proposal generator when saved data is absent. -/ savedOnly : Bool := false
  /-- The optional completed-write count at which the restart regression terminates its child. -/ killAfterWrites :
    Option Nat := none

constructive_injectivity Control

/-- Error-preserving execution with the original four proposal counters.

The state lies below the error transformer, so a failed IO action retains the
completed counter updates together with its original structured IO error. -/
abbrev Execution := ExceptT IO.Error (StateT Counts BaseIO)

/-- Run the retained execution from the supplied exact proposal counts.

Both success and failure return the complete updated counts. This operation
allocates, reads and mutates no reference. -/
@[expose] def Execution.run {Alpha : Type} (action : Execution Alpha) (counts : Counts) :
    BaseIO (Except IO.Error Alpha × Counts) := ExceptT.run action counts

/-- Lift one original IO action without changing the current proposal counts.

The action executes once. Its original successful value or structured error
is returned with the same complete counters and original world ordering. -/
@[expose] def Execution.liftIO {Alpha : Type} (action : IO Alpha) : Execution Alpha :=
  fun counts => do
    let result ← action.toBaseIO
    return (result, counts)

/-- Execute original IO operations inside the error-preserving counter state. -/
instance : MonadLift IO Execution := ⟨Execution.liftIO⟩

/-- Read the original four proposal counters without allocating a reference. -/
@[expose] def Execution.counts [MonadStateOf Counts m] : m Counts := getThe Counts

/-- Apply one original scalar update to the exact proposal counters. -/
@[expose] def Execution.update [MonadStateOf Counts m] (change : Counts → Counts) : m Unit := modifyThe Counts change

/-- Create the original saved-only and interruption policies without reference state. -/
@[expose] def Control.create (savedOnly : Bool := false) (killAfterWrites : Option Nat := none) : IO Control :=
  pure ⟨savedOnly, killAfterWrites⟩

set_option genInjectivity false in
/-- Loaders returning the exact original vertical and horizontal line clearances.

Each result keeps equality to the supplied source clearance, preserving the elimination certificate and ambient box. -/
structure ClearanceLoader {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
      (source : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
    (m : Type → Type := IO) where
  /-- Restore a vertical clearance with equality to the original source at the retained nonzero axis value. -/ vertical
    : (directory : System.FilePath) → (ambient : Rational.Box) → (x : Coordinate) →
    (safe : elimination.vertical.eval x ≠ 0) →
    m { value : Clearance.Box.Line.Basic.VerticalLineClearance p ambient x // value = source.vertical ambient x safe }
  /-- Restore a horizontal clearance with equality to the original source at the retained nonzero axis value. -/
    horizontal : (directory : System.FilePath) → (ambient : Rational.Box) → (y : Coordinate) →
    (safe : elimination.horizontal.eval y ≠ 0) →
    m { value : Clearance.Box.Line.Basic.HorizontalLineClearance p ambient y // value = source.horizontal ambient y safe
      }

constructive_injectivity ClearanceLoader

/-- The explicit quadratic formulas are inexpensive direct constructors. Generic separated-Sylvester consumers instead
use `separated` below. -/
@[expose] def ClearanceLoader.direct {p degreeBound} (elimination :
  Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p degreeBound)
    (source : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination) : ClearanceLoader elimination source m
      where
  vertical _ ambient x safe := pure ⟨source.vertical ambient x safe, rfl⟩
  horizontal _ ambient y safe := pure ⟨source.horizontal ambient y safe, rfl⟩

/-- Restore original axis clearances from checked separated-Sylvester columns.

Horizontal restoration uses the exact quarter-turned polynomial and its retained degree equation. -/
@[expose] def ClearanceLoader.separated (control : ClearanceCheckpoint.Control m)
    (p : GaussianPolynomial) (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    ClearanceLoader (Elimination.Axis.Separated.separatedAxisEliminationCertificate p nonzero positive)
      (.canonical (Elimination.Axis.Separated.separatedAxisEliminationCertificate p nonzero positive)) m where
  vertical directory ambient x safe := do
    let column ← ClearanceCheckpoint.load control directory p positive x
    let coprime := column.vertical nonzero safe
    let line := Clearance.Box.Line.Bezout.verticalOfCoprime p ambient x coprime.val
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("bound.json")))) (fractionData line.bound)
    return ⟨line, by dsimp only [line]; rw [coprime.property]; rfl⟩
  horizontal directory ambient y safe := do
    let rotated := Dense.Gaussian.Substitution.QuarterTurn.quarterTurn p
    have rotatedPositive : 0 < rotated.natDegree := by
      rw [Dense.Gaussian.Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]; exact positive
    let column ← ClearanceCheckpoint.load control directory rotated rotatedPositive y
    let coprime := Elimination.Axis.Separated.Replay.horizontal p nonzero positive y safe column
    let line := Clearance.Box.Line.Bezout.horizontalOfCoprime p ambient y coprime.val
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("bound.json")))) (fractionData line.bound)
    return ⟨line, by dsimp only [line]; rw [coprime.property]; rfl⟩

/-- Compute the two integer floors on the original proposal grid. -/
@[expose, noinline] def generateRounding (box : Rational.Box) (epsilon : Coordinate)
    (extraBits : Nat) (proposal : Gaussian) : Witness :=
  dbg_trace "ROOT_TRACE_ROUNDING_GENERATOR_FORCED"
  let spacing := Gaussian.Grid.Box.grid box epsilon extraBits
  ⟨Floor.floor (proposal.re / spacing),
    Floor.floor (proposal.im / spacing)⟩

/-- Compute the original exact Gaussian Newton update at the retained center. -/
@[expose, noinline] def generateNewton (polynomial : GaussianPolynomial) (center : Gaussian) : Gaussian :=
  dbg_trace "ROOT_TRACE_NEWTON_GENERATOR_FORCED"
  Data.Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter polynomial center)

/-- Used only by the short restart regression. The saved file has already been flushed and atomically renamed when the
child is killed. -/
@[expose] def afterWrite [MonadStateOf Counts m] (control : Control) : m Unit := do
  let counts ← Execution.counts
  if control.killAfterWrites == some (counts.generatedRounding + counts.generatedNewton) then
    (← IO.getStdout).flush
    let pid ← IO.Process.getPID
    discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
    throw (IO.userError "restart test kill unexpectedly returned")

/-- Load or atomically save a rounding witness and update the stage counters.

The trace driver separately checks its floor inequalities against the original grid and proposal. -/
@[expose] def loadRounding [MonadStateOf Counts m] (control : Control) (directory : System.FilePath) (index : Nat)
    (box : Rational.Box) (epsilon : Coordinate) (extraBits : Nat) (proposal : Gaussian) : m Witness :=
      do
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"proposal-{index}-rounding.json")))
  if ← path.pathExists then
    let raw : RawWitness ← loadJson path
    let result ← checked "saved rounding" (decode raw)
    Execution.update fun counts => { counts with reusedRounding := counts.reusedRounding + 1 }
    profile directory s!"REUSED rounding proposal {index}"
    return result
  if control.savedOnly then throw (IO.userError s!"completed rounding generator forbidden: {path}")
  let result := generateRounding box epsilon extraBits proposal
  saveJson path (encode result)
  Execution.update fun counts => { counts with generatedRounding := counts.generatedRounding + 1 }
  profile directory s!"SAVED rounding proposal {index}"
  afterWrite control
  return result

/-- Load or atomically save a Newton proposal and update the stage counters.

The trace driver separately checks the exact Newton identity before advancing. -/
@[expose] def loadNewton [MonadStateOf Counts m] (control : Control) (directory : System.FilePath) (index : Nat)
    (polynomial : GaussianPolynomial) (center : Gaussian) : m Gaussian := do
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"proposal-{index}-newton.json")))
  if ← path.pathExists then
    let raw : GaussianData ← loadJson path
    let result ← checked "saved Newton update" (decodeGaussian raw)
    Execution.update fun counts => { counts with reusedNewton := counts.reusedNewton + 1 }
    profile directory s!"REUSED Newton proposal {index}"
    return result
  if control.savedOnly then throw (IO.userError s!"completed Newton generator forbidden: {path}")
  let result := generateNewton polynomial center
  saveJson path (gaussianData result)
  Execution.update fun counts => { counts with generatedNewton := counts.generatedNewton + 1 }
  profile directory s!"SAVED Newton proposal {index}"
  afterWrite control
  return result

variable {p : GaussianPolynomial} {ambient : Purelib.Geometry.Rational.Box} {degreeBound : Nat}
  (elimination : Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
    degreeBound)
  (current : Purelib.RootIsolation.State.Raw.RawWindingState p ambient) (epsilon : Coordinate)
  (clearances : Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
  (initialProposal : Gaussian)
  (loader : ClearanceLoader elimination clearances m)

/-- Serialize an accepted proposal or an inconclusive exhausted or zero-derivative attempt. -/
@[expose] def finishedReport : Newton.Search.Trace.Finished elimination current epsilon clearances initialProposal →
  Json
  | .accepted value inspected _ _ _ => Json.mkObj
      [("kind", toJson "accepted"), ("inspected", toJson inspected),
       ("budget", toJson (6 : Nat)),
       ("box", toJson (RootStateCheckpoint.boxData value.state.box))]
  | .exhausted inspected _ _ _ => Json.mkObj
      [("kind", toJson "inconclusive: proposal budget exhausted; total fallback unresolved"),
       ("inspected", toJson inspected), ("budget", toJson (6 : Nat))]
  | .zeroDerivative center derivative inspected _ _ _ _ _ => Json.mkObj
      [("kind", toJson "inconclusive: zero derivative; total fallback unresolved"),
       ("inspected", toJson inspected), ("budget", toJson (6 : Nat)),
       ("center", toJson (gaussianData center)), ("derivative", toJson (gaussianData derivative))]

/-- Serialize the exact ordered numerical data of an actually checked search proposal. -/
@[expose] def attemptedReport : Newton.Search.Trace.Attempted current epsilon → Json
  | .accepted bits proposal center value => Json.mkObj
      [("kind", toJson "accepted"), ("bits", toJson bits), ("proposal", toJson (gaussianData proposal)),
       ("center", toJson (gaussianData center)), ("box", toJson (RootStateCheckpoint.boxData value.state.box))]
  | .stationary bits proposal center derivative => Json.mkObj
      [("kind", toJson "zero derivative"), ("bits", toJson bits), ("proposal", toJson (gaussianData proposal)),
       ("center", toJson (gaussianData center)), ("derivative", toJson (gaussianData derivative))]
  | .exhausted bits proposal center derivative => Json.mkObj
      [("kind", toJson "budget exhausted"), ("bits", toJson bits), ("proposal", toJson (gaussianData proposal)),
       ("center", toJson (gaussianData center)), ("derivative", toJson (gaussianData derivative))]
  | .rejected bits proposal center derivative next => Json.mkObj
      [("kind", toJson "rejected; continued"), ("bits", toJson bits), ("proposal", toJson (gaussianData proposal)),
       ("center", toJson (gaussianData center)), ("derivative", toJson (gaussianData derivative)),
       ("next", toJson (gaussianData next))]

/-- Return a checked proposal stage or save its exact violated condition before stopping. -/
@[expose] def checkIO {α : Type} (directory : System.FilePath) (index : Nat)
    (stage : String) (result : Except Invalid α) : IO α := do
  match result with
  | .ok value => return value
  | .error failure =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid.json")))) (Json.mkObj
        [("proposal", toJson index), ("stage", toJson stage), ("failure", invalidReport failure)])
      throw (IO.userError s!"invalid saved {stage} at proposal {index}; failed operands saved")

/-- Restore all four original line-clearance witnesses for a retained candidate band. -/
@[expose] def restoreLines (center : Gaussian) (pending : Newton.Search.Center.Replay.Pending elimination current
  epsilon center)
    (directory : System.FilePath) :
    m (Newton.Search.Center.Replay.Lines elimination current epsilon center clearances pending) := do
  let left ← loader.vertical ((Purelib.System.FilePath.join directory (System.FilePath.mk ("left")))) ambient
    pending.band.box.xLower (by
    rw [pending.band_eq]; exact Elimination.Axis.Band.selectedBand_left_nonzero elimination center pending.positive)
  let right ← loader.vertical ((Purelib.System.FilePath.join directory (System.FilePath.mk ("right")))) ambient
    pending.band.box.xUpper (by
    rw [pending.band_eq]; exact Elimination.Axis.Band.selectedBand_right_nonzero elimination center pending.positive)
  let bottom ← loader.horizontal ((Purelib.System.FilePath.join directory (System.FilePath.mk ("bottom")))) ambient
    pending.band.box.yLower (by
    rw [pending.band_eq]; exact Elimination.Axis.Band.selectedBand_bottom_nonzero elimination center pending.positive)
  let top ← loader.horizontal ((Purelib.System.FilePath.join directory (System.FilePath.mk ("top")))) ambient
    pending.band.box.yUpper (by
    rw [pending.band_eq]; exact Elimination.Axis.Band.selectedBand_top_nonzero elimination center pending.positive)
  return ⟨left.val, right.val, bottom.val, top.val,
    left.property, right.property, bottom.property, top.property⟩

/-- Recursion is bounded independently of disk contents. Checking a saved entry never invokes either proposal generator.
-/
@[expose] def finish [MonadStateOf Counts m] (control : Control) (directory : System.FilePath) :
    (fuel : Nat) → (pending : Newton.Search.Trace.Pending elimination current epsilon clearances initialProposal) →
      m (Newton.Search.Trace.Retained elimination current epsilon clearances initialProposal
        pending.remaining pending.extraBits pending.proposal)
  | 0, _ => throw (IO.userError "internal trace driver exhausted its six-step bound")
  | fuel + 1, pending => do
      if terminal : pending.remaining = 0 then
        have historyZero : Newton.Search.Trace.Prefix elimination current epsilon clearances
            initialProposal 0 pending.extraBits pending.proposal pending.inspected := by
          simpa only [terminal] using pending.history
        let exhausted : Newton.Search.Trace.Finished elimination current epsilon clearances initialProposal :=
          .exhausted pending.inspected (by have := pending.budget; omega) (by
            rw [pending.equation, terminal, Newton.Search.Iteration.search_zero])
            (.exhausted historyZero)
        return ⟨exhausted, [], by rw [terminal]; exact .exhausted⟩
      else do
        let witness ←
          loadRounding control directory pending.inspected current.box epsilon pending.extraBits pending.proposal
        let center ← checkIO directory pending.inspected "rounding"
          (Newton.Search.Replay.Input.checkRounded current.box epsilon pending.extraBits pending.proposal witness)
        let candidate : { result : Option (Refinement current epsilon) //
            result = Newton.Search.Center.Basic.checkCenter elimination current epsilon center.val clearances } ←
          match Newton.Search.Center.Replay.prepare elimination current epsilon center.val clearances with
          | .rejected _ equation => pure ⟨none, equation.symm⟩
          | .pending candidate => do
              let winding ← WindingCheckpoint.box ⟨control.savedOnly, pure ()⟩
                ((Purelib.System.FilePath.join directory
                    (System.FilePath.mk (s!"proposal-{pending.inspected}-winding"))))
                  p candidate.band.box
              let outcome ← if four : winding.val = 4 then do
                  profile directory s!"BEGIN checked original candidate {pending.inspected} clearance restoration"
                  let lines ← restoreLines elimination current epsilon clearances loader center.val candidate
                    ((Purelib.System.FilePath.join directory (System.FilePath.mk
                      (s!"proposal-{pending.inspected}-clearances"))))
                  profile directory s!"END checked original candidate {pending.inspected} clearance restoration"
                  pure (Newton.Search.Center.Replay.Pending.finish elimination current epsilon center.val
                    clearances candidate winding (fun _ => lines))
                else pure (Newton.Search.Center.Replay.Pending.finish elimination current epsilon center.val
                  clearances candidate winding (fun impossible => (four impossible).elim))
              match outcome with
              | .accepted value equation => pure ⟨some value, equation⟩
              | .rejected _ equation => pure ⟨none, equation⟩
        match count : pending.remaining with
        | 0 => return (False.elim (terminal count))
        | remaining + 1 => do
            have history : Newton.Search.Trace.Prefix elimination current epsilon clearances initialProposal
                (remaining + 1) pending.extraBits pending.proposal pending.inspected := by
              simpa only [count] using pending.history
            have unfoldSearch : Newton.Search.Iteration.search elimination current epsilon 6 0
                initialProposal clearances =
                (match Newton.Search.Center.Basic.checkCenter elimination current epsilon center.val clearances with
                | some accepted => some accepted
                | none => if Data.Gaussian.Basic.value
                    (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center.val) = 0 then none
                  else Newton.Search.Iteration.search elimination current epsilon remaining
                    (pending.extraBits + 2)
                    (Data.Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center.val))
                    clearances) := by
              rw [pending.equation, count]
              exact (Newton.Search.Iteration.search_succ elimination current epsilon remaining
                pending.extraBits pending.proposal clearances).trans
                (congrArg (fun point => match Newton.Search.Center.Basic.checkCenter
                    elimination current epsilon point clearances with
                  | some accepted => some accepted
                  | none => if Data.Gaussian.Basic.value
                      (Dense.Gaussian.Derivative.Evaluation.derivativeEval p point) = 0 then none
                    else Newton.Search.Iteration.search elimination current epsilon remaining (pending.extraBits + 2)
                      (Data.Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p point)) clearances)
                  center.property.symm)
            match restored : candidate.val with
            | some value =>
                have checked := candidate.property.symm.trans restored
                let result : Newton.Search.Trace.Finished elimination current epsilon clearances initialProposal :=
                  .accepted value (pending.inspected + 1) (by have := pending.budget; omega)
                    (by rw [unfoldSearch, checked]) (.accepted history center.val center.property value checked)
                saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("result.json"))))
                  (finishedReport elimination current epsilon clearances initialProposal result)
                return ⟨result, [.accepted pending.extraBits pending.proposal center.val value], by
                  rw [count]; exact .accepted center.property checked⟩
            | none =>
                have checked := candidate.property.symm.trans restored
                let derivative := Data.Gaussian.Basic.value
                  (Dense.Gaussian.Derivative.Evaluation.derivativeEval p center.val)
                if zero : derivative = 0 then
                  let result : Newton.Search.Trace.Finished elimination current epsilon clearances initialProposal :=
                    .zeroDerivative center.val derivative (pending.inspected + 1)
                      (by have := pending.budget; omega)
                      (Dense.Gaussian.Derivative.Evaluation.value_derivativeEval _ _) zero
                      (by rw [unfoldSearch, checked]; exact if_pos zero)
                      (.zeroDerivative history center.val center.property checked zero)
                  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("result.json"))))
                    (finishedReport elimination current epsilon clearances initialProposal result)
                  return ⟨result, [.stationary pending.extraBits pending.proposal center.val derivative], by
                    rw [count]; exact .stationary center.property checked rfl zero⟩
                else if exhausted : remaining = 0 then
                  let result : Newton.Search.Trace.Finished elimination current epsilon clearances initialProposal :=
                    .exhausted (pending.inspected + 1) (by have := pending.budget; omega) (by
                      rw [unfoldSearch, checked, if_neg zero, exhausted, Newton.Search.Iteration.search_zero])
                      (.exhausted (exhausted ▸ Newton.Search.Trace.Prefix.step history center.val _
                        center.property checked zero rfl))
                  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("result.json"))))
                    (finishedReport elimination current epsilon clearances initialProposal result)
                  return ⟨result, [.exhausted pending.extraBits pending.proposal center.val derivative], by
                    rw [count, exhausted]; exact .exhaustedAfter center.property checked rfl zero⟩
                else
                  let proposed ← loadNewton control directory pending.inspected p center.val
                  let next ← checkIO directory pending.inspected "Newton update"
                    (SquareRoot.Replay.CheckedDiameterReplay.checkNewton p center.val proposed derivative
                      (Dense.Gaussian.Derivative.Evaluation.value_derivativeEval _ _) zero)
                  let following : Newton.Search.Trace.Pending elimination current epsilon clearances initialProposal :=
                    ⟨remaining, pending.inspected + 1, by have := pending.budget; omega,
                      pending.extraBits + 2, next.val,
                      .step history center.val next.val center.property checked zero next.property, by
                        rw [unfoldSearch, checked, if_neg zero]
                        exact congrArg (fun point => Newton.Search.Iteration.search elimination current epsilon
                          remaining (pending.extraBits + 2) point clearances) next.property.symm⟩
                  let tail ← finish control directory fuel following
                  return ⟨tail.finished,
                    .rejected pending.extraBits pending.proposal center.val derivative next.val :: tail.steps, by
                      rw [count]
                      exact .rejected (by omega) center.property checked rfl zero next.property tail.execution⟩

/-- Exact request data remain independent of the generator binary. Ordinary midpoint attempts retain their v1 header; a
supplied starting proposal uses v2. -/
@[expose] def requestHeader (proposal : Option Gaussian) : Json :=
  Json.mkObj
    ([("format", toJson (if proposal.isSome then "ccl-checked-newton-trace-v2"
        else "ccl-checked-newton-trace-v1")),
      ("polynomial", toJson (p.coeffs.map gaussianData)),
      ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
      ("box", toJson (RootStateCheckpoint.boxData current.box)),
      ("epsilon", toJson (fractionData epsilon)), ("budget", toJson (6 : Nat))] ++
      match proposal with
      | none => []
      | some value => [("initialProposal", toJson (gaussianData value))])

/-- Bind the finite Newton trace to its exact saved request before replaying its original six-step search. -/
@[expose] def runWithHeader [MonadStateOf Counts m] (control : Control) (directory : System.FilePath) (header : Json) :
    m (Newton.Search.Trace.Retained elimination current epsilon clearances initialProposal 6 0 initialProposal) := do
  IO.FS.createDirAll directory
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("request.json")))
  if ← path.pathExists then
    let saved : Json ← loadJson path
    unless saved == header do
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request.json")))) (saved, header)
      throw (IO.userError "trace request differs from saved exact inputs; both requests retained")
  else
    if control.savedOnly then throw (IO.userError "missing trace request; generation forbidden")
    saveJson path header
  let retained ← finish elimination current epsilon clearances initialProposal loader control directory 7
    (Newton.Search.Trace.first elimination current epsilon clearances initialProposal)
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("retained.json")))) (Json.mkObj
    [("terminal", finishedReport elimination current epsilon clearances initialProposal retained.finished),
     ("steps", toJson (retained.steps.map (attemptedReport current epsilon)))])
  return retained

/-- Replay six candidates from a supplied checked warm-up result. The start is bound by the exact request header and
every following proposal is checked. -/
@[expose] def runFrom [MonadStateOf Counts m] (control : Control) (directory : System.FilePath) :
    m (Newton.Search.Trace.Retained elimination current epsilon clearances initialProposal 6 0 initialProposal) :=
  runWithHeader elimination current epsilon clearances initialProposal loader control directory
    (requestHeader current epsilon (some initialProposal))

/-- Ordinary refinement still starts at the same box midpoint and reads its unchanged v1 trace files. Both clients share
the generalized checker/driver. -/
@[expose] def run [MonadStateOf Counts m] (control : Control) (directory : System.FilePath) :
    m (Newton.Search.Trace.Finished elimination current epsilon clearances
      ⟨(current.box.xLower + current.box.xUpper) / 2,
        (current.box.yLower + current.box.yUpper) / 2⟩) := do
  let retained ← runWithHeader elimination current epsilon clearances
    ⟨(current.box.xLower + current.box.xUpper) / 2,
      (current.box.yLower + current.box.yUpper) / 2⟩ loader control directory
    (requestHeader current epsilon none)
  return retained.finished

end RootRefinementCheckpoint

/-! Restore the original strict-inset fallback from resumable winding chains. -/

namespace QuadraticFallbackCheckpoint

open IntegrationCheckpoint
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay
open Purelib.RootIsolation.SquareRoot.Replay.QuadraticSampleReplay (Coordinate Gaussian Box)

variable {parameter : Gaussian} {ambient : Box} (current :
  State parameter ambient)

set_option genInjectivity false in
/-- A retained strict-inset attempt with original input, winding and decision equations. -/
structure Attempt (expected : SquareRoot.Replay.QuadraticFallbackReplay.Inset current) where
  /-- The exact inset supplied to the replayed check. -/ input : SquareRoot.Replay.QuadraticFallbackReplay.Inset current
  /-- The retained inset equals the expected original input. -/ input_eq : input = expected
  /-- The checked quadrupled winding of the inset box. -/ winding : Int
  /-- The retained winding equals the original root-polynomial box winding. -/ winding_eq : winding =
    Winding.Box.Basic.quadrupledBoxWinding
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
      (SquareRoot.Replay.QuadraticFallbackReplay.insetBox (current := current) input)
  /-- The retained original strict-inset decision. -/ decision : SquareRoot.Replay.QuadraticFallbackReplay.InsetDecision
    current input
  /-- The decision is the original check using the retained winding witness. -/ decision_eq : decision =
    SquareRoot.Replay.QuadraticFallbackReplay.checkInset current input ⟨winding, winding_eq⟩

constructive_injectivity Attempt

/-- Transport the retained inset decision to its expected original input. -/
@[expose] def Attempt.checked {expected : SquareRoot.Replay.QuadraticFallbackReplay.Inset current} (attempt : Attempt
  current expected) : SquareRoot.Replay.QuadraticFallbackReplay.InsetDecision current expected :=
  attempt.input_eq ▸ attempt.decision

/-- An accepted inset retains the exact winding of its selected raw-state box. -/
theorem Attempt.selected_winding {expected : SquareRoot.Replay.QuadraticFallbackReplay.Inset current} (attempt : Attempt
  current expected)
    (inset : SquareRoot.Replay.QuadraticFallbackReplay.RawInset current) (found : (attempt.checked current).val = some
      inset) :
    attempt.winding = Winding.Box.Basic.quadrupledBoxWinding
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (SquareRoot.Replay.QuadraticFallbackReplay.rawState (current := current) inset).box := by
  cases attempt with
  | mk input equal winding windingEq decision decisionEq =>
      cases equal
      cases decisionEq
      exact SquareRoot.Replay.QuadraticFallbackReplay.checkInset_winding current expected ⟨winding, windingEq⟩ inset
        found

/-- Serialize the attempted inset box, retained winding and acceptance flag. -/
@[expose] def Attempt.report {expected : SquareRoot.Replay.QuadraticFallbackReplay.Inset current} (attempt : Attempt
  current expected) : Json :=
  Json.mkObj [("box", toJson (RootStateCheckpoint.boxData (SquareRoot.Replay.QuadraticFallbackReplay.insetBox (current
    := current) attempt.input))),
    ("winding", toJson attempt.winding),
    ("accepted", toJson attempt.decision.val.isSome)]

/-- Restore the original inset winding and retain its exact check result. -/
@[expose] def loadInset (control : WindingCheckpoint.Control) (directory : System.FilePath)
    (input : SquareRoot.Replay.QuadraticFallbackReplay.Inset current) : IO (Attempt current input) := do
  let winding ← WindingCheckpoint.box control directory
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
      (SquareRoot.Replay.QuadraticFallbackReplay.insetBox (current := current) input)
  let decision := SquareRoot.Replay.QuadraticFallbackReplay.checkInset current input winding
  return ⟨input, rfl, winding.val, winding.property, decision, rfl⟩

open Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay in
set_option genInjectivity false in
/-- The precise unresolved obligation in finite replay of the original quadratic fallback.

Retain the original subdivision depths, attempted insets and failed promotion rather than claiming global failure. -/
inductive Pending (epsilon : Coordinate) (positive : 0 < epsilon) where
  /-- The original raw state needs a nonzero subdivision depth not restored by this loader. -/ | initialSubdivision
    (depth : Nat)
      (depth_eq : depth = Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2))
      (unresolved : depth ≠ 0)
  /-- Both original inset checks missed, leaving the generic extractor unresolved. -/ | noInset (fixed : Attempt current
    (fixedInset current))
      (fixedMiss : (fixed.checked current).val = none)
      (narrow : Attempt current (protectedInset current))
      (narrowMiss : (narrow.checked current).val = none)
      (original : SquareRoot.Replay.QuadraticFallbackReplay.InsetAttempt current) (missing : original.val = none)
  /-- The selected original inset requires a nonzero unresolved subdivision depth. -/ | insetSubdivision (selected :
    SquareRoot.Replay.QuadraticFallbackReplay.SelectedInset current) (depth : Nat)
      (depth_eq : depth = Subdivision.Raw.Request.refinementDepth (SquareRoot.Replay.QuadraticFallbackReplay.rawState
        (current := current) selected.value) (epsilon ^ 2))
      (unresolved : depth ≠ 0)
  /-- Both subdivision depths are zero, but the original inset promotion returned no result. -/ | promotion (selected :
    SquareRoot.Replay.QuadraticFallbackReplay.SelectedInset current)
      (initialDepth : Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2) = 0)
      (insetDepth : Subdivision.Raw.Request.refinementDepth (SquareRoot.Replay.QuadraticFallbackReplay.rawState (current
        := current) selected.value) (epsilon ^ 2) = 0)
      (missed : SquareRoot.Replay.QuadraticFallbackReplay.subdivision current epsilon positive = none)

constructive_injectivity Pending

/-- Serialize the exact original fallback state and its remaining finite replay obligation. -/
@[expose] def Pending.report {epsilon : Coordinate} {positive : 0 < epsilon}
    (pending : Pending current epsilon positive) : Json :=
  let details := match pending with
    | .initialSubdivision depth _ _ =>
        [("reason", toJson "original raw subdivision needs a saved subdivision loader"),
         ("depth", toJson depth)]
    | .noInset fixed _ narrow _ _ _ =>
        [("reason", toJson "both original strict-inset checks missed; generic extractor remains unresolved"),
         ("fixed", fixed.report current), ("protected", narrow.report current)]
    | .insetSubdivision selected depth _ _ =>
        [("reason", toJson "selected original inset needs raw subdivision"),
         ("depth", toJson depth), ("inset", toJson (RootStateCheckpoint.boxData
           (SquareRoot.Replay.QuadraticFallbackReplay.rawState (current := current) selected.value).box)),
         ("winding", toJson selected.winding)]
    | .promotion selected _ _ _ =>
        [("reason", toJson "original inset promotion missed; generic extractor remains unresolved"),
         ("inset", toJson (RootStateCheckpoint.boxData (SquareRoot.Replay.QuadraticFallbackReplay.rawState (current :=
           current) selected.value).box)),
         ("winding", toJson selected.winding)]
  Json.mkObj ([("kind", toJson "inconclusive finite original-fallback replay"),
    ("state", toJson (RootStateCheckpoint.capture current)),
    ("epsilon", toJson (fractionData epsilon)), ("restoredSubdivisionBudget", toJson (0 : Nat))] ++ details)

/-- Check zero-depth inset promotion and return its original-result equation or retained unresolved obligation. -/
@[expose] def finish (epsilon : Coordinate) (positive : 0 < epsilon)
    (initialDepth : Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2) = 0)
    (selected : SquareRoot.Replay.QuadraticFallbackReplay.SelectedInset current) :
    Except (Pending current epsilon positive)
      { value : SquareRoot.Replay.QuadraticFallbackReplay.Fast current epsilon //
        SquareRoot.Replay.QuadraticFallbackReplay.subdivision current epsilon positive = some value } := by
  let depth := Subdivision.Raw.Request.refinementDepth (SquareRoot.Replay.QuadraticFallbackReplay.rawState (current :=
    current) selected.value) (epsilon ^ 2)
  if zero : depth = 0 then
    have accurate := SquareRoot.Replay.QuadraticFallbackReplay.zero_accurate
      (SquareRoot.Replay.QuadraticFallbackReplay.rawState (current := current) selected.value) epsilon positive zero
    let accepted := SquareRoot.Replay.QuadraticFallbackReplay.promote current epsilon selected.value accurate
      ⟨selected.winding, selected.winding_eq⟩
    have equal := (SquareRoot.Replay.QuadraticFallbackReplay.subdivision_zero current epsilon positive initialDepth
      selected.value selected.equation zero accurate).trans
      accepted.property.symm
    cases found : accepted.val with
    | none => exact .error (.promotion selected initialDepth zero (equal.trans found))
    | some value => exact .ok ⟨value, equal.trans found⟩
  else exact .error (.insetSubdivision selected depth rfl zero)

open Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay in
/-- Replay the original fixed and protected inset checks in order.

Only a checked original result is returned as success; nonzero subdivision, two misses or failed promotion retain typed
inconclusive evidence. -/
@[expose] def run (epsilon : Coordinate) (positive : 0 < epsilon)
    (control : WindingCheckpoint.Control) (directory : System.FilePath) :
    IO (Except (Pending current epsilon positive)
      { value : SquareRoot.Replay.QuadraticFallbackReplay.Fast current epsilon //
        SquareRoot.Replay.QuadraticFallbackReplay.subdivision current epsilon positive = some value }) := do
  let depth := Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2)
  if zero : depth = 0 then
    let fixed ← loadInset current control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("fixed"))))
      (fixedInset current)
    match found : (fixed.checked current).val with
    | some inset =>
        return finish current epsilon positive zero
          ⟨inset, SquareRoot.Replay.QuadraticFallbackReplay.firstInset current (fixed.checked current) inset found,
            fixed.winding, fixed.selected_winding current inset found⟩
    | none =>
        let narrow ← loadInset current control ((Purelib.System.FilePath.join directory (System.FilePath.mk
          ("protected")))) (protectedInset current)
        match next : (narrow.checked current).val with
        | some inset =>
            return finish current epsilon positive zero
              ⟨inset, (SquareRoot.Replay.QuadraticFallbackReplay.secondInset current (fixed.checked current) found
                (narrow.checked current)).trans next,
                narrow.winding, narrow.selected_winding current inset next⟩
        | none =>
            return .error (.noInset fixed found narrow next
              (SquareRoot.Replay.QuadraticFallbackReplay.missingInsets current (fixed.checked current) found
                (narrow.checked current) next) rfl)
  else return .error (.initialSubdivision depth rfl zero)

end QuadraticFallbackCheckpoint
