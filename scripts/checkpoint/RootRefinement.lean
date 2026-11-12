module

import Purelib.Data.ByteArray.UTF8

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
public import Purelib.Polynomial.Elimination.Axis.Replay
-- Prepared loaders expose their same retained original two-axis parent.
public import Purelib.Polynomial.Elimination.Axis.Preparation
import Purelib.Polynomial.Elimination.Axis.Separated
public import Purelib.Polynomial.Elimination.Axis.Separated.Replay
import Purelib.Polynomial.Elimination.Separated.Replay
import Purelib.Polynomial.Elimination.Separated.Quadratic
import Purelib.Polynomial.Elimination.Separated.Replay.Computation
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

open Purelib.Polynomial.Dense.Gaussian
open Purelib.Polynomial.Elimination

open Purelib.RootIsolation.SquareRoot.Replay
open Purelib.Polynomial.Elimination.Axis
open Purelib.Polynomial.Clearance.Box.Line
open Purelib.Polynomial.Elimination.Separated.Replay
open Purelib.Polynomial.Elimination.Separated.Preparation renaming Prepared -> SylvesterPreparation
open Purelib.Polynomial.Elimination.Axis.Preparation renaming Prepared -> AxisPreparation

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

open Purelib.Polynomial.Dense.Rational

open Purelib.Polynomial.Dense.Rational.Division.Replay

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
@[expose] def polynomialData (p : Dense) : List FractionData := p.coeffs.map
  fractionData

/-- Decode ordered rational coefficients, retaining exact supplied operands where their parsed fields agree.

The expected coefficients supply their original heads and tails. Missing
expected entries use the original scalar decoder, and remaining expected
entries leave the decoded source length and first scalar failure unchanged. -/
@[expose] def decodePolynomial (data : List FractionData) (expected : Option Dense := none) :
    Except InvalidData Dense := do
  let rec decodeExpected : List FractionData → List Fraction.Rational → List Fraction.Rational →
      Except InvalidData (List Fraction.Rational)
    | [], _, accumulator => .ok accumulator.reverse
    | first :: tail, retained, accumulator => do
        let value ← decodeFraction first retained.head?
        decodeExpected tail retained.tail (value :: accumulator)
  let coefficients ← match expected with
    | none => decodeFractions data
    | some value => decodeExpected data value.coeffs []
  return ⟨coefficients⟩

/-- Supplied original coefficients preserve every ordered decode result and scalar failure.

The accumulator follows the original left-to-right monadic traversal for
arbitrary source and expected lengths, including an early scalar failure. -/
theorem decodePolynomial_expected_eq_default (data : List FractionData) (expected : Option Dense) :
    decodePolynomial data expected = decodePolynomial data := by
  have equal : ∀ (values : List FractionData) (retained accumulator : List Fraction.Rational),
      decodePolynomial.decodeExpected values retained accumulator =
        List.mapM.loop (fun value => decodeFraction value) values accumulator := by
    intro values
    induction values with
    | nil => intro retained accumulator; rfl
    | cons first tail ih =>
        intro retained accumulator
        unfold decodePolynomial.decodeExpected List.mapM.loop
        have firstEqual := decodeFraction_expected_eq_default first retained.head?
        rewrite [firstEqual]
        cases decoded : decodeFraction first with
        | error failure => rfl
        | ok value => exact ih retained.tail (value :: accumulator)
  unfold decodePolynomial
  cases expected with
  | none => rfl
  | some value =>
      dsimp only
      rewrite [equal data value.coeffs []]
      rfl

/-- Serialize both original division operands and the saved quotient/remainder witness. -/
@[expose] def encode (p q : Dense) (witness :
  Witness) :
  RawStep :=
  ⟨polynomialData p, polynomialData q, polynomialData witness.quotient,
    polynomialData witness.remainder⟩

set_option genInjectivity false in
/-- A scalar, operand-identity or division-certificate failure for the original chain step. -/
inductive Failure (p q : Dense) where
  /-- An invalid exact scalar encoding. -/ | field (failure : InvalidData)
  /-- A decoded dividend certified different from the original operand. -/ | dividend (saved :
    Dense) (failed : saved ≠ p)
  /-- A decoded divisor certified different from the original operand. -/ | divisor (saved :
    Dense) (failed : saved ≠ q)
  /-- A proposed division witness failing normalization, degree or exact identity checks. -/ | witness (saved :
    Witness) (failure : Division.Replay.Invalid p q saved)

constructive_injectivity Failure

/-- Check a saved division against its exact original operands and nonzero divisor.

Decode all coefficients, require operand equality and verify the polynomial identity and strict remainder-degree bound.
An empty quotient supplies the original normalized dividend as an expected
coefficient cache. Each scalar still checks its parsed coordinates before reuse.
-/
@[expose] def decode (p q : Dense) (nonzero : q.isZero = false) (raw : RawStep) :
    Except (Failure p q) (Step p q) := do
  let savedP ← (decodePolynomial raw.dividend (some p)).mapError .field
  let savedQ ← (decodePolynomial raw.divisor (some q)).mapError .field
  if sameP : savedP = p then
    if sameQ : savedQ = q then
      let quotient ← (decodePolynomial raw.quotient).mapError .field
      let expectedRemainder := if raw.quotient.isEmpty then some p.normalize else none
      let remainder ← (decodePolynomial raw.remainder expectedRemainder).mapError .field
      let witness : Witness := ⟨quotient, remainder⟩
      (Division.Replay.check p q nonzero witness).mapError (.witness witness)
    else .error (.divisor savedQ sameQ)
  else .error (.dividend savedP sameP)

/-- Serialize the failed scalar, operand comparison or exact division condition. -/
@[expose] def Failure.report {p q : Dense} : Failure p q → Json
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
  /-- An optional retained operation hashing the exact original UTF8 input bytes. -/
  inputDigest : Option (String → IO String) := none

constructive_injectivity Control

/-- Generate one original exact polynomial-division witness, emitting the generation diagnostic. -/
@[expose, noinline] def generateStep (p q : Dense) :
  Step p q
  :=
  dbg_trace "WINDING_DIVISION_GENERATOR_FORCED"
  Division.Replay.generate p q

/-- Restore a checked division witness or atomically save a newly generated one.

Saved-only replay retains the next exact operands when a file is missing; invalid saved data retains the failed
condition. -/
@[expose] def loadStep (control : Control m) (directory : System.FilePath) (index : Nat)
    (p q : Dense) (nonzero : q.isZero = false) : m
      (Step p q)
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

set_option genInjectivity false in
/-- One original edge-input manifest shared by its ordered winding divisions.

The original starting operands, recursion fuel and first division index are
retained separately from the format protocol. Their decoded identities are
checked once before any compact witness refers to this manifest.
-/
structure RawInput where
  /-- The exact shared-input format protocol. -/
  protocol : String
  /-- The original recursion fuel, independent of saved file counts. -/
  fuel : Nat
  /-- The original first division index. -/
  firstIndex : Nat
  /-- The original initial dividend coefficients in ascending order. -/
  dividend : List FractionData
  /-- The original initial divisor coefficients in ascending order. -/
  divisor : List FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawInput

set_option genInjectivity false in
/-- Checked identities of a shared manifest with its original edge input. -/
structure InputCertificate (p q : Dense) (fuel firstIndex : Nat) (raw : RawInput) : Type where
  /-- The manifest uses the exact compact-input protocol. -/
  protocol : raw.protocol = "original-winding-input-v1"
  /-- The manifest retains the original recursion fuel. -/
  fuel_eq : raw.fuel = fuel
  /-- The manifest retains the original first index. -/
  firstIndex_eq : raw.firstIndex = firstIndex
  /-- Its original dividend encoding decodes to that exact supplied operand. -/
  dividend : decodePolynomial raw.dividend = .ok p
  /-- Its original divisor encoding decodes to that exact supplied operand. -/
  divisor : decodePolynomial raw.divisor = .ok q

constructive_injectivity InputCertificate

set_option genInjectivity false in
/-- A protocol, request or exact-operand failure of a retained shared input. -/
inductive InputFailure (p q : Dense) (fuel firstIndex : Nat) (raw : RawInput) where
  /-- The retained format protocol is different. -/
  | protocol (failed : raw.protocol ≠ "original-winding-input-v1")
  /-- The retained recursion fuel is different. -/
  | fuel (failed : raw.fuel ≠ fuel)
  /-- The retained original first index is different. -/
  | firstIndex (failed : raw.firstIndex ≠ firstIndex)
  /-- A scalar encoding or original operand identity failed. -/
  | operand (failure : Failure p q)

constructive_injectivity InputFailure

/-- Check the complete shared input against the original edge operands and request.

The original protocol, fuel and first-index checks precede ordered operand
decoding. Retained decoder results keep exact links to the original decoder
equations used by the returned input certificate. -/
@[expose] def checkInput (p q : Dense) (fuel firstIndex : Nat) (raw : RawInput) :
    Except (InputFailure p q fuel firstIndex raw) (InputCertificate p q fuel firstIndex raw) := do
  if protocol : raw.protocol = "original-winding-input-v1" then
    if fuelEq : raw.fuel = fuel then
      if indexEq : raw.firstIndex = firstIndex then
        let checkOperands
            (dividendResult : {value : Except InvalidData Dense // value = decodePolynomial raw.dividend})
            (divisor : Unit → {value : Except InvalidData Dense // value = decodePolynomial raw.divisor}) :
            Except (InputFailure p q fuel firstIndex raw) (InputCertificate p q fuel firstIndex raw) :=
          match dividend : dividendResult.val with
          | .error failure => .error (.operand (.field failure))
          | .ok savedP =>
              if sameP : savedP = p then
                let divisorResult := divisor ()
                match decoded : divisorResult.val with
                | .error failure => .error (.operand (.field failure))
                | .ok savedQ =>
                    if sameQ : savedQ = q then
                      .ok ⟨protocol, fuelEq, indexEq,
                        dividendResult.property.symm.trans (dividend.trans (congrArg Except.ok sameP)),
                        divisorResult.property.symm.trans (decoded.trans (congrArg Except.ok sameQ))⟩
                    else .error (.operand (.divisor savedQ sameQ))
              else .error (.operand (.dividend savedP sameP))
        checkOperands
          ⟨decodePolynomial raw.dividend (some p), decodePolynomial_expected_eq_default raw.dividend (some p)⟩
          (fun _ => ⟨decodePolynomial raw.divisor (some q),
            decodePolynomial_expected_eq_default raw.divisor (some q)⟩)
      else .error (.firstIndex indexEq)
    else .error (.fuel fuelEq)
  else .error (.protocol protocol)

/-- Retain the failed shared-input condition with its exact expected request. -/
@[expose] def InputFailure.report {p q : Dense} {fuel firstIndex : Nat} {raw : RawInput} :
    InputFailure p q fuel firstIndex raw → Json
  | .protocol _ => Json.mkObj [("kind", toJson "winding input protocol differs"), ("saved", toJson raw)]
  | .fuel _ => Json.mkObj [("kind", toJson "original winding fuel differs"),
      ("expectedFuel", toJson fuel), ("saved", toJson raw)]
  | .firstIndex _ => Json.mkObj [("kind", toJson "original winding first index differs"),
      ("expectedIndex", toJson firstIndex), ("saved", toJson raw)]
  | .operand failure => Json.mkObj [("kind", toJson "original winding input operands differ"),
      ("failure", failure.report), ("saved", toJson raw)]

set_option genInjectivity false in
/-- Actual retained manifest bytes and fingerprint, with checked original input identities.

The byte fingerprint identifies the shared file referenced by compact witnesses.
It supplies no executable or historical producer provenance. Mathematical
ownership is carried separately by the original-operand certificate.
-/
structure InputManifest (p q : Dense) (fuel firstIndex : Nat) where
  /-- The actual decoded shared record. -/
  raw : RawInput
  /-- The original operands and request checked against that record. -/
  valid : InputCertificate p q fuel firstIndex raw
  /-- The actual retained file bytes read as UTF8 text. -/
  bytes : String
  /-- The SHA256 of the retained shared file. -/
  sha256 : String

constructive_injectivity InputManifest

/-- Hash one exact retained input through a supplied operation or the original subprocess.

The optional operation receives the same complete UTF8 text. Omitting it
retains the original command, output checks and failure diagnostics.
-/
def inputDigest (bytes : String) (retained : Option (String → IO String) := none) : IO String :=
  match retained with
  | some digest => digest bytes
  | none => do
    let result ← Purelib.System.IO.Process.output { cmd := "sha256sum", args := #["-"] } (some bytes)
    if result.exitCode = 0 then
      let digest := (Data.String.splitOn result.stdout " ").head!
      if Data.String.length digest = 64 then return digest
      else throw (IO.userError "invalid shared winding input fingerprint output")
    else throw (IO.userError s!"shared winding input fingerprint failed: {result.stderr}")

/-- Request SHA256 of the exact retained bytes from the existing supervising process.

The length-framed stdout request carries the actual UTF8 payload. The same
retained stdin stream supplies one complete lowercase hexadecimal reply; EOF
or a malformed reply fails without substituting a saved digest.
-/
def streamedInputDigest (bytes : String) : IO String := do
  let output ← IO.getStdout
  output.putStr s!"CCL_WINDING_SHA256_V1 {bytes.utf8ByteSize}\n"
  output.putStr bytes
  output.flush
  let reply ← (← IO.getStdin).getLine
  let digest := (Data.String.splitOn reply "\n").head!
  let hexadecimal := match Data.ByteArray.UTF8.decode? digest.toByteArray with
    | none => false
    | some characters => characters.val.all fun value =>
        ('0' ≤ value && value ≤ '9') || ('a' ≤ value && value ≤ 'f')
  if Data.String.length digest == 64 && reply == digest ++ "\n" && hexadecimal then return digest
  else throw (IO.userError "invalid shared winding input fingerprint output")

/-- Load the actual shared bytes and check their original edge-input ownership. -/
def readInput (directory : System.FilePath) (p q : Dense) (fuel firstIndex : Nat)
    (retained : Option (String → IO String) := none) :
    m (InputManifest p q fuel firstIndex) := do
  let path := Purelib.System.FilePath.join directory "input.json"
  let bytes ← Purelib.System.IO.FS.readFile path
  let raw : RawInput ← parseJson path.toString bytes
  match checkInput p q fuel firstIndex raw with
  | .error failure =>
      saveJson (Purelib.System.FilePath.join directory "invalid-input.json") failure.report
      throw (IO.userError "invalid shared winding input; violated condition and original operands retained")
  | .ok valid =>
      let digest ← inputDigest bytes retained
      return ⟨raw, valid, bytes, digest⟩

/-- Reuse one checked shared manifest, or atomically create it at the first newly saved witness.

A manifest required by an existing compact artifact is never regenerated.
Saved-only replay retains the exact missing request. Existing legacy-only
chains need no new manifest and remain independently checked.
-/
def retainInput (control : Control m) (directory : System.FilePath) (p q : Dense)
    (fuel firstIndex : Nat) (cached : Option (InputManifest p q fuel firstIndex))
    (requireSaved : Bool) : m (InputManifest p q fuel firstIndex) := do
  if let some manifest := cached then return manifest
  let path := Purelib.System.FilePath.join directory "input.json"
  if ← path.pathExists then
    return ← readInput directory p q fuel firstIndex control.inputDigest
  if control.savedOnly || requireSaved then
    saveJson (Purelib.System.FilePath.join directory "missing-input.json") (Json.mkObj
      [("kind", toJson "missing original shared winding input; generation forbidden"),
        ("fuel", toJson fuel), ("firstIndex", toJson firstIndex),
        ("dividend", toJson (polynomialData p)), ("divisor", toJson (polynomialData q))])
    throw (IO.userError "missing original shared winding input; exact request retained")
  let raw : RawInput := ⟨"original-winding-input-v1", fuel, firstIndex, polynomialData p, polynomialData q⟩
  saveJson path raw
  readInput directory p q fuel firstIndex control.inputDigest

set_option genInjectivity false in
/-- Compact original division witness referring to one retained shared edge input.

Only the ordered quotient and remainder coefficients are repeated. The manifest
fingerprint and actual original division index identify the checked input
chain; the original current operands still index the division verifier.
-/
structure RawWitness where
  /-- The exact compact-witness format protocol. -/
  protocol : String
  /-- The fingerprint of the actual checked original edge-input manifest. -/
  inputSha256 : String
  /-- The actual original division index. -/
  index : Nat
  /-- The exact proposed quotient coefficients. -/
  quotient : List FractionData
  /-- The exact proposed remainder coefficients. -/
  remainder : List FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawWitness

set_option genInjectivity false in
/-- Exact compact protocol, reference, index or mathematical division failure. -/
inductive WitnessFailure (p q : Dense) (sha256 : String) (index : Nat) (raw : RawWitness) where
  /-- The retained witness protocol is different. -/
  | protocol (failed : raw.protocol ≠ "original-winding-division-v1")
  /-- The retained shared-input fingerprint is different. -/
  | input (failed : raw.inputSha256 ≠ sha256)
  /-- The retained original division index is different. -/
  | index (failed : raw.index ≠ index)
  /-- A scalar encoding or original mathematical division check failed. -/
  | division (failure : Failure p q)

constructive_injectivity WitnessFailure

/-- Check a compact witness against its shared reference and exact original current operands.

The original division verifier checks normalized remainder, strict degree
decrease and the complete polynomial identity. No supplied file count or
fingerprint can replace those mathematical checks or extend recursion fuel.
For an empty quotient, matching parsed remainder coordinates reuse the original
normalized dividend through the same complete-result decoder law.
-/
@[expose] def checkWitness (p q : Dense) (nonzero : q.isZero = false) (sha256 : String) (index : Nat)
    (raw : RawWitness) : Except (WitnessFailure p q sha256 index raw) (Division.Replay.Step p q) := do
  if protocol : raw.protocol = "original-winding-division-v1" then
    if input : raw.inputSha256 = sha256 then
      if indexEq : raw.index = index then
        let quotient ← (decodePolynomial raw.quotient).mapError (fun failure => .division (.field failure))
        let expectedRemainder := if raw.quotient.isEmpty then some p.normalize else none
        let remainder ← (decodePolynomial raw.remainder expectedRemainder).mapError
          (fun failure => .division (.field failure))
        let witness : Division.Replay.Witness := ⟨quotient, remainder⟩
        (Division.Replay.check p q nonzero witness).mapError
          (fun failure => .division (.witness witness failure))
      else .error (.index indexEq)
    else .error (.input input)
  else .error (.protocol protocol)

/-- Retain the exact compact condition and attempted quotient/remainder on failure. -/
@[expose] def WitnessFailure.report {p q : Dense} {sha256 : String} {index : Nat} {raw : RawWitness} :
    WitnessFailure p q sha256 index raw → Json
  | .protocol _ => Json.mkObj [("kind", toJson "compact winding witness protocol differs"), ("saved", toJson raw)]
  | .input _ => Json.mkObj [("kind", toJson "compact winding input fingerprint differs"),
      ("expectedInput", toJson sha256), ("saved", toJson raw)]
  | .index _ => Json.mkObj [("kind", toJson "original winding division index differs"),
      ("expectedIndex", toJson index), ("saved", toJson raw)]
  | .division failure => Json.mkObj [("kind", toJson "original winding division failed"),
      ("failure", failure.report), ("saved", toJson raw)]

/-- Read an existing compact witness, rejecting its actual reference or original division failure. -/
def readWitness (directory : System.FilePath) (index : Nat) (p q : Dense) (nonzero : q.isZero = false)
    (sha256 : String) : m (Division.Replay.Step p q) := do
  let raw : RawWitness ← loadJson (Purelib.System.FilePath.join directory s!"witness-{index}.json")
  match checkWitness p q nonzero sha256 index raw with
  | .ok step =>
      profile directory s!"REUSED compact winding division {index}"
      return step
  | .error failure =>
      saveJson (Purelib.System.FilePath.join directory "invalid-witness.json") failure.report
      throw (IO.userError s!"invalid compact winding division {index}; exact failure retained")

/-- Restore either original legacy or compact witnesses, preserving every existing artifact's checks.

Both existing forms are checked if both are present. A corrupt existing form
is rejected rather than replaced. A new witness follows the same original
generator and is atomically saved before the existing after-save hook runs.
The returned cache retains the actual shared input for the next original step.
-/
def loadRetainedStep (control : Control m) (directory : System.FilePath)
    (initialP initialQ : Dense) (initialFuel firstIndex : Nat)
    (cached : Option (InputManifest initialP initialQ initialFuel firstIndex))
    (index : Nat) (p q : Dense) (nonzero : q.isZero = false) :
    m (Division.Replay.Step p q ×
      Option (InputManifest initialP initialQ initialFuel firstIndex)) := do
  let legacy := Purelib.System.FilePath.join directory s!"division-{index}.json"
  let compact := Purelib.System.FilePath.join directory s!"witness-{index}.json"
  if ← legacy.pathExists then
    let step ← loadStep control directory index p q nonzero
    if ← compact.pathExists then
      let manifest ← retainInput control directory initialP initialQ initialFuel firstIndex cached true
      let _ ← readWitness directory index p q nonzero manifest.sha256
      return (step, some manifest)
    return (step, cached)
  if ← compact.pathExists then
    let manifest ← retainInput control directory initialP initialQ initialFuel firstIndex cached true
    let step ← readWitness directory index p q nonzero manifest.sha256
    return (step, some manifest)
  if control.savedOnly then
    let step ← loadStep control directory index p q nonzero
    return (step, cached)
  let manifest ← retainInput control directory initialP initialQ initialFuel firstIndex cached false
  let step := generateStep p q
  let raw : RawWitness := ⟨"original-winding-division-v1", manifest.sha256, index,
    polynomialData step.witness.quotient, polynomialData step.witness.remainder⟩
  saveJson compact raw
  profile directory s!"SAVED compact winding division {index}"
  control.afterSave
  return (step, some manifest)

/-- Restore the same ordered original chain with one retained shared input manifest. -/
def chainRetained (control : Control m) (directory : System.FilePath)
    (initialP initialQ : Dense) (initialFuel firstIndex : Nat)
    (cached : Option (InputManifest initialP initialQ initialFuel firstIndex)) :
    (fuel index : Nat) → (p q : Dense) → q.degreeCount ≤ fuel →
      m { values : List Dense // values = SignedRemainder.Basic.Sturm.signedRemainderChain p q }
  | 0, _, p, q, bound => do
      have zero := Dense.Basic.DensePolynomial.isZero_true_of_degreeCount_eq_zero (show q.degreeCount = 0 by omega)
      return ⟨[p], (SignedRemainder.Replay.terminal p q zero).symm⟩
  | fuel + 1, index, p, q, bound => do
      if zero : q.isZero = true then return ⟨[p], (SignedRemainder.Replay.terminal p q zero).symm⟩
      else
        have nonzero : q.isZero = false := Bool.eq_false_iff.mpr zero
        let restored ← loadRetainedStep control directory initialP initialQ initialFuel firstIndex
          cached index p q nonzero
        let step := restored.1
        let tail ← chainRetained control directory initialP initialQ initialFuel firstIndex restored.2
          fuel (index + 1)
          q (-step.witness.remainder) (by have := step.small nonzero; omega)
        return ⟨p :: tail.val, step.prepend nonzero tail.val tail.property⟩

/-- Restore the original signed-remainder chain from compatible legacy and compact certificates.

The original fuel and first index are retained in one checked edge-input
manifest. Every step still consumes its original current operands and the
original degree-decrease certificate. Existing legacy artifacts remain usable;
existing malformed manifests or witnesses are rejected without regeneration.
-/
@[expose] def chain (control : Control m) (directory : System.FilePath)
    (fuel index : Nat) (p q : Dense.Rational.Basic.CoordinatePolynomial) (bound : q.degreeCount ≤ fuel) :
    m { values : List Dense.Rational.Basic.CoordinatePolynomial // values =
      SignedRemainder.Basic.Sturm.signedRemainderChain p q } := do
  let cached ←
    if ← (Purelib.System.FilePath.join directory "input.json").pathExists then
      pure (some (← readInput directory p q fuel index control.inputDigest))
    else pure none
  chainRetained control directory p q fuel index cached fuel index p q bound

/-- Reconstruct the original doubled edge winding from its checked signed-remainder chain. -/
@[expose] def edge (control : Control m) (directory : System.FilePath) (edge :
  Dense.Rational.Pair.Path.Basic.PolynomialEdge) :
    m { value : Int // value = edge.doubledWinding } := do
  IO.FS.createDirAll directory
  let values ← chain control directory edge.realPart.degreeCount 0 edge.imagPart edge.realPart le_rfl
  return ⟨(SignedRemainder.Variation.Sturm.endpointVariation2 values.val edge.start : Int) -
      SignedRemainder.Variation.Sturm.endpointVariation2 values.val edge.stop, by
    rw [values.property]; rfl⟩

/-- Reconstruct the original quadrupled box winding from four ordered checked edge chains.

Save the exact polynomial, box and winding readback, with an equation to the original winding operation. -/
@[expose] def box (control : Control m) (directory : System.FilePath)
    (p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial) (box : Rational.Box) :
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
  /-- Permit the checked Euclidean proposal for non-binomial cubic coefficients. -/ generalCubic : Bool := false

constructive_injectivity Control

/-- Serialize a checked separated-Sylvester column with its original polynomial and parameter. -/
@[expose] def encode {p positive parameter} (column : Column p positive parameter) :
  RawColumn :=
  ⟨p.coeffs.map gaussianData, fractionData parameter,
    (List.ofFn fun index => column.values index).map gaussianData⟩

set_option genInjectivity false in
/-- A scalar, polynomial-identity, dimension or matrix-equation failure for a saved column. -/
inductive Failure (p : GaussianPolynomial) (positive : 0 <
  p.natDegree) (parameter
  : Rational) where
  /-- A failed scalar decode or exact axis-parameter comparison. -/ | field (failure : InvalidData)
  /-- A decoded polynomial certified different from the original input. -/ | polynomial (saved :
    GaussianPolynomial) (failed : saved ≠ p)
  /-- A saved column length different from twice the polynomial degree. -/ | size (values : List
    Gaussian) (failed : values.length ≠ p.natDegree + p.natDegree)
  /-- A finite vector failing the original evaluated Sylvester equation. -/ | equation (values : Vector
    Gaussian (p.natDegree + p.natDegree))
      (failure : Invalid p positive parameter values)

constructive_injectivity Failure

/-- Check a saved column against the original polynomial, parameter and matrix equation.

Only an exactly sized vector satisfying that equation becomes a retained clearance certificate. -/
@[expose] def decode (p : GaussianPolynomial) (positive : 0 <
  p.natDegree)
  (parameter : Rational)
    (raw : RawColumn) : Except (Failure p positive parameter) (Column p positive parameter)
      := do
  let coefficients ← (raw.polynomial.mapM decodeGaussian).mapError .field
  let saved : GaussianPolynomial := ⟨coefficients⟩
  if same : saved = p then
    let savedParameter ← (decodeFraction raw.parameter (some parameter)).mapError .field
    if sameParameter : savedParameter = parameter then
      let values ← (decodeGaussians raw.values).mapError .field
      if size : values.length = p.natDegree + p.natDegree then
        let vector := Data.Vector.Basic.vectorOfFn fun index : Fin (p.natDegree + p.natDegree) =>
          values[index.val]'(by have := index.isLt; omega)
        (Separated.Replay.check p positive parameter vector).mapError (.equation vector)
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
@[expose, noinline] def generate (p : GaussianPolynomial)
  (positive : 0 <
  p.natDegree) (parameter : Rational) :=
  dbg_trace "CLEARANCE_COLUMN_GENERATOR_FORCED"
  Separated.Replay.propose p positive parameter

/-- Retain checked direct column attempts and expose their actual producer invocation. -/
@[expose, noinline] def generateDirect (p : GaussianPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (generalCubic : Bool := false) :=
  dbg_trace "DIRECT_COLUMN_GENERATOR_FORCED"
  Separated.Replay.Computation.compute p positive parameter generalCubic

/-- Restore a verified column or run one supplied checked producer after the absence policy.

The original format, row-equation verifier, rejection and saved-only diagnostics
are shared. A fresh successful producer retains its actual save description;
the atomic save precedes the original after-save action exactly once. -/
@[expose] def loadUsing (control : Control m) (directory : System.FilePath)
    (p : GaussianPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (produce : Unit → m (Column p positive parameter × String)) :
    m (Column p positive parameter) := do
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
  let generated ← produce ()
  saveJson path (encode generated.1)
  profile directory generated.2
  control.afterSave
  return generated.1

/-- Restore the original direct proposals and Action fallback through the shared column loader.

The original producer order, retained rejections and complete saved certificate
remain unchanged. A successful direct proposal returns from its producer action
before the fallback; the shared loader then performs its one save and callback. -/
@[expose] def load (control : Control m) (directory : System.FilePath)
    (p : GaussianPolynomial) (positive : 0 < p.natDegree) (parameter : Rational) :
    m (Column p positive parameter) :=
  loadUsing control directory p positive parameter fun _ => do
    match generateDirect p positive parameter control.generalCubic with
    | .quadratic _ result _ =>
        return (result, "SAVED original clearance column from checked quadratic proposal")
    | .cubic _ result _ =>
        return (result, "SAVED original clearance column from checked cubic proposal")
    | .fallback quadratic cubic =>
        match quadratic with
        | .rejected _ values _ failure =>
            saveJson (Purelib.System.FilePath.join directory "rejected-quadratic.json") (Json.mkObj
              [("polynomial", toJson (p.coeffs.map gaussianData)), ("parameter", toJson (fractionData parameter)),
                ("failure", Failure.report (.equation values failure))])
            profile directory "FALLBACK rejected quadratic proposal; original Action follows"
        | _ => pure ()
        match cubic with
        | .rejected values _ failure =>
            saveJson (Purelib.System.FilePath.join directory "rejected-cubic.json") (Json.mkObj
              [("polynomial", toJson (p.coeffs.map gaussianData)), ("parameter", toJson (fractionData parameter)),
                ("failure", Failure.report (.equation values failure))])
            profile directory "FALLBACK rejected cubic proposal; original Action follows"
        | _ => pure ()
    let values := generate p positive parameter
    match Separated.Replay.check p positive parameter values with
    | .error failure =>
        saveJson (Purelib.System.FilePath.join directory "invalid-generated.json")
          (Failure.report (.equation values failure))
        throw (IO.userError "finite clearance-column proposal failed its equation; this is not input invalidity")
    | .ok result => return (result, "SAVED original clearance column")

/-- Produce the exact prepared inverse's unit column while retaining the generator boundary. -/
@[expose, noinline] def generatePrepared (p : GaussianPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (prepared : SylvesterPreparation p)
    (safe : prepared.eliminant.eval parameter ≠ 0) :=
  dbg_trace "PREPARED_COLUMN_GENERATOR_FORCED"
  (Separated.Replay.Column.ofPrepared (positive := positive) (parameter := parameter)
    prepared (prepared.scalar_ne_zero parameter safe)).values

/-- Restore one original-format column using its same retained prepared inverse on a fresh request.

Existing data is checked against the original matrix and parameter first.
Only an absent permitted request evaluates the prepared column; its complete
unit equation is rechecked before the shared atomic save and after-save hook. -/
@[expose] def loadFromPrepared (control : Control m) (directory : System.FilePath)
    (p : GaussianPolynomial) (positive : 0 < p.natDegree) (parameter : Rational)
    (prepared : SylvesterPreparation p) (safe : prepared.eliminant.eval parameter ≠ 0) :
    m (Column p positive parameter) :=
  loadUsing control directory p positive parameter fun _ => do
    let values := generatePrepared p positive parameter prepared safe
    match Separated.Replay.check p positive parameter values with
    | .error failure =>
        saveJson (Purelib.System.FilePath.join directory "invalid-generated.json")
          (Failure.report (.equation values failure))
        throw (IO.userError "finite prepared-column proposal failed its equation; this is not input invalidity")
    | .ok result => return (result, "SAVED original clearance column from retained prepared inverse")

end ClearanceCheckpoint

namespace RootRefinementCheckpoint

open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)

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
@[expose] def encode (witness : Witness) : RawWitness :=
  ⟨toString witness.realFloor, toString witness.imaginaryFloor⟩

/-- Decode the two signed grid-floor integers, retaining invalid syntax. -/
@[expose] def decode (raw : RawWitness) : Except InvalidData Witness := do
  let some real := (Data.String.toInt? raw.realFloor)
    | .error (.syntax s!"invalid real floor {raw.realFloor}")
  let some imaginary := (Data.String.toInt? raw.imaginaryFloor)
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
  /-- The retained exact-byte digest operation forwarded to original winding checks. -/
  inputDigest : Option (String → IO String) := none

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
  pure ⟨savedOnly, killAfterWrites, none⟩

set_option genInjectivity false in
/-- Loaders returning the exact original vertical and horizontal line clearances.

Each result keeps equality to the supplied source clearance, preserving the elimination certificate and ambient box. -/
structure ClearanceLoader {p : GaussianPolynomial} {degreeBound : Nat}
    (elimination : AxisEliminationCertificate p degreeBound)
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

section

omit [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]

/-- Transport a complete original clearance loader along an exact elimination-certificate equality.

The polynomial and degree bound stay fixed. Both retained loading operations
are reused, while their canonical-source certificate indices follow the same
complete elimination equality.
-/
@[expose] def ClearanceLoader.cast
    {p : GaussianPolynomial} {degreeBound : Nat}
    {left right : AxisEliminationCertificate p degreeBound}
    (same : left = right) (loader : ClearanceLoader left (.canonical left) m) :
    ClearanceLoader right (.canonical right) m := by
  cases same
  exact loader

/-- Inverse elimination transport retains the complete original clearance loader. -/
theorem ClearanceLoader.cast_inverse
    {p : GaussianPolynomial} {degreeBound : Nat}
    {left right : AxisEliminationCertificate p degreeBound}
    (same : left = right) (loader : ClearanceLoader left (.canonical left) m) :
    ClearanceLoader.cast same.symm (ClearanceLoader.cast same loader) = loader := by
  cases same
  rfl

/-- Transport the same complete canonical clearance loader along an exact degree-bound equality. -/
@[expose] def ClearanceLoader.castDegree
    {p : GaussianPolynomial} {left right : Nat}
    (same : left = right)
    (elimination : AxisEliminationCertificate p left)
    (loader : ClearanceLoader elimination (.canonical elimination) m) :
    ClearanceLoader (elimination.castDegree same) (.canonical (elimination.castDegree same)) m := by
  cases same
  exact loader

/-- Inverse degree transport retains the complete original clearance loader. -/
theorem ClearanceLoader.castDegree_inverse
    {p : GaussianPolynomial} {left right : Nat}
    (same : left = right)
    (elimination : AxisEliminationCertificate p left)
    (loader : ClearanceLoader elimination (.canonical elimination) m) :
    ClearanceLoader.castDegree same.symm (elimination.castDegree same)
      (ClearanceLoader.castDegree same elimination loader) =
      ClearanceLoader.cast ((elimination.castDegree_inverse same).symm) loader := by
  cases same
  rfl

end

/-- The explicit quadratic formulas are inexpensive direct constructors. Generic separated-Sylvester consumers instead
use `separated` below. -/
@[expose] def ClearanceLoader.direct {p degreeBound} (elimination :
  AxisEliminationCertificate p degreeBound)
    (source : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination) : ClearanceLoader elimination source m
      where
  vertical _ ambient x safe := pure ⟨source.vertical ambient x safe, rfl⟩
  horizontal _ ambient y safe := pure ⟨source.horizontal ambient y safe, rfl⟩

/-- Restore canonical axis clearances from the two actual saved inverse computations.

Each request reads the retained normalized cofactors. Its complete coprimality
certificate is compared with the canonical checked-column result before
transporting the original line clearance; no inverse or column is rebuilt.
-/
@[expose] def ClearanceLoader.replay {p : GaussianPolynomial}
    (first : Elimination.Separated.Bezout.Replay.Saved p)
    (second : Elimination.Separated.Bezout.Replay.Saved
      (Substitution.QuarterTurn.quarterTurn p))
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    ClearanceLoader (Replay.certificate first second nonzero positive)
      (.canonical (Replay.certificate first second nonzero positive)) m where
  vertical _ ambient x safe :=
    let coprime := Replay.vertical first nonzero positive x safe
    let line := Bezout.verticalOfCoprime p ambient x coprime
    pure ⟨line, by
      have originalSafe : (Elimination.Separated.Scalar.scalarEliminant p).eval x ≠ 0 := by
        rewrite [← Elimination.Separated.Bezout.Replay.eliminant_eq first]
        exact safe
      change Bezout.verticalOfCoprime p ambient x coprime =
        Bezout.verticalOfCoprime p ambient x
          (Separated.Replay.computeVertical p nonzero positive x originalSafe).val
      exact congrArg (Bezout.verticalOfCoprime p ambient x)
        ((Replay.vertical_eq first nonzero positive x safe).trans
          (Separated.Replay.computeVertical p nonzero positive x originalSafe).property.symm)⟩
  horizontal _ ambient y safe :=
    let coprime := Replay.horizontal second nonzero positive y safe
    let line := Bezout.horizontalOfCoprime p ambient y coprime
    pure ⟨line, by
      have originalSafe : (Separated.Eliminant.horizontalEliminant p).eval y ≠ 0 := by
        change (Elimination.Separated.Scalar.scalarEliminant
          (Substitution.QuarterTurn.quarterTurn p)).eval y ≠ 0
        rewrite [← Elimination.Separated.Bezout.Replay.eliminant_eq second]
        exact safe
      change Bezout.horizontalOfCoprime p ambient y coprime =
        Bezout.horizontalOfCoprime p ambient y
          (Separated.Replay.computeHorizontal p nonzero positive y originalSafe).val
      exact congrArg (Bezout.horizontalOfCoprime p ambient y)
        ((Replay.horizontal_eq second nonzero positive y safe).trans
          (Separated.Replay.computeHorizontal p nonzero positive y originalSafe).property.symm)⟩

/-- Restore original axis clearances from checked separated-Sylvester columns.

Horizontal restoration uses the exact quarter-turned polynomial and its retained degree equation. -/
@[expose] def ClearanceLoader.separated (control : ClearanceCheckpoint.Control m)
    (p : GaussianPolynomial) (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    ClearanceLoader (Separated.separatedAxisEliminationCertificate p nonzero positive)
      (.canonical (Separated.separatedAxisEliminationCertificate p nonzero positive)) m where
  vertical directory ambient x safe := do
    let column ← ClearanceCheckpoint.load control directory p positive x
    let coprime := column.vertical nonzero safe
    let line := Bezout.verticalOfCoprime p ambient x coprime.val
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("bound.json")))) (fractionData line.bound)
    return ⟨line, by
      change Bezout.verticalOfCoprime p ambient x coprime.val =
        Bezout.verticalOfCoprime p ambient x
          (Separated.Replay.computeVertical p nonzero positive x safe).val
      exact congrArg (Bezout.verticalOfCoprime p ambient x)
        (coprime.property.trans
          (Separated.Replay.computeVertical p nonzero positive x safe).property.symm)⟩
  horizontal directory ambient y safe := do
    let rotated := Substitution.QuarterTurn.quarterTurn p
    have rotatedPositive : 0 < rotated.natDegree := by
      rw [Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]; exact positive
    let column ← ClearanceCheckpoint.load control directory rotated rotatedPositive y
    let coprime := Separated.Replay.horizontal p nonzero positive y safe column
    let line := Bezout.horizontalOfCoprime p ambient y coprime.val
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("bound.json")))) (fractionData line.bound)
    return ⟨line, by
      change Bezout.horizontalOfCoprime p ambient y coprime.val =
        Bezout.horizontalOfCoprime p ambient y
          (Separated.Replay.computeHorizontal p nonzero positive y safe).val
      exact congrArg (Bezout.horizontalOfCoprime p ambient y)
        (coprime.property.trans
          (Separated.Replay.computeHorizontal p nonzero positive y safe).property.symm)⟩

/-- Restore both canonical line clearances of the same retained prepared axis certificate.

Each original matrix and coordinate uses the existing checked column format.
The complete coprimality equality identifies the retained prepared callback,
including its actual cofactors; no canonical axis family is substituted. -/
@[expose] def ClearanceLoader.prepared (control : ClearanceCheckpoint.Control m)
    (p : GaussianPolynomial) (axes : AxisPreparation p)
    (nonzero : p.isZero = false) (positive : 0 < p.natDegree) :
    ClearanceLoader (axes.certificate nonzero positive) (.canonical (axes.certificate nonzero positive)) m where
  vertical directory ambient x safe := do
    let column ← ClearanceCheckpoint.loadFromPrepared control directory p positive x axes.vertical safe
    let coprime := column.verticalFromPrepared axes.vertical nonzero safe
    let line := Bezout.verticalOfCoprime p ambient x coprime.val
    saveJson (Purelib.System.FilePath.join directory "bound.json") (fractionData line.bound)
    return ⟨line, congrArg (Bezout.verticalOfCoprime p ambient x) coprime.property⟩
  horizontal directory ambient y safe := do
    let rotated := Substitution.QuarterTurn.quarterTurn p
    have rotatedPositive : 0 < rotated.natDegree := by
      rewrite [Substitution.QuarterTurn.quarterTurn_natDegree p nonzero]
      exact positive
    let column ← ClearanceCheckpoint.loadFromPrepared control directory rotated rotatedPositive y axes.horizontal safe
    let coprime := Separated.Replay.horizontalFromPrepared p axes.horizontal nonzero positive y safe column
    let line := Bezout.horizontalOfCoprime p ambient y coprime.val
    saveJson (Purelib.System.FilePath.join directory "bound.json") (fractionData line.bound)
    return ⟨line, congrArg (Bezout.horizontalOfCoprime p ambient y) coprime.property⟩

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
    discard <| System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
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

variable {p : GaussianPolynomial} {ambient : Rational.Box} {degreeBound : Nat}
  (elimination : AxisEliminationCertificate p
    degreeBound)
  (current : State.Raw.RawWindingState p ambient) (epsilon : Coordinate)
  (clearances : Clearance.Box.Line.Elimination.Provider.AxisClearances elimination)
  (initialProposal : Gaussian)
  (loader : ClearanceLoader elimination clearances m)

/-- Serialize an accepted proposal or an inconclusive exhausted or zero-derivative attempt. -/
@[expose] def finishedReport : Newton.Search.Trace.Finished elimination current epsilon clearances initialProposal →
  Json
  | .accepted value inspected _ _ _ => Json.mkObj
      [("kind", toJson "accepted"), ("inspected", toJson inspected),
       ("budget", toJson (6 : Nat)),
       ("box", toJson (RootStateCheckpoint.boxData value.state.box))]
  | .exhausted inspected _ _ _ _ => Json.mkObj
      [("kind", toJson "inconclusive: proposal budget exhausted; total fallback unresolved"),
       ("inspected", toJson inspected), ("budget", toJson (6 : Nat))]
  | .zeroDerivative center derivative inspected _ _ _ _ _ _ => Json.mkObj
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
            (.exhausted historyZero) ⟨pending.extraBits, pending.proposal, historyZero⟩
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
              let winding ← WindingCheckpoint.box ⟨control.savedOnly, pure (), control.inputDigest⟩
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
                      ⟨remaining, pending.extraBits, pending.proposal, pending.inspected, rfl, history,
                        center.property, checked⟩
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
                      ⟨pending.extraBits + 2,
                        Data.Gaussian.Basic.value (Dense.Gaussian.Newton.Basic.newtonCenter p center.val),
                        exhausted ▸ Newton.Search.Trace.Prefix.step history center.val _
                        center.property checked zero rfl⟩
                  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("result.json"))))
                    (finishedReport elimination current epsilon clearances initialProposal result)
                  return ⟨result, [.exhausted pending.extraBits pending.proposal center.val derivative], by
                    rw [count, exhausted]; exact .exhaustedAfter center.property checked rfl zero⟩
                else
                  let proposed ← loadNewton control directory pending.inspected p center.val
                  let next ← checkIO directory pending.inspected "Newton update"
                    (CheckedDiameterReplay.checkNewton p center.val proposed derivative
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
structure Attempt (expected : Inset current) where
  /-- The exact inset supplied to the replayed check. -/ input : Inset current
  /-- The retained inset equals the expected original input. -/ input_eq : input = expected
  /-- The checked quadrupled winding of the inset box. -/ winding : Int
  /-- The retained winding equals the original root-polynomial box winding. -/ winding_eq : winding =
    Winding.Box.Basic.quadrupledBoxWinding
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
      (QuadraticFallbackReplay.insetBox (current := current) input)
  /-- The retained original strict-inset decision. -/ decision : InsetDecision
    current input
  /-- The decision is the original check using the retained winding witness. -/ decision_eq : decision =
    QuadraticFallbackReplay.checkInset current input ⟨winding, winding_eq⟩

constructive_injectivity Attempt

/-- Transport the retained inset decision to its expected original input. -/
@[expose] def Attempt.checked {expected : Inset current} (attempt : Attempt
  current expected) : InsetDecision current expected :=
  attempt.input_eq ▸ attempt.decision

/-- An accepted inset retains the exact winding of its selected raw-state box. -/
theorem Attempt.selected_winding {expected : Inset current} (attempt : Attempt
  current expected)
    (inset : RawInset current) (found : (attempt.checked current).val = some
      inset) :
    attempt.winding = Winding.Box.Basic.quadrupledBoxWinding
      (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
        (QuadraticFallbackReplay.rawState (current := current) inset).box := by
  cases attempt with
  | mk input equal winding windingEq decision decisionEq =>
      cases equal
      cases decisionEq
      exact QuadraticFallbackReplay.checkInset_winding current expected ⟨winding, windingEq⟩ inset
        found

/-- Serialize the attempted inset box, retained winding and acceptance flag. -/
@[expose] def Attempt.report {expected : Inset current} (attempt : Attempt
  current expected) : Json :=
  Json.mkObj [("box", toJson (RootStateCheckpoint.boxData (QuadraticFallbackReplay.insetBox (current
    := current) attempt.input))),
    ("winding", toJson attempt.winding),
    ("accepted", toJson attempt.decision.val.isSome)]

/-- Restore the original inset winding and retain its exact check result. -/
@[expose] def loadInset (control : WindingCheckpoint.Control) (directory : System.FilePath)
    (input : Inset current) : IO (Attempt current input) := do
  let winding ← WindingCheckpoint.box control directory
    (SquareRoot.Clearance.ExactQuadraticOwnerClearance.rootPolynomial parameter)
      (QuadraticFallbackReplay.insetBox (current := current) input)
  let decision := QuadraticFallbackReplay.checkInset current input winding
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
      (original : InsetAttempt current) (missing : original.val = none)
  /-- The selected original inset requires a nonzero unresolved subdivision depth. -/ | insetSubdivision (selected :
    SelectedInset current) (depth : Nat)
      (depth_eq : depth = Subdivision.Raw.Request.refinementDepth (QuadraticFallbackReplay.rawState
        (current := current) selected.value) (epsilon ^ 2))
      (unresolved : depth ≠ 0)
  /-- Both subdivision depths are zero, but the original inset promotion returned no result. -/ | promotion (selected :
    SelectedInset current)
      (initialDepth : Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2) = 0)
      (insetDepth : Subdivision.Raw.Request.refinementDepth (QuadraticFallbackReplay.rawState (current
        := current) selected.value) (epsilon ^ 2) = 0)
      (missed : QuadraticFallbackReplay.subdivision current epsilon positive = none)

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
           (QuadraticFallbackReplay.rawState (current := current) selected.value).box)),
         ("winding", toJson selected.winding)]
    | .promotion selected _ _ _ =>
        [("reason", toJson "original inset promotion missed; generic extractor remains unresolved"),
         ("inset", toJson (RootStateCheckpoint.boxData (QuadraticFallbackReplay.rawState (current :=
           current) selected.value).box)),
         ("winding", toJson selected.winding)]
  Json.mkObj ([("kind", toJson "inconclusive finite original-fallback replay"),
    ("state", toJson (RootStateCheckpoint.capture current)),
    ("epsilon", toJson (fractionData epsilon)), ("restoredSubdivisionBudget", toJson (0 : Nat))] ++ details)

/-- Check zero-depth inset promotion and return its original-result equation or retained unresolved obligation. -/
@[expose] def finish (epsilon : Coordinate) (positive : 0 < epsilon)
    (initialDepth : Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2) = 0)
    (selected : SelectedInset current) :
    Except (Pending current epsilon positive)
      { value : Fast current epsilon //
        QuadraticFallbackReplay.subdivision current epsilon positive = some value } := by
  let depth := Subdivision.Raw.Request.refinementDepth (QuadraticFallbackReplay.rawState (current :=
    current) selected.value) (epsilon ^ 2)
  if zero : depth = 0 then
    have accurate := QuadraticFallbackReplay.zero_accurate
      (QuadraticFallbackReplay.rawState (current := current) selected.value) epsilon positive zero
    let accepted := QuadraticFallbackReplay.promote current epsilon selected.value accurate
      ⟨selected.winding, selected.winding_eq⟩
    have equal := (QuadraticFallbackReplay.subdivision_zero current epsilon positive initialDepth
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
      { value : Fast current epsilon //
        QuadraticFallbackReplay.subdivision current epsilon positive = some value }) := do
  let depth := Subdivision.Raw.Request.refinementDepth current.raw (epsilon ^ 2)
  if zero : depth = 0 then
    let fixed ← loadInset current control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("fixed"))))
      (fixedInset current)
    match found : (fixed.checked current).val with
    | some inset =>
        return finish current epsilon positive zero
          ⟨inset, QuadraticFallbackReplay.firstInset current (fixed.checked current) inset found,
            fixed.winding, fixed.selected_winding current inset found⟩
    | none =>
        let narrow ← loadInset current control ((Purelib.System.FilePath.join directory (System.FilePath.mk
          ("protected")))) (protectedInset current)
        match next : (narrow.checked current).val with
        | some inset =>
            return finish current epsilon positive zero
              ⟨inset, (QuadraticFallbackReplay.secondInset current (fixed.checked current) found
                (narrow.checked current)).trans next,
                narrow.winding, narrow.selected_winding current inset next⟩
        | none =>
            return .error (.noInset fixed found narrow next
              (QuadraticFallbackReplay.missingInsets current (fixed.checked current) found
                (narrow.checked current) next) rfl)
  else return .error (.initialSubdivision depth rfl zero)

end QuadraticFallbackCheckpoint
