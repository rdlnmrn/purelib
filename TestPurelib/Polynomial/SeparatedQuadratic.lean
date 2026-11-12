module

public import Purelib.Polynomial.Elimination.Separated.Quadratic
public import Purelib.System.IO
public import Purelib.System.FilePath
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.Integration
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Vector.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Rat.Fraction.Square

public section

namespace TestPurelib.Polynomial.SeparatedQuadratic

open Purelib
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Polynomial
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open IntegrationCheckpoint
open Elimination.Separated

/-- Turn a checked finite checkpoint decode into an IO result with its actual error. -/
def checked {α : Type} (result : Except String α) : IO α :=
  match result with
  | .ok value => pure value
  | .error message => throw (IO.userError message)

/-- Force a displayed finite vector inside a separate IO operation for producer timing. -/
@[noinline] def produce {n : Nat} (producer : Unit → Data.Vector Gaussian.Basic.Canonical n) :
    IO (Data.Vector Gaussian.Basic.Canonical n) := pure (producer ())

/-- Compare the direct and original producers on the same original polynomial and coordinate.

Both vectors undergo the complete original row checker. Pointwise equality
checks every retained entry; timings distinguish producers and verification.
-/
def compare (label : String) (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational) : IO Unit := do
  let some source := Quadratic.shape p
    | throw (IO.userError "comparison input is outside the direct quadratic rule")
  let beginning ← IO.monoMsNow
  let direct ← produce (fun _ => source.propose parameter)
  let produced ← IO.monoMsNow
  let .ok directColumn := Replay.check p positive parameter direct
    | throw (IO.userError "quadratic proposal failed the original matrix equation")
  let verified ← IO.monoMsNow
  let original ← produce (fun _ => Replay.propose p positive parameter)
  let originalProduced ← IO.monoMsNow
  let .ok _ := Replay.check p positive parameter original
    | throw (IO.userError "original Action proposal failed its original matrix equation")
  let originalVerified ← IO.monoMsNow
  unless ∀ row, directColumn.values row = original row do
    throw (IO.userError "direct proposal differs from the exact original normalized column")
  System.IO.println s!"quadratic-column {label}: direct producer {produced-beginning} ms, \
    check {verified-produced} ms; original producer {originalProduced-verified} ms, \
    check {originalVerified-originalProduced} ms; all original entries agree"

/-- Compare actual retained clearance-column or missing-request inputs without generating a root state. -/
def compareStored (path : System.FilePath) : IO Unit := do
  let raw : Json ← loadJson path
  let coefficients : List GaussianData ← checked (raw.getObjValAs? (List GaussianData) "polynomial")
  let parameterData : FractionData ← checked (raw.getObjValAs? FractionData "parameter")
  let decoded ← checked ((coefficients.mapM decodeGaussian).mapError (fun failure => failure.message))
  let parameter ← checked ((decodeFraction parameterData).mapError (fun failure => failure.message))
  let p : CoefficientPolynomial := ⟨decoded⟩
  if positive : 0 < p.natDegree then
    match raw.getObjVal? "values" with
    | .ok _ =>
        let values : List GaussianData ← checked (raw.getObjValAs? (List GaussianData) "values")
        match ClearanceCheckpoint.decode p positive parameter ⟨coefficients, parameterData, values⟩ with
        | .error failure => throw (IO.userError s!"retained original column rejected: {failure.report}")
        | .ok _ => pure ()
    | .error _ => pure ()
    compare path.toString p positive parameter
  else throw (IO.userError "retained original column polynomial has no positive degree")

/-- Force one original rational arithmetic phase inside its own IO timing boundary. -/
@[noinline] private def produceFraction (producer : Unit → Fraction.Rational) : IO Fraction.Rational :=
  pure (producer ())

/-- Retain the original multiplication-based quadratic proposal for exact controlled phase comparisons. -/
@[noinline] private def originalProposal {p : CoefficientPolynomial} (source : Quadratic.Shape p)
    (parameter : Fraction.Rational) : Data.Vector Gaussian.Basic.Canonical (p.natDegree + p.natDegree) :=
  let four := Fraction.Cast.fromInt 4
  let three := Fraction.Cast.fromInt 3
  let denominator := four * (source.constant.re + source.leading.re * (parameter * parameter))
  let common := denominator⁻¹
  let linear := common / parameter
  let reflectedConstant := Gaussian.Cast.Path.ofCoordinate common
  let reflectedLinear := Gaussian.Cast.Path.ofCoordinate linear
  let liftedConstant := Gaussian.Cast.Path.ofCoordinate (three * common)
  let liftedLinear := Gaussian.Cast.Path.ofCoordinate (-linear)
  Vector.Basic.vectorOfFn fun row =>
    if row.val = 0 then reflectedConstant
    else if row.val = 1 then reflectedLinear
    else if row.val = 2 then liftedConstant
    else liftedLinear

example {p : CoefficientPolynomial} (source : Quadratic.Shape p) (parameter : Fraction.Rational) :
    source.propose parameter = originalProposal source parameter := by
  unfold originalProposal
  exact source.propose_eq parameter

/-- Time the actual rational square, denominator normalization, reciprocal and linear factor on one retained input. -/
private def profilePhases {p : CoefficientPolynomial} (source : Quadratic.Shape p)
    (parameter : Fraction.Rational) (directSquare : Bool) : IO Fraction.Rational := do
  let beginning ← IO.monoNanosNow
  let squared ← produceFraction (fun _ => if directSquare then Fraction.square parameter else parameter * parameter)
  let squareTime ← IO.monoNanosNow
  let denominator ← produceFraction (fun _ => Fraction.Cast.fromInt 4 *
    (source.constant.re + source.leading.re * squared))
  let denominatorTime ← IO.monoNanosNow
  let common ← produceFraction (fun _ => denominator⁻¹)
  let inverseTime ← IO.monoNanosNow
  let linear ← produceFraction (fun _ => common / parameter)
  let linearTime ← IO.monoNanosNow
  unless squared = parameter * parameter ∧ common = denominator⁻¹ ∧ linear = common / parameter do
    throw (IO.userError "quadratic reciprocal profile changed an original rational phase")
  System.IO.println s!"quadratic rational phases directSquare={directSquare}: \
    square {(squareTime-beginning)/1000} us, denominator {(denominatorTime-squareTime)/1000} us, \
    reciprocal {(inverseTime-denominatorTime)/1000} us, linear {(linearTime-inverseTime)/1000} us"
  (← IO.getStdout).flush
  return common

/-- Measure exact original and direct-square proposals, their complete checkers and retained entries in both orders. -/
private def profileProposals {p : CoefficientPolynomial} (source : Quadratic.Shape p) (positive : 0 < p.natDegree)
    (parameter : Fraction.Rational) (directFirst : Bool) : IO Unit := do
  let beginning ← IO.monoNanosNow
  let first ← produce (fun _ => if directFirst then source.propose parameter else originalProposal source parameter)
  let producedFirst ← IO.monoNanosNow
  let .ok firstColumn := Replay.check p positive parameter first
    | throw (IO.userError "first exact quadratic proposal failed its complete original matrix equation")
  let checkedFirst ← IO.monoNanosNow
  let second ← produce (fun _ =>
    if directFirst then originalProposal source parameter else source.propose parameter)
  let producedSecond ← IO.monoNanosNow
  let .ok secondColumn := Replay.check p positive parameter second
    | throw (IO.userError "second exact quadratic proposal failed its complete original matrix equation")
  let checkedSecond ← IO.monoNanosNow
  unless ∀ row, firstColumn.values row = secondColumn.values row do
    throw (IO.userError "direct parameter square changed an original retained quadratic vector entry")
  let retained ← IO.monoNanosNow
  System.IO.println s!"quadratic original proposal directFirst={directFirst}: \
    first {(producedFirst-beginning)/1000} us/check {(checkedFirst-producedFirst)/1000} us, \
    second {(producedSecond-checkedFirst)/1000} us/check {(checkedSecond-producedSecond)/1000} us, \
    retain all entries {(retained-checkedSecond)/1000} us"
  (← IO.getStdout).flush

/-- Profile an immutable saved original quadratic column without generating or changing any root-state request.

The complete original decode checks its retained polynomial, coordinate and
all matrix rows before timing. Every measured proposal again consumes that
same input and complete equation; repeated timing exchanges execution order.
-/
def profileStored (path : System.FilePath) : IO Unit := do
  let raw : Json ← loadJson path
  let coefficients : List GaussianData ← checked (raw.getObjValAs? (List GaussianData) "polynomial")
  let parameterData : FractionData ← checked (raw.getObjValAs? FractionData "parameter")
  let values : List GaussianData ← checked (raw.getObjValAs? (List GaussianData) "values")
  let decoded ← checked ((coefficients.mapM decodeGaussian).mapError (fun failure => failure.message))
  let parameter ← checked ((decodeFraction parameterData).mapError (fun failure => failure.message))
  let p : CoefficientPolynomial := ⟨decoded⟩
  if positive : 0 < p.natDegree then
    match ClearanceCheckpoint.decode p positive parameter ⟨coefficients, parameterData, values⟩ with
    | .error failure => throw (IO.userError s!"retained original quadratic column rejected: {failure.report}")
    | .ok _ => pure ()
    let some source := Quadratic.shape p
      | throw (IO.userError "retained original input is outside the real quadratic proposal rule")
    System.IO.println "quadratic reciprocal profile: complete retained original column validated"
    (← IO.getStdout).flush
    for directFirst in [false, true, false, true] do
      let first ← profilePhases source parameter directFirst
      let second ← profilePhases source parameter (!directFirst)
      unless first = second do throw (IO.userError "parameter squaring changed the original denominator reciprocal")
      profileProposals source positive parameter directFirst
  else throw (IO.userError "retained original quadratic has no positive degree")

/-- The original real quadratic and its quarter-turn shape used for boundary regressions. -/
def polynomial (leading : Int) : CoefficientPolynomial :=
  ⟨[Gaussian.Cast.Path.ofCoordinate (Fraction.Cast.fromInt leading),
    Gaussian.Cast.Path.ofCoordinate (Fraction.Cast.fromInt 0),
    Gaussian.Cast.Path.ofCoordinate (Fraction.Cast.fromInt (-4))]⟩

/-- Exercise both original real quadratic signs, singular rejections and the generic fallback. -/
def selfTest (directory : System.FilePath) : IO Unit := do
  if ← directory.pathExists then throw (IO.userError "quadratic self-test needs a fresh store")
  IO.FS.createDirAll directory
  let p := polynomial 1
  have positive : 0 < p.natDegree := by decide +kernel
  let q := polynomial (-1)
  have qPositive : 0 < q.natDegree := by decide +kernel
  compare "Z^2-4" p positive (Fraction.Cast.fromInt 3)
  compare "-Z^2-4" q qPositive (Fraction.Cast.fromInt 3)
  let acceptedDirectory := Purelib.System.FilePath.join directory "quadratic-accepted"
  let first ← ClearanceCheckpoint.load {} acceptedDirectory p positive (Fraction.Cast.fromInt 3)
  let cold ← ClearanceCheckpoint.load { savedOnly := true } acceptedDirectory p positive (Fraction.Cast.fromInt 3)
  unless ∀ row, first.values row = cold.values row do
    throw (IO.userError "saved-only replay changed a checked quadratic column")
  for parameter in [Fraction.Cast.fromInt 0, Fraction.Cast.fromInt 2] do
    match Quadratic.attempt p positive parameter with
    | .rejected _ _ _ _ => pure ()
    | _ => throw (IO.userError "singular quadratic proposal was not retained as a rejected equation")
  let linear : CoefficientPolynomial := ⟨[1, -1]⟩
  have linearPositive : 0 < linear.natDegree := by decide +kernel
  match Quadratic.attempt linear linearPositive (Fraction.Cast.fromInt 3) with
  | .unavailable _ _ _ => pure ()
  | _ => throw (IO.userError "nonquadratic source was accepted by the direct shape rule")
  let fallbackDirectory := Purelib.System.FilePath.join directory "linear-fallback"
  let fallback ← ClearanceCheckpoint.load {} fallbackDirectory linear linearPositive (Fraction.Cast.fromInt 3)
  let original := Replay.propose linear linearPositive (Fraction.Cast.fromInt 3)
  unless ∀ row, fallback.values row = original row do
    throw (IO.userError "generic Action fallback changed its actual original column")
  let rejectedDirectory := Purelib.System.FilePath.join directory "quadratic-rejected"
  let stopped ← try
    let _ ← ClearanceCheckpoint.load {} rejectedDirectory p positive (Fraction.Cast.fromInt 0)
    pure false
  catch _ => pure true
  unless stopped do throw (IO.userError "singular original fallback unexpectedly succeeded")
  unless (← (Purelib.System.FilePath.join rejectedDirectory "rejected-quadratic.json").pathExists) &&
      (← (Purelib.System.FilePath.join rejectedDirectory "invalid-generated.json").pathExists) do
    throw (IO.userError "rejected quadratic or exact original fallback failure was not retained")
  System.IO.println "quadratic shapes, original entry comparisons, singular rejection and generic fallback passed"

end TestPurelib.Polynomial.SeparatedQuadratic

end
