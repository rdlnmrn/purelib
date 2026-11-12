module

import Purelib.Polynomial.Elimination.Separated.Cubic
import Purelib.Polynomial.Dense.Gaussian.Substitution.QuarterTurn
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Cast
import Purelib.Data.Rat.Fraction.Square
import Purelib.Data.Nat.BitWidth
import Purelib.Polynomial.Dense.Arithmetic
import Purelib.System.IO
import Purelib.System.FilePath
import scripts.checkpoint.RootRefinement

namespace TestPurelib.Polynomial.Elimination.Separated.Cubic

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational square)
open Purelib.Data.Gaussian
open Purelib.Data.Nat
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Polynomial.Elimination.Separated
open Purelib.Polynomial.Dense.Gaussian.Substitution
open IntegrationCheckpoint

/-- The original cubic binomial at parameter one. -/
private def polynomial : CoefficientPolynomial := ⟨[1, 0, 0, -1]⟩

example : Cubic.propose? (⟨[1, 0, -1]⟩ : CoefficientPolynomial) 2 = none := by
  decide +kernel

example : Cubic.propose? (⟨[1, 1, 0, -1]⟩ : CoefficientPolynomial) 2 = none := by
  decide +kernel

example (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (column : Replay.Column p positive parameter)
    (safe : (Scalar.scalarEliminant p).eval parameter ≠ 0)
    (row : Fin (p.natDegree + p.natDegree)) :
    column.values row =
      ((Bezout.separatedData p).scalar.eval
        (Purelib.Data.Gaussian.Cast.Path.ofCoordinate parameter))⁻¹ *
      ((Bezout.separatedData p).inverse row (Bezout.firstColumnIndex p positive)).eval
        (Purelib.Data.Gaussian.Cast.Path.ofCoordinate parameter) :=
  column.value_eq safe row

/-- Check a cubic candidate and compare every original row with the generic producer. -/
private def checkAccepted (p : CoefficientPolynomial) (positive : 0 < p.natDegree)
    (parameter : Rational) (generalCubic : Bool := false) : IO Unit := do
  match Cubic.attempt p positive parameter generalCubic with
  | .accepted column _ =>
      let original := Replay.propose p positive parameter
      unless ∀ row, column.values row = original row do
        throw (IO.userError "cubic candidate changed an original normalized column entry")
  | .unavailable _ _ _ => throw (IO.userError "actual cubic proposal was unavailable")
  | .rejected _ _ _ => throw (IO.userError "cubic candidate failed its original matrix equation")

/-- Exercise real, conjugated, quarter-turn and nonmonic cubic columns and failures.

The accepted vectors are compared with the unchanged generic action. A
singular candidate retains its failed equation; another degree retains its
actual unavailable coefficient table and original generic fallback.
-/
public def check : IO Unit := do
  checkAccepted polynomial (by decide +kernel) 2
  checkAccepted polynomial (by decide +kernel) (-3)
  let rotated := QuarterTurn.quarterTurn polynomial
  checkAccepted rotated (by decide +kernel) 2
  let nonmonic : CoefficientPolynomial := ⟨[⟨2, 1⟩, 0, 0, ⟨-3, 2⟩]⟩
  checkAccepted nonmonic (by decide +kernel) 2
  let originalQ : CoefficientPolynomial := ⟨[1, -3, -2, 6]⟩
  checkAccepted originalQ (by decide +kernel) 1 true
  checkAccepted originalQ (by decide +kernel) 2 true
  let rotatedQ := QuarterTurn.quarterTurn originalQ
  checkAccepted rotatedQ (by decide +kernel) 1 true
  checkAccepted rotatedQ (by decide +kernel) 2 true
  let complexCubic : CoefficientPolynomial := ⟨[⟨2, 1⟩, ⟨3, -2⟩, ⟨-1, 4⟩, ⟨5, -1⟩]⟩
  checkAccepted complexCubic (by decide +kernel) 2 true
  let singular : CoefficientPolynomial := ⟨[1, 0, 0, 0]⟩
  match Cubic.attempt singular (by decide +kernel) 0 with
  | .rejected _ _ (.equation actual _ _) =>
      unless actual ⟨0, by decide +kernel⟩ = 0 do
        throw (IO.userError "singular cubic rejection lost its actual failed product")
  | _ => throw (IO.userError "singular cubic candidate was not rejected")
  let linear : CoefficientPolynomial := ⟨[1, -1]⟩
  have linearPositive : 0 < linear.natDegree := by decide +kernel
  match Cubic.attempt linear linearPositive 2 with
  | .unavailable coefficients _ _ =>
      unless coefficients = linear.normalize.coeffs do
        throw (IO.userError "unavailable cubic shape lost its actual normalized table")
      match Replay.check linear linearPositive 2
          (Replay.propose linear linearPositive 2) with
      | .ok _ => pure ()
      | .error _ => throw (IO.userError "unavailable cubic shape lost the generic fallback")
  | _ => throw (IO.userError "linear source incorrectly selected cubic proposal")
  Purelib.System.IO.println "cubic-column: all original rows, original q/quarter-turn, \
    nonmonic complex cubic and failures checked"

/-- Recheck one exact saved column using either the cubic or original generic producer.

The saved polynomial and coordinate are decoded from their actual bytes. Both
producers must solve all original rows and reproduce every retained column
entry. Separate processes can measure the same request with either producer.
-/
public def checkStored (path : System.FilePath) (generic : Bool)
    (generalCubic : Bool := false) : IO Unit := do
  let raw : ClearanceCheckpoint.RawColumn ← loadJson path
  let coefficients ← checked "original cubic coefficients" (raw.polynomial.mapM decodeGaussian)
  let parameter ← checked "original cubic parameter" (decodeFraction raw.parameter)
  let p : CoefficientPolynomial := ⟨coefficients⟩
  if positive : 0 < p.natDegree then
    let original ← match ClearanceCheckpoint.decode p positive parameter raw with
      | .ok column => pure column
      | .error _ => throw (IO.userError "original saved cubic column failed its exact checker")
    Purelib.System.IO.println "cubic-column: original saved operands and all rows checked; producer starts"
    (← IO.getStdout).flush
    let values ← if generic then pure (Replay.propose p positive parameter) else
      match Cubic.attempt p positive parameter generalCubic with
      | .accepted column _ => pure column.values
      | .rejected _ _ _ => throw (IO.userError "saved cubic request rejected compact candidate")
      | .unavailable _ _ _ => throw (IO.userError "saved cubic request lacks checked proposal")
    match Replay.check p positive parameter values with
    | .error _ => throw (IO.userError "producer failed an original saved matrix row")
    | .ok column =>
        unless ∀ row, column.values row = original.values row do
          throw (IO.userError "producer changed an original saved cubic column entry")
    Purelib.System.IO.println "cubic-column: original retained column reproduced and all rows checked"
  else throw (IO.userError "saved cubic column has no positive degree")

/-- Measure one original missing-column proposal, retain it, and check every original matrix row.

The decoded polynomial and coordinate are unchanged. The complete proposed
vector is saved as untrusted numerical data before its original six-row
checker runs, so completed arithmetic can be reused independently of checking.
The terminal result distinguishes actual checked success from failed shape or
matrix validation; no timeout supplies a mathematical obstruction.
-/
public def measureRequest (path directory : System.FilePath) (retainAgain : Bool := false) : IO Unit := do
  let raw : Purelib.Data.Json ← loadJson path
  let coefficients : List GaussianData ← match raw.getObjValAs? (List GaussianData) "polynomial" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let parameterData : FractionData ← match raw.getObjValAs? FractionData "parameter" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let coefficients ← checked "original cubic coefficients" (coefficients.mapM decodeGaussian)
  let parameter ← checked "original cubic coordinate" (decodeFraction parameterData)
  let p : CoefficientPolynomial := ⟨coefficients⟩
  IO.FS.createDirAll directory
  if positive : 0 < p.natDegree then
    let proposalPath := Purelib.System.FilePath.join directory "proposal.json"
    if ← proposalPath.pathExists then
      Purelib.System.IO.println "cubic-request: retained original proposal reload; all-row check starts"
      (← IO.getStdout).flush
      let proposed : ClearanceCheckpoint.RawColumn ← loadJson proposalPath
      match ClearanceCheckpoint.decode p positive parameter proposed with
      | .error _ => throw (IO.userError "retained proposal failed the current original input or matrix checker")
      | .ok column =>
          Purelib.System.IO.println "cubic-request: retained original proposal checked; generator not called"
          (← IO.getStdout).flush
          if retainAgain then
            Purelib.System.IO.println "cubic-request: current original checked-column retention starts"
            (← IO.getStdout).flush
            saveJson (Purelib.System.FilePath.join directory "reencoded.json") (ClearanceCheckpoint.encode column)
            Purelib.System.IO.println "cubic-request: current original checked-column retention complete"
            (← IO.getStdout).flush
          saveJson (Purelib.System.FilePath.join directory "result.json")
            (Purelib.Data.Json.mkObj [("kind", Purelib.Data.Json.toJson "all original matrix rows checked"),
              ("dimension", Purelib.Data.Json.toJson (p.natDegree + p.natDegree))])
          return
    Purelib.System.IO.println "cubic-request: actual original proposal starts"
    (← IO.getStdout).flush
    let values ← match Cubic.propose? p parameter with
      | some values => pure values
      | none => throw (IO.userError "retained original request has no binomial cubic proposal")
    Purelib.System.IO.println "cubic-request: actual original proposal complete; retention starts"
    (← IO.getStdout).flush
    let proposed : ClearanceCheckpoint.RawColumn :=
      ⟨p.coeffs.map gaussianData, fractionData parameter,
        (List.ofFn fun index => values index).map gaussianData⟩
    saveJson proposalPath proposed
    Purelib.System.IO.println "cubic-request: actual original proposal retained; all-row check starts"
    (← IO.getStdout).flush
    match Replay.check p positive parameter values with
    | .error _ =>
        saveJson (Purelib.System.FilePath.join directory "result.json")
          (Purelib.Data.Json.mkObj [("kind", Purelib.Data.Json.toJson "original matrix equation rejected")])
        throw (IO.userError "retained proposal failed an actual original matrix row")
    | .ok _column =>
        Purelib.System.IO.println "cubic-request: every original matrix row checked"
        (← IO.getStdout).flush
        saveJson (Purelib.System.FilePath.join directory "result.json")
          (Purelib.Data.Json.mkObj [("kind", Purelib.Data.Json.toJson "all original matrix rows checked"),
            ("dimension", Purelib.Data.Json.toJson (p.natDegree + p.natDegree))])
        pure ()
  else throw (IO.userError "retained original cubic request has no positive degree")

/-- Force the original Gaussian self-product inside a named numerical stage. -/
@[noinline] private def originalSquare (value : Canonical) : IO Canonical := pure (value * value)

/-- Force direct retained rational squares while sharing the original mixed coordinate product. -/
@[noinline] private def directSquare (value : Canonical) : IO Canonical :=
  let mixed := value.re * value.im
  pure ⟨square value.re - square value.im, mixed + mixed⟩

/-- Force the exact original Gaussian norm square inside a numerical stage. -/
@[noinline] private def originalNormSquare (value : Canonical) : IO Rational :=
  pure (Canonical.normSq value)

/-- Force the retained-coordinate norm-square prototype without changing the original owner. -/
@[noinline] private def directNormSquare (value : Canonical) : IO Rational :=
  pure (square value.re + square value.im)

/-- Force the unchanged total Gaussian reciprocal inside a numerical stage. -/
@[noinline] private def originalInverse (value : Canonical) : IO Canonical := pure value⁻¹

/-- Force one unchanged Gaussian product inside a numerical stage. -/
@[noinline] private def originalProduct (left right : Canonical) : IO Canonical := pure (left * right)

/-- Retain and measure one complete original Gaussian arithmetic result. -/
private def measureValue (label : String) (value : IO Canonical) : IO Canonical := do
  let start ← IO.monoMsNow
  let retained ← value
  let stop ← IO.monoMsNow
  Purelib.System.IO.println s!"cubic-stage {label}: {stop-start} ms; denominator widths \
    {BitWidth.natWidth retained.re.den}/{BitWidth.natWidth retained.im.den}"
  (← IO.getStdout).flush
  return retained

/-- Measure both complete Gaussian square constructions on one actual retained argument. -/
private def compareSquare (label : String) (value : Canonical) : IO Canonical := do
  let start ← IO.monoMsNow
  let original ← originalSquare value
  let originalEnd ← IO.monoMsNow
  let direct ← directSquare value
  let directEnd ← IO.monoMsNow
  unless original = direct do
    throw (IO.userError "direct retained-coordinate square differs from the complete original Gaussian")
  Purelib.System.IO.println s!"cubic-square {label}: original {originalEnd-start} ms; \
    direct {directEnd-originalEnd} ms; denominator widths \
    {BitWidth.natWidth original.re.den}/{BitWidth.natWidth original.im.den}; complete Gaussian agrees"
  (← IO.getStdout).flush
  return original

/-- Measure the four original cubic self-products at the unchanged decoded parameter.

The original normalized coefficients and total inverse construct the same
leading factors and scalar arguments as `Cubic.propose?`. Each complete
Gaussian result is checked against a direct retained-coordinate prototype;
this numerical diagnostic changes no production arithmetic or proposal.
-/
public def measureSquares (path : System.FilePath) : IO Unit := do
  let raw : Purelib.Data.Json ← loadJson path
  let coefficients : List GaussianData ← match raw.getObjValAs? (List GaussianData) "polynomial" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let parameterData : FractionData ← match raw.getObjValAs? FractionData "parameter" with
    | .ok value => pure value
    | .error error => throw (IO.userError error)
  let coefficients ← checked "original cubic coefficients" (coefficients.mapM decodeGaussian)
  let parameter ← checked "original cubic coordinate" (decodeFraction parameterData)
  let p : CoefficientPolynomial := ⟨coefficients⟩
  match p.normalize.coeffs with
  | [leading, quadratic, linear, constant] =>
      if leading = 0 ∨ quadratic ≠ 0 ∨ linear ≠ 0 then
        throw (IO.userError "retained original cubic has no binomial proposal")
      let leadingInverse := leading⁻¹
      let conjugateInverse := (Canonical.conj leading)⁻¹
      let c := constant * leadingInverse
      let d := Canonical.conj constant * conjugateInverse
      let h := 2 * Cast.Path.ofCoordinate parameter
      let hSquared ← compareSquare "h" h
      let a := 3 * h
      let b := -(3 * hSquared)
      let k := hSquared * h + c + d
      let aSquared ← compareSquare "a" a
      let bSquared ← compareSquare "b" b
      let kSquared ← compareSquare "k" k
      let x := kSquared + c * a * b
      let y := -(b * k) - c * aSquared
      let z := bSquared - a * k
      let denominator := kSquared * k + 3 * c * a * b * k +
        c * c * aSquared * a - c * bSquared * b
      let normStart ← IO.monoMsNow
      let originalNorm ← originalNormSquare denominator
      let normEnd ← IO.monoMsNow
      let directNorm ← directNormSquare denominator
      let directNormEnd ← IO.monoMsNow
      unless originalNorm = directNorm do
        throw (IO.userError "retained-coordinate norm square differs from the original complete rational")
      Purelib.System.IO.println s!"cubic-stage denominator-norm: original {normEnd-normStart} ms; \
        direct {directNormEnd-normEnd} ms; complete rational agrees"
      (← IO.getStdout).flush
      let reciprocal ← measureValue "denominator-inverse" (originalInverse denominator)
      let leftScale ← measureValue "left-scale" (originalProduct reciprocal conjugateInverse)
      let rightScale ← measureValue "right-scale" (originalProduct reciprocal leadingInverse)
      let _ ← measureValue "left-zero" (originalProduct leftScale x)
      let _ ← measureValue "left-one" (originalProduct leftScale y)
      let _ ← measureValue "left-two" (originalProduct leftScale z)
      let _ ← measureValue "right-zero" (originalProduct rightScale (x - a * y - b * z))
      let _ ← measureValue "right-one" (originalProduct rightScale (y - a * z))
      let _ ← measureValue "right-two" (originalProduct rightScale z)
  | _ => throw (IO.userError "retained original coefficient table is not cubic")

end TestPurelib.Polynomial.Elimination.Separated.Cubic
