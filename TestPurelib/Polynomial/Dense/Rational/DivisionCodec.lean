module

import Purelib.System.IO
import Purelib.System.FilePath
import Purelib.Data.String.Parsing
import Purelib.Data.ByteArray.Basic
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.Rat.Fraction.Cast
import Purelib.Data.Nat.BitWidth
import Purelib.Data.Nat.Decimal
import Purelib.Data.Task.Parallel
import scripts.checkpoint.Integration
import scripts.checkpoint.RootRefinement

namespace TestPurelib.Polynomial.Dense.Rational.DivisionCodec

open Purelib
open Purelib.Data.Rat
open Purelib.Data (Json)
open Purelib.Polynomial.Dense.Rational.Basic (CoordinatePolynomial)
open IntegrationCheckpoint
open WindingCheckpoint

/-- The public joined traversal retains repeated successful occurrences through its ordinary readback law. -/
example : Data.Task.Parallel.mapExcept (fun value : Nat => (Except.ok (value + 1) : Except Nat Nat))
    [1, 2, 1] = .ok [2, 3, 2] := by
  rewrite [Data.Task.Parallel.mapExcept_eq]
  decide +kernel

/-- An earlier failed occurrence remains the first typed error across the retained halves. -/
example : Data.Task.Parallel.mapExcept (fun value : Nat =>
    if value = 2 then (Except.error value : Except Nat Nat) else if value = 3 then
      .error value else .ok value) [1, 2, 3, 4] = .error 2 := by
  rewrite [Data.Task.Parallel.mapExcept_eq]
  decide +kernel

set_option genInjectivity false in
/-- Cache the actual parsed signed numerator and positive denominator before normalization. -/
structure Parsed where
  /-- The original parsed signed numerator. -/ numerator : Int
  /-- The original parsed denominator. -/ denominator : Nat
  /-- The decoded denominator is positive. -/ positive : 0 < denominator

/-- Parse the same decimal grammar used by the original fraction decoder. -/
@[noinline] def parse (data : FractionData) : IO Parsed := do
  let some numerator := Data.String.toInt? data.numerator
    | throw (IO.userError "invalid original signed decimal")
  let some denominator := Data.String.toNat? data.denominator
    | throw (IO.userError "invalid original natural decimal")
  if positive : 0 < denominator then return ⟨numerator, denominator, positive⟩
  else throw (IO.userError "nonpositive original denominator")

/-- Construct the original canonical fraction from retained parsed integers. -/
@[noinline] def normalize (data : Parsed) : IO Fraction.Rational :=
  pure (Fraction.Cast.fromInt data.numerator / Fraction.Cast.fromInt data.denominator)

/-- Retain the original signed constructor branches and natural renderer for payload comparison. -/
def originalFractionData (value : Fraction.Rational) : FractionData :=
  let numerator := match value.num with
    | .ofNat magnitude => Nat.repr magnitude
    | .negSucc magnitude => Data.String.append "-" (Nat.repr (magnitude + 1))
  ⟨numerator, Nat.repr value.den⟩

/-- Render the complete original JSON payload on the same retained numerical operands and witness. -/
@[noinline] def originalPayload (p q : CoordinatePolynomial)
    (witness : Purelib.Polynomial.Dense.Rational.Division.Replay.Witness) : IO _root_.String :=
  let raw : RawStep := ⟨p.coeffs.map originalFractionData, q.coeffs.map originalFractionData,
    witness.quotient.coeffs.map originalFractionData, witness.remainder.coeffs.map originalFractionData⟩
  pure ((Data.Json.toJson raw).compress)

/-- Render the actual production JSON payload on those same retained operands and witness. -/
@[noinline] def productionPayload (p q : CoordinatePolynomial)
    (witness : Purelib.Polynomial.Dense.Rational.Division.Replay.Witness) : IO _root_.String :=
  pure ((Data.Json.toJson (encode p q witness)).compress)

/-- Profile codec phases on one retained numerical division witness, preserving every exact check.

The legacy and compact payloads use identical decoded operands and ordered
quotient/remainder coefficients. This measures numerical byte/codec costs;
original root-state ownership is checked separately by the saved-only replay.
Disable `compareOriginalRendering` to isolate these phases without timing the
old decimal renderer. Both current payloads still undergo their full byte checks.
-/
public def profile (path : System.FilePath) (compareOriginalRendering : Bool := true) : IO Unit := do
  let begin ← IO.monoMsNow
  let bytes ← Purelib.System.IO.FS.readFile path
  let loaded ← IO.monoMsNow
  let raw : RawStep ← parseJson path.toString bytes
  let jsonRead ← IO.monoMsNow
  let p ← checked "dividend" (decodePolynomial raw.dividend)
  let q ← checked "divisor" (decodePolynomial raw.divisor)
  let quotient ← checked "quotient" (decodePolynomial raw.quotient)
  let remainder ← checked "remainder" (decodePolynomial raw.remainder)
  let decoded ← IO.monoMsNow
  if nonzero : q.isZero = false then
    let witness : Purelib.Polynomial.Dense.Rational.Division.Replay.Witness := ⟨quotient, remainder⟩
    match Purelib.Polynomial.Dense.Rational.Division.Replay.check p q nonzero witness with
    | .error _ => throw (IO.userError "retained original division witness failed its complete checker")
    | .ok _ => pure ()
    let divisionChecked ← IO.monoMsNow
    let legacyCoefficients := raw.dividend ++ raw.divisor ++ raw.quotient ++ raw.remainder
    let parsedLegacy ← legacyCoefficients.mapM parse
    let legacyParsed ← IO.monoMsNow
    let normalizedLegacy ← parsedLegacy.mapM normalize
    let legacyNormalized ← IO.monoMsNow
    unless normalizedLegacy = p.coeffs ++ q.coeffs ++ quotient.coeffs ++ remainder.coeffs do
      throw (IO.userError "legacy normalization changed an original decoded coefficient")
    let compactCoefficients := raw.quotient ++ raw.remainder
    let parsedCompact ← compactCoefficients.mapM parse
    let compactParsed ← IO.monoMsNow
    let normalizedCompact ← parsedCompact.mapM normalize
    let compactNormalized ← IO.monoMsNow
    unless normalizedCompact = normalizedLegacy.drop (raw.dividend.length + raw.divisor.length) do
      throw (IO.userError "compact normalization changed an original witness coefficient")
    match decode p q nonzero raw with
    | .error _ => throw (IO.userError "complete legacy codec rejected retained operands")
    | .ok _ => pure ()
    let legacyChecked ← IO.monoMsNow
    let digest := "same-retained-numerical-input-for-codec-comparison"
    let compact : RawWitness := ⟨"original-winding-division-v1", digest, 0, raw.quotient, raw.remainder⟩
    match checkWitness p q nonzero digest 0 compact with
    | .error _ => throw (IO.userError "complete compact codec rejected the same original witness")
    | .ok _ => pure ()
    let compactChecked ← IO.monoMsNow
    let rendered := encode p q witness
    let renderedBytes := (Data.Json.toJson rendered).compress
    unless renderedBytes = (Data.Json.toJson raw).compress do
      throw (IO.userError "original decimal render did not preserve the saved canonical payload bytes")
    let legacyRendered ← IO.monoMsNow
    let compactRendered := (Data.Json.toJson
      (RawWitness.mk compact.protocol digest 0 (polynomialData quotient) (polynomialData remainder))).compress
    unless compactRendered = (Data.Json.toJson compact).compress do
      throw (IO.userError "compact decimal render changed an original coefficient byte")
    let renderedEnd ← IO.monoMsNow
    System.IO.println s!"division-codec {path}: file {loaded-begin} ms, JSON {jsonRead-loaded} ms, \
      original decode {decoded-jsonRead} ms, exact division {divisionChecked-decoded} ms"
    System.IO.println s!"division-codec legacy: parse {legacyParsed-divisionChecked} ms, \
      normalize {legacyNormalized-legacyParsed} ms, full codec {legacyChecked-compactNormalized} ms, \
      render {legacyRendered-compactChecked} ms; coefficients {legacyCoefficients.length}"
    System.IO.println s!"division-codec compact: parse {compactParsed-legacyNormalized} ms, \
      normalize {compactNormalized-compactParsed} ms, full codec {compactChecked-legacyChecked} ms, \
      render {renderedEnd-legacyRendered} ms; coefficients {compactCoefficients.length}"
    if compareOriginalRendering then
      let referenceStart ← IO.monoMsNow
      let referenceBytes ← originalPayload p q witness
      let referenceEnd ← IO.monoMsNow
      let productionBytes ← productionPayload p q witness
      let productionEnd ← IO.monoMsNow
      let productionFirst ← productionPayload p q witness
      let reverseFirstEnd ← IO.monoMsNow
      let referenceLast ← originalPayload p q witness
      let reverseEnd ← IO.monoMsNow
      for actual in [referenceBytes, productionBytes, productionFirst, referenceLast] do
        unless actual = renderedBytes do
          throw (IO.userError "complete rendering comparison changed original saved payload bytes")
      System.IO.println s!"division-codec complete rendering: original {referenceEnd-referenceStart} ms, \
        production {productionEnd-referenceEnd} ms; reverse production {reverseFirstEnd-productionEnd} ms, \
        original {reverseEnd-reverseFirstEnd} ms; all complete original payload bytes agree"
  else throw (IO.userError "retained original divisor is zero")

/-- Force the original natural renderer on one retained magnitude for timing. -/
@[noinline] def originalRender (value : Nat) : IO _root_.String := pure (Nat.repr value)

/-- Prototype the same original digit recursion with a displayed binary-width counter.

This numerical diagnostic changes no production renderer. Every result below
is compared byte for byte with the exact original renderer before it is reported.
-/
@[noinline] def widthRender (value : Nat) : IO _root_.String :=
  pure (_root_.String.ofList (Nat.toDigitsCore 10 (Purelib.Data.Nat.BitWidth.natWidth value + 1) value []))

/-- Force the actual proposed production natural renderer on a retained magnitude. -/
@[noinline] def productionRender (value : Nat) : IO _root_.String :=
  pure (Purelib.Data.Nat.Decimal.repr value)

/-- Compare both rendering orders on the same retained signed magnitudes and denominators.

The original, shorter-fuel prototype and actual production path all return the
same complete original bytes. The reverse-order round keeps those same parsed
magnitudes and distinguishes producer cost from codec and normalization work.
-/
public def profileRendering (path : System.FilePath) : IO Unit :=
  letI : DecidableEq _root_.ByteArray := Data.ByteArray.decEq
  do
    let raw : RawStep ← loadJson path
    let parsed ← (raw.dividend ++ raw.divisor ++ raw.quotient ++ raw.remainder).mapM parse
    let magnitudes := parsed.flatMap (fun value => [value.numerator.natAbs, value.denominator])
    let beginning ← IO.monoMsNow
    let original ← magnitudes.mapM originalRender
    let originalEnd ← IO.monoMsNow
    let candidate ← magnitudes.mapM widthRender
    let candidateEnd ← IO.monoMsNow
    let production ← magnitudes.mapM productionRender
    let productionEnd ← IO.monoMsNow
    let productionFirst ← magnitudes.mapM productionRender
    let reverseFirstEnd ← IO.monoMsNow
    let originalLast ← magnitudes.mapM originalRender
    let reverseEnd ← IO.monoMsNow
    unless (original.map (fun text => text.toByteArray)) = candidate.map (fun text => text.toByteArray) do
      throw (IO.userError "binary-width rendering prototype differs from exact original bytes")
    for actual in [production, productionFirst, originalLast] do
      unless original.map (fun text => text.toByteArray) = actual.map (fun text => text.toByteArray) do
        throw (IO.userError "production or reversed-order rendering differs from exact original bytes")
    System.IO.println s!"decimal-render {path}: original {originalEnd-beginning} ms, \
    width-fuel {candidateEnd-originalEnd} ms, production {productionEnd-candidateEnd} ms; \
    reverse production {reverseFirstEnd-productionEnd} ms, original {reverseEnd-reverseFirstEnd} ms; \
    {magnitudes.length} retained magnitudes, all original bytes agree"

/-- Decode the original ordered scalar list in one sequential native call. -/
@[noinline] private def sequentialDecode (data : List FractionData) :
    IO (Except InvalidData (List Fraction.Rational)) :=
  pure (data.mapM decodeFraction)

/-- Decode the same ordered scalars through the bounded joined-task procedure. -/
@[noinline] private def parallelDecode (data : List FractionData) :
    IO (Except InvalidData (List Fraction.Rational)) :=
  pure (decodeFractions data)

/-- Compare complete successful scalar lists or their original first invalidity diagnostics. -/
private def sameDecode {Value : Type} [DecidableEq Value]
    (first second : Except InvalidData (List Value)) : Bool :=
  match first, second with
  | .ok left, .ok right => decide (left = right)
  | .error left, .error right => left.message == right.message
  | _, _ => false

/-- Check ordered scalar values and first failures for the two-half decoding diagnostic. -/
private def checkParallelDecoding : IO Unit := do
  for data in ([[], [⟨"1", "2"⟩], [⟨"3", "6"⟩, ⟨"-1", "2"⟩, ⟨"0", "7"⟩],
      [⟨"bad", "1"⟩, ⟨"1", "0"⟩], [⟨"1", "0"⟩, ⟨"bad", "2"⟩],
      [⟨"1", "2"⟩, ⟨"1", "bad"⟩, ⟨"bad", "3"⟩],
      [⟨"-0", "001"⟩, ⟨"0001", "0002"⟩]] : List (List FractionData)) do
    let original ← sequentialDecode data
    let candidate ← parallelDecode data
    unless sameDecode original candidate do
      throw (IO.userError "two-half decoding changed an original value or first failure")
  for data in ([[], [⟨⟨"1", "2"⟩, ⟨"-1", "3"⟩⟩, ⟨⟨"0", "7"⟩, ⟨"6", "8"⟩⟩],
      [⟨⟨"bad", "1"⟩, ⟨"1", "2"⟩⟩, ⟨⟨"1", "0"⟩, ⟨"1", "2"⟩⟩],
      [⟨⟨"1", "2"⟩, ⟨"1", "bad"⟩⟩, ⟨⟨"bad", "1"⟩, ⟨"1", "2"⟩⟩]] :
      List (List GaussianData)) do
    unless sameDecode (data.mapM decodeGaussian) (decodeGaussians data) do
      throw (IO.userError "joined Gaussian decoding changed an original coordinate or first failure")

/-- Compare both scalar-decoding orders on the actual entries of a saved clearance column.

The original JSON and complete real/imaginary encodings are retained. Timings
cover scalar parsing and normalization after file and JSON loading; complete
successful values and first-failure diagnostics are compared outside them.
The production path uses the same owned scalar decoder and joined-task
procedure; no mathematical request or scalar encoding is changed.
-/
public def profileDecoding (path : System.FilePath) : IO Unit := do
  checkParallelDecoding
  let raw : ClearanceCheckpoint.RawColumn ← loadJson path
  let data := raw.values.flatMap fun value => [value.real, value.imaginary]
  let beginning ← IO.monoMsNow
  let original ← sequentialDecode data
  let originalEnd ← IO.monoMsNow
  let candidate ← parallelDecode data
  let candidateEnd ← IO.monoMsNow
  let reverseCandidate ← parallelDecode data
  let reverseCandidateEnd ← IO.monoMsNow
  let reverseOriginal ← sequentialDecode data
  let reverseOriginalEnd ← IO.monoMsNow
  for actual in [candidate, reverseCandidate, reverseOriginal] do
    unless sameDecode original actual do
      throw (IO.userError "two-half decoding changed an original complete scalar result")
  match original with
  | .error failure => throw (IO.userError s!"retained original column scalar failed: {failure.message}")
  | .ok values =>
      System.IO.println s!"fraction-decoding {path}: sequential {originalEnd-beginning} ms, \
        two-half {candidateEnd-originalEnd} ms; reverse two-half \
        {reverseCandidateEnd-candidateEnd} ms, sequential {reverseOriginalEnd-reverseCandidateEnd} ms; \
        {values.length} original scalars, complete values and first-failure fixtures agree"

end TestPurelib.Polynomial.Dense.Rational.DivisionCodec
