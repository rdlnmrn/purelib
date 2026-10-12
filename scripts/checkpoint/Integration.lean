module

-- Exposed checkpoint paths retain the same lexical FilePath operation owner.
public import Purelib.System.FilePath

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
-- Public JSON APIs and exposed wire operations retain the owned codec path.
public import Purelib.Data.Json.Codec
-- The exposed syntax decoder retains the owned parser operation.
public import Purelib.Data.Json.Parser
-- Exposed rational encoders retain the original signed-decimal renderer.
public import Purelib.Data.Int.Decimal
import Purelib.Data.Json.Basic
import Purelib.Data.Json.Printer
import Purelib.Data.String.Basic
-- Exposed checkpoint readers retain the original IO carrier and certified text operations.
public import Purelib.System.IO
-- Exposed profile reads retain this original list coordinate owner.
public import Purelib.Data.List.GetD
-- Exposed diagnostics retain their original finite list rendering grammar.
public import Purelib.Data.List.ToString
-- Exposed loops retain the original list and natural-range iterator owners.
public import Purelib.Data.List.Control
public import Purelib.Data.Range
-- Exposed decimal decoding retains the owned String parsing owner.
public import Purelib.Data.String.Parsing
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Approximation.Gaussian.Sequence.Geometric.Control.Check
public import Purelib.Data.Rat.Fraction.Cast
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Check
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
public import Purelib.Integration.Polynomial.Gaussian.Path.Check
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Basic
import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Record
public import Purelib.Integration.Program.Gaussian.CCL.Replay.Observation.Replay
import Purelib.Polynomial.Ascending.Gaussian.Basic
import Purelib.Polynomial.Ascending.Gaussian.Evaluation

public import Purelib.Integration.CertifiedProgram

import Init.Core
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Purelib.Approximation.Gaussian.Enclosure.Ball.Basic
import Purelib.Computation.Query.Basic
import Purelib.Computation.Query.Replay
import Purelib.Data.CCL.Transducer.Replay.Failure
import Purelib.Data.CCL.Transducer.Replay.Machine.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance

open Purelib

open Purelib.Approximation.Gaussian.Sequence.Geometric

open Purelib.CCL.Progressive

open Purelib.Data.Rat

open Purelib.Integration

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Integration.Program.Gaussian

open Purelib.Integration.Program.Gaussian.CCL.Replay

open Purelib.Integration.Program.Gaussian.CCL.Replay.Observation

open Purelib.Integration.Program.Gaussian.Cached

open Purelib.Polynomial

open Purelib.Polynomial.Ascending.Gaussian

open Purelib.Data (Json)
open Purelib.System.IO
open scoped Purelib.Data.String Purelib.Data.List Purelib.Data.Range
open scoped Purelib.Data.Int.Decimal
open Purelib.Data.Json (toJson fromJson?)

public section

/-!
Finite, checked, disk-backed numerical model checkpoints for observation
diagnostics.  JSON is untrusted data: loading reconstructs local observation
proofs and verifies the cached integral and allowance against the saved cells.
It never reconstructs a period-ownership certificate from a filename or hash.
The files support source-free numerical replay.  Explicit restoration hooks
can additionally identify the original source using independently restored
finite data; filenames and hashes never provide that equation.  No
paper-facing API imports this IO module.  The JSON operations retain the owned finite carrier, scalar codecs,
parser/printer and record deriving handler.
-/

namespace IntegrationCheckpoint

variable {Result : Type}

open Purelib.Integration.CertifiedProgram (Request InvalidRequest)

open Purelib.CCL.Progressive.IntegrationReplay
open _root_.Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Gaussian.Norm.Basic (normSq_eq_canonical)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel LocalObservation)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

set_option genInjectivity false in
/-- A signed integer numerator and natural denominator serialized as decimal strings.

Both strings retain the exact signed numerator and natural denominator text.
The record itself is untrusted data; decoding checks the denominator before
constructing a canonical rational. -/
structure FractionData where
  /-- The signed integer numerator encoded in decimal. -/ numerator : String
  /-- The natural denominator encoded in decimal. -/ denominator : String
deriving Json.ToJson, Json.FromJson

constructive_injectivity FractionData

set_option genInjectivity false in
/-- Serialized exact real and imaginary rational coordinates.

The real and imaginary fields retain separate exact rational encodings.
Their scalar strings are checked independently before a Gaussian value is built. -/
structure GaussianData where
  /-- The exact serialized real coordinate. -/ real : FractionData
  /-- The exact serialized imaginary coordinate. -/ imaginary : FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity GaussianData

set_option genInjectivity false in
/-- Serialized local parameter, integrand reading and retained error.

The parameter, reading and error retain the original local observation data.
Decoding checks their scalar values and retained polynomial-error relation. -/
structure LocalData where
  /-- The exact serialized local polynomial parameter. -/ parameter : FractionData
  /-- The retained integrand reading. -/ reading : GaussianData
  /-- The retained error from the original polynomial value. -/ error : GaussianData
deriving Json.ToJson, Json.FromJson

constructive_injectivity LocalData

set_option genInjectivity false in
/-- The complete serialized finite cell model and its local observations.

Endpoints, ordered coefficients, allowance and local observations remain
separate retained fields. Decoding checks the scalar conditions and each local
observation before constructing the complete cell model. -/
structure CellData where
  /-- The original starting endpoint. -/ start : GaussianData
  /-- The original finishing endpoint. -/ finish : GaussianData
  /-- The polynomial coefficients in their retained order. -/ coefficients : List GaussianData
  /-- The serialized nonnegative local squared-error allowance. -/ allowance : FractionData
  /-- The ordered retained local observations. -/ observations : List LocalData
deriving Json.ToJson, Json.FromJson

constructive_injectivity CellData

set_option genInjectivity false in
/-- The serialized cached integral sample and aggregate allowance.

The sample and allowance retain the numerical reply independently.
Decoding compares both fields with the original model rather than reconstructing
model ownership from the serialized reply. -/
structure ReplyData where
  /-- The exact cached integral sample. -/ sample : GaussianData
  /-- The exact cached aggregate allowance. -/ allowance : FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity ReplyData

set_option genInjectivity false in
/-- Serialized controller error-scale and center bounds.

The two retained bounds remain separate exact rational encodings.
Their scalar conditions are checked before constructing the geometric controller. -/
structure ControlData where
  /-- The serialized nonnegative geometric error scale. -/ errorScale : FractionData
  /-- The serialized nonnegative sample-center bound. -/ centerBound : FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity ControlData

set_option genInjectivity false in
/-- Typed invalidity of an exact numerical checkpoint field or equation.

Each constructor retains the actual malformed data or scalar operands together
with the failed condition. Numerical invalidity does not supply source ownership. -/
inductive InvalidData where
  /-- A malformed scalar or JSON field with its diagnostic description. -/ | syntax (description : String)
  /-- A retained denominator certified not to be positive. -/ | denominator (value : Nat) (invalid : ¬ 0 < value)
  /-- A labeled retained scalar certified not to be nonnegative. -/ | negative (label : String) (value : Coordinate)
    (invalid : ¬ 0 ≤ value)
  /-- The actual and expected Gaussian values with their inequality proof. -/ | gaussianMismatch (label : String)
    (actual expected : Gaussian) (invalid : actual ≠ expected)
  /-- The actual and expected rational values with their inequality proof. -/ | rationalMismatch (label : String)
    (actual expected : Coordinate) (invalid : actual ≠ expected)
  /-- The retained local error violates its squared-norm allowance. -/ | localBound (error : Gaussian) (allowance :
    Coordinate) (invalid : ¬ Data.Gaussian.Norm.Basic.normSq error ≤ allowance)

constructive_injectivity InvalidData

/-- Render an exact rational with its retained numerator and denominator. -/
@[expose] def fractionText (value : Coordinate) : String := s!"{value.num}/{value.den}"
/-- Render the two exact rational coordinates of a Gaussian value. -/
@[expose] def gaussianText (value : Gaussian) : String := s!"({fractionText value.re},{fractionText value.im})"

/-- Describe the retained invalidity using the exact failed numerical operands. -/
@[expose] def InvalidData.message : InvalidData → String
  | .syntax description => description
  | .denominator value _ => s!"nonpositive denominator {value}"
  | .negative label value _ => s!"{label}: negative value {fractionText value}"
  | .gaussianMismatch label actual expected _ =>
      s!"{label}: {gaussianText actual} differs from {gaussianText expected}"
  | .rationalMismatch label actual expected _ =>
      s!"{label}: {fractionText actual} differs from {fractionText expected}"
  | .localBound error allowance _ =>
      s!"local error {gaussianText error} exceeds allowance {fractionText allowance}"

/-- Serialize the exact rational numerator and denominator as decimal strings. -/
@[expose] def fractionData (value : Coordinate) : FractionData := ⟨toString value.num, toString value.den⟩
/-- Serialize both exact rational coordinates of a Gaussian value. -/
@[expose] def gaussianData (value : Gaussian) : GaussianData := ⟨fractionData value.re, fractionData value.im⟩

set_option backward.match.sparseCases false in
/-- Parse a signed numerator and certify a positive denominator before constructing the exact rational.

The owned decimal parsers retain the original signed magnitude and separator
grammar. Failure retains the original syntax diagnostic or denominator invalidity. -/
@[expose] def decodeFraction (data : FractionData) : Except InvalidData Coordinate := do
  let some numerator := Data.String.toInt? data.numerator
    | .error (.syntax s!"invalid integer numerator {data.numerator}")
  let some denominator := Data.String.toNat? data.denominator
    | .error (.syntax s!"invalid natural denominator {data.denominator}")
  if positive : 0 < denominator then
    .ok (Fraction.Cast.fromInt numerator / Fraction.Cast.fromInt denominator)
  else .error (.denominator denominator positive)

/-- Decode the exact real and imaginary rational coordinates. -/
@[expose] def decodeGaussian (data : GaussianData) : Except InvalidData Gaussian := do
  return ⟨← decodeFraction data.real, ← decodeFraction data.imaginary⟩

/-- Serialize the original local observation parameter, reading and error. -/
@[expose] def localData {polynomial : Polynomial.Ascending.Gaussian.CoefficientPolynomial} {allowance : Coordinate}
    (value : Polynomial.Gaussian.Cell.Basic.LocalObservation polynomial allowance) : LocalData :=
  ⟨fractionData value.parameter, gaussianData value.integrandReading, gaussianData value.error⟩

/-- Decode a local observation and certify its exact error decomposition and squared-norm bound. -/
@[expose] def decodeLocal (polynomial : Polynomial.Ascending.Gaussian.CoefficientPolynomial) (allowance : Coordinate)
    (data : LocalData) : Except InvalidData (Polynomial.Gaussian.Cell.Basic.LocalObservation polynomial allowance) := do
  let parameter ← decodeFraction data.parameter
  let reading ← decodeGaussian data.reading
  let error ← decodeGaussian data.error
  let difference := reading - Evaluation.eval polynomial ⟨parameter, 0⟩
  if decomposition : difference = error then
    if bounded : Data.Gaussian.Norm.Basic.normSq error ≤ allowance then
      .ok ⟨parameter, reading, error, decomposition, by
        have scalar := bounded
        rw [normSq_eq_canonical] at scalar
        exact scalar⟩
    else .error (.localBound error allowance bounded)
  else .error (.gaussianMismatch "local decomposition" difference error decomposition)

/-- Serialize the original cell endpoints, polynomial, allowance and ordered observations. -/
@[expose] def cellData (cell : Polynomial.Gaussian.Cell.Basic.CellModel) : CellData :=
  ⟨gaussianData cell.start, gaussianData cell.finish,
    cell.polynomial.coefficients.map gaussianData, fractionData cell.localAllowance,
    cell.observations.map localData⟩

/-- Serialize every finite field of a checked cell view. -/
@[expose] def cellViewData (view : Polynomial.Gaussian.Cell.Check.CellView) : CellData :=
  ⟨gaussianData view.start, gaussianData view.finish, view.coefficients.map gaussianData,
    fractionData view.allowance, view.observations.map fun value =>
      ⟨fractionData value.parameter, gaussianData value.reading, gaussianData value.error⟩⟩

/-- Decode the complete finite cell and reconstruct all nonnegative-allowance and local-observation proofs. -/
@[expose] def decodeCell (data : CellData) : Except InvalidData CellModel := do
  let start ← decodeGaussian data.start
  let finish ← decodeGaussian data.finish
  let coefficients ← data.coefficients.mapM decodeGaussian
  let allowance ← decodeFraction data.allowance
  if nonnegative : 0 ≤ allowance then
    let polynomial : Polynomial.Ascending.Gaussian.CoefficientPolynomial := ⟨coefficients⟩
    let observations ← data.observations.mapM (decodeLocal polynomial allowance)
    .ok ⟨start, finish, polynomial, allowance, nonnegative, observations⟩
  else .error (.negative "cell allowance" allowance nonnegative)

/-- Serialize the retained cached sample and allowance. -/
@[expose] def replyData (reply : CachedModel) : ReplyData :=
  ⟨gaussianData reply.sample, fractionData reply.allowance⟩

/-- Decode a cached reply and certify both exact aggregate equations against its original model. -/
@[expose] def decodeReply (model : Path.Basic.PathModel) (data : ReplyData) :
    Except InvalidData {reply : CachedModel // reply.model = model} := do
  let sample ← decodeGaussian data.sample
  let allowance ← decodeFraction data.allowance
  let expectedSample := model.integralSample
  if sampleEqual : sample = expectedSample then
    let expectedAllowance := model.aggregateAllowance
    if allowanceEqual : allowance = expectedAllowance then
      .ok ⟨⟨model, sample, sampleEqual, allowance, allowanceEqual⟩, rfl⟩
    else .error (.rationalMismatch "cached allowance" allowance expectedAllowance allowanceEqual)
  else .error (.gaussianMismatch "cached sample" sample expectedSample sampleEqual)

/-- Serialize the controller's retained error scale and center bound. -/
@[expose] def controlData (control : Control) : ControlData :=
  ⟨fractionData control.errorScale, fractionData control.centerBound⟩

/-- Decode controller bounds and certify both are nonnegative. -/
@[expose] def decodeControl (data : ControlData) : Except InvalidData Control := do
  let scale ← decodeFraction data.errorScale
  let center ← decodeFraction data.centerBound
  if scaleNonnegative : 0 ≤ scale then
    if centerNonnegative : 0 ≤ center then .ok ⟨scale, scaleNonnegative, center, centerNonnegative⟩
    else .error (.negative "center bound" center centerNonnegative)
  else .error (.negative "error scale" scale scaleNonnegative)

/-- Return checked numerical data or report its typed invalidity with the supplied context. -/
@[expose] def checked {α : Type} (context : String) (result : Except InvalidData α) : IO α :=
  match result with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error.message}")

/-- Render a value as compact JSON. -/
@[expose] def jsonText {α : Type} [Json.ToJson α] (value : α) : String := (toJson value).compress

/-- Decode typed JSON and attach the supplied context to any syntax or type error. -/
@[expose] def parseJson {α : Type} [Json.FromJson α] (context text : String) : IO α :=
  match Json.parse text >>= fromJson? with
  | .ok value => pure value
  | .error error => throw (IO.userError s!"{context}: {error}")

namespace SharedJson

/-- A finite lookup key only. Reuse always compares the complete bytes; a hash collision leaves the requested record
independent of the existing object. -/
@[expose] def objectPath (directory : System.FilePath) (bytes : ByteArray) : System.FilePath :=
  let key := hash bytes
  (Purelib.System.FilePath.join (Purelib.System.FilePath.join directory (System.FilePath.mk (toString (key.toNat %
    256)))) (System.FilePath.mk (s!"{bytes.size}-{key}.json")))

/-- Check regular-file type, length and every retained byte before reuse. -/
@[expose] def sameBytes (path : System.FilePath) (bytes : ByteArray) : IO Bool := do
  if !(← path.pathExists) then return false
  let metadata ← path.symlinkMetadata
  if metadata.type != .file || metadata.byteSize != bytes.size.toUInt64 then return false
  return (← IO.FS.readBinFile path) == bytes

/-- Remove an existing interrupted temporary path before writing or linking. -/
@[expose] def removePending (path : System.FilePath) : IO Unit := do
  if ← path.pathExists then IO.FS.removeFile path

/-- Publish an immutable object link while preserving a concurrently published object. -/
@[expose] def publish (source object : System.FilePath) : IO Unit := do
  if !(← object.pathExists) then
    try IO.FS.hardLink source object
    catch error =>
      -- Another writer may have published the same lookup key. Its bytes
      -- still have to pass `sameBytes`; existence is not a certificate.
      unless ← object.pathExists do throw error

/-- Atomically link a retained object only after exact byte equality is checked. -/
@[expose] def reuse (object path : System.FilePath) (bytes : ByteArray) : IO Bool := do
  if !(← sameBytes object bytes) then return false
  let pending := System.FilePath.mk (path.toString ++ ".shared-link.pending")
  removePending pending
  IO.FS.hardLink object pending
  if ← sameBytes pending bytes then
    IO.FS.rename pending path
    return true
  removePending pending
  return false

set_option backward.match.sparseCases false in
/-- Store immutable JSON without changing its bytes or ordinary lookup path. The object directory must be on the
destination's filesystem. All writers to shared records must replace them atomically; append-only logs are excluded by
the public writer below. Interrupted temporary links are unlinked before reuse, so a later write cannot truncate an
object used by another checkpoint. -/
@[expose] def write (directory path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  let object := objectPath directory bytes
  if let some parent := (Purelib.System.FilePath.parent object) then IO.FS.createDirAll parent
  if ← reuse object path bytes then return
  if ← sameBytes path bytes then
    -- Adopt already saved work without allocating a second copy.
    publish path object
    return
  let pending := System.FilePath.mk (path.toString ++ ".shared-write.pending")
  removePending pending
  IO.FS.withFile pending .write fun handle => do
    handle.write bytes
    handle.flush
  publish pending object
  if ← reuse object path bytes then
    removePending pending
  else
    -- In particular, an unequal object at the same key must never replace
    -- the bytes supplied by the caller.
    IO.FS.rename pending path

end SharedJson

set_option backward.match.sparseCases false in
/-- Write beside the destination and atomically publish complete bytes. `CCL_CHECKPOINT_SHARED_JSON` optionally supplies
an immutable JSON object store. This changes physical storage only: every existing data reader and mathematical verifier
still reads and checks the ordinary checkpoint path. -/
@[expose] def atomicBytes (path : System.FilePath) (bytes : ByteArray) : IO Unit := do
  if Data.String.endsWith path.toString ".json" then
    if let some directory ← IO.getEnv "CCL_CHECKPOINT_SHARED_JSON" then
      SharedJson.write directory path bytes
      return
  let pending := System.FilePath.mk (path.toString ++ ".pending")
  if ← pending.pathExists then IO.FS.removeFile pending
  IO.FS.withFile pending .write fun handle => do
    handle.write bytes
    handle.flush
  IO.FS.rename pending path

/-- Atomically publish UTF-8 text at the retained checkpoint path. -/
@[expose] def atomicText (path : System.FilePath) (text : String) : IO Unit :=
  atomicBytes path text.toUTF8

/-- Atomically save one compact JSON record with its terminating newline. -/
@[expose] def saveJson {α : Type} [Json.ToJson α] (path : System.FilePath) (value : α) : IO Unit :=
  atomicText path (jsonText value ++ "\n")

/-- Read and decode one typed JSON checkpoint.

The original file path identifies the retained UTF8 bytes. Syntax and field
errors carry that same path context, while invalid UTF8 and filesystem failures
retain the original text-reader diagnostics. -/
@[expose] def loadJson {α : Type} [Json.FromJson α] (path : System.FilePath) : IO α := do
  parseJson path.toString (← FS.readFile path)

set_option genInjectivity false in
/-- A retained phase marker with monotonic time, process CPU ticks and memory readings.

The phase, elapsed milliseconds, CPU ticks and memory lines retain the measured
execution observations. Their serialization preserves the original field values
and ordering without inferring numerical or source correctness. -/
structure Profile where
  /-- The exact checkpoint phase label. -/ phase : String
  /-- The monotonic process timestamp in milliseconds. -/ monotonicMs : Nat
  /-- The retained Linux user-CPU tick reading. -/ cpuUserTicks : String
  /-- The retained Linux system-CPU tick reading. -/ cpuSystemTicks : String
  /-- The retained resident and peak resident-memory status lines. -/ memory : List String
deriving Json.ToJson, Json.FromJson

constructive_injectivity Profile

/-- Append a process timing and memory snapshot and flush the matching progress message.

The same proc fields, two memory prefixes and original phase label determine
the retained profile record. Owned splitting and prefix comparison preserve their order. -/
@[expose] def profile (directory : System.FilePath) (phase : String) : IO Unit := do
  let now ← IO.monoMsNow
  let stat ← FS.readFile "/proc/self/stat"
  let fields := Data.String.splitOn ((Data.String.splitOn stat ")").getLast!) " " |>.filter (· != "")
  let status ← FS.readFile "/proc/self/status"
  let memory := (Data.String.splitOn status "\n").filter fun line =>
    Data.String.startsWith line "VmRSS:" || Data.String.startsWith line "VmHWM:"
  let value : Profile := ⟨phase, now, Data.List.getD fields 11 "?", Data.List.getD fields 12 "?", memory⟩
  IO.FS.withFile ((Purelib.System.FilePath.join directory (System.FilePath.mk ("profile.jsonl")))) .append fun handle =>
    do
    Purelib.System.IO.FS.Handle.putStrLn handle (jsonText value)
    handle.flush
  println
    s!"PROFILE {phase}; monotonic_ms={now}; user_ticks={value.cpuUserTicks}; system_ticks={value.cpuSystemTicks}; \
      {memory}"
  (← IO.getStdout).flush

/-- Store complete original models before computing their aggregate integral.

The original declared count and ordered cells are written to the same pending
handle, each as its own complete JSON line. Flushing and atomic rename retain
completed-work recovery and the original numerical verification boundary. -/
@[expose] def saveModel (directory : System.FilePath) (index : Nat) (model : Path.Basic.PathModel) : IO Unit := do
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"model-{index}.cells.jsonl")))
  let pending := System.FilePath.mk (path.toString ++ ".pending")
  let count := model.cells.length
  IO.FS.withFile pending .write fun handle => do
    Purelib.System.IO.FS.Handle.putStrLn handle "ccl-integration-cells-v1"
    Purelib.System.IO.FS.Handle.putStrLn handle (toString count)
    let mut written := 0
    for cell in model.cells do
      Purelib.System.IO.FS.Handle.putStrLn handle (jsonText (cellData cell))
      written := written + 1
      if written % 4096 == 0 then
        handle.flush
        profile directory s!"model {index}: saved {written}/{count} cells"
    handle.flush
  IO.FS.rename pending path
  profile directory s!"model {index}: checkpoint complete, {count} cells"

set_option backward.match.sparseCases false in
/-- Decode a complete declared cell stream and reject missing or extra records.

The original header and declared count are read from the same handle, with only
space, tab, carriage return and newline removed at their ends. Exactly that many
ordered cells are decoded and checked; a nonempty following line is rejected. -/
@[expose] def loadModel (directory : System.FilePath) (index : Nat) : IO PathModel := do
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"model-{index}.cells.jsonl")))
  IO.FS.withFile path .read fun handle => do
    unless Data.String.trimAscii (← handle.getLine) == "ccl-integration-cells-v1" do
      throw (IO.userError s!"{path}: wrong model format")
    let countText := Data.String.trimAscii (← handle.getLine)
    let some count := Data.String.toNat? countText
      | throw (IO.userError s!"{path}: invalid cell count")
    let mut cells := #[]
    for index in [:count] do
      let raw : CellData ← parseJson s!"{path}, cell {index}" (← handle.getLine)
      cells := cells.push (← checked s!"{path}, cell {index}" (decodeCell raw))
    unless (← handle.getLine).isEmpty do
      throw (IO.userError s!"{path}: extra data after declared cells")
    pure ⟨cells.toList⟩

/-- Atomically save the cached numerical reply for the original model index. -/
@[expose] def saveReply (directory : System.FilePath) (index : Nat) (reply : CachedModel) : IO Unit :=
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"model-{index}.reply.json")))) (replyData
    reply)

/-- Load the complete model and certify its saved sample and allowance. -/
@[expose] def loadReply (directory : System.FilePath) (index : Nat) : IO CachedModel := do
  let model ← loadModel directory index
  let data : ReplyData ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    (s!"model-{index}.reply.json"))))
  return (← checked s!"model {index}" (decodeReply model data)).val

set_option genInjectivity false in
/-- Fresh cells retain their exact source equation. Disk cells acquire that equation only through the explicit
comparison with restored source data.

The ordered checked cells remain separate from the original specification.
The optional equality retains evidence for that same specification when available. -/
structure CellBatch (specification : List Polynomial.Gaussian.Cell.Basic.CellModel) where
  /-- The checked cells in their original requested order. -/ cells : List Polynomial.Gaussian.Cell.Basic.CellModel
  /-- An exact source-list equation when every cell has original-source evidence. -/ source_eq : Option (PLift (cells =
    specification))

constructive_injectivity CellBatch

set_option genInjectivity false in
/-- One checked finite cell with an optional exact original-source equation.

The retained cell and specification remain the original two owners. An absent
equality records numerical-only reuse rather than inventing source association. -/
structure CellResult (specification : Polynomial.Gaussian.Cell.Basic.CellModel) where
  /-- The retained checked finite cell. -/ cell : Polynomial.Gaussian.Cell.Basic.CellModel
  /-- The optional exact equality to the original cell specification. -/ source_eq : Option (PLift (cell =
    specification))

constructive_injectivity CellResult

set_option genInjectivity false in
/-- Reload may use an independently restored finite source cell. Without that data it remains explicitly numerical-only;
a path or hash cannot stand in for the missing source equation.

The cached branch retains its exact source thunk and equality. The numerical
branch retains no source equation and does not force an original generator. -/
inductive CellReload (source : Polynomial.Gaussian.Cell.Basic.CellModel) where
  /-- Reuse checked numerical data without claiming original-source equality. -/ | numericalOnly
  /-- Use independently restored finite cell data with its exact original-source equation. -/ | cached (value : Thunk
    Polynomial.Gaussian.Cell.Basic.CellModel) (equal : value.get = source)

constructive_injectivity CellReload

set_option genInjectivity false in
/-- The original cell thunk and its explicit numerical or certified reload policy.

The policy is indexed by that same original thunk value. Its cached witness
therefore refers to the retained source instead of a newly selected cell. -/
structure CellTask where
  /-- The original executable cell specification retained as a thunk. -/ source : Thunk
    Polynomial.Gaussian.Cell.Basic.CellModel
  /-- The exact reload policy indexed by that original cell. -/ reload : CellReload source.get

constructive_injectivity CellTask

/-- Create a cell task whose saved data can be reused only as numerical evidence. -/
@[expose] def CellTask.numerical (source : Thunk Polynomial.Gaussian.Cell.Basic.CellModel) : CellTask := ⟨source,
  .numericalOnly⟩

/-- The source constructor is only a proof index during checked reload. Callers derive the cached value from their
restored geometric/model data. -/
@[expose] def CellTask.fromCached (source value : Thunk Polynomial.Gaussian.Cell.Basic.CellModel) (equal : value.get =
  source.get) :
    CellTask := ⟨source, .cached value equal⟩

/-- Read the original cell specification retained by the task. -/
@[expose] def CellTask.specification (task : CellTask) : CellModel := task.source.get

/-- Force one original cell thunk and retain equality to that exact source value. -/
@[expose, noinline] def forceCell (work : Thunk Polynomial.Gaussian.Cell.Basic.CellModel) : IO {cell :
  Polynomial.Gaussian.Cell.Basic.CellModel // cell = work.get} :=
  pure ⟨work.get, rfl⟩

set_option backward.match.sparseCases false in
/-- Persist each completed cell before starting the next one. A restart can reuse a proper prefix without forcing those
cell generators. The caller must first open the input-fingerprinted store. -/
@[expose] def materializeCells (directory : System.FilePath) (modelIndex : Nat) :
    (offset : Nat) → (work : List CellTask) →
      IO (CellBatch (work.map CellTask.specification))
  | _, [] => pure ⟨[], some ⟨rfl⟩⟩
  | offset, head :: tail => do
      let cellsDirectory := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"model-{modelIndex}.cells")))
      IO.FS.createDirAll cellsDirectory
      let path := (Purelib.System.FilePath.join cellsDirectory (System.FilePath.mk (s!"cell-{offset}.json")))
      let result : CellResult head.specification ←
        if ← path.pathExists then do
          profile directory s!"model {modelIndex}, cell {offset}: BEGIN checked reuse"
          let raw : CellData ← loadJson path
          let cell ← checked path.toString (decodeCell raw)
          match head.reload with
          | .numericalOnly =>
              profile directory
                s!"model {modelIndex}, cell {offset}: END numerical reuse; source association unresolved"
              pure ⟨cell, none⟩
          | .cached expected sourceEqual =>
              match Polynomial.Gaussian.Cell.Check.cell expected.get cell with
              | .error failure =>
                  saveJson ((Purelib.System.FilePath.join cellsDirectory (System.FilePath.mk
                    (s!"cell-{offset}-source-mismatch.json"))))
                    (cellViewData failure.actual, cellViewData failure.expected)
                  throw (IO.userError
                    s!"model {modelIndex}, cell {offset}: certified source-cell mismatch; both finite cells retained")
              | .ok restored =>
                  profile directory
                    s!"model {modelIndex}, cell {offset}: END source-certified reuse; generator not called"
                  pure ⟨restored.val, some ⟨restored.property.trans sourceEqual⟩⟩
        else do
          profile directory s!"model {modelIndex}, cell {offset}: BEGIN generation"
          let cell ← forceCell head.source
          saveJson path (cellData cell.val)
          profile directory s!"model {modelIndex}, cell {offset}: END generation; cell saved"
          pure ⟨cell.val, some ⟨cell.property⟩⟩
      let rest ← materializeCells directory modelIndex (offset + 1) tail
      let sourceEqual := match result.source_eq, rest.source_eq with
        | some headEqual, some tailEqual =>
            some (PLift.up (show result.cell :: rest.cells = (head :: tail).map CellTask.specification from by
              change result.cell :: rest.cells = head.specification :: tail.map CellTask.specification
              rw [headEqual.down, tailEqual.down]))
        | _, _ => none
      pure ⟨result.cell :: rest.cells, sourceEqual⟩

set_option genInjectivity false in
/-- A model together with its actual source equation. Fresh generation and independently restored source data can supply
it; disk decoding alone cannot.

The retained model is identified with the exact source stage at the same index.
That equation is independent of any filename, numerical sample or checkpoint hash. -/
structure FreshModel (source : CachedProgram) (index : Nat) where
  /-- The retained finite model restored or generated from the original source. -/ model : Path.Basic.PathModel
  /-- The model equals the original source stage at the retained index. -/ equal : model = (source.stage index).model

constructive_injectivity FreshModel

set_option genInjectivity false in
/-- A retained cached reply with its original source index and exact stage equation.

The same ordered source index identifies the retained complete reply. Its
equality links that reply to the original source stage rather than its readback. -/
structure KnownReply (source : CachedProgram) where
  /-- The original source-stage index. -/ index : Nat
  /-- The retained complete cached reply. -/ reply : CachedModel
  /-- The reply equals that exact original source stage. -/ equal : reply = source.stage index

constructive_injectivity KnownReply

set_option genInjectivity false in
/-- Fresh controller data carry exact source equations. Keeping the source only in proof fields permits phased
preparation without forcing it again.

The same retained numerical controller has separate error-scale and center-bound
equalities to its original source, with no duplicated source computation. -/
structure KnownControl (source : CachedProgram) where
  /-- The retained numerical controller data. -/ value : Control
  /-- The controller error scale equals the original source scale. -/ errorScale_eq : value.errorScale =
    source.errorScale
  /-- The controller center bound equals the original source bound. -/ centerBound_eq : value.centerBound =
    source.centerBound

constructive_injectivity KnownControl

/-- Retain the original controller and its exact source-bound equations. -/
@[expose] def KnownControl.canonical (source : CachedProgram) : KnownControl source :=
  ⟨IntegrationReplay.control source, rfl, rfl⟩

set_option genInjectivity false in
/-- Preparation states explicitly whether original-source evidence is present.

Certified preparation keeps the retained controller and seeded replies with
their original equations. Checked preparation retains numerical data without them. -/
inductive Preparation (source : CachedProgram) where
  /-- Retain exact original-source controller and seeded-reply equations. -/ | certified (control : KnownControl source)
    (seeds : List (KnownReply source))
  /-- Retain numerical controller and seeded replies without original-source equations. -/ | checked (control : Control)
    (seeds : List (Nat × CachedModel))

constructive_injectivity Preparation

/-- Canonical aggregation of a cached model reconstructs its original certified reply. -/
theorem canonical_model (reply : CachedModel) :
    CertifiedProgram.CachedModel.canonical (operations := Cached.Basic.modelOperations) reply.model = reply := by
  cases reply with
  | mk model sample sampleEq allowance allowanceEq =>
      cases sampleEq
      cases allowanceEq
      rfl

set_option genInjectivity false in
/-- A generated model may include checked disk cells. Such reuse retains numerical certificates without manufacturing
the stronger source equation.

The original model stage and its exact index remain separate from the retained
model. Its optional equality records whether source association was established. -/
structure PendingModel (source : CachedProgram) (index : Nat) where
  /-- The retained complete finite model. -/ model : Path.Basic.PathModel
  /-- The optional exact original-source model equation. -/ source_eq : Option (PLift (model = (source.stage
    index).model))

constructive_injectivity PendingModel

/-- Retain the exact original-source equation when converting a fresh model to a pending model. -/
@[expose] def FreshModel.pending {source : CachedProgram} {index : Nat}
    (fresh : FreshModel source index) : PendingModel source index :=
  ⟨fresh.model, some ⟨fresh.equal⟩⟩

universe u

/-- Generate one original model while retaining the preparation state.

The continuation may return any ordinary IO result. Its higher-universe state
is threaded through the exact query sequence, cache hits and checked disk reuse. -/
abbrev ModelGenerator (source : CachedProgram) (State : Type u) :=
  {Result : Type} → (index : Nat) → State →
    (PendingModel source index → State → IO Result) → IO Result

set_option genInjectivity false in
/-- Source restoration is an explicit alternative to numerical-only reuse. It must consume restored data, not invoke the
completed model generator. The continuation also retains any reconstructed higher-universe state.

The certified branch threads the same input state through a retained source-model
restoration continuation and returns its exact callback result. The numerical
branch preserves the state without an equation. -/
inductive ModelReload (source : CachedProgram) (State : Type u) where
  /-- Reuse only numerical model evidence while preserving the retained state. -/ | numericalOnly
  /-- Restore original model data and its source equation while threading the retained state. -/ | certified (restore :
    {Result : Type} → (index : Nat) → State →
      (FreshModel source index → State → IO Result) → IO Result)

constructive_injectivity ModelReload

set_option genInjectivity false in
/-- An explicit choice between numerical controller reuse and certified source restoration.

Certified restoration returns the same retained controller with both original
source-bound equations. Numerical reuse retains only its checked scalar data. -/
inductive ControlReload (source : CachedProgram) where
  /-- Reuse checked controller data without original-source equations. -/ | numericalOnly
  /-- Restore controller data carrying both original-source bound equations. -/ | certified (restore : IO (KnownControl
    source))

constructive_injectivity ControlReload

set_option genInjectivity false in
/-- The independent controller and model restoration policies for one retained source.

Both policies refer to the same original cached program. Model restoration
also retains the requested state carrier and its threaded continuation. -/
structure Reload (source : CachedProgram) (State : Type u) where
  /-- The retained controller restoration policy. -/ control : ControlReload source
  /-- The retained state-threaded model restoration policy. -/ model : ModelReload source State

constructive_injectivity Reload

/-- Inline this constructor so its proof-only source index is not evaluated as an otherwise unused strict argument at a
cross-module call boundary. -/
@[expose, inline] def Reload.numericalOnly {source : CachedProgram} {State : Type u} : Reload source State :=
  ⟨.numericalOnly, .numericalOnly⟩

/-- Compare the saved model with independently restored source data. An equal integral is insufficient: all ordered
cells must be the original ones. -/
@[expose] def associateModel {source : CachedProgram} {State : Type u}
    (directory : System.FilePath) (reload : ModelReload source State)
    (index : Nat) (model : Path.Basic.PathModel) (state : State)
    (done : PendingModel source index → State → IO Result) : IO Result := do
  match reload with
  | .numericalOnly => done ⟨model, none⟩ state
  | .certified restore =>
      restore index state fun expected retained => do
        match Path.Check.model expected.model model with
        | .error failure =>
            saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
              (s!"model-{index}-source-mismatch.json"))))
              (failure.actual.map cellViewData, failure.expected.map cellViewData)
            throw (IO.userError s!"model {index}: certified source-model mismatch; both ordered cell lists retained")
        | .ok checked =>
            profile directory s!"query {index}: original source-model equation restored"
            done ⟨checked.val, some ⟨checked.property.trans expected.equal⟩⟩ retained

/-- Read a matching retained original reply or evaluate the source stage when no entry is present. -/
@[expose] def knownStage (source : Thunk CachedProgram) : List (KnownReply source.get) → Nat → CachedModel
  | [], index => source.get.stage index
  | head :: rest, index => if index = head.index then head.reply else knownStage source rest index

/-- Every retained-cache stage equals the corresponding original source stage. -/
theorem knownStage_eq (source : Thunk CachedProgram) (entries : List (KnownReply source.get)) (index : Nat) :
    knownStage source entries index = source.get.stage index := by
  induction entries with
  | nil => rfl
  | cons head rest induction =>
      unfold knownStage
      split
      · rename_i equal
        rw [equal]
        exact head.equal
      · exact induction

/-- The ordinary complete runner can reuse freshly generated replies without repeating generation. Every pointwise
source equality is derived here. -/
@[expose] def knownProgram (source : Thunk CachedProgram) (control : KnownControl source.get)
    (entries : List (KnownReply source.get)) : CachedProgram where
  stage := knownStage source entries
  errorScale := control.value.errorScale
  errorScale_nonneg := control.value.errorScale_nonneg
  centerBound := control.value.centerBound
  centerBound_nonneg := control.value.centerBound_nonneg
  modelAllowance_le := by
    intro index
    rw [knownStage_eq, control.errorScale_eq]
    exact source.get.modelAllowance_le index
  later_close := by
    intro earlier later order
    rw [knownStage_eq, knownStage_eq, control.errorScale_eq]
    exact source.get.later_close order
  sample_bounded := by
    intro index
    rw [knownStage_eq, control.centerBound_eq]
    exact source.get.sample_bounded index

set_option genInjectivity false in
/-- The exact checkpoint format, executable fingerprint and requested source identity.

The format, binary digest and source identity remain distinct retained strings.
Compatibility checks compare the original fields; their presence alone supplies
no reconstructed executable or mathematical provenance. -/
structure Manifest where
  /-- The exact checkpoint-format identifier. -/ format : String
  /-- The fingerprint of the executable opening this store. -/ binarySha256 : String
  /-- The exact caller-supplied original input identity. -/ sourceIdentity : String
deriving Json.ToJson, Json.FromJson, BEq

constructive_injectivity Manifest

set_option genInjectivity false in
/-- The retained finite observation result and its explicit source-verification status.

The requested payment, ordered words and queries, selected observation,
allowance and geometric readings remain separate fields. Source verification is
retained explicitly rather than inferred from the serialized numerical data. -/
structure ReceiptData where
  /-- The original requested output-prefix length. -/ requestedBits : Nat
  /-- The retained emitted bit sequence. -/ word : List Bool
  /-- The exact ordered source queries, including repetitions. -/ queries : List Nat
  /-- The retained selected source-model index. -/ selectedIndex : Nat
  /-- The exact selected numerical sample. -/ sample : GaussianData
  /-- The exact selected model allowance. -/ allowance : FractionData
  /-- The exact selected enclosure center. -/ ballCenter : GaussianData
  /-- The exact squared enclosure radius. -/ ballRadiusSq : FractionData
  /-- Whether this run additionally checked complete original-source agreement. -/ freshSourceVerified : Bool
deriving Json.ToJson, Json.FromJson

constructive_injectivity ReceiptData

/-- Serialize the requested bit count, ordered queries and complete selected numerical enclosure. -/
@[expose] def receiptData (count : Nat) (trace : Trace) (observation :
  Integration.Program.Gaussian.CCL.Replay.Observation)
    (freshSourceVerified : Bool) : ReceiptData :=
  ⟨count, observation.word, trace.map (·.query), observation.selected.index,
    gaussianData observation.selected.sample, fractionData observation.selected.allowance,
    gaussianData observation.selected.ball.center, fractionData observation.selected.ball.radiusSq,
    freshSourceVerified⟩

/-- Compare the complete replay machine and selected numerical enclosure data. -/
@[expose] def sameObservation (left right : Integration.Program.Gaussian.CCL.Replay.Observation) : Bool :=
  left.machine == right.machine && left.selected.index == right.selected.index &&
    left.selected.sample == right.selected.sample && left.selected.allowance == right.selected.allowance &&
    left.selected.ball.center == right.selected.ball.center &&
    left.selected.ball.radiusSq == right.selected.ball.radiusSq

/-- Create or validate a store bound to the exact executable and requested input identity.

The original executable is hashed by the same process request. Existing manifests
must agree with the complete format, fingerprint and source identity; a mismatch
leaves completed work intact, and a new store saves those exact fields. -/
@[expose] def openStore (directory : System.FilePath) (sourceIdentity : String) : IO Unit := do
  IO.FS.createDirAll directory
  let hashed ← Process.output { cmd := "sha256sum", args := #[(← IO.appPath).toString] }
  unless hashed.exitCode == 0 do throw (IO.userError "could not fingerprint the generator executable")
  let digest := (Data.String.splitOn hashed.stdout " ").head!
  let expected : Manifest := ⟨"ccl-integration-checkpoint-v1", digest, sourceIdentity⟩
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("manifest.json")))
  if ← path.pathExists then
    let retained : Manifest ← loadJson path
    unless retained == expected do
      throw (IO.userError
        "checkpoint input or generator differs; use a new store (old data remain available to replay-only)")
  else saveJson path expected
  profile directory "store opened; binary/input identity checked"

/-- Compute and persist one model's cached integral and allowance, then verify the disk roundtrip.

An original-source reply equation is retained only when the pending model already carries its exact source equation. -/
@[expose] def aggregateReply (directory : System.FilePath) (source : Thunk CachedProgram)
    (index : Nat) (pending : PendingModel source.get index) :
    IO (CachedModel × Option (KnownReply source.get)) := do
  let model := pending.model
  profile directory s!"query {index}: BEGIN aggregate integral/allowance"
  let reply := CertifiedProgram.CachedModel.canonical (operations := Cached.Basic.modelOperations) model
  -- Saving forces both cached values inside this separately timed phase.
  saveReply directory index reply
  profile directory s!"query {index}: END aggregate integral/allowance; reply saved"
  -- A disk roundtrip is checked once during generation, not assumed correct.
  let loaded ← loadReply directory index
  unless loaded.sample == reply.sample && loaded.allowance == reply.allowance do
    throw (IO.userError "saved reply changed during checked roundtrip")
  profile directory s!"query {index}: checked disk roundtrip complete"
  let known := pending.source_eq.map fun equal =>
    { index := index, reply := reply
      equal := by
        change CertifiedProgram.CachedModel.canonical (operations := Cached.Basic.modelOperations) pending.model =
          source.get.stage index
        rw [equal.down]
        exact canonical_model _ : KnownReply source.get }
  return (reply, known)

/-- Reuse each complete model and thread its retained preparation through generation.

An unfinished cell-file rename is not a complete model. Every successful branch
returns the exact continuation result; restoration errors remain IO errors. -/
@[expose] def acquireReply {State : Type u} (directory : System.FilePath)
    (source : Thunk CachedProgram) (generate : ModelGenerator source.get State)
    (reload : ModelReload source.get State)
    (index : Nat) (state : State)
    (done : CachedModel → Option (KnownReply source.get) → State → IO Result) : IO Result := do
  let replyExists ← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    (s!"model-{index}.reply.json")))).pathExists
  if replyExists || (← ((Purelib.System.FilePath.join directory (System.FilePath.mk
    (s!"model-{index}.cells.jsonl")))).pathExists) then
    profile directory s!"query {index}: loading/checking saved model"
    let model ← loadModel directory index
    associateModel directory reload index model state fun pending retained => do
      if replyExists then
        let raw : ReplyData ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
          (s!"model-{index}.reply.json"))))
        let decoded ← checked s!"model {index}" (decodeReply pending.model raw)
        let reply := decoded.val
        let known := pending.source_eq.map fun equal =>
          { index := index, reply := reply
            equal := CertifiedProgram.CachedModel.eq_of_model_eq _ _
              (decoded.property.trans equal.down) : KnownReply source.get }
        profile directory s!"query {index}: saved reply checked; model generator not called"
        done reply known retained
      else
        let (reply, known) ← aggregateReply directory source index pending
        done reply known retained
  else
    profile directory s!"query {index}: BEGIN canonical cell-model generation"
    generate index state fun pending retained => do
      profile directory s!"query {index}: END canonical cell-model generation"
      saveModel directory index pending.model
      let (reply, known) ← aggregateReply directory source index pending
      done reply known retained

/-- Check the requested output and accuracy, then preserve the completed observation receipt.

Historical numerical receipts remain unchanged; fresh source certification receives its own separate acceptance record.
-/
@[expose] def finishObservation (directory : System.FilePath) (request : Request) (count : Nat)
    (trace : Trace) (observation : Integration.Program.Gaussian.CCL.Replay.Observation) (fresh : Bool) : IO Unit := do
  unless observation.word.length == count && observation.selected.ball.radiusSq < request.target &&
      observation.selected.allowance < request.target do
    throw (IO.userError "completed replay failed its prefix/accuracy checks")
  let receiptPath := (Purelib.System.FilePath.join directory (System.FilePath.mk (s!"receipt-{count}.json")))
  if ← receiptPath.pathExists then
    let previous : ReceiptData ← loadJson receiptPath
    unless jsonText (receiptData count trace observation previous.freshSourceVerified) == jsonText previous do
      throw (IO.userError "new replay differs from the completed saved receipt; refusing to overwrite it")
  else
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"trace-{count}.json")))) (trace.map
      (·.query))
    saveJson receiptPath (receiptData count trace observation fresh)
  -- A previous numerical-only receipt remains historical evidence.  A new
  -- source-certified run records its own acceptance instead of copying or
  -- silently upgrading the previous receipt's verification flag.
  if fresh then
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"source-verified-receipt-{count}.json"))))
      (receiptData count trace observation true)
  profile directory
    s!"COMPLETE {count} bits; word={observation.word}; queries={trace.map (·.query)}; fresh_source_verified={fresh}"

set_option backward.match.sparseCases false in
/-- Follow the actual replay protocol; never guess which source model the prefix needs. The diagnostic bound reports its
missing query and preserves all completed checkpoints, not a mathematical non-certifiability result. -/
@[expose] def acquire {State : Type u} (directory : System.FilePath) (source : Thunk CachedProgram)
    (generate : ModelGenerator source.get State)
    (reload : ModelReload source.get State)
    (control : Control) (controlProof : Option (KnownControl source.get))
    (request : Request) (count : Nat) :
    Nat → State → Trace → List (Nat × CachedModel) → Option (List (KnownReply source.get)) → IO Unit
  | remaining, state, trace, cache, known => do
      match Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay control request count trace with
      | .ok observation =>
          let fresh ← match controlProof, known with
            | some certifiedControl, some entries => do
                profile directory "BEGIN original complete runner on certified in-memory source cache"
                let recorded := Record.record (knownProgram source certifiedControl entries) request count
                unless sameObservation recorded.observation observation &&
                    recorded.trace.map (·.query) == trace.map (·.query) do
                  throw (IO.userError "checkpoint acquisition differs from the original complete runner")
                profile directory "END original complete runner; observation agrees exactly"
                pure true
            | _, _ => pure false
          finishObservation directory request count trace observation fresh
      | .error (.transcript (.missing index)) =>
          match remaining with
          | 0 =>
              saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("inconclusive.json"))))
                ("query budget exhausted; not non-certifiability", index, trace.map (·.query))
              throw (IO.userError
                s!"diagnostic acquisition budget exhausted before query {index}; completed data retained")
          | remaining + 1 =>
              let resume := fun reply cache known retained => do
                let next := trace ++ [⟨index, reply⟩]
                saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
                  (s!"pending-trace-{count}.json")))) (next.map (·.query))
                acquire directory source generate reload control controlProof request count
                  remaining retained next cache known
              match cache.lookup index with
              | some reply => resume reply cache known state
              | none =>
                  acquireReply directory source generate reload index state fun reply newKnown retained => do
                    let known := match known, newKnown with
                      | some entries, some entry => some (entry :: entries)
                      | _, _ => none
                    resume reply ((index, reply) :: cache) known retained
      | .error _ => throw (IO.userError "saved/generated transcript failed typed numerical replay validation")

/-- The preparation hook may persist and retain initial models before computing controller metadata. Its source
equations are used by the complete-runner comparison without replaying the original expensive constructor. -/
@[expose] def observeWithState {State : Type u} (directory : System.FilePath) (identity : String)
    (source : Thunk CachedProgram)
    (prepare : IO (Preparation source.get))
    (state : State) (generate : ModelGenerator source.get State)
    (reload : Reload source.get State)
    (request : Request) (count : Nat) : IO Unit := do
  unless 0 < count do throw (IO.userError "observation must request a nonempty prefix")
  openStore directory identity
  let metadataPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("control.json")))
  let (metadata, controlProof, seeds, knownSeeds) ← if ← metadataPath.pathExists then do
      let data : ControlData ← loadJson metadataPath
      let metadata ← checked "saved control" (decodeControl data)
      match reload.control with
      | .numericalOnly => pure (metadata, none, [], none)
      | .certified restore =>
          let expected ← restore
          match Control.Check.control expected.value metadata with
          | .error failure =>
              saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("control-source-mismatch.json"))))
                ((fractionData failure.actual.1, fractionData failure.actual.2),
                  (fractionData failure.expected.1, fractionData failure.expected.2))
              throw (IO.userError "certified source-control mismatch; actual and expected values retained")
          | .ok restored =>
              let known : KnownControl source.get :=
                ⟨restored.val,
                  (congrArg Control.errorScale restored.property).trans expected.errorScale_eq,
                  (congrArg Control.centerBound restored.property).trans expected.centerBound_eq⟩
              profile directory "Saved control retains its original source equations; preparation generator not called"
              pure (restored.val, some known, [], some [])
    else do
      profile directory "BEGIN canonical numerical control/preparation"
      let prepared ← prepare
      let (metadata, controlProof, seeds, knownSeeds) := match prepared with
        | .certified certifiedControl preparedSeeds =>
            (certifiedControl.value, some certifiedControl,
              preparedSeeds.map fun seed => (seed.index, seed.reply), some preparedSeeds)
        | .checked checkedControl preparedSeeds => (checkedControl, none, preparedSeeds, none)
      saveJson metadataPath (controlData metadata)
      profile directory "END canonical numerical control/preparation; control saved"
      pure (metadata, controlProof, seeds, knownSeeds)
  let requestPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("request.json")))
  if ← requestPath.pathExists then
    let previous : Nat × FractionData ← loadJson requestPath
    let target ← checked "saved request" (decodeFraction previous.2)
    unless previous.1 == request.current && target == request.target do
      throw (IO.userError "request differs from the checkpoint store; existing data preserved")
  else saveJson requestPath (request.current, fractionData request.target)
  acquire directory source generate reload.model metadata controlProof request count 4096 state []
    seeds knownSeeds

/-- Stateless producers use the same state-threaded acquisition core. -/
@[expose] def observeWithPreparation (directory : System.FilePath) (identity : String)
    (source : Thunk CachedProgram) (prepare : IO (Preparation source.get))
    (generate : (index : Nat) → IO (PendingModel source.get index))
    (reload : Reload source.get Unit)
    (request : Request) (count : Nat) : IO Unit :=
  observeWithState directory identity source prepare ()
    (fun {_} index state done => do done (← generate index) state) reload request count

/-- Prepare the original certified controller without forcing a source stage. -/
@[expose, noinline] def prepareCanonicalControl (source : Thunk CachedProgram) :
    IO (Preparation source.get) :=
  pure (.certified (KnownControl.canonical source.get) [])

/-- Run the shared checkpoint observation pipeline with original controller preparation. -/
@[expose] def observe (directory : System.FilePath) (identity : String) (source : Thunk CachedProgram)
    (generate : (index : Nat) → IO (PendingModel source.get index))
    (reload : Reload source.get Unit)
    (request : Request) (count : Nat) : IO Unit :=
  observeWithPreparation directory identity source
    (prepareCanonicalControl source) generate reload request count

/-- This command has no source callback. Stored files prove numerical model consistency/replay; their manifest is
provenance metadata, not a curve theorem. -/
@[expose] def replayOnly (directory : System.FilePath) (count : Nat) : IO Unit := do
  let manifest : Manifest ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("manifest.json"))))
  unless manifest.format == "ccl-integration-checkpoint-v1" do
    throw (IO.userError "unsupported checkpoint format")
  let rawControl : ControlData ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("control.json"))))
  let control ← checked "saved control" (decodeControl rawControl)
  let rawRequest : Nat × FractionData ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("request.json"))))
  let target ← checked "saved target" (decodeFraction rawRequest.2)
  let request ← match Request.checked rawRequest.1 target with
    | .ok request => pure request
    | .error _ => throw (IO.userError "saved request has a certified nonpositive target")
  let indices : List Nat ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    (s!"trace-{count}.json"))))
  let expected : ReceiptData ← loadJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    (s!"receipt-{count}.json"))))
  let mut cache : List (Nat × CachedModel) := []
  let mut trace : Trace := []
  profile directory "BEGIN source-free checked disk replay"
  for index in indices do
    let reply ← match cache.lookup index with
      | some reply => pure reply
      | none => do
          let reply ← loadReply directory index
          cache := (index, reply) :: cache
          pure reply
    trace := trace ++ [⟨index, reply⟩]
  match Integration.Program.Gaussian.CCL.Replay.Observation.Transcript.replay control request count trace with
  | .error _ => throw (IO.userError "saved complete transcript failed replay")
  | .ok observation =>
      let actual := receiptData count trace observation expected.freshSourceVerified
      unless jsonText actual == jsonText expected do
        throw (IO.userError "saved receipt differs from replayed numerical fields")
      unless observation.word.length == count && observation.selected.ball.radiusSq < request.target &&
          observation.selected.allowance < request.target do
        throw (IO.userError "saved replay failed accuracy or prefix checks")
      profile directory
        s!"PASS source-free checked disk replay; word={observation.word}; generator={manifest.binarySha256}"
      println
        "Numerical replay checked without source access; manifest provenance is not a newly reconstructed \
          curve-ownership proof."

end IntegrationCheckpoint
