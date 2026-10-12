module

import Purelib.System.FilePath

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Riemann.Integration.PreparedConstantModels

import Purelib.RootIsolation.SquareRoot.Replay.QuadraticFallbackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackReplay
import Purelib.RootIsolation.SquareRoot.Replay.QuadraticTrackSampleReplay
public import scripts.checkpoint.QuadraticSample
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Name.Coherent
import Purelib.Approximation.Gaussian.Name.Coherent.Power
import Purelib.Approximation.Gaussian.Process.Apart.Preparation
import Purelib.Approximation.Gaussian.Process.Basic
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Curves.Hyperelliptic.Differentials.PreparedModels
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Power.Gaussian
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Riemann.RootContinuation.SquareRootDegree
import Purelib.Riemann.Topology.SquareRootContinuationChain
import Purelib.Riemann.Transport.PreparedCenterReplay
import Purelib.RootIsolation.SquareRoot.Clearance.ExactQuadraticOwnerClearance
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration
import scripts.checkpoint.RootRefinement
import scripts.checkpoint.RootState

open Purelib

open Purelib.Curves

open Purelib.Curves.Hyperelliptic

open Purelib.Riemann.Integration

open Purelib.RootIsolation.SquareRoot.Replay

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-!
Shared numeric center-cursor codec.  Loading verifies the exact cursor
calculation but does not invent canonical source or sample association.
The producer can save this record without evaluating a coefficient witness.
`run` additionally consumes the original source track and checked sample
traces to reconstruct the complete canonical center, including its thunks.
-/

namespace CenterCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m]
  [MonadExceptOf IO.Error m] [MonadStateOf RootRefinementCheckpoint.Counts m]

open IntegrationCheckpoint
open Purelib.Riemann.Transport.PreparedCenterReplay

set_option genInjectivity false in
/-- The serialized numerical inputs for a prepared coefficient's center cursor.

These bytes describe the requested calculation; association with an original prepared edge is supplied separately. -/
structure RawMetadata where
  /-- The serialized exact square-root parameter. -/ parameter : GaussianData
  /-- The serialized ambient box of the original root calculation. -/ rootAmbient : List FractionData
  /-- The serialized retained root box. -/ rootBox : List FractionData
  /-- The serialized exact coefficient numerator. -/ numerator : GaussianData
  /-- The serialized numerator magnitude bound. -/ numeratorBound : FractionData
  /-- The serialized target for the root residual. -/ rootResidualTarget : FractionData
  /-- The serialized target for the coefficient reading. -/ readingTarget : FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawMetadata

set_option genInjectivity false in
/-- Serialized center metadata and its proposed reading index.

The metadata and index retain the original serialized traversal request.
Reloading checks the request identity and selected index before resuming work. -/
structure RawCursor where
  /-- The original serialized numerical center inputs. -/ metadata : RawMetadata
  /-- The proposed saved reading index. -/ index : Nat
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawCursor

/-- Serialize each exact numerical field of the center metadata. -/
@[expose] def encode (data : Metadata) : RawMetadata :=
  ⟨gaussianData data.parameter, RootStateCheckpoint.boxData data.rootAmbient,
    RootStateCheckpoint.boxData data.rootBox, gaussianData data.numerator,
    fractionData data.numeratorBound, fractionData data.rootResidualTarget,
    fractionData data.readingTarget⟩

/-- Serialize the center metadata together with its calculated reading index. -/
@[expose] def cursor (data : Metadata) : RawCursor := ⟨encode data, data.readingIndex⟩

/-- Capture the numerical center cursor of the original prepared edge. -/
@[expose] def capture {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (edge : PreparedConstantModels.PreparedEdge curve differential) : RawCursor :=
  cursor (metadata edge)

set_option genInjectivity false in
/-- Typed invalidity found while decoding center metadata or checking its cursor index. -/
inductive Failure where
  /-- A failed exact Gaussian or rational scalar decoding. -/ | field (failure : InvalidData)
  /-- A failed root-ambient box decoding. -/ | ambient (failure : RootStateCheckpoint.BoxFailure)
  /-- A failed retained root-box decoding. -/ | box (failure : RootStateCheckpoint.BoxFailure)
  /-- A saved reading index inconsistent with the decoded metadata. -/ | index (failure : Invalidity)

constructive_injectivity Failure

/-- Decode every numerical metadata field and retain the exact failed field or box check. -/
@[expose] def decode (raw : RawMetadata) : Except Failure Metadata := do
  let parameter ← (decodeGaussian raw.parameter).mapError .field
  let ambient ← (RootStateCheckpoint.decodeBox raw.rootAmbient).mapError .ambient
  let box ← (RootStateCheckpoint.decodeBox raw.rootBox).mapError .box
  let numerator ← (decodeGaussian raw.numerator).mapError .field
  let numeratorBound ← (decodeFraction raw.numeratorBound).mapError .field
  let residual ← (decodeFraction raw.rootResidualTarget).mapError .field
  let reading ← (decodeFraction raw.readingTarget).mapError .field
  return ⟨parameter, ambient, box, numerator, numeratorBound, residual, reading⟩

set_option genInjectivity false in
/-- Decoded center metadata with a reading index certified equal to its original calculation. -/
structure Checked where
  /-- The decoded exact center metadata. -/ data : Metadata
  /-- The retained saved reading index. -/ index : Nat
  /-- The saved index equals the index calculated from the exact metadata. -/ index_eq : index = data.readingIndex

constructive_injectivity Checked

/-- Decode a saved cursor and certify that its index matches the retained metadata. -/
@[expose] def check (raw : RawCursor) : Except Failure Checked := do
  let data ← decode raw.metadata
  let index ← (checkIndex data raw.index).mapError .index
  return ⟨data, index.val, index.property⟩

/-- Exact restoration from the checked saved index; no second cursor scan. Association is a mathematical input to this
internal loader, not a hash. -/
@[expose] def Checked.restore {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (checked : Checked)
    (edge : PreparedConstantModels.PreparedEdge curve differential)
    (associated : checked.data = metadata edge) :
    { state : (edge.coefficient 0 edge.baseInside).name.process.State //
      state = edge.readingState 0 edge.baseInside } :=
  let same := checked.index_eq.trans
    ((congrArg Metadata.readingIndex associated).trans (readingIndex_eq edge))
  ⟨stateOfIndex edge checked.index same, stateOfIndex_eq edge checked.index same⟩

/-- Check the saved center value using the original prepared edge and its associated sample.

Success retains equality to the complete canonical center state, including its original owner and cached data. -/
@[expose] def Checked.restoreCenter {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (checked : Checked)
    (edge : PreparedConstantModels.PreparedEdge curve differential)
    (associated : checked.data = metadata edge) (sample : Sample edge) (value : Gaussian) :
    Except Invalidity { center : PreparedConstantModels.PreparedEdge.CenterState edge //
      center = PreparedConstantModels.PreparedEdge.CenterState.canonical edge } :=
  checkCenter edge checked.data associated ⟨checked.index, checked.index_eq⟩ sample value

/-- Consume a checked prefix of the actual source track. No denominator association or equality to a replacement refiner
is asked of the caller. -/
@[expose] def Checked.restoreFromCursor {genus : Nat}
    {curve : Hyperelliptic.Basic.HyperellipticCurve genus}
    {differential : Differentials.Basic.Differential genus}
    (checked : Checked)
    (edge : PreparedConstantModels.PreparedEdge curve differential)
    (associated : checked.data = metadata edge)
    (cursor : QuadraticTrackSampleReplay.Cursor
      (edge.directQueryOwner 0 edge.baseInside).track
      (metadata edge).sampleIndex)
    (value : Gaussian) :
    Except Invalidity { center : PreparedConstantModels.PreparedEdge.CenterState edge //
      center = PreparedConstantModels.PreparedEdge.CenterState.canonical edge } :=
  checked.restoreCenter edge associated
    (QuadraticTrackSampleReplay.centerSample edge cursor) value

section Driver

open Purelib.Riemann
open Purelib.Riemann.Transport Purelib.Riemann.RootContinuation
open Purelib.Riemann.Branches Purelib.Riemann.Integration Purelib.Riemann.Topology

variable {genus : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {differential : Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}
  (edge : PreparedConstantModels.PreparedEdge curve differential)

set_option genInjectivity false in
/-- A typed center invalidity or inconclusive source-track sample attempt. -/
inductive RunFailure where
  /-- The invalid cursor or quotient-product certificate. -/ | center (failure : Invalidity)
  /-- The retained inconclusive sample attempt on the original source track. -/ | sample (failure :
    QuadraticSampleCheckpoint.Stopped
      (edge.directQueryOwner 0 edge.baseInside).track (metadata edge).sampleIndex)

constructive_injectivity RunFailure

/-- Serialize the exact cursor, quotient-product or sample failure evidence. -/
@[expose] def RunFailure.report : RunFailure edge → Json
  | .center (.cursor saved expected _) => Json.mkObj
      [("kind", toJson "invalid center reading index"),
       ("saved", toJson saved), ("expected", toJson expected)]
  | .center (.quotient saved expected _) => Json.mkObj
      [("kind", toJson "invalid center quotient product"),
       ("actualProduct", toJson (gaussianData saved)),
       ("expectedNumerator", toJson (gaussianData expected))]
  | .sample failure => failure.report _

/-- Generate the numerical quotient from the supplied numerator and denominator. -/
@[expose, noinline] def generateValue (numerator denominator : Gaussian) : Data.Gaussian.Basic.Canonical :=
  dbg_trace "CENTER_QUOTIENT_GENERATOR_FORCED"
  numerator / denominator

/-- The source edge and its checked-first-attempt law come from the original preparation. Disk metadata never
establishes that association. Completed sample proposals and the quotient are checked without regenerating them; the
result retains equality to the entire original center state. -/
@[expose] def run (ready : QuadraticTrackReplay.Ready (edge.directQueryOwner 0 edge.baseInside))
    (plan : IO (QuadraticFallbackReplay.Plan (edge.directQueryOwner 0 edge.baseInside).track))
    (control : RootRefinementCheckpoint.Control) (directory : System.FilePath) :
    m (Except (RunFailure edge)
      {center : PreparedConstantModels.PreparedEdge.CenterState edge //
        center = PreparedConstantModels.PreparedEdge.CenterState.canonical edge}) := do
  IO.FS.createDirAll directory
  let data := metadata edge
  let cursorPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("center-cursor.json")))
  let raw ← if ← cursorPath.pathExists then loadJson cursorPath else do
    if control.savedOnly then throw (IO.userError "missing center cursor; generation forbidden")
    let raw := cursor data
    saveJson cursorPath raw
    pure raw
  unless toJson raw.metadata == toJson (encode data) do
    saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request.json")))) (raw.metadata,
      encode data)
    throw (IO.userError "center metadata differs from the source edge; both inputs retained")
  let outcome ← match checkIndex data raw.index with
    | .error failure => pure (.error (.center failure))
    | .ok index => do
      let sample ← QuadraticSampleCheckpoint.run
        (edge.directQueryOwner 0 edge.baseInside).track ready
        plan control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("sample")))) data.sampleIndex
      match sample with
      | .error failure => pure (.error (.sample failure))
      | .ok sample =>
        let denominator := sample.state.box.anchor
        let valuePath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("coefficient.json")))
        let value ← if ← valuePath.pathExists then do
          let saved : GaussianData ← loadJson valuePath
          checked "saved center coefficient" (decodeGaussian saved)
        else do
          if control.savedOnly then throw (IO.userError "missing center quotient; generation forbidden")
          let value := generateValue data.numerator denominator
          saveJson valuePath (gaussianData value)
          pure value
        let checkedCursor : Checked := ⟨data, index.val, index.property⟩
        pure ((checkedCursor.restoreFromCursor edge rfl sample value).mapError
          RunFailure.center)
  match outcome with
  | .error failure => saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk
    ("inconclusive-or-invalid.json")))) (failure.report edge)
  | .ok center =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("center-result.json"))))
        ("complete original center restored from source-associated sample", raw.index, gaussianData center.val.value)
      profile directory "COMPLETE original center restored; source equality retained"
  return outcome

end Driver

end CenterCheckpoint
