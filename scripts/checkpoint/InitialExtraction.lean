module
import Purelib.Data.Int.Order

import Purelib.System.IO
import Purelib.System.FilePath

meta import Purelib.Elab.ConstructiveInjectivity
meta import Purelib.Elab.Deriving.Json
import Purelib.Data.Json.Codec
import Purelib.Data.Json.Basic
import Purelib.Data.String.Basic
import scripts.checkpoint.RootState
import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Block
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic
import Purelib.Polynomial.Elimination.Axis.Certificate
import Purelib.Polynomial.Winding.Box.Basic
import Purelib.Polynomial.Winding.Box.Nonnegative.Squarefree
import Purelib.Polynomial.Winding.Box.Region.Selection
import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.RootIsolation.Exact.Build
import Purelib.RootIsolation.Exact.LargeSquare
import Purelib.RootIsolation.Exact.Run
import Purelib.RootIsolation.Exact.State
import Purelib.RootIsolation.Exact.Step
import Purelib.RootIsolation.Isolation.InitialExtractionReplay
import Purelib.RootIsolation.Newton.Band.Basic
import Purelib.RootIsolation.Newton.Band.Build
public import Purelib.RootIsolation.Newton.Band.Replay
public import Purelib.RootIsolation.Newton.Band.State.Replay
import Purelib.RootIsolation.Newton.Extraction.Basic
import Purelib.RootIsolation.Newton.Extraction.Build
public import Purelib.RootIsolation.Newton.Extraction.Replay
import Purelib.RootIsolation.Newton.Extraction.Source
public import Purelib.RootIsolation.Newton.Extraction.Source.Replay
import Purelib.RootIsolation.Refinement.Basic
import Purelib.RootIsolation.State.Raw
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.RootIsolation.Subdivision.Raw.Iteration.Forward
import Purelib.RootIsolation.Subdivision.Raw.Rebase
import Purelib.RootIsolation.Track.Newton.Refinement
import Purelib.Geometry.Rational.Box.Sample.Five
import Purelib.Polynomial.Clearance.Box.Grid.Four.Replay
public import Purelib.RootIsolation.Exact.Extraction.Replay
import Purelib.RootIsolation.Exact.LargeSquare.Region
public import Purelib.RootIsolation.Exact.LargeSquare.Replay
public import Purelib.RootIsolation.Exact.Replay
public import Purelib.RootIsolation.Exact.Run.Replay
public import Purelib.RootIsolation.Exact.Step.Replay
import Purelib.RootIsolation.Newton.Extraction.Initial.Build

public import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay
public import Purelib.RootIsolation.Isolation.InitialExtractionFallbackReplay
public import Purelib.RootIsolation.Isolation.RawSubdivisionReplay
public import scripts.checkpoint.RootRefinement
import Purelib.RootIsolation.Newton.Band.Prepare
import Purelib.RootIsolation.Newton.Band.State
import Purelib.RootIsolation.Newton.Extraction.Prepare
import Purelib.RootIsolation.Exact.Basic
import Purelib.Tactic.Ring
import Init.Core
import Init.Data.Int.Basic
public import Init.Data.Int.Order
import Init.Data.List.OfFn
import Init.Prelude
import Init.System.FilePath
import Init.System.IO
import Init.System.IOError
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Order.Defs.PartialOrder
import Purelib.CCL.Progressive.IntegrationQueries
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Compute
import Purelib.Polynomial.Clearance.Box.Boundary.Basic
import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Clearance.Box.Line.Elimination.Provider
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Multiplication
import Purelib.RootIsolation.Exact.Extraction
import Purelib.RootIsolation.Newton.Search.Trace
import Purelib.RootIsolation.State.Raw.FromRegion
import Purelib.RootIsolation.State.WindingOne.Raw
import Purelib.RootIsolation.Track.Basic
import scripts.checkpoint.Integration

open Purelib

open Purelib.Geometry.Rational.Box.Sample

open Purelib.LinearAlgebra

open Purelib.LinearAlgebra.PolynomialMatrix.Inverse

open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled

open Purelib.Polynomial

open Purelib.Polynomial.Clearance.Box

open Purelib.Polynomial.Clearance.Box.Grid.Four

open Purelib.Polynomial.Dense.Gaussian.Bounds

open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic

open Purelib.Polynomial.Winding.Box

open Purelib.Polynomial.Winding.Box.Region

open Purelib.RootIsolation

open Purelib.RootIsolation.Exact

open Purelib.RootIsolation.Exact.Extraction

open Purelib.RootIsolation.Exact.LargeSquare

open Purelib.RootIsolation.Exact.Run

open Purelib.RootIsolation.Exact.State

open Purelib.RootIsolation.Exact.Step

open Purelib.RootIsolation.Isolation

open Purelib.RootIsolation.State

open Purelib.RootIsolation.Subdivision.Raw

open Purelib.RootIsolation.Subdivision.Raw.Iteration

open Purelib.RootIsolation.Track.Newton

open Purelib.Data (Json)
open scoped Purelib.Data.String
open Purelib.Data.Json (toJson)

public section

/-!
Incremental checkpoint driver for the canonical five-seed initial extractor.
Every seed uses the shared checked proposal, winding and clearance loaders.
The supplied clearance loader restores the original constructors, including
separated-Sylvester coefficients for the canonical initial extractor.
Both the seed path and the total Newton-band fallback reconstruct the exact
original isolation step, retaining all attempted seeds and subdivision stages.
-/

/-!
Atomic stage checkpoints for the existing polynomial inverse recursion.
Reload checks local arithmetic and exact parent ownership. It does not run
the recursive producer; the arithmetic checks themselves are not cached.
The matrix dimension bounds both recursion and decoded row lengths.
-/

namespace PolynomialInverseCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]

open IntegrationCheckpoint
open Purelib.LinearAlgebra.PolynomialMatrix
open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay

/-- The exact Gaussian-rational coefficient carrier. -/
abbrev Gaussian := Data.Gaussian.Basic.Canonical
/-- Serialized matrix rows containing ordered lists of exact Gaussian polynomial coefficients. -/
abbrev RawMatrix := List (List (List GaussianData))

/-- Serialize the retained polynomial coefficients in their original order. -/
@[expose] def polynomialData (value : PolynomialMatrix.Basic.Polynomial Gaussian) : List GaussianData :=
  value.coeffs.map gaussianData

/-- Serialize the exact square matrix in finite row and column order. -/
@[expose] def matrixData {n : Nat} (value : PolynomialMatrix.Basic.Matrix Gaussian n) : RawMatrix :=
  List.ofFn fun row => List.ofFn fun column => polynomialData (value row column)

set_option genInjectivity false in
/-- The serialized scalar and polynomial matrix of a scaled inverse.

The scalar polynomial and inverse matrix retain their original ordered
coefficient encodings. Verification checks the supplied inverse equations
without selecting a new polynomial or matrix. -/
structure RawInverse where
  /-- The exact serialized polynomial scaling factor. -/ scalar : List GaussianData
  /-- The serialized retained inverse matrix. -/ inverse : RawMatrix
deriving Json.ToJson, Json.FromJson

constructive_injectivity RawInverse

/-- Serialize the original scaled inverse without recomputing its recursive construction. -/
@[expose] def inverseData {n : Nat} (value : Scaled.Basic.ScaledInverseData Gaussian n) : RawInverse :=
  ⟨polynomialData value.scalar, matrixData value.inverse⟩

/-- Decode a list at its exact expected length, rejecting missing or excess matrix entries. -/
@[expose] def vectorFromList {α : Type} : (n : Nat) → List α → Except InvalidData (Data.Vector α n)
  | 0, [] => .ok .nil
  | 0, _ :: _ => .error (.syntax "excess matrix entries")
  | _ + 1, [] => .error (.syntax "missing matrix entries")
  | n + 1, head :: tail => do return .cons head (← vectorFromList n tail)

/-- Decode every exact Gaussian coefficient of the retained polynomial. -/
@[expose] def decodePolynomial (raw : List GaussianData) : Except InvalidData (PolynomialMatrix.Basic.Polynomial
  Gaussian) := do
  return ⟨← raw.mapM decodeGaussian⟩

/-- Decode a square polynomial matrix and check each row and column count. -/
@[expose] def decodeMatrix (n : Nat) (raw : RawMatrix) : Except InvalidData (PolynomialMatrix.Basic.Matrix Gaussian n)
  := do
  let rows ← raw.mapM fun row => do
    let entries ← row.mapM decodePolynomial
    vectorFromList n entries
  vectorFromList n rows

/-- Decode the retained scalar and square inverse matrix at the original dimension. -/
@[expose] def decodeInverse (n : Nat) (raw : RawInverse) : Except InvalidData (Scaled.Basic.ScaledInverseData Gaussian
  n) := do
  return ⟨← decodePolynomial raw.scalar, ← decodeMatrix n raw.inverse⟩

/-- Serialize the exact failed scalar-product or matrix-entry equation. -/
@[expose] def invalidReport : Replay.Invalid Gaussian → Json
  | .scalar actual expected _ => Json.mkObj
      [("condition", toJson "canonical scalar product"),
       ("actual", toJson (polynomialData actual)), ("expected", toJson (polynomialData expected))]
  | .entries actual expected _ => Json.mkObj
      [("condition", toJson "canonical matrix entries"),
       ("actual", toJson (matrixData actual)), ("expected", toJson (matrixData expected))]

/-- Return checked inverse data or persist both operands of the failed stage equation. -/
@[expose] def checkedArithmetic {α : Type} (directory : System.FilePath) (stage : String)
    (result : Except (Replay.Invalid Gaussian) α) : IO α := do
  match result with
  | .ok value => return value
  | .error failure =>
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"invalid-{stage}.json")))) (invalidReport
        failure)
      throw (IO.userError s!"invalid polynomial inverse {stage}; failed equation operands retained")

set_option genInjectivity false in
/-- The numbers of generated and reused completed polynomial checkpoints.

The counters retain separate generated and reused outcomes. Constructor
defaults initialize absent construction arguments; decoding still requires
every nonoptional serialized field. -/
structure Counts where
  /-- The number of newly written completed stages. -/ generated : Nat := 0
  /-- The number of validated retained stages reused. -/ reused : Nat := 0
deriving Json.ToJson, Json.FromJson

constructive_injectivity Counts

set_option genInjectivity false in
/-- Saved-only policy and interruption boundary for the original polynomial stages.

The two generated/reused counts are threaded by their own execution state;
configuration never allocates or aliases another counter family. -/
structure Control where
  /-- Forbid generation when a required completed stage is absent. -/ savedOnly : Bool
  /-- The optional completed-write count at which the interruption regression stops. -/ killAfterWrites : Option Nat

constructive_injectivity Control

/-- Error-preserving execution of the original two polynomial-stage counters.

Updated counts accompany both success and the original structured IO error. -/
abbrev Execution := ExceptT IO.Error (StateT Counts BaseIO)

/-- Return the completed original counter updates with the execution outcome. -/
@[expose] def Execution.run {Alpha : Type} (action : Execution Alpha) (counts : Counts) :
    BaseIO (Except IO.Error Alpha × Counts) := ExceptT.run action counts

/-- Execute the supplied original IO action once, preserving the polynomial counts. -/
@[expose] def Execution.liftIO {Alpha : Type} (action : IO Alpha) : Execution Alpha :=
  fun counts => do
    let result ← action.toBaseIO
    return (result, counts)

/-- Lift original IO effects into the separate polynomial-counter execution. -/
instance : MonadLift IO Execution := ⟨Execution.liftIO⟩

/-- Read only the exact polynomial-stage counter family. -/
@[expose] def Execution.counts [MonadStateOf Counts m] : m Counts := getThe Counts

/-- Apply one original update only to the polynomial-stage counter family. -/
@[expose] def Execution.update [MonadStateOf Counts m] (change : Counts → Counts) : m Unit := modifyThe Counts change

/-- Retain the requested replay policy without allocating reference state. -/
@[expose] def Control.create (savedOnly : Bool := false) (killAfterWrites : Option Nat := none) : IO Control :=
  pure ⟨savedOnly, killAfterWrites⟩

variable [MonadStateOf Counts m]

/-- Record a completed atomic stage and honor the requested interruption boundary. -/
@[expose] def wrote (control : Control) : m Unit := do
  Execution.update fun counts => { counts with generated := counts.generated + 1 }
  let counts ← Execution.counts
  if control.killAfterWrites == some counts.generated then
    (← IO.getStdout).flush
    let pid ← IO.Process.getPID
    discard <| Purelib.System.IO.Process.output { cmd := "/bin/kill", args := #["-KILL", toString pid] }
    throw (IO.userError "SIGKILL did not terminate polynomial checkpoint writer")

/-- Generate the original Schur complement with its diagnostic marker. -/
@[expose, noinline] def generateComplement {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix Gaussian (n + 1)) :
  PolynomialMatrix.Basic.Matrix Gaussian n :=
  dbg_trace "POLYNOMIAL_COMPLEMENT_GENERATOR_FORCED"
  PolynomialMatrix.Basic.schur matrix

/-- Generate the original scaled parent inverse from the retained child inverse. -/
@[expose, noinline] def generateParent {n : Nat} (matrix : PolynomialMatrix.Basic.Matrix Gaussian (n + 1))
    (child : Scaled.Basic.ScaledInverseData Gaussian n) : Scaled.Basic.ScaledInverseData Gaussian (n + 1) :=
  dbg_trace "POLYNOMIAL_PARENT_GENERATOR_FORCED"
  ⟨PolynomialMatrix.Basic.head matrix * child.scalar, Block.blockInverse matrix child⟩

open Purelib.LinearAlgebra.PolynomialMatrix.Inverse.Scaled.Replay in
/-- Restore the original recursive scaled inverse through checked local stages.

Validate the request matrix, Schur complement and parent equations; reuse completed stages and preserve the exact
recursive child owner. -/
@[expose] def run (control : Control) (directory : System.FilePath) :
    (n : Nat) → (matrix : PolynomialMatrix.Basic.Matrix Gaussian n) → m (Replay.Completed matrix)
  | 0, matrix => pure (Replay.base matrix)
  | n + 1, matrix => do
      IO.FS.createDirAll directory
      let requestPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("matrix-v1.json")))
      if ← requestPath.pathExists then
        let raw : RawMatrix ← loadJson requestPath
        let saved ← checked "polynomial matrix request" (decodeMatrix (n + 1) raw)
        discard <| checkedArithmetic directory "request" (Replay.checkMatrix saved matrix)
      else
        if control.savedOnly then throw (IO.userError "missing matrix request; generation forbidden")
        saveJson requestPath (matrixData matrix)
      let complementPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("complement-v1.json")))
      let complement ← if ← complementPath.pathExists then do
          let raw : RawMatrix ← loadJson complementPath
          let value ← checked "polynomial complement" (decodeMatrix n raw)
          Execution.update fun counts => { counts with reused := counts.reused + 1 }
          pure value
        else do
          if control.savedOnly then throw (IO.userError "missing complement; generation forbidden")
          let value := generateComplement matrix
          saveJson complementPath (matrixData value)
          wrote control
          pure value
      let complement ← checkedArithmetic directory "complement" (checkComplement matrix complement)
      let child ← run control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("child")))) n complement.val
      let parentPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("inverse-v1.json")))
      let parent ← if ← parentPath.pathExists then do
          let raw : RawInverse ← loadJson parentPath
          let value ← checked "polynomial inverse" (decodeInverse (n + 1) raw)
          Execution.update fun counts => { counts with reused := counts.reused + 1 }
          pure value
        else do
          if control.savedOnly then throw (IO.userError "missing inverse; generation forbidden")
          let value := generateParent matrix child.val
          saveJson parentPath (inverseData value)
          wrote control
          pure value
      checkedArithmetic directory "inverse" (Replay.restore matrix complement child parent)

end PolynomialInverseCheckpoint

namespace RawSubdivisionCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]
variable [MonadStateOf PolynomialInverseCheckpoint.Counts m]

open IntegrationCheckpoint

set_option genInjectivity false in
/-- Serialized original safe-cut coordinates and reciprocal bounds.

The four retained rational encodings remain separate coordinate and geometry
readings. Scalar checks reconstruct their exact values without identifying
unrelated horizontal and vertical bounds. -/
structure Data where
  /-- The original vertical cut coordinate. -/ x : FractionData
  /-- The original horizontal cut coordinate. -/ y : FractionData
  /-- The retained vertical reciprocal bound. -/ vertical : FractionData
  /-- The retained horizontal reciprocal bound. -/ horizontal : FractionData
deriving Json.ToJson, Json.FromJson

constructive_injectivity Data

/-- Serialize all four exact raw-subdivision stage values. -/
@[expose] def encode (data : Replay.Data) : Data :=
  ⟨fractionData data.x, fractionData data.y, fractionData data.vertical, fractionData data.horizontal⟩

/-- Decode the four retained raw-subdivision stage values. -/
@[expose] def decode (data : Data) : Except InvalidData Replay.Data := do
  return ⟨← decodeFraction data.x, ← decodeFraction data.y,
    ← decodeFraction data.vertical, ← decodeFraction data.horizontal⟩

/-- Serialize a failed canonical-cut or original reciprocal equation with its exact operands. -/
@[expose] def invalidReport : Replay.Invalid → Json
  | .coordinate vertical actual expected _ => Json.mkObj
      [("kind", toJson "noncanonical safe cut"), ("vertical", toJson vertical),
       ("actual", toJson (fractionData actual)), ("expected", toJson (fractionData expected))]
  | .reciprocal vertical bound majorant product _ _ => Json.mkObj
      [("kind", toJson "original reciprocal identity violated"), ("vertical", toJson vertical),
       ("bound", toJson (fractionData bound)), ("majorant", toJson (fractionData majorant)),
       ("product", toJson (fractionData product)), ("expected", toJson (fractionData 1))]

/-- The shared atomic stage policy and counters used by subdivision replay. -/
abbrev Control := PolynomialInverseCheckpoint.Control

variable {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient :
  Purelib.Geometry.Rational.Box} {degreeBound : Nat}
  (elimination : Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts.AxisEliminationCertificate p
    degreeBound)

/-- Generate the original coefficient-selected safe cuts and reciprocal bounds. -/
@[expose, noinline] def generate (state : Raw.RawWindingState p ambient) : Replay.Data :=
  dbg_trace "RAW_SUBDIVISION_GRID_GENERATOR_FORCED"
  Replay.capture elimination state.box state.proper

/-- Serialize the exact polynomial, ambient box, current state and remaining subdivision depth. -/
@[expose] def request (state : Raw.RawWindingState p ambient) (remaining : Nat) : Json :=
  Json.mkObj
    [("polynomial", toJson (p.coeffs.map gaussianData)),
     ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
     ("box", toJson (RootStateCheckpoint.boxData state.box)),
     ("boundary", toJson (fractionData state.clearance.bound)),
     ("remaining", toJson remaining)]

/-- Each saved stage retains the original cut coordinates and reciprocal bounds. Replay still checks finite cut
selection, majorants and winding; it does not force the recursive subdivision producer or regenerate bounds. -/
@[expose] def run (control : Control) (directory : System.FilePath) :
    (remaining : Nat) → (state : Raw.RawWindingState p ambient) →
      m {result : Raw.RawWindingState p ambient // result = Forward.refineForwardN elimination remaining state}
  | 0, state => pure ⟨state, rfl⟩
  | remaining + 1, state => do
      IO.FS.createDirAll directory
      let header := request state (remaining + 1)
      let requestPath := (Purelib.System.FilePath.join directory (System.FilePath.mk ("request-v1.json")))
      if ← requestPath.pathExists then
        let actual : Json ← loadJson requestPath
        unless actual == header do
          saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request.json")))) (Json.mkObj
            [("kind", toJson "saved raw subdivision request differs"), ("actual", actual), ("expected", header)])
          throw (IO.userError "raw subdivision request mismatch; exact operands retained")
      else
        if control.savedOnly then throw (IO.userError "raw subdivision request absent; generation forbidden")
        saveJson requestPath header
      let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("grid-v1.json")))
      let saved ← if ← path.pathExists then do
          let raw : Data ← loadJson path
          let data ← checked "raw subdivision grid" (decode raw)
          PolynomialInverseCheckpoint.Execution.update fun counts => { counts with reused := counts.reused + 1 }
          pure data
        else do
          if control.savedOnly then throw (IO.userError "raw subdivision grid absent; generation forbidden")
          let data := generate elimination state
          saveJson path (encode data)
          PolynomialInverseCheckpoint.wrote control
          pure data
      let checkedGrid ← match Replay.check elimination state.box state.proper saved with
        | .ok grid => pure grid
        | .error failure =>
            saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-grid.json"))))
              (invalidReport failure)
            throw (IO.userError "raw subdivision grid rejected; violated equation retained")
      let next := RawSubdivisionReplay.step elimination state checkedGrid
      let tail ← run control ((Purelib.System.FilePath.join directory (System.FilePath.mk ("next")))) remaining next
      return ⟨tail.val, RawSubdivisionReplay.advance_eq elimination state checkedGrid remaining tail.val tail.property⟩

end RawSubdivisionCheckpoint

namespace NewtonExtractionCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]
variable [MonadStateOf PolynomialInverseCheckpoint.Counts m]

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction renaming Rational -> Coordinate
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.Raw (RawWindingState)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)

open Purelib.RootIsolation.Newton.Extraction

variable {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
  (squarefree : SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
  (current : RawWindingState p ambient) (epsilon : Coordinate) (positive : 0 < epsilon)

/-- The original threshold and subdivision count determine the saved source request; the exact ownership equation is
carried into the local extraction. -/
@[expose] def source (control : RawSubdivisionCheckpoint.Control) (directory : System.FilePath) :
    m {value : Newton.Extraction.Source.SourceOutput squarefree current epsilon //
      value = Newton.Extraction.Source.selectSource squarefree elimination current positive} := do
  IO.FS.createDirAll directory
  let initial := Rebase.initial current
  let depth := Newton.Extraction.Source.Replay.depth squarefree current epsilon
  IntegrationCheckpoint.saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("source-budget.json"))))
    (Json.mkObj
    [("depth", toJson depth), ("epsilon", toJson (IntegrationCheckpoint.fractionData epsilon)),
     ("threshold", toJson (IntegrationCheckpoint.fractionData (Newton.Extraction.Source.Replay.threshold squarefree
       current epsilon)))])
  let restored ← RawSubdivisionCheckpoint.run elimination control ((Purelib.System.FilePath.join directory
    (System.FilePath.mk ("subdivision")))) depth initial
  return ⟨Newton.Extraction.Source.Replay.source squarefree elimination current epsilon positive restored,
    Newton.Extraction.Source.Replay.source_eq squarefree elimination current epsilon positive restored⟩

/-- Restore the original Newton extraction from its exact coefficient-selected source. -/
@[expose] def core (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (control : RawSubdivisionCheckpoint.Control) (directory : System.FilePath) :
    m {value : Newton.Extraction.Basic.Output squarefree current epsilon //
      value = Newton.Extraction.Build.extract degreeAtLeastTwo squarefree elimination current positive} := do
  let saved ← source squarefree elimination current epsilon positive control directory
  return ⟨Newton.Extraction.Prepare.fromSource degreeAtLeastTwo squarefree current positive saved.val,
    Newton.Extraction.Replay.fromSource_eq degreeAtLeastTwo squarefree elimination current positive saved.val
      saved.property⟩

/-- Restore the original Newton band from the retained exact extraction core. -/
@[expose] def band (degreeAtLeastTwo : 2 ≤ p.natDegree)
    (control : RawSubdivisionCheckpoint.Control) (directory : System.FilePath) :
    m {value : Newton.Band.Basic.Output squarefree current epsilon //
      value = Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current positive} := do
  let saved ← core squarefree elimination current epsilon positive degreeAtLeastTwo control directory
  return ⟨Newton.Band.Prepare.fromCore degreeAtLeastTwo squarefree elimination current positive saved,
    Newton.Band.Replay.fromCore_eq degreeAtLeastTwo squarefree elimination current positive saved⟩

/-- Restore the original complete track-refinement state, including the ambient clearances consumed by branch-grid
construction. -/
@[expose] def refineState {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
    (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree :
      SquarefreeCertificate p)
    (elimination : AxisEliminationCertificate p degreeBound)
    (current : WindingOne.Basic.WindingOneState p ambient) (epsilon : Coordinate) (positive : 0 < epsilon)
    (control : RawSubdivisionCheckpoint.Control) (directory : System.FilePath) :
    m {value : WindingOne.Basic.WindingOneState p ambient //
      value = Refinement.refineState degreeAtLeastTwo squarefree elimination current epsilon positive} := do
  let saved ← band squarefree elimination current.raw epsilon positive degreeAtLeastTwo control directory
  return ⟨Newton.Band.State.state squarefree current epsilon saved.val,
    Newton.Band.State.Replay.state_eq degreeAtLeastTwo squarefree elimination current epsilon positive saved.val
      saved.property⟩

end NewtonExtractionCheckpoint

namespace InitialExtractionCheckpoint

variable {m : Type → Type} [Monad m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadExceptOf IO.Error m]
variable [MonadStateOf RootRefinementCheckpoint.Counts m]

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Data.Rat.Fraction renaming Rational -> Coordinate
open Purelib.Geometry.Rational (Box)
open _root_.Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients renaming CoefficientPolynomial ->
  GaussianPolynomial
open Purelib.Polynomial.Elimination.Axis.Certificate.AxisSafeCuts (AxisEliminationCertificate)
open Purelib.RootIsolation.State.Raw (RawWindingState)
open Purelib.Polynomial.Dense.Gaussian.Squarefree.Basic (SquarefreeCertificate)
open Purelib.RootIsolation.Exact.Basic (Output)

open IntegrationCheckpoint RootRefinementCheckpoint

variable {p : GaussianPolynomial} {ambient : Box} {degreeBound : Nat}
  (elimination : AxisEliminationCertificate p degreeBound)
  (current : RawWindingState p ambient) (epsilon : Coordinate)
  (loader : ClearanceLoader elimination (.canonical elimination) m)

/-- Serialize the original root box and boundary plus ambient-line clearances. -/
@[expose] def stateData (state : WindingOne.Basic.WindingOneState p ambient) : Json :=
  Json.mkObj
    [("box", toJson (RootStateCheckpoint.boxData state.box)),
     ("bounds", toJson
       ([state.clearance.bound, state.ambientLeftClearance.bound, state.ambientRightClearance.bound,
         state.ambientBottomClearance.bound, state.ambientTopClearance.bound].map fractionData))]

/-- Try original seeds in order and retain every failed trace before the first success. -/
@[expose] def seeds (control : Control) (directory : System.FilePath) :
    (values : List Gaussian) → (index : Nat) →
      m ((value : Option (RootIsolation.Refinement current epsilon)) ×
        InitialExtractionReplay.Trace elimination current epsilon values value)
  | [], _ => pure ⟨none, .exhausted⟩
  | seed :: rest, index => do
      let trial ← RootRefinementCheckpoint.runFrom elimination current epsilon
        (.canonical elimination) seed loader control ((Purelib.System.FilePath.join directory (System.FilePath.mk
          (s!"seed-{index}"))))
      match found : trial.finished.value with
      | some value => return ⟨some value, .accepted trial.finished value found⟩
      | none =>
          let tail ← seeds control directory rest (index + 1)
          return ⟨tail.1, .missed trial.finished found tail.2⟩

/-- Serialize every retained seed attempt in its original order. -/
@[expose] def traceReport {values : List Gaussian} {value : Option (RootIsolation.Refinement current epsilon)} :
    InitialExtractionReplay.Trace elimination current epsilon values value → List Json
  | .exhausted => []
  | .accepted trial _ _ => [finishedReport _ _ _ _ _ trial]
  | .missed trial _ tail => finishedReport _ _ _ _ _ trial :: traceReport tail

/-- Replay the original five-seed initial extraction request.

Validate exact polynomial, boxes, tolerance and seed order; retain all attempted traces and leave a total fallback
explicit when finite seeds miss. -/
@[expose] def run (control : Control) (directory : System.FilePath) :
    m (InitialExtractionReplay.Replay elimination current epsilon) := do
  IO.FS.createDirAll directory
  let values := Five.seeds current.box
  let header := Json.mkObj
    [("format", toJson "ccl-initial-extraction-v1"),
     ("polynomial", toJson (p.coeffs.map gaussianData)),
     ("ambient", toJson (RootStateCheckpoint.boxData ambient)),
     ("box", toJson (RootStateCheckpoint.boxData current.box)),
     ("epsilon", toJson (fractionData epsilon)),
     ("seeds", toJson (values.map gaussianData)),
     ("proposalsPerSeed", toJson (6 : Nat))]
  let path := (Purelib.System.FilePath.join directory (System.FilePath.mk ("request.json")))
  if ← path.pathExists then
    let saved : Json ← loadJson path
    unless saved == header do
      saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("invalid-request.json")))) (saved, header)
      throw (IO.userError "initial extraction request differs; both exact requests retained")
  else
    if control.savedOnly then throw (IO.userError "missing initial extraction request; generation forbidden")
    saveJson path header
  let result ← seeds elimination current epsilon loader control directory values 0
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("result.json")))) (Json.mkObj
    [("kind", toJson (if result.1.isSome then "accepted: first successful canonical seed"
        else "all five bounded seeds missed; canonical total fallback required")),
     ("tried", toJson result.2.tried),
     ("trials", toJson (traceReport elimination current epsilon result.2))])
  return ⟨result.1, result.2⟩

variable (degreeAtLeastTwo : 2 ≤ p.natDegree) (squarefree : SquarefreeCertificate p)

section Steps

variable (state : IsolationState p ambient)
  (nonnegative : ∀ region ∈ state.regions, 0 ≤ Purelib.Polynomial.Winding.Box.Basic.quadrupledBoxWinding p region.box)
  (positive : 0 < Purelib.Polynomial.Winding.Box.Region.Sum.totalRaw state.regions)

/-- Restore both canonical extraction branches. The total branch reuses checked raw-subdivision stages and the original
Newton band. -/
@[expose] def step (control : Control) (directory : System.FilePath) :
    m {value : Step.StepResult state // value = Step.step
      degreeAtLeastTwo squarefree elimination state nonnegative positive} := do
  let selection := Selection.selectPositive state.regions nonnegative positive
  let current := selection.selected.raw (fun zero => Data.Int.Order.lt_irrefl 0 (zero ▸ selection.positive))
  let replay ← run elimination current 1 loader control directory
  let value : {value : RootIsolation.Refinement current 1 //
      value = Newton.Extraction.Initial.Build.extract degreeAtLeastTwo squarefree elimination current (by decide)} ←
    match found : replay.value with
    | some value => pure ⟨value, (InitialExtractionReplay.extract_eq elimination current 1
        degreeAtLeastTwo squarefree (by decide) replay value found).symm⟩
    | none => do
        let fallbackControl ← PolynomialInverseCheckpoint.Control.create control.savedOnly control.killAfterWrites
        let fallbackAction : PolynomialInverseCheckpoint.Execution
            { value : Newton.Band.Basic.Output squarefree current 1 //
              value = Newton.Band.Build.extract degreeAtLeastTwo squarefree elimination current
                (by decide : (0 : Coordinate) < 1) } :=
          NewtonExtractionCheckpoint.band squarefree elimination current 1 (by decide)
            degreeAtLeastTwo fallbackControl ((Purelib.System.FilePath.join directory (System.FilePath.mk
              ("fallback"))))
        let (fallbackResult, fallbackCounts) ← PolynomialInverseCheckpoint.Execution.run fallbackAction {}
        let saved ← (@IO.ofExcept IO.Error _ ⟨Purelib.System.IO.Error.toString⟩) fallbackResult
        saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("fallback-counts.json")))) fallbackCounts
        pure ⟨InitialExtractionReplay.fallback degreeAtLeastTwo squarefree elimination current 1 (by decide) saved,
          InitialExtractionReplay.fallback_eq degreeAtLeastTwo squarefree elimination current 1
            (by decide) replay found saved⟩
  let input : Replay.StepInput
      degreeAtLeastTwo squarefree elimination state nonnegative positive :=
    { selection := selection
      selection_eq := rfl
      extracted := Replay.extraction degreeAtLeastTwo squarefree elimination
        selection.selected selection.positive value.val
      extracted_eq := Replay.extraction_eq degreeAtLeastTwo squarefree elimination
        selection.selected selection.positive value.val value.property }
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("extracted-state.json")))) (stateData
    value.val.state)
  saveJson ((Purelib.System.FilePath.join directory (System.FilePath.mk ("completed.json")))) (Json.mkObj
    [("kind", toJson (if replay.value.isSome then "canonical seed extraction" else
      "canonical total Newton-band fallback")),
     ("state", stateData value.val.state)])
  return ⟨input.restore, input.restore_eq⟩

end Steps

/-- Every successful return reconstructs the complete original run. Invalid saved data still stops at its checked
witness, and unfinished work stays on disk. -/
@[expose] def runIsolation (control : Control) (directory : System.FilePath) :
    (remaining : Nat) → (state : State.IsolationState p ambient) →
      (total : Region.Sum.totalRaw state.regions = (4 : Int) * remaining) → (index : Nat) →
      m {result : Run.RunResult state remaining // result =
        Run.run degreeAtLeastTwo squarefree elimination remaining state total}
  | 0, state, total, _ =>
      pure ⟨
        { final := state
          support_final := rfl
          totalRaw_final := by simpa only [Int.natCast_zero, mul_zero] using total
          tracks_length_final := (Nat.add_zero _).symm }, rfl⟩
  | remaining + 1, state, total, index => do
      have positive : 0 < Region.Sum.totalRaw state.regions := by
        rw [total]
        exact Data.Int.Order.mul_pos (by decide) (Data.Int.Order.natCast_pos (Nat.zero_lt_succ remaining))
      have nonnegative : ∀ region ∈ state.regions, 0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
        intro region _member
        exact Nonnegative.Squarefree.quadrupledBoxWinding_nonnegative degreeAtLeastTwo squarefree elimination
          region.refinesAmbient region.proper region.clearance
      let first ← step elimination loader degreeAtLeastTwo squarefree state nonnegative positive
        control ((Purelib.System.FilePath.join directory (System.FilePath.mk (s!"step-{index}"))))
      have nextTotal : Region.Sum.totalRaw first.val.next.regions = (4 : Int) * remaining := by
        rw [first.val.totalRaw_next, total, Nat.cast_succ]
        ring1
      let tail ← runIsolation control directory remaining first.val.next nextTotal (index + 1)
      return ⟨Replay.join first.val remaining tail.val,
        Replay.join_eq degreeAtLeastTwo squarefree elimination remaining total
          nonnegative positive first.val first.property nextTotal tail.val tail.property⟩

/-- Restore the exact original root family from a certified clear region and winding count. -/
@[expose] def isolateFromRegion (initial : Region.ClearRegion p ambient) (count : Nat)
    (raw : Winding.Box.Basic.quadrupledBoxWinding p initial.box = (4 : Int) * count)
    (control : Control) (directory : System.FilePath) :
    m {result : Output p ambient count // result =
      Build.isolateFromRegion degreeAtLeastTwo squarefree elimination initial count raw} := do
  have total : Region.Sum.totalRaw (IsolationState.initial initial).regions = (4 : Int) * count := by
    change Winding.Box.Basic.quadrupledBoxWinding p initial.box + 0 = _
    rw [raw, add_zero]
  let result ← runIsolation elimination loader degreeAtLeastTwo squarefree control directory count
    (IsolationState.initial initial) total 0
  return ⟨Replay.output degreeAtLeastTwo squarefree elimination initial count result.val,
    Replay.output_eq degreeAtLeastTwo squarefree elimination initial count raw total
      result.val result.property⟩

/-- Restore the original coefficient-selected complete root family. -/
@[expose] def isolateLargeSquare (control : Control) (directory : System.FilePath) :
    m {result : Output p (RootRadius.Box.largeSquareBox p) p.natDegree // result =
      LargeSquare.isolateLargeSquare degreeAtLeastTwo squarefree elimination} := do
  let result ← isolateFromRegion elimination loader degreeAtLeastTwo squarefree
    (Region.largeSquareRegion degreeAtLeastTwo) p.natDegree
    (Region.largeSquareRegion_winding degreeAtLeastTwo) control directory
  return ⟨result.val, result.property.trans
    (Replay.largeSquare_eq degreeAtLeastTwo squarefree elimination).symm⟩

end InitialExtractionCheckpoint
