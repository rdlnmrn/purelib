module

public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Interior
public import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Expression.Trace
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Expression
import Purelib.Riemann.RootContinuation.CoherentRoot.Chamber.Denominator
import Purelib.Approximation.Gaussian.Sequence.SamplePrefix
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.System.FilePath
import Purelib.System.IO
import scripts.checkpoint.Integration
import Init.System.IOError

/-! # Observations of genuine original prepared interior expression families -/

namespace TestPurelib.Riemann.RootContinuation.PowerInteriorRuntime

open Purelib
open Purelib.Riemann.RootContinuation.CoherentRoot.Chamber
open Purelib.RootIsolation.Progressive.Chamber.Frame (ChamberFrame)
open Purelib.RootIsolation.Progressive.Chamber.Path.Basic (ChamberPath)
open Purelib.RootIsolation.Progressive.Chamber.Overlap (ChamberOverlap)
open Purelib.Approximation.Gaussian
open Purelib.Approximation.Gaussian.Acquisition.Expression
open Purelib.Approximation.Gaussian.Acquisition.Expression.Checked.Geometric
open Purelib.Approximation.Gaussian.Enclosure (Ball)
open Purelib.Data.Rat.Fraction.Order.Arithmetic
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Json (toJson)
open Purelib.System.FilePath (join)
open IntegrationCheckpoint (fractionData gaussianData loadJson saveJson)
open InteriorStep (Inside)
open InteriorStep.Expression (Program)
open InteriorStep.Denominator (Kind)

/-- Persist one exact original request or observation, rejecting changes on checked reload. -/
private def persist (path : System.FilePath) (value : Data.Json) : IO Unit := do
  if ← path.pathExists then
    unless (← loadJson path) == value do
      throw (IO.userError "prepared interior request or observation differs from its retained original bytes")
  else saveJson path value

/-- Read the literal reciprocal originalExpr for the original root or ordered affine denominator. -/
private def expression (kind : Kind) : Checked.Expr 1 :=
  .inverse (kind.expression InteriorStep.Denominator.Point.atomIndex)

/-- Cache actual primitive expression observations at indices computed from its original geometric bound.

The two requests use the retained output scale and the exact original common
ball authenticated against that realization. Equal computed indices consume
one actual observation. The original coherent comparison and typed complete
construction remain retained; no residual sample identity is inferred from
the displayed equation of a root.
-/
private def observe {arity : Nat} {environment : Fin arity → Acquisition.Annotated}
    {originalExpr : Checked.Expr arity} (actual : Realization environment originalExpr)
    (bound : {ball : Ball // ball = actual.enclosing.ball})
    (directory : System.FilePath) : IO Unit := do
  let source := actual.enclosing.source
  let target := 8 * (source.errorScale + 1)
  have positive : 0 < target := mul_pos_direct (by decide)
    (add_pos_of_nonneg_of_pos_direct source.errorScale_nonneg (by decide))
  let retryTarget := 4 * (source.errorScale + 1)
  have retryPositive : 0 < retryTarget := mul_pos_direct (by decide)
    (add_pos_of_nonneg_of_pos_direct source.errorScale_nonneg (by decide))
  let index := source.toApproximation.refineIndex 0 target positive
  let retryIndex := source.toApproximation.refineIndex 0 retryTarget retryPositive
  let request := Data.Json.mkObj
    [("protocol", toJson "original-prepared-interior-expression-v1"),
     ("scale", toJson (fractionData source.errorScale)),
     ("ballCenter", toJson (gaussianData bound.val.center)),
     ("ballRadiusSq", toJson (fractionData bound.val.radiusSq)),
     ("start", toJson (0 : Nat)), ("targetSq", toJson (fractionData target)),
     ("retryTargetSq", toJson (fractionData retryTarget)),
     ("index", toJson index), ("retryIndex", toJson retryIndex)]
  IO.FS.createDirAll directory
  persist (join directory "request.json") request
  let value := source.sample index
  let retried := if retryIndex = index then value else source.sample retryIndex
  have retry_eq : retried = source.sample retryIndex := by
    dsimp only [retried]
    split
    · rename_i same
      exact congrArg source.sample same.symm
    · rfl
  let entries : List (Sequence.SamplePrefix.Entry source.toApproximation) :=
    [⟨index, value, rfl⟩, ⟨retryIndex, retried, retry_eq⟩]
  let cached := Sequence.SamplePrefix.ofEntries source.toApproximation entries
  let first := cached.view.sample index
  let second := cached.view.sample retryIndex
  unless bound.val.Contains first ∧ bound.val.Contains second ∧
      first = value ∧ second = retried do
    throw (IO.userError "prepared interior expression lost an actual bounded original cached observation")
  persist (join directory "observations.json") (Data.Json.mkObj
    [("request", request), ("value", toJson (gaussianData first)), ("retry", toJson (gaussianData second))])

/-- Inspect one actual specialization while preserving its typed exact-zero or finite missing-evidence distinction. -/
private def checkAssessment {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
    {source : Root start index} {target : Root middle (step.matching.forward index)}
    {piece : InteriorStep step index source target} {originalExpr : Checked.Expr 1}
    {program : Program piece originalExpr}
    {time : Rational} {inside : Inside time} (assessment : program.Assessment time inside)
    (directory : System.FilePath) : IO Unit :=
  match assessment.result with
  | .missing _ => throw (IO.userError "prepared interior expression retains missing original used-leaf geometry")
  | .specialized actual =>
      match completed : actual.result with
      | .completed value =>
          match positive : assessment.bounds.result with
          | .prepared common => do
              have sameBall := actual.completed_ball positive completed
              unless value.enclosing.ball.center = common.ball.center ∧
                  value.enclosing.ball.radiusSq = common.ball.radiusSq do
                throw (IO.userError "prepared interior output lost its retained common programme ball")
              observe value ⟨common.ball, sameBall.symm⟩ directory
          | .requested _ =>
              throw (IO.userError "a requested common programme returned an uncertified completion")
      | .invalid _ => throw (IO.userError "prepared interior expression retains an actual exact-zero denominator")
      | .requested _ => throw (IO.userError "prepared interior expression retains a finite original clearance request")

/-- The two endpoint point computations retained as actual shared data. -/
private abbrev EndpointPoints {start middle : ChamberFrame} {step : ChamberOverlap start middle}
    {index : start.Index} {source : Root start index} {target : Root middle (step.matching.forward index)}
    (piece : InteriorStep step index source target) : Type 1 :=
  Thunk (InteriorStep.Denominator.Point piece 0 InteriorStep.zero_inside) ×
    Thunk (InteriorStep.Denominator.Point piece 1 InteriorStep.one_inside)

/-- Retain the configured endpoint points before dispatching either parameter or reciprocal form. -/
private def endpointPoints {start middle : ChamberFrame} {step : ChamberOverlap start middle}
    {index : start.Index} {source : Root start index} {target : Root middle (step.matching.forward index)}
    (piece : InteriorStep step index source target) : EndpointPoints piece :=
  (⟨fun _ => InteriorStep.Denominator.pointFromProgram piece 0 InteriorStep.zero_inside⟩,
   ⟨fun _ => InteriorStep.Denominator.pointFromProgram piece 1 InteriorStep.one_inside⟩)

/-- Read the shared endpoint points or the same configured family at another actual parameter. -/
private def endpointAt {start middle : ChamberFrame} {step : ChamberOverlap start middle}
    {index : start.Index} {source : Root start index} {target : Root middle (step.matching.forward index)}
    {piece : InteriorStep step index source target} (points : EndpointPoints piece)
    (time : Rational) (inside : Inside time) : InteriorStep.Denominator.Point piece time inside :=
  if same : time = 0 then by
    subst time
    exact points.1.get
  else if same : time = 1 then by
    subst time
    exact points.2.get
  else InteriorStep.Denominator.pointFromProgram piece time inside

/-- The original piece order indexes a shared parameter factory for each actual piece. -/
private def Points {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    (family : Trace.Interior trace) : Type 2 :=
  Trace.Interior.casesOn (motive := fun {_ _ _ _ _ _} _ => Type 2) family
    (fun {_ _} _ => PUnit)
    (fun {_ _ _ _ _ _ _ _ _} _ _ piece tail =>
      EndpointPoints piece × Points tail)
termination_by structural family

/-- Build the shared endpoint factories once without forcing a later point before an earlier assessment. -/
private def points {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    (family : Trace.Interior trace) : Points family :=
  Trace.Interior.casesOn (motive := fun {_ _ _ _ _ _} family => Points family) family
    (fun {_ _} _ => PUnit.unit)
    (fun {_ _ _ _ _ _ _ _ _} _ _ piece tail => (endpointPoints piece, points tail))
termination_by structural family

/-- Observe both endpoint parameters using the same actual configured points in both reciprocal forms. -/
private def checkProgram {start middle : ChamberFrame} {step : ChamberOverlap start middle} {index : start.Index}
    {source : Root start index} {target : Root middle (step.matching.forward index)}
    {piece : InteriorStep step index source target} (kind : Kind) (program : Program piece (expression kind))
    (points : EndpointPoints piece)
    (directory : System.FilePath) : IO Unit := do
  let family : Program.Family program := by
    cases kind with
    | root => exact program.family (fun time inside =>
        InteriorStep.Expression.rootInverseInput program (endpointAt points time inside))
    | oneAddRoot => exact program.family (fun time inside =>
        InteriorStep.Expression.oneAddRootInverseInput program (endpointAt points time inside))
  checkAssessment (family.at 0 InteriorStep.zero_inside) (join directory "zero")
  checkAssessment (family.at 1 InteriorStep.one_inside) (join directory "one")

/-- Consume every original occurrence's stored programme in order, without repeating its bound inspection. -/
private def checkPieces (kind : Kind) {start finish : ChamberFrame} {path : ChamberPath start finish}
    {index : start.Index} {source : Root start index} {trace : Trace path index source}
    {family : Trace.Interior trace} {displayed : Data.Gaussian.Basic.Canonical → Fin 2 → Ball}
    (pieces : Trace.Expression.Pieces (expression kind) displayed family) (points : Points family)
    (directory : System.FilePath) : IO Unit :=
  Trace.Expression.Pieces.casesOn
    (motive := fun {_ _ _ _ _ _} family _ => Points family → System.FilePath → IO Unit) pieces
    (fun {_ _} _ _ _ => pure ())
    (fun {_ _ _ _ _ _ _ _ _} _ _ _ _ program _ remaining points directory => do
      checkProgram kind program points.1 (join directory "piece")
      checkPieces kind remaining points.2 (join directory "remaining")) points directory
termination_by structural pieces

/-- Observe both supplied original programme trees using one shared actual endpoint-point tree.

The stored outcomes, separation witnesses and complete common bounds are
consumed directly. No common-ball inspection or endpoint acceleration is
repeated, and each actual point remains shared between both reciprocal forms.
-/
public def checkPrograms {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} {trace : Trace path index source} (family : Trace.Interior trace)
    (displayed : Data.Gaussian.Basic.Canonical → Fin 2 → Ball)
    (first : Trace.Expression.Pieces
      (.inverse (Kind.root.expression InteriorStep.Denominator.Point.atomIndex)) displayed family)
    (second : Trace.Expression.Pieces
      (.inverse (Kind.oneAddRoot.expression InteriorStep.Denominator.Point.atomIndex)) displayed family)
    (directory : System.FilePath) : IO Unit := do
  let retainedPoints := points family
  checkPieces .root first retainedPoints (join directory "root-inverse")
  checkPieces .oneAddRoot second retainedPoints (join directory "one-plus-root-inverse")
  System.IO.println "cubic-continuation: actual three-piece original interior reciprocal endpoint observations checked"

/-- Inspect and observe both original reciprocal forms on the same actual retained interior family.

The whole original trace and every selected piece remain in each production
programme tree. The explicit caller supplies genuine interior data; failures
remain typed original geometric or exact-zero outcomes. Both forms share each
actual configured endpoint root, its stored original-channel comparison and
its retained elimination cache, including the root used for endpoint protection.
-/
public def check {start finish : ChamberFrame} {path : ChamberPath start finish} {index : start.Index}
    {source : Root start index} {trace : Trace path index source} (family : Trace.Interior trace)
    (directory : System.FilePath) : IO Unit := do
  let displayed := fun (_ : Data.Gaussian.Basic.Canonical) (_ : Fin 2) => Ball.point 0
  let first := Trace.Expression.inspect family (expression .root) displayed
  let second := Trace.Expression.inspect family (expression .oneAddRoot) displayed
  checkPrograms family displayed first second directory

end TestPurelib.Riemann.RootContinuation.PowerInteriorRuntime
