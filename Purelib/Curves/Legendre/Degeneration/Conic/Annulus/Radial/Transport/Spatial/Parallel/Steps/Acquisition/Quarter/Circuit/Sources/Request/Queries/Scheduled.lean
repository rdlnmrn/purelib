module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Input.Schedule

/-! # Base all-query agreement from the same four scheduled actual Numerical caches

The original schedule-factory equalities pay four depth-ten inequalities.
The original completeScheduled producer materializes the fine Completion
once; BASE5 then consumes its SAME origins and literal attempt completion.
No numerical Layer, source family, source request or observation is replayed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Riemann.Meshes
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge

section ScheduledInputs

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Clearance.Envelope
open Purelib.Curves.Legendre.Periods.Jets

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable (data : (index : Fin 6) →
  Waist.Differential.Bounds.Data site parameter (Specification.Table.forms parameter index))
variable {row : Fin 6} {initialAccuracy : AccuracyRequest}
variable (target : AccuracyRequest)
variable (firstCoarse : Numerators.Cache (quarter := .first) circuit.first.regular 7
  UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)
variable (firstPiece : Piece (data row) circuit.first.actual initialAccuracy)
variable (firstQueried : firstPiece.Queried) (firstAtSource : firstPiece.span.lower = 0)
variable (firstAtFinish : firstPiece.span.upper = 1)
variable (firstFinish : { reading : ReadingAt circuit.first.actual firstPiece.upperEndpoint //
  QueryCache circuit.first.actual firstPiece.upperEndpoint reading })
variable (firstScheduled : { value : Input.Numerical (data := data row) circuit.first //
  value = Input.Numerical.scheduled data firstCoarse firstPiece target
    firstQueried firstAtSource firstAtFinish firstFinish })
variable (secondCoarse : Numerators.Cache (quarter := .second) circuit.second.regular 7
  UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)
variable (secondPiece : Piece (data row) circuit.second.actual initialAccuracy)
variable (secondQueried : secondPiece.Queried) (secondAtSource : secondPiece.span.lower = 0)
variable (secondAtFinish : secondPiece.span.upper = 1)
variable (secondFinish : { reading : ReadingAt circuit.second.actual secondPiece.upperEndpoint //
  QueryCache circuit.second.actual secondPiece.upperEndpoint reading })
variable (secondScheduled : { value : Input.Numerical (data := data row) circuit.second //
  value = Input.Numerical.scheduled data secondCoarse secondPiece target
    secondQueried secondAtSource secondAtFinish secondFinish })
variable (thirdCoarse : Numerators.Cache (quarter := .third) circuit.third.regular 7
  UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)
variable (thirdPiece : Piece (data row) circuit.third.actual initialAccuracy)
variable (thirdQueried : thirdPiece.Queried) (thirdAtSource : thirdPiece.span.lower = 0)
variable (thirdAtFinish : thirdPiece.span.upper = 1)
variable (thirdFinish : { reading : ReadingAt circuit.third.actual thirdPiece.upperEndpoint //
  QueryCache circuit.third.actual thirdPiece.upperEndpoint reading })
variable (thirdScheduled : { value : Input.Numerical (data := data row) circuit.third //
  value = Input.Numerical.scheduled data thirdCoarse thirdPiece target
    thirdQueried thirdAtSource thirdAtFinish thirdFinish })
variable (fourthCoarse : Numerators.Cache (quarter := .fourth) circuit.fourth.regular 7
  UniformPrimitiveMesh.firstEndpoint UniformPrimitiveMesh.lastEndpoint)
variable (fourthPiece : Piece (data row) circuit.fourth.actual initialAccuracy)
variable (fourthQueried : fourthPiece.Queried) (fourthAtSource : fourthPiece.span.lower = 0)
variable (fourthAtFinish : fourthPiece.span.upper = 1)
variable (fourthFinish : { reading : ReadingAt circuit.fourth.actual fourthPiece.upperEndpoint //
  QueryCache circuit.fourth.actual fourthPiece.upperEndpoint reading })
variable (fourthScheduled : { value : Input.Numerical (data := data row) circuit.fourth //
  value = Input.Numerical.scheduled data fourthCoarse fourthPiece target
    fourthQueried fourthAtSource fourthAtFinish fourthFinish })

/- Each original Fine tuple contains the supplied whole Numerical cache.
No scheduled producer expression occurs in an executable input index. -/
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
  firstScheduled.val.initial.lowerEndpoint}
variable {agreement : InitialAgreement firstScheduled.val.initial.lowerEndpoint
  firstScheduled.val.initial.source sourceOwner}
variable {initial : Input.Realization
  (.inr (⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row, firstScheduled.val⟩ :
    Input.Fine circuit.first)) sourceOwner agreement}
variable {execution : Execution.Cache initial
  (.inr (⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row, secondScheduled.val⟩ :
    Input.Fine circuit.second))
  (.inr (⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row, thirdScheduled.val⟩ :
    Input.Fine circuit.third))
  (.inr (⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row, fourthScheduled.val⟩ :
    Input.Fine circuit.fourth))}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {sourceStage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath sourceStage}
variable {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
variable {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}

namespace Execution.Cache.Sources.Requested

/-- Materialize the original scheduled Completion once and derive base all-query agreement on its literal old attempt.

The complete scheduled factory equality is retained with that SAME cached
value. Four erased depth proofs come only from the original actual schedule
identities, not from a supplied old Completion or desired signed relation.
-/
def completeScheduledQueries (retained : Requested sources current freshFloor rootStage accuracy) :
    (_completed : { value : FineCompletion (site := site) (parameter := parameter) (circuit := circuit)
      (firstFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
        firstScheduled.val⟩)
      (secondFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
        secondScheduled.val⟩)
      (thirdFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
        thirdScheduled.val⟩)
      (fourthFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
        fourthScheduled.val⟩)
      (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
      (execution := execution) (sources := sources) retained //
      value = completeScheduled (data := data) (row := row) (initialAccuracy := initialAccuracy) (target := target)
      (firstCoarse := firstCoarse) (firstPiece := firstPiece) (firstQueried := firstQueried)
      (firstAtSource := firstAtSource) (firstAtFinish := firstAtFinish) (firstFinish := firstFinish)
      (firstScheduled := firstScheduled)
      (secondCoarse := secondCoarse) (secondPiece := secondPiece) (secondQueried := secondQueried)
      (secondAtSource := secondAtSource) (secondAtFinish := secondAtFinish) (secondFinish := secondFinish)
      (secondScheduled := secondScheduled)
      (thirdCoarse := thirdCoarse) (thirdPiece := thirdPiece) (thirdQueried := thirdQueried)
      (thirdAtSource := thirdAtSource) (thirdAtFinish := thirdAtFinish) (thirdFinish := thirdFinish)
      (thirdScheduled := thirdScheduled)
      (fourthCoarse := fourthCoarse) (fourthPiece := fourthPiece) (fourthQueried := fourthQueried)
      (fourthAtSource := fourthAtSource) (fourthAtFinish := fourthAtFinish) (fourthFinish := fourthFinish)
      (fourthScheduled := fourthScheduled) retained }) ×
    PreparedParents.QueryAgreement retained.attempt.2.1 := by
  have firstTen : 10 ≤ firstScheduled.val.depth :=
    Eq.mpr (congrArg (fun numerical : Input.Numerical (data := data row) circuit.first =>
      10 ≤ numerical.depth) firstScheduled.property)
      (Input.Numerical.scheduled_ten_le data firstCoarse firstPiece target
        firstQueried firstAtSource firstAtFinish firstFinish)
  have secondTen : 10 ≤ secondScheduled.val.depth :=
    Eq.mpr (congrArg (fun numerical : Input.Numerical (data := data row) circuit.second =>
      10 ≤ numerical.depth) secondScheduled.property)
      (Input.Numerical.scheduled_ten_le data secondCoarse secondPiece target
        secondQueried secondAtSource secondAtFinish secondFinish)
  have thirdTen : 10 ≤ thirdScheduled.val.depth :=
    Eq.mpr (congrArg (fun numerical : Input.Numerical (data := data row) circuit.third =>
      10 ≤ numerical.depth) thirdScheduled.property)
      (Input.Numerical.scheduled_ten_le data thirdCoarse thirdPiece target
        thirdQueried thirdAtSource thirdAtFinish thirdFinish)
  have fourthTen : 10 ≤ fourthScheduled.val.depth :=
    Eq.mpr (congrArg (fun numerical : Input.Numerical (data := data row) circuit.fourth =>
      10 ≤ numerical.depth) fourthScheduled.property)
      (Input.Numerical.scheduled_ten_le data fourthCoarse fourthPiece target
        fourthQueried fourthAtSource fourthAtFinish fourthFinish)
  let completed := completeScheduled (data := data) (row := row) (initialAccuracy := initialAccuracy) (target := target)
      (firstCoarse := firstCoarse) (firstPiece := firstPiece) (firstQueried := firstQueried)
      (firstAtSource := firstAtSource) (firstAtFinish := firstAtFinish) (firstFinish := firstFinish)
      (firstScheduled := firstScheduled)
      (secondCoarse := secondCoarse) (secondPiece := secondPiece) (secondQueried := secondQueried)
      (secondAtSource := secondAtSource) (secondAtFinish := secondAtFinish) (secondFinish := secondFinish)
      (secondScheduled := secondScheduled)
      (thirdCoarse := thirdCoarse) (thirdPiece := thirdPiece) (thirdQueried := thirdQueried)
      (thirdAtSource := thirdAtSource) (thirdAtFinish := thirdAtFinish) (thirdFinish := thirdFinish)
      (thirdScheduled := thirdScheduled)
      (fourthCoarse := fourthCoarse) (fourthPiece := fourthPiece) (fourthQueried := fourthQueried)
      (fourthAtSource := fourthAtSource) (fourthAtFinish := fourthAtFinish) (fourthFinish := fourthFinish)
      (fourthScheduled := fourthScheduled) retained
  let queries := completed.queries firstTen secondTen thirdTen fourthTen
  exact ⟨⟨completed, rfl⟩, queries⟩

end Execution.Cache.Sources.Requested

end ScheduledInputs

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
