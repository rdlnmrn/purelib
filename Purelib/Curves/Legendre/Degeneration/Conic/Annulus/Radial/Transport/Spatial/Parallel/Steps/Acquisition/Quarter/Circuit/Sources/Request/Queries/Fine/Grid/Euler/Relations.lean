module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Queries.Fine.Grid.Euler.Endpoint
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence.Arithmetic.Global.TargetPrograms.Source.Relations
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Grid.Completion.Relations
import Purelib.Data.Vector.Basic
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Approximation.Rational.Grid.Unit

/-! # Original connection and scalar comparisons on the same finite Euler endpoint

The actual last positive node supplies its stored programme blocks and
Completion family. One original sourceRelations factory attaches those
six whole programmes and derives their two original all-request relation
certificates. The scalar Euler endpoint bound is kept separate from these
progressive fixed-parameter comparison owners.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib.Curves.Legendre.Periods.Jets.Specification

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.Shifted
open Purelib.Curves.Legendre.Periods.Jets.Variation
open Purelib.Curves.Legendre.Periods.Jets.Basic (SynchronizedPeriodJet)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Approximation.Rational
open Purelib.Data.Vector.Basic (vectorOfFn_apply)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Integration.Program.Gaussian.Basic (RefinementProgram)
open Steps.Acquisition

section

variable
    {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
    {firstFine : Input.Fine circuit.first}
    {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
    {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
      sourceOwner}
    {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
    {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
    {fourthFine : Input.Fine circuit.fourth}
    {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
    {frame : Paths.Frame parameter} {basis : Differential 1}
    {modelCount floor : Nat} {sheet : Fin 2}
    {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {sourceTargets : CellEndpoints.Targets sourcePath stage}
    {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
      (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
    {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
    {requested : Requested sources current freshFloor rootStage accuracy}
    (completed : FineCompletion requested)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (direction : Canonical) (moving : direction ≠ 0) (request spatial : AccuracyRequest) (commonCurrent : Nat)
    (ranges : PreparedParents.ParameterRange requested.covered)
    (allocation : PreparedParents.ParameterRange.StripAllocation ranges)
    (admitted : Data.Gaussian.Norm.Basic.normSq direction ≤ allocation.bound)
    (widths : Fin (requested.shape.val.1 :: requested.shape.val.2).length → AccuracyRequest)
    (targetCurrent targetFloor targetRootStage : Nat)

variable {completed firstTen secondTen thirdTen fourthTen direction moving request spatial commonCurrent
    ranges allocation admitted widths targetCurrent targetFloor targetRootStage}
    (retained : EulerExecution completed firstTen secondTen thirdTen fourthTen direction moving request spatial
      commonCurrent ranges allocation admitted widths targetCurrent targetFloor targetRootStage)

namespace EulerExecution

/-- One retained original sourceRelations value on the SAME stored last-node programmes and Completion family.

The subtype keeps the whole original factory. Both comparison certificates
belong to its same original jet, frame and cycle. This is an exact retained
operation result in the original container, not a new root/period owner or
an all-node bank of unused comparison work.
-/
@[expose] def EndpointRelations :=
  retained.grid.completions.Relations retained.endpointIndex

/-- Construct the two original operational relation certificates once on the stored endpoint's actual six programmes.

The supplied execution is read only. Its original node, programme blocks
and selected Completion stay literal. Only sourceRelations is newly run;
its original calls to the retained family keep their existing behavior at
other stages. No global memoization of that family is asserted. Original
ofJet constructors derive both named all-request sample comparisons with
their own retained primitive, budget and schedule data.
-/
@[expose, macro_inline] def endpointRelations : EndpointRelations retained :=
  retained.grid.completions.relations retained.endpointIndex

/-- The whole result retains the original single sourceRelations call on the same literal cached entries. -/
private theorem endpointRelations_factory : endpointRelations retained =
    (let actual := (retained.grid.table.programmes.entry retained.endpointIndex).sourceRelations
       (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
       (retained.grid.completions.family retained.endpointIndex)
     ⟨actual, rfl⟩) :=
  retained.grid.completions.relations_factory retained.endpointIndex

namespace EndpointRelations

variable {retained} (relations : EndpointRelations retained)

/-- Read the SAME original endpoint jet from the single retained sourceRelations factory result. -/
@[expose, macro_inline] def jet : SynchronizedPeriodJet
    (retained.grid.table.nodes.node retained.endpointIndex).target := relations.val.1

/-- Read the original connection certificate, including connection_samples_close at all its own scheduled requests. -/
@[expose, macro_inline] def connection : Jets.Connection.ConnectionCertificate relations.jet := relations.val.2.1

/-- Read the original scalar certificate, including residual_samples_close at all its own scheduled requests. -/
@[expose, macro_inline] def residual : Jets.PicardFuchs.PicardFuchsCertificate relations.jet := relations.val.2.2

/-- The whole comparison bundle is the original once-invoked factory on the SAME stored programme and family entries. -/
theorem factory_eq : relations.val =
    (retained.grid.table.programmes.entry retained.endpointIndex).sourceRelations
      (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
      (retained.grid.completions.family retained.endpointIndex) := relations.property

/-- The returned jet is the exact original sourceJet construction on those same endpoint caches. -/
theorem jet_eq : relations.jet =
    (retained.grid.table.programmes.entry retained.endpointIndex).sourceJet
      (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
      (retained.grid.completions.family retained.endpointIndex) :=
  PreparedParents.ShiftedGeometry.ValueBlocks.SourceRelations.jet_eq
    (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
    (retained := retained.grid.table.programmes.entry retained.endpointIndex)
    (completed := retained.grid.completions.family retained.endpointIndex) relations

/-- All six endpoint rows retain the original last-node lifted cycle at every progressive stage. -/
theorem cycle_eq : relations.jet.cycle = PreparedParents.constantCycle
    (retained.grid.table.nodes.node retained.endpointIndex).next.requested.request.chain :=
  PreparedParents.ShiftedGeometry.ValueBlocks.SourceRelations.cycle_eq
    (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
    (retained := retained.grid.table.programmes.entry retained.endpointIndex)
    (completed := retained.grid.completions.family retained.endpointIndex) relations

/-- The whole original value programme is the SAME stored endpoint target programme, hence every stage is retained. -/
theorem value_integral (coordinate : Fin 2) : (relations.jet.value coordinate).integral =
    (retained.grid.table.programmes.entry retained.endpointIndex).targetProgram
      (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
      (Table.valueIndex coordinate) :=
  PreparedParents.ShiftedGeometry.ValueBlocks.SourceRelations.value_integral
    (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
    (retained := retained.grid.table.programmes.entry retained.endpointIndex)
    (completed := retained.grid.completions.family retained.endpointIndex) relations coordinate

/-- The whole original first programme is the SAME stored endpoint first target programme at every stage. -/
theorem first_integral (coordinate : Fin 2) : (relations.jet.first coordinate).integral =
    (retained.grid.table.programmes.entry retained.endpointIndex).targetProgram
      (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
      (Table.firstIndex coordinate) :=
  PreparedParents.ShiftedGeometry.ValueBlocks.SourceRelations.first_integral
    (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
    (retained := retained.grid.table.programmes.entry retained.endpointIndex)
    (completed := retained.grid.completions.family retained.endpointIndex) relations coordinate

/-- The whole original second programme is the SAME stored endpoint second target programme at every stage. -/
theorem second_integral (coordinate : Fin 2) : (relations.jet.second coordinate).integral =
    (retained.grid.table.programmes.entry retained.endpointIndex).targetProgram
      (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
      (Table.secondIndex coordinate) :=
  PreparedParents.ShiftedGeometry.ValueBlocks.SourceRelations.second_integral
    (next := (retained.grid.table.nodes.node retained.endpointIndex).next)
    (retained := retained.grid.table.programmes.entry retained.endpointIndex)
    (completed := retained.grid.completions.family retained.endpointIndex) relations coordinate

end EndpointRelations

namespace EndpointRelations

variable {retained} (relations : EndpointRelations retained)

/-- The same jet value reading is the literal terminal sample used by the original Euler endpoint certificate. -/
theorem terminal_value (coordinate : Fin 2) :
    ((relations.jet.value coordinate).integral.model
      (retained.grid.table.nodes.node retained.endpointIndex).next.requested.selected.stage).integralSample =
        retained.trace.eulerValues ⟨retained.fineCount, Nat.lt_succ_self retained.fineCount⟩ coordinate :=
  (congrArg (fun programme : RefinementProgram =>
    (programme.model
      (retained.grid.table.nodes.node retained.endpointIndex).next.requested.selected.stage).integralSample)
      (relations.value_integral coordinate)).trans (retained.terminal_sample coordinate).symm

end EndpointRelations

end EulerExecution

end

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested.FineCompletion

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
