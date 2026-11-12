module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Completion.Closing
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.FineOrigin.Physical
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly.ParentOccurrence.Trace

/-! # The literal closing join at the same stored physical trace occurrences

The independently retained closing Query comparison is consumed with the
same original global SourceOrigins and finite paid Trace.View readers.
The actual moving and reserve-retention results remain distinct whole
caches. The physical incidence chain retains their selected paid traces.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.Paths.PreparedSubdivisionTrace

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstFine : Input.Fine circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
  firstFine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
  sourceOwner}
variable {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
variable {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
variable {fourthFine : Input.Fine circuit.fourth}
variable {execution : Execution.Cache (site := site) (parameter := parameter) (circuit := circuit)
  (firstInput := .inr firstFine) (sourceOwner := sourceOwner) (agreement := agreement)
  initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {sourceStage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath sourceStage}
variable {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
variable {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
variable (retained : Requested sources current freshFloor rootStage accuracy)

namespace FineCompletion

variable {retained}
variable (completed : FineCompletion retained)
variable (closure : Closure.Result.Cache (site := site) (parameter := parameter) (circuit := circuit)
  (firstInput := .inr firstFine) (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
  (secondInput := .inr secondFine) (thirdInput := .inr thirdFine) (fourthInput := .inr fourthFine) execution)
variable (lastQuery : PreparedEdge.Query (retained.parentAt retained.terminalIndex).edge 1 (of_decide_eq_true rfl))
variable (firstQuery : PreparedEdge.Query
  (retained.parentAt ⟨0, Nat.zero_lt_succ _⟩).edge 0
  (retained.parentAt ⟨0, Nat.zero_lt_succ _⟩).edge.baseInside)

/-- Read both exact physical endpoint results and the first inherited Owner through the SAME stored global origins.

The two SourceOrigins already belong to completed.origins. Their original
ParentOccurrence views select literal paid Trace suffixes, including source
and retention handoffs. The moving and reset results are retained whole;
no comparison budget, View bank or new root Owner is constructed.
-/
def traceClosing :
    Σ moving : PreparedTraceBudget.Comparison.Cache.EndpointResult (retained.parentAt retained.terminalIndex),
    Σ kept : PreparedTraceBudget.Comparison.Cache.EndpointResult (retained.parentAt retained.terminalIndex),
      NamedEquivalent (ownerName moving.1) (ownerName execution.returnOwner) ×
      NamedEquivalent (ownerName kept.1) (ownerName execution.returnOwner) ×
      NamedEquivalent (ownerName sourceOwner)
        (ownerName (retained.parentAt ⟨0, Nat.zero_lt_succ _⟩).edge.owner) :=
  let boundary := completed.closingQueries closure lastQuery firstQuery
  let lastOrigin := completed.originAt retained.terminalIndex
  let firstOrigin := completed.originAt ⟨0, Nat.zero_lt_succ _⟩
  let lastEndpoints := lastOrigin.physicalOccurrence.traceEndpoints
  let firstEndpoints := firstOrigin.physicalOccurrence.traceEndpoints
  let moving := lastEndpoints.2.1 lastQuery
  let kept := lastEndpoints.2.2 lastQuery
  let queryToReturn := NamedEquivalent.transport lastQuery.name_eq.symm rfl boundary.1
  let sourceToQuery := NamedEquivalent.transport rfl firstQuery.name_eq.symm boundary.2
  ⟨moving, kept, moving.2.symm.trans queryToReturn, kept.2.symm.trans queryToReturn,
    sourceToQuery.trans (firstEndpoints.1 firstQuery)⟩

/-- The closing consumer keeps the whole actual moving EndpointResult from its stored last physical occurrence. -/
theorem traceClosing_moving_eq : (completed.traceClosing closure lastQuery firstQuery).1 =
    (completed.originAt retained.terminalIndex).physicalOccurrence.traceEndpoints.2.1 lastQuery := by
  unfold traceClosing
  rfl

/-- The closing consumer keeps the distinct whole actual retention EndpointResult at that SAME occurrence. -/
theorem traceClosing_retained_eq : (completed.traceClosing closure lastQuery firstQuery).2.1 =
    (completed.originAt retained.terminalIndex).physicalOccurrence.traceEndpoints.2.2 lastQuery := by
  unfold traceClosing
  rfl

end FineCompletion

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
