module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Completion
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Closure
public import Purelib.Riemann.Readings.UniformPreparedRequests.Query
import Purelib.Riemann.Paths.OwnerTraceReadings.Comparison
import Purelib.Riemann.Topology.PreparedRefinementRootChains.Occurrence
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Literal closing queries and Points on the retained fine paid circuit

The same completed request supplies its signed root chain. The separate
original closure retains its actual operational OwnerJoin. Both original
endpoint Queries and independent primitive Points are compared through
these certificates; no physical View dispatcher, new observation, Owner
identification or primitive normalization is required by this module.
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
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.Paths.OwnerTraceReadings (ownerName)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

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

/-- The literal last parent occurrence of this same nonempty retained global request. -/
@[expose] def terminalIndex : Fin (retained.shape.val.1 :: retained.shape.val.2).length :=
  ⟨retained.shape.val.2.length, Nat.lt_succ_self _⟩

/-- The terminal reader reserves exactly the final position, including a singleton parent word. -/
theorem terminalIndex_last : retained.terminalIndex.val + 1 =
    (retained.shape.val.1 :: retained.shape.val.2).length := by
  rfl

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

/-- Attach the two actual boundary Queries to the literal returned and initial Owners of the SAME closing join.

The last comparison factors the retained terminal-chain witness through
this actual join in reverse. The first comparison reads the retained
incoming witness. These are signed comparisons, not whole-Owner identity
or identification of a particular final moving/reset occurrence.
-/
def closingQueries :
    NamedEquivalent (ownerName lastQuery.owner) (ownerName execution.returnOwner) ×
      NamedEquivalent (ownerName sourceOwner) (ownerName firstQuery.owner) := by
  have sourceName : ownerRootName sourceOwner.parameterNonzero sourceOwner = ownerName sourceOwner := rfl
  have terminalName :
      ((retained.shape.val.1 :: retained.shape.val.2)[
        retained.terminalIndex.val]'retained.terminalIndex.isLt).edge.rootName 1 (of_decide_eq_true rfl) =
      (retained.parentAt retained.terminalIndex).edge.rootName 1 (of_decide_eq_true rfl) := rfl
  have terminal := NamedEquivalent.transport terminalName sourceName
    (RootChain.terminalEquivalent (retained.shape.val.1 :: retained.shape.val.2) completed.roots
      retained.terminalIndex retained.terminalIndex_last)
  have headName : (retained.shape.val.1).edge.rootName 0 (retained.shape.val.1).edge.baseInside =
      (retained.parentAt ⟨0, Nat.zero_lt_succ _⟩).edge.rootName 0
        (retained.parentAt ⟨0, Nat.zero_lt_succ _⟩).edge.baseInside := rfl
  have incoming := NamedEquivalent.transport sourceName headName completed.roots.firstEquivalent
  exact ⟨NamedEquivalent.transport lastQuery.name_eq rfl (terminal.trans closure.join.equivalent.symm),
    NamedEquivalent.transport rfl firstQuery.name_eq incoming⟩

/-- Compare the SAME supplied endpoint Points through both retained Queries and the literal operational closing join.

The two requests and neighborhoods remain independent. Each original
Point refinement is consumed once, with endpoint containment derived by
its own LocalRequest. No Point, query, Entry or closing join is reacquired,
and no equality of primitive constants is concluded.
-/
def closingPoints {lastCount firstCount : Nat} {lastTarget firstTarget : Rational}
    (lastRequest : LocalRequest (retained.parentAt retained.terminalIndex) lastCount lastTarget)
    (firstRequest : LocalRequest (retained.parentAt ⟨0, Nat.zero_lt_succ _⟩) firstCount firstTarget)
    (lastPoint : ContinuedNeighborhood.Point lastRequest.neighborhood
      ((retained.parentAt retained.terminalIndex).edge.point 1))
    (firstPoint : ContinuedNeighborhood.Point firstRequest.neighborhood
      ((retained.parentAt ⟨0, Nat.zero_lt_succ _⟩).edge.point 0)) :
    NamedEquivalent lastPoint.certificate.value.name (ownerName execution.returnOwner) ×
      NamedEquivalent (ownerName sourceOwner) firstPoint.certificate.value.name ×
      NamedEquivalent lastPoint.certificate.value.name firstPoint.certificate.value.name :=
  let boundary := completed.closingQueries closure lastQuery firstQuery
  let lastReading := lastRequest.retainedQueryEquivalent 1 (of_decide_eq_true rfl) lastQuery rfl
    (lastRequest.point_inside (of_decide_eq_true rfl)) lastPoint
  let firstReading := firstRequest.retainedQueryEquivalent 0
    (retained.parentAt ⟨0, Nat.zero_lt_succ _⟩).edge.baseInside firstQuery rfl
    (firstRequest.point_inside (retained.parentAt ⟨0, Nat.zero_lt_succ _⟩).edge.baseInside) firstPoint
  let lastToQuery := (NamedEquivalent.transport lastQuery.name_eq rfl lastReading).symm
  let firstFromQuery := NamedEquivalent.transport firstQuery.name_eq rfl firstReading
  let lastToReturn := lastToQuery.trans boundary.1
  let sourceToFirst := boundary.2.trans firstFromQuery
  ⟨lastToReturn, sourceToFirst, lastToReturn.trans (closure.join.equivalent.trans sourceToFirst)⟩

end FineCompletion

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources.Requested

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
