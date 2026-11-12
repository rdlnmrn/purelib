module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request.Completion.Adjacent

import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.FineOrigin
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Repeat
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Input.Schedule
import Purelib.Data.List.DependentProduct
import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.SubdivisionRoots
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Entries
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Data.Fin
import Purelib.Riemann.Topology.PreparedRefinementRootChains.Occurrence
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Occurrence
import Purelib.Data.List.Append
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank.Root

/-! # Endpoint completion on retained fine-quarter sources and schedules -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

namespace Steps.Acquisition.Quarter.Circuit

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source (Vertex)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients (CoefficientPolynomial)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement (Piece)
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer.Spatial
  renaming Block → LayerBlock
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Paths.PreparedPathPrimitiveCover.PreparedClearPathModels (CoveredTracedPath)
open Purelib.Riemann.Topology.PreparedBankRootChains
open Purelib.Riemann.Topology.SquareRootContinuationChain (Owner)
open Factors.Segment.Reading.Payment (widthRequest)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Meshes

section AllFineInputs

open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstFine : Input.Fine circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl)
  firstFine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
  sourceOwner}
variable {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
variable {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
variable {fourthFine : Input.Fine circuit.fourth}
variable {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {sourceStage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath sourceStage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Execution.Cache.Sources.Requested

variable {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
variable {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
variable (retained : Requested sources current freshFloor rootStage accuracy)

/-- A materialized product of actual fine source origins in the SAME original global parent order.

Each entry retains its original global and Block positions, complete Entry,
preceding Reading/Samples when needed, and original SourceOccurrence. The
product has the original parent list as its only occurrence index.
-/
@[expose] def SourceOrigins :=
  DependentProduct (retained.shape.val.1 :: retained.shape.val.2)
    (fun index => SourceOrigin retained index)

/-- Read each actual original fine source origin once before endpoint completion and retain the complete product. -/
def sourceOrigins : SourceOrigins retained :=
  DependentProduct.ofFn (retained.shape.val.1 :: retained.shape.val.2)
    (fun index => keepSourceOrigin retained index)

/-- Each stored origin is the WHOLE original readonly descent on that SAME bounded global occurrence. -/
theorem sourceOrigins_entry (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    DependentProduct.get (retained.shape.val.1 :: retained.shape.val.2) retained.sourceOrigins index =
      keepSourceOrigin retained index := by
  unfold sourceOrigins
  exact DependentProduct.get_ofFn (retained.shape.val.1 :: retained.shape.val.2)
    (fun index => keepSourceOrigin retained index) index

/-- Read the next literal global source occurrence, wrapping only the actual last parent to index zero. -/
@[expose] def nextIndex (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    Fin (retained.shape.val.1 :: retained.shape.val.2).length :=
  if later : index.val + 1 < (retained.shape.val.1 :: retained.shape.val.2).length then
    ⟨index.val + 1, later⟩
  else ⟨0, Nat.zero_lt_succ _⟩

/-- The actual global geometric chain supplies every successor point, including the literal closing edge.

Empty physical edge/Block words contribute no occurrence. Adjacency is
read from the retained flattened chain; only its actual last parent wraps
to the first. The original lifted sheet is retained in this equality.
-/
theorem next_start_eq (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    PreparedParent.startPoint (retained.parentAt (retained.nextIndex index)) =
      PreparedParent.finishPoint (retained.parentAt index) := by
  unfold nextIndex
  split
  · rename_i later
    exact CenteredPathChain.adjacent_eq (retained.shape.val.1 :: retained.shape.val.2)
      retained.chain index later
  · rename_i notLater
    have atLast : index.val + 1 = (retained.shape.val.1 :: retained.shape.val.2).length :=
      Nat.le_antisymm (Nat.succ_le_of_lt index.isLt) (Nat.le_of_not_gt notLater)
    have first := CenteredPathChain.startAt_eq (retained.shape.val.1 :: retained.shape.val.2)
      retained.chain (⟨0, Nat.zero_lt_succ _⟩ : Fin (retained.shape.val.1 :: retained.shape.val.2).length) rfl
    have last := CenteredPathChain.finishAt_eq (retained.shape.val.1 :: retained.shape.val.2)
      retained.chain index atLast
    exact first.trans last.symm

/-- Read successor signed query agreement from the exact retained closed root chain.

This private worker receives the chain computed by the same source
assembly. The public completion producer constructs and stores that chain;
it never requests a caller-supplied root relation.
-/
private def nextQuery {root : Named}
    (roots : RootChain (retained.shape.val.1 :: retained.shape.val.2) root root)
    (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    NamedEquivalent ((retained.parentAt index).edge.rootName 1 (of_decide_eq_true rfl))
      ((retained.parentAt (retained.nextIndex index)).edge.rootName 0
        (retained.parentAt (retained.nextIndex index)).edge.baseInside) := by
  unfold nextIndex
  split
  · rename_i later
    exact RootChain.adjacentEquivalent (retained.shape.val.1 :: retained.shape.val.2) roots index later
  · rename_i notLater
    have atLast : index.val + 1 = (retained.shape.val.1 :: retained.shape.val.2).length :=
      Nat.le_antisymm (Nat.succ_le_of_lt index.isLt) (Nat.le_of_not_gt notLater)
    exact (RootChain.terminalEquivalent (retained.shape.val.1 :: retained.shape.val.2) roots index atLast).trans
      roots.firstEquivalent

/-- The actual request bank contains every original source entry of this SAME fresh preparation product. -/
private theorem sourceMembers : PreparedParents.SourceMembers retained.covered retained.prepared retained.bank :=
  Eq.mp (congrArg (fun bank => PreparedParents.SourceMembers retained.covered retained.prepared bank)
    retained.attempt.2.2.1.property.symm)
    (PreparedParents.requestBank_sourceMembers retained.covered retained.prepared)

/-- Membership of the identical cached source occurrence rules out absence of the actual first lookup. -/
private theorem firstPresent (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    ∃ entry, entry ∈ retained.bank ∧ entry.point = PreparedParent.startPoint (retained.parentAt index) :=
  ⟨Vertex.Entry.request (retained.prepared.entry index).firstVertex.val
      retained.targets.endpoint retained.targets.endpoint_positive,
    retained.sourceMembers index, rfl⟩

/-- The SAME actual successor entry pays last-lookup membership across every global and closing boundary. -/
private theorem lastPresent (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    ∃ entry, entry ∈ retained.bank ∧ entry.point = PreparedParent.finishPoint (retained.parentAt index) :=
  ⟨Vertex.Entry.request (retained.prepared.entry (retained.nextIndex index)).firstVertex.val
      retained.targets.endpoint retained.targets.endpoint_positive,
    retained.sourceMembers (retained.nextIndex index), retained.next_start_eq index⟩

variable (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
variable (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)

/-- Compare a literal visiting source to THAT stored first Found using both actual retained fine origins. -/
private def sourceToFound (origins : SourceOrigins retained)
    (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length)
    {point : LiftedPoint 2} (samePoint : PreparedParent.startPoint (retained.parentAt index) = point)
    {found : Vertex.Bank.Found retained.bank point} (position : Vertex.Bank.Position (.found found)) :
    NamedEquivalent ((retained.parentAt index).edge.rootName 0 (retained.parentAt index).edge.baseInside)
      found.original.sample.certificate.value.name := by
  let visiting := DependentProduct.get (retained.shape.val.1 :: retained.shape.val.2) origins index
  let selected := DependentProduct.get (retained.shape.val.1 :: retained.shape.val.2) origins
    (retained.foundSourceIndex position)
  have selectedPoint := retained.attempt.found_source_point position
  let compared := SourceOrigin.queries_at_repeat visiting selected firstTen secondTen thirdTen fourthTen
    (congrArg (fun value : LiftedPoint 2 => value.coordinate) (samePoint.trans selectedPoint.symm))
  exact compared.trans (retained.attempt.foundQueryEquivalent position)

/-- Complete one SAME actual parent check using literal lookup Positions and the retained repeat/chain comparisons.

The first and last outcomes are read from the original checking cache.
Erased membership excludes absence, while locate_eq transports their SAME
stored Positions. Ready Commons survive unchanged; only unpaid endpoints
execute the existing common-refinement acquisition.
-/
private def completeAt {root : Named}
    (roots : RootChain (retained.shape.val.1 :: retained.shape.val.2) root root)
    (origins : SourceOrigins retained)
    (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    PreparedParent.Checked.Completion (retained.checkedAt index) := by
  let checked := retained.checkedAt index
  let first := checked.first.1.locate (retained.firstPresent index)
  let last := checked.last.1.locate (retained.lastPresent index)
  have firstLookup : checked.first.1 = .found first :=
    checked.first.1.locate_eq (retained.firstPresent index)
  have lastLookup : checked.last.1 = .found last :=
    checked.last.1.locate_eq (retained.lastPresent index)
  let firstPosition := retained.firstPosition index firstLookup
  let lastPosition := retained.lastPosition index lastLookup
  let firstQuery := sourceToFound retained firstTen secondTen thirdTen fourthTen origins index rfl firstPosition
  let lastSource := sourceToFound retained firstTen secondTen thirdTen fourthTen origins
    (retained.nextIndex index) (retained.next_start_eq index) lastPosition
  let lastQuery := (retained.nextQuery roots index).trans lastSource
  exact PreparedParent.Checked.complete checked (retained.firstPresent index) (retained.lastPresent index)
    (fun found => NamedEquivalent.transport rfl
      (congrArg (fun vertex : Vertex parameter (PreparedParent.startPoint (retained.parentAt index)) =>
        vertex.sample.certificate.value.name) (first.original_eq found)) firstQuery)
    (fun found => NamedEquivalent.transport rfl
      (congrArg (fun vertex : Vertex parameter (PreparedParent.finishPoint (retained.parentAt index)) =>
        vertex.sample.certificate.value.name) (last.original_eq found)) lastQuery)

/-- Complete the original global StageAttempt from these SAME retained root and origin caches. -/
private def completeFrom {root : Named}
    (roots : RootChain (retained.shape.val.1 :: retained.shape.val.2) root root)
    (origins : SourceOrigins retained) : PreparedParents.StageAttempt.Completion retained.attempt :=
  let acquired := DependentProduct.ofFn (retained.shape.val.1 :: retained.shape.val.2)
    (fun index => completeAt retained firstTen secondTen thirdTen fourthTen roots origins index)
  let result := PreparedParents.Acquisitions.stage retained.covered retained.chain
    retained.attempt.1.val retained.attempt.1.property retained.prepared retained.bank retained.attempt.2.2.2.1
    retained.attempt.2.2.2.2.1 acquired
  ⟨acquired, ⟨result, rfl⟩⟩

/-- The SAME original global attempt completed from its actual internally derived root and fine-origin caches.

This is an existing Sigma/subtype retention boundary for two derived
certificate products and the original StageAttempt.Completion. It adds no
root Owner, trace, request or observation. The actual whole chain and
ordered origin product are stored once with their complete factory laws.
-/
@[expose] def FineCompletion :=
  (_roots : { value : RootChain (retained.shape.val.1 :: retained.shape.val.2)
      (Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
        sourceOwner.parameterNonzero sourceOwner)
      (Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName
        sourceOwner.parameterNonzero sourceOwner) // value = retained.rootChain }) ×
  (_origins : { value : SourceOrigins retained // value = retained.sourceOrigins }) ×
  PreparedParents.StageAttempt.Completion retained.attempt

/-- Complete a depth-paid actual all-fine request without Distinct, Ready, RootChain or endpoint-relation inputs.

The four depth payments concern the SAME actual fine numerical Layers.
A genuine Numerical.scheduled input derives them before its observations.
The producer computes the original source chain once, materializes each
actual origin once, then completes the SAME old parent checks. No source,
lookup, observer, paid execution or original preparation is replayed.
-/
def completeFine : FineCompletion retained :=
  let roots := retained.rootChain
  let origins := retained.sourceOrigins
  let completed := completeFrom retained firstTen secondTen thirdTen fourthTen roots origins
  ⟨⟨roots, rfl⟩, ⟨origins, rfl⟩, completed⟩

namespace FineCompletion

variable {retained} (completed : FineCompletion retained)

/-- Read the whole internally constructed original signed source-chain cache. -/
@[expose] def roots := completed.1.val

/-- The retained chain is the exact original same-source assembly operation. -/
theorem roots_eq : completed.roots = retained.rootChain := completed.1.property

/-- Read the complete ordered original fine-origin product used by every endpoint comparison. -/
@[expose] def origins := completed.2.1.val

/-- Every origin in the retained product comes from the identical one-pass readonly materialization. -/
theorem origins_eq : completed.origins = retained.sourceOrigins := completed.2.1.property

/-- Read the SAME stored fine origin at an actual global parent occurrence. -/
@[expose] def originAt (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    SourceOrigin retained index :=
  DependentProduct.get (retained.shape.val.1 :: retained.shape.val.2) completed.origins index

/-- The stored origin is the WHOLE original readonly factory on this literal occurrence. -/
theorem originAt_eq (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    completed.originAt index = keepSourceOrigin retained index :=
  (congrArg (fun values : SourceOrigins retained =>
    DependentProduct.get (retained.shape.val.1 :: retained.shape.val.2) values index)
      completed.origins_eq).trans (retained.sourceOrigins_entry index)

/-- Read the original completed attempt with its old sources, bank and ready/unpaid checker caches. -/
@[expose] def completion : PreparedParents.StageAttempt.Completion retained.attempt := completed.2.2

/-- Read the SAME actual original Stage constructed from the retained endpoint completion product. -/
@[expose] def stage := completed.completion.2.val

/-- The whole Stage is its original factory on these SAME retained source/check/completion caches. -/
theorem stage_eq : completed.stage = PreparedParents.Acquisitions.stage retained.covered retained.chain
    retained.attempt.1.val retained.attempt.1.property retained.prepared retained.bank retained.attempt.2.2.2.1
    retained.attempt.2.2.2.2.1 completed.completion.1 := completed.completion.2.property

end FineCompletion

end Execution.Cache.Sources.Requested

end AllFineInputs

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

/-- Complete the SAME actual four scheduled fine quarters with every depth payment derived internally.

The four supplied actual Numerical caches remain runtime inputs. Their
whole original scheduled-factory equalities transport only erased depth
propositions. The paid execution, source families and fresh Requested stay
unchanged. No Layer, query, source or observation factory is replayed.
-/
def completeScheduled (retained : Requested sources current freshFloor rootStage accuracy) :
    FineCompletion (site := site) (parameter := parameter) (circuit := circuit)
      (firstFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
        firstScheduled.val⟩)
      (secondFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
        secondScheduled.val⟩)
      (thirdFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
        thirdScheduled.val⟩)
      (fourthFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
        fourthScheduled.val⟩)
      (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
      (execution := execution) (sources := sources) retained := by
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
  exact completeFine (site := site) (parameter := parameter) (circuit := circuit)
    (firstFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
      firstScheduled.val⟩)
    (secondFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
      secondScheduled.val⟩)
    (thirdFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
      thirdScheduled.val⟩)
    (fourthFine := ⟨Paths.polynomial parameter, Specification.Table.forms parameter row, data row,
      fourthScheduled.val⟩)
    (sourceOwner := sourceOwner) (agreement := agreement) (initial := initial)
    (execution := execution) (sources := sources) retained firstTen secondTen thirdTen fourthTen

end Execution.Cache.Sources.Requested

end ScheduledInputs

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
