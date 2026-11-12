module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.FineOrigin
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Block.Sources.Repeat
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Input.Schedule
import Purelib.Data.List.DependentProduct
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.SubdivisionRoots
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

/-! # Paid endpoint completion from actual fine source occurrences and retained first-match lookups

The original shared Requested, old Checked entries, actual Found positions,
actual fine Layer Blocks and their source-origin views remain inputs.
Original source incidence, actual subdivision joins and paid fine widths derive query
comparisons; Checked.complete reuses ready Commons and acquires only unpaid
endpoints. An existing inconclusive outcome is never declared Ready.
-/

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

section ActualInputs

variable {site : Fin 2} {parameter : Canonical}
variable {circuit : Transport.Circuit site parameter} {firstInput : Input circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstInput.sourceEndpoint}
variable {agreement : InitialAgreement firstInput.sourceEndpoint firstInput.sourceReading sourceOwner}
variable {initial : Input.Realization firstInput sourceOwner agreement}
variable {secondInput : Input circuit.second} {thirdInput : Input circuit.third} {fourthInput : Input circuit.fourth}
variable {execution : Execution.Cache initial secondInput thirdInput fourthInput}

variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {sourceStage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath sourceStage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

namespace Execution.Cache.Sources.Requested

variable {sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution}
variable {current freshFloor rootStage : Nat} {accuracy : Approximation.AccuracyRequest}
variable (retained : Requested sources current freshFloor rootStage accuracy)

/-- Read the same actual centered parent at one original bounded fresh-stage occurrence. -/
@[expose] def parentAt (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    CenteredEdge (Fibre.frameCurve frame) basis :=
  (retained.shape.val.1 :: retained.shape.val.2)[index.val]'index.isLt

/-- Read the SAME old endpoint-check pair at the original stage occurrence without checking or looking up again. -/
@[expose] def checkedAt (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length) :
    PreparedParent.Checked (retained.prepared.entry index) retained.bank rootStage :=
  DependentProduct.get (retained.shape.val.1 :: retained.shape.val.2)
    (family := fun index => PreparedParent.Checked (retained.prepared.entry index) retained.bank rootStage)
    retained.attempt.2.2.2.2.1 index

variable (index : Fin (retained.shape.val.1 :: retained.shape.val.2).length)
variable {firstFound : Vertex.Bank.Found retained.bank (PreparedParent.startPoint (retained.parentAt index))}
variable {lastFound : Vertex.Bank.Found retained.bank (PreparedParent.finishPoint (retained.parentAt index))}
variable (firstLookup : (retained.checkedAt index).first.1 = .found firstFound)
variable (lastLookup : (retained.checkedAt index).last.1 = .found lastFound)

/-- Transport only the SAME stored first endpoint occurrence to its actual Found outcome. -/
@[expose] def firstPosition : Vertex.Bank.Position (.found firstFound) :=
  Eq.mp (congrArg Vertex.Bank.Position firstLookup) (retained.checkedAt index).first.occurrence

/-- Transport only the SAME stored last endpoint occurrence to its actual Found outcome. -/
@[expose] def lastPosition : Vertex.Bank.Position (.found lastFound) :=
  Eq.mp (congrArg Vertex.Bank.Position lastLookup) (retained.checkedAt index).last.occurrence

variable {firstVisitQuarter : UnitCircuitQuarter}
variable {firstVisitLeg : Transport.Leg site parameter firstVisitQuarter}
variable {firstVisitRadicand : CoefficientPolynomial}
variable {firstVisitDifferential : OddPowerDifferential firstVisitRadicand}
variable {firstVisitData : Waist.Differential.Bounds.Data site parameter firstVisitDifferential}
variable {firstVisitNumerical : Input.Numerical (data := firstVisitData) firstVisitLeg}
variable (firstVisitTen : 10 ≤ firstVisitNumerical.depth)
variable {firstVisitPiece : Piece firstVisitData firstVisitLeg.actual
  firstVisitNumerical.layer.accuracy}
variable (firstVisitMember : firstVisitPiece ∈ firstVisitNumerical.layer.pieces)
variable {firstVisitTarget : Endpoint}
variable {firstVisitQueried : { reading : ReadingAt firstVisitLeg.actual firstVisitTarget //
  QueryCache firstVisitLeg.actual firstVisitTarget reading }}
variable {firstVisitOwner : OwnerAt site parameter firstVisitQuarter
  (of_decide_eq_true rfl) firstVisitPiece.lowerEndpoint}
variable {firstVisitAgreement : InitialAgreement firstVisitPiece.lowerEndpoint
  firstVisitPiece.source firstVisitOwner}
variable {firstVisitBlock : LayerBlock (regular := firstVisitLeg.regular) firstVisitPiece firstVisitQueried
  firstVisitOwner firstVisitAgreement}
variable {firstVisitSources : Spine.Sources (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
  (sheet := sheet) (targets := sourceTargets)
  (fun {_start _finish} segment => widthRequest firstVisitBlock.paid.anchor segment)
  firstVisitBlock.geometry.route.path firstVisitBlock.geometry.route.within
  firstVisitOwner firstVisitBlock.paid.paid.spine}
variable {firstVisitIndex : Fin (Spine.Sources.assemble
  (fun {_start _finish} segment => widthRequest firstVisitBlock.paid.anchor segment)
  firstVisitBlock.geometry.route.path firstVisitBlock.geometry.route.within
  firstVisitOwner firstVisitBlock.paid.paid.spine
  firstVisitSources).geometry.parents.length}
variable (firstVisit : Steps.Acquisition.Block.SourceOccurrence
  firstVisitBlock.paid firstVisitSources firstVisitIndex)

variable {firstSelectedQuarter : UnitCircuitQuarter}
variable {firstSelectedLeg : Transport.Leg site parameter firstSelectedQuarter}
variable {firstSelectedRadicand : CoefficientPolynomial}
variable {firstSelectedDifferential : OddPowerDifferential firstSelectedRadicand}
variable {firstSelectedData : Waist.Differential.Bounds.Data site parameter firstSelectedDifferential}
variable {firstSelectedNumerical : Input.Numerical (data := firstSelectedData) firstSelectedLeg}
variable (firstSelectedTen : 10 ≤ firstSelectedNumerical.depth)
variable {firstSelectedPiece : Piece firstSelectedData firstSelectedLeg.actual
  firstSelectedNumerical.layer.accuracy}
variable (firstSelectedMember : firstSelectedPiece ∈ firstSelectedNumerical.layer.pieces)
variable {firstSelectedTarget : Endpoint}
variable {firstSelectedQueried : { reading : ReadingAt firstSelectedLeg.actual firstSelectedTarget //
  QueryCache firstSelectedLeg.actual firstSelectedTarget reading }}
variable {firstSelectedOwner : OwnerAt site parameter firstSelectedQuarter
  (of_decide_eq_true rfl) firstSelectedPiece.lowerEndpoint}
variable {firstSelectedAgreement : InitialAgreement firstSelectedPiece.lowerEndpoint
  firstSelectedPiece.source firstSelectedOwner}
variable {firstSelectedBlock : LayerBlock (regular := firstSelectedLeg.regular) firstSelectedPiece firstSelectedQueried
  firstSelectedOwner firstSelectedAgreement}
variable {firstSelectedSources : Spine.Sources (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
  (sheet := sheet) (targets := sourceTargets)
  (fun {_start _finish} segment => widthRequest firstSelectedBlock.paid.anchor segment)
  firstSelectedBlock.geometry.route.path firstSelectedBlock.geometry.route.within
  firstSelectedOwner firstSelectedBlock.paid.paid.spine}
variable {firstSelectedIndex : Fin (Spine.Sources.assemble
  (fun {_start _finish} segment => widthRequest firstSelectedBlock.paid.anchor segment)
  firstSelectedBlock.geometry.route.path firstSelectedBlock.geometry.route.within
  firstSelectedOwner firstSelectedBlock.paid.paid.spine
  firstSelectedSources).geometry.parents.length}
variable (firstSelected : Steps.Acquisition.Block.SourceOccurrence
  firstSelectedBlock.paid firstSelectedSources firstSelectedIndex)

variable {lastVisitQuarter : UnitCircuitQuarter}
variable {lastVisitLeg : Transport.Leg site parameter lastVisitQuarter}
variable {lastVisitRadicand : CoefficientPolynomial}
variable {lastVisitDifferential : OddPowerDifferential lastVisitRadicand}
variable {lastVisitData : Waist.Differential.Bounds.Data site parameter lastVisitDifferential}
variable {lastVisitNumerical : Input.Numerical (data := lastVisitData) lastVisitLeg}
variable (lastVisitTen : 10 ≤ lastVisitNumerical.depth)
variable {lastVisitPiece : Piece lastVisitData lastVisitLeg.actual
  lastVisitNumerical.layer.accuracy}
variable (lastVisitMember : lastVisitPiece ∈ lastVisitNumerical.layer.pieces)
variable {lastVisitTarget : Endpoint}
variable {lastVisitQueried : { reading : ReadingAt lastVisitLeg.actual lastVisitTarget //
  QueryCache lastVisitLeg.actual lastVisitTarget reading }}
variable {lastVisitOwner : OwnerAt site parameter lastVisitQuarter
  (of_decide_eq_true rfl) lastVisitPiece.lowerEndpoint}
variable {lastVisitAgreement : InitialAgreement lastVisitPiece.lowerEndpoint
  lastVisitPiece.source lastVisitOwner}
variable {lastVisitBlock : LayerBlock (regular := lastVisitLeg.regular) lastVisitPiece lastVisitQueried
  lastVisitOwner lastVisitAgreement}
variable {lastVisitSources : Spine.Sources (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
  (sheet := sheet) (targets := sourceTargets)
  (fun {_start _finish} segment => widthRequest lastVisitBlock.paid.anchor segment)
  lastVisitBlock.geometry.route.path lastVisitBlock.geometry.route.within
  lastVisitOwner lastVisitBlock.paid.paid.spine}
variable {lastVisitIndex : Fin (Spine.Sources.assemble
  (fun {_start _finish} segment => widthRequest lastVisitBlock.paid.anchor segment)
  lastVisitBlock.geometry.route.path lastVisitBlock.geometry.route.within
  lastVisitOwner lastVisitBlock.paid.paid.spine
  lastVisitSources).geometry.parents.length}
variable (lastVisit : Steps.Acquisition.Block.SourceOccurrence
  lastVisitBlock.paid lastVisitSources lastVisitIndex)

variable {lastSelectedQuarter : UnitCircuitQuarter}
variable {lastSelectedLeg : Transport.Leg site parameter lastSelectedQuarter}
variable {lastSelectedRadicand : CoefficientPolynomial}
variable {lastSelectedDifferential : OddPowerDifferential lastSelectedRadicand}
variable {lastSelectedData : Waist.Differential.Bounds.Data site parameter lastSelectedDifferential}
variable {lastSelectedNumerical : Input.Numerical (data := lastSelectedData) lastSelectedLeg}
variable (lastSelectedTen : 10 ≤ lastSelectedNumerical.depth)
variable {lastSelectedPiece : Piece lastSelectedData lastSelectedLeg.actual
  lastSelectedNumerical.layer.accuracy}
variable (lastSelectedMember : lastSelectedPiece ∈ lastSelectedNumerical.layer.pieces)
variable {lastSelectedTarget : Endpoint}
variable {lastSelectedQueried : { reading : ReadingAt lastSelectedLeg.actual lastSelectedTarget //
  QueryCache lastSelectedLeg.actual lastSelectedTarget reading }}
variable {lastSelectedOwner : OwnerAt site parameter lastSelectedQuarter
  (of_decide_eq_true rfl) lastSelectedPiece.lowerEndpoint}
variable {lastSelectedAgreement : InitialAgreement lastSelectedPiece.lowerEndpoint
  lastSelectedPiece.source lastSelectedOwner}
variable {lastSelectedBlock : LayerBlock (regular := lastSelectedLeg.regular) lastSelectedPiece lastSelectedQueried
  lastSelectedOwner lastSelectedAgreement}
variable {lastSelectedSources : Spine.Sources (frame := frame) (basis := basis) (count := modelCount) (floor := floor)
  (sheet := sheet) (targets := sourceTargets)
  (fun {_start _finish} segment => widthRequest lastSelectedBlock.paid.anchor segment)
  lastSelectedBlock.geometry.route.path lastSelectedBlock.geometry.route.within
  lastSelectedOwner lastSelectedBlock.paid.paid.spine}
variable {lastSelectedIndex : Fin (Spine.Sources.assemble
  (fun {_start _finish} segment => widthRequest lastSelectedBlock.paid.anchor segment)
  lastSelectedBlock.geometry.route.path lastSelectedBlock.geometry.route.within
  lastSelectedOwner lastSelectedBlock.paid.paid.spine
  lastSelectedSources).geometry.parents.length}
variable (lastSelected : Steps.Acquisition.Block.SourceOccurrence
  lastSelectedBlock.paid lastSelectedSources lastSelectedIndex)

variable (firstVisitParent : firstVisit.parent = retained.parentAt index)
variable (firstSelectedParent : firstSelected.parent =
  retained.parentAt (retained.attempt.foundSourceIndex (retained.firstPosition index firstLookup)))
variable {nextParent : CenteredEdge (Fibre.frameCurve frame) basis}
variable {remainingParents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
variable {physicalBox : Purelib.Geometry.Rational.Box} {physicalStart physicalFinish : Canonical}
variable {physicalSegment : ClearSegment (Fibre.frameCurve frame).polynomial physicalBox physicalStart physicalFinish}
variable {physicalWithin : physicalSegment.WithinAmbient}
variable {physicalOwner : Owner ((Fibre.frameCurve frame).polynomial.eval physicalStart)}
variable {physicalRequest : AccuracyRequest}
variable {physicalPaid : CoveredTracedPath.Acquisition.Segment (segment := physicalSegment)
  (within := physicalWithin) (owner := physicalOwner) physicalRequest}
variable (physicalParents : CoveredTracedPath.Acquisition.Segment.Parents basis sheet modelCount physicalPaid)
variable (physicalShape : physicalParents.covered.parents = retained.parentAt index :: nextParent :: remainingParents)
variable (lastVisitParent : lastVisit.parent = nextParent)
variable (lastSelectedParent : lastSelected.parent =
  retained.parentAt (retained.attempt.foundSourceIndex (retained.lastPosition index lastLookup)))

include firstVisitParent firstSelectedParent in
/-- The first-endpoint occurrences have equal physical coordinates by original parent and Found incidence. -/
theorem first_samePoint : firstVisit.point = firstSelected.point := by
  have visit := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    (PreparedParent.startPoint parent).coordinate) firstVisitParent
  have found := congrArg (fun point : LiftedPoint 2 => point.coordinate)
    (retained.attempt.found_source_point (retained.firstPosition index firstLookup))
  have selected := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    (PreparedParent.startPoint parent).coordinate) firstSelectedParent
  exact firstVisit.point_start.trans (visit.trans (found.symm.trans
    (selected.symm.trans firstSelected.point_start.symm)))

include physicalParents physicalShape lastVisitParent lastSelectedParent in
/-- The last-endpoint occurrences coincide by the SAME original geometric tail and retained Found incidence. -/
theorem last_samePoint : lastVisit.point = lastSelected.point := by
  have visit := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    (PreparedParent.startPoint parent).coordinate) lastVisitParent
  have adjacent : PreparedParent.startPoint nextParent = PreparedParent.finishPoint (retained.parentAt index) :=
    (physicalParents.covered.chain.castParents physicalShape).remaining.start_eq
  have joined := congrArg (fun point : LiftedPoint 2 => point.coordinate) adjacent
  have found := congrArg (fun point : LiftedPoint 2 => point.coordinate)
    (retained.attempt.found_source_point (retained.lastPosition index lastLookup))
  have selected := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    (PreparedParent.startPoint parent).coordinate) lastSelectedParent
  exact lastVisit.point_start.trans (visit.trans (joined.trans (found.symm.trans
    (selected.symm.trans lastSelected.point_start.symm))))

/-- Derive the first actual query comparison to THAT stored first Found, preserving both original endpoint owners. -/
def firstChosen : NamedEquivalent
    ((retained.parentAt index).edge.rootName 0 (retained.parentAt index).edge.baseInside)
    firstFound.original.sample.certificate.value.name := by
  have firstWidth := firstVisitBlock.width_eq.trans_le
    (firstVisitNumerical.layer.width_le 10 firstVisitTen firstVisitPiece firstVisitMember)
  have selectedWidth := firstSelectedBlock.width_eq.trans_le
    (firstSelectedNumerical.layer.width_le 10 firstSelectedTen firstSelectedPiece firstSelectedMember)
  let compared := Steps.Acquisition.Block.SourceOccurrence.queries_at_repeat
    firstVisit firstSelected firstWidth selectedWidth
    (first_samePoint (retained := retained) (index := index) (firstLookup := firstLookup)
      (firstVisit := firstVisit) (firstSelected := firstSelected)
      (firstVisitParent := firstVisitParent) (firstSelectedParent := firstSelectedParent))
  have start := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) firstVisitParent
  have chosen := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) firstSelectedParent
  let selected := NamedEquivalent.transport chosen.symm rfl
    (retained.attempt.foundQueryEquivalent (retained.firstPosition index firstLookup))
  exact (NamedEquivalent.transport start rfl compared).trans selected

/-- Derive the last actual query comparison from original adjacency and both retained repeated source origins. -/
def lastChosen : NamedEquivalent ((retained.parentAt index).edge.rootName 1 (of_decide_eq_true rfl))
    lastFound.original.sample.certificate.value.name := by
  have lastWidth := lastVisitBlock.width_eq.trans_le
    (lastVisitNumerical.layer.width_le 10 lastVisitTen lastVisitPiece lastVisitMember)
  have selectedWidth := lastSelectedBlock.width_eq.trans_le
    (lastSelectedNumerical.layer.width_le 10 lastSelectedTen lastSelectedPiece lastSelectedMember)
  let compared := Steps.Acquisition.Block.SourceOccurrence.queries_at_repeat
    lastVisit lastSelected lastWidth selectedWidth
    (last_samePoint (retained := retained) (index := index) (lastLookup := lastLookup)
      (lastVisit := lastVisit) (lastSelected := lastSelected)
      (physicalParents := physicalParents) (physicalShape := physicalShape)
      (lastVisitParent := lastVisitParent) (lastSelectedParent := lastSelectedParent))
  have start := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) lastVisitParent
  have chosen := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) lastSelectedParent
  let selected := NamedEquivalent.transport chosen.symm rfl
    (retained.attempt.foundQueryEquivalent (retained.lastPosition index lastLookup))
  let roots := RootChain.castChildren physicalShape physicalParents.subdivisionRoots
  exact roots.nextEquivalent.trans ((NamedEquivalent.transport start rfl compared).trans selected)

/-- Complete the SAME original checks using derived repeated-visit comparisons, reusing ready Commons exactly.

The supplied proofs concern whole original parent incidence and the actual
paid segment's parent list. Its retained preparation derives the signed
adjacent root chain internally; no root or sample comparison is an input. Actual
member/depth laws pay every width, and both actual lookups retain first
positions. Only originally unpaid endpoints acquire additional refinements.
The original inconclusive outcomes and all source/model observations remain.
-/
def completeAdjacent : PreparedParent.Checked.Completion (retained.checkedAt index) :=
  let firstQuery := firstChosen (retained := retained) (index := index) (firstLookup := firstLookup)
    (firstVisitTen := firstVisitTen) (firstVisitMember := firstVisitMember) (firstVisit := firstVisit)
    (firstSelectedTen := firstSelectedTen) (firstSelectedMember := firstSelectedMember)
    (firstSelected := firstSelected) (firstVisitParent := firstVisitParent)
    (firstSelectedParent := firstSelectedParent)
  let lastQuery := lastChosen (retained := retained) (index := index) (lastLookup := lastLookup)
    (lastVisitTen := lastVisitTen) (lastVisitMember := lastVisitMember) (lastVisit := lastVisit)
    (lastSelectedTen := lastSelectedTen) (lastSelectedMember := lastSelectedMember)
    (lastSelected := lastSelected) (physicalParents := physicalParents) (physicalShape := physicalShape)
    (lastVisitParent := lastVisitParent) (lastSelectedParent := lastSelectedParent)
  PreparedParent.Checked.complete (retained.checkedAt index)
    ⟨firstFound.entry, firstFound.member, firstFound.point_eq⟩
    ⟨lastFound.entry, lastFound.member, lastFound.point_eq⟩
    (fun found => NamedEquivalent.transport rfl
      (congrArg (fun vertex : Vertex parameter (PreparedParent.startPoint (retained.parentAt index)) =>
        vertex.sample.certificate.value.name) (firstFound.original_eq found)) firstQuery)
    (fun found => NamedEquivalent.transport rfl
      (congrArg (fun vertex : Vertex parameter (PreparedParent.finishPoint (retained.parentAt index)) =>
        vertex.sample.certificate.value.name) (lastFound.original_eq found)) lastQuery)

end Execution.Cache.Sources.Requested

end ActualInputs

end Steps.Acquisition.Quarter.Circuit

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
