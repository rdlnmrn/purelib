module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Circuit.Sources.Request
public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Quarter.Realization.Sources.Fine
import Purelib.Data.Fin
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Vertices.Bank.Root

/-! # Literal global source origins on the same scheduled fine quarter execution

The original shared four-quarter Execution.Cache and source families stay
inputs. Finite quarter dispatch reads the same retained fine BlockEntry;
its exact original source occurrence is retained once. A global source index
or the actual first Found position selects that SAME original cached origin,
without a new geometry, source request, observation or continuation.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Steps.Acquisition.Quarter.Input

namespace Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

open Purelib
open Purelib.Curves.Legendre.Periods
open Purelib.Curves.Legendre.Periods.Jets.Source (Vertex)
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Approximation.Rational
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Input.Realization.Sources (FineOriginCache)

variable {site : Fin 2} {parameter : Canonical} {circuit : Transport.Circuit site parameter}
variable {firstFine : Input.Fine circuit.first}
variable {sourceOwner : OwnerAt site parameter .first (of_decide_eq_true rfl) firstFine.numerical.initial.lowerEndpoint}
variable {agreement : InitialAgreement firstFine.numerical.initial.lowerEndpoint firstFine.numerical.initial.source
  sourceOwner}
variable {initial : Input.Realization (.inr firstFine) sourceOwner agreement}
variable {secondFine : Input.Fine circuit.second} {thirdFine : Input.Fine circuit.third}
variable {fourthFine : Input.Fine circuit.fourth}
variable {execution : Execution.Cache initial (.inr secondFine) (.inr thirdFine) (.inr fourthFine)}
variable {frame : Paths.Frame parameter} {basis : Differential 1}
variable {modelCount floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}
variable (sources : Execution.Cache.Sources (frame := frame) (basis := basis) (modelCount := modelCount)
  (floor := floor) (sheet := sheet) (sourceTargets := sourceTargets) execution)

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- The actual selected fine Origin cache on one SAME quarter/Block occurrence of this original execution.

This is the existing four-case finite dependent selection of the original
quarter cache types. Each case remains the actual fine Realization parent;
no old Steps execution, replacement Owner or parallel circuit is introduced.
-/
@[expose] def FineOrigin : (quarter : Fin 4) →
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length) →
    Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index) → Type 1 :=
  Data.Fin.casesDependent
    (motive := fun selected : Fin 4 =>
      (index : Fin (quarterSource sources selected).2.geometry.parents.length) →
      (position : Flatten.Occurrence (blockWords sources selected)
        (blockFlattenedIndex sources selected index)) →
      Type 1)
    (fun index position => Realization.Sources.FineOriginCache
      firstFine execution.first sources.1 index position)
    (fun second => Data.Fin.casesDependent
      (motive := fun selected : Fin 3 =>
        (index : Fin (quarterSource sources selected.succ).2.geometry.parents.length) →
        (position : Flatten.Occurrence (blockWords sources selected.succ)
          (blockFlattenedIndex sources selected.succ index)) →
        Type 1)
      (fun index position => Realization.Sources.FineOriginCache
        secondFine execution.second.paid sources.2.1 index position)
      (fun third => Data.Fin.casesDependent
        (motive := fun selected : Fin 2 =>
          (index : Fin (quarterSource sources selected.succ.succ).2.geometry.parents.length) →
          (position : Flatten.Occurrence (blockWords sources selected.succ.succ)
            (blockFlattenedIndex sources selected.succ.succ index)) →
          Type 1)
        (fun index position => Realization.Sources.FineOriginCache
          thirdFine execution.third.paid sources.2.2.1 index position)
        (fun _ : Fin 1 => fun index position => Realization.Sources.FineOriginCache
          fourthFine execution.fourth.paid sources.2.2.2 index position) third) second)

/-- Retain the exact selected original Entry/origin pair once on the SAME four-quarter source occurrence. -/
def fineOrigin : (quarter : Fin 4) →
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length) →
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) →
    FineOrigin sources quarter index position :=
  Data.Fin.casesDependent
    (motive := fun selected : Fin 4 =>
      (index : Fin (quarterSource sources selected).2.geometry.parents.length) →
      (position : Flatten.Occurrence (blockWords sources selected)
        (blockFlattenedIndex sources selected index)) →
      FineOrigin sources selected index position)
    (fun index position => Realization.Sources.keepFineOrigin
      firstFine execution.first sources.1 index position)
    (fun second => Data.Fin.casesDependent
      (motive := fun selected : Fin 3 =>
        (index : Fin (quarterSource sources selected.succ).2.geometry.parents.length) →
        (position : Flatten.Occurrence (blockWords sources selected.succ)
          (blockFlattenedIndex sources selected.succ index)) →
        FineOrigin sources selected.succ index position)
      (fun index position => Realization.Sources.keepFineOrigin
        secondFine execution.second.paid sources.2.1 index position)
      (fun third => Data.Fin.casesDependent
        (motive := fun selected : Fin 2 =>
          (index : Fin (quarterSource sources selected.succ.succ).2.geometry.parents.length) →
          (position : Flatten.Occurrence (blockWords sources selected.succ.succ)
            (blockFlattenedIndex sources selected.succ.succ index)) →
          FineOrigin sources selected.succ.succ index position)
        (fun index position => Realization.Sources.keepFineOrigin
          thirdFine execution.third.paid sources.2.2.1 index position)
        (fun _ : Fin 1 => fun index position => Realization.Sources.keepFineOrigin
          fourthFine execution.fourth.paid sources.2.2.2 index position) third) second)

namespace FineOrigin

variable {sources}

/-- Read the literal original centered parent carried by the actual selected fine source occurrence. -/
@[expose] def parent : (quarter : Fin 4) →
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length) →
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) →
    FineOrigin sources quarter index position → CenteredEdge (Fibre.frameCurve frame) basis :=
  Data.Fin.casesDependent
    (motive := fun selected : Fin 4 =>
      (index : Fin (quarterSource sources selected).2.geometry.parents.length) →
      (position : Flatten.Occurrence (blockWords sources selected)
        (blockFlattenedIndex sources selected index)) →
      FineOrigin sources selected index position →
      CenteredEdge (Fibre.frameCurve frame) basis)
    (fun _index _position cached => cached.origin.occurrence.parent)
    (fun second => Data.Fin.casesDependent
      (motive := fun selected : Fin 3 =>
        (index : Fin (quarterSource sources selected.succ).2.geometry.parents.length) →
        (position : Flatten.Occurrence (blockWords sources selected.succ)
          (blockFlattenedIndex sources selected.succ index)) →
        FineOrigin sources selected.succ index position →
        CenteredEdge (Fibre.frameCurve frame) basis)
      (fun _index _position cached => cached.origin.occurrence.parent)
      (fun third => Data.Fin.casesDependent
        (motive := fun selected : Fin 2 =>
          (index : Fin (quarterSource sources selected.succ.succ).2.geometry.parents.length) →
          (position : Flatten.Occurrence (blockWords sources selected.succ.succ)
            (blockFlattenedIndex sources selected.succ.succ index)) →
          FineOrigin sources selected.succ.succ index position →
          CenteredEdge (Fibre.frameCurve frame) basis)
        (fun _index _position cached => cached.origin.occurrence.parent)
        (fun _ : Fin 1 => fun _index _position cached => cached.origin.occurrence.parent) third) second)

/-- Every finite branch retains the SAME entire original selected quarter parent, including its root/Step caches. -/
theorem parent_eq (quarter : Fin 4)
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index))
    (cached : FineOrigin sources quarter index position) :
    parent quarter index position cached =
      (quarterSource sources quarter).2.geometry.parents[index.val]'index.isLt := by
  revert index position cached
  refine Data.Fin.cases_induction ?_ (fun second => ?_) quarter
  · intro index position cached
    exact FineOriginCache.parent_eq cached
  · refine Data.Fin.cases_induction ?_ (fun third => ?_) second
    · intro index position cached
      exact FineOriginCache.parent_eq cached
    · refine Data.Fin.cases_induction ?_ (fun _fourth => ?_) third
      · intro index position cached
        exact FineOriginCache.parent_eq cached
      · intro index position cached
        exact FineOriginCache.parent_eq cached

/-- Read the SAME selected Block's actual squared source-to-target time width. -/
@[expose] def width : (quarter : Fin 4) →
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length) →
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index)) →
    FineOrigin sources quarter index position → Fraction.Rational :=
  Data.Fin.casesDependent
    (motive := fun selected : Fin 4 =>
      (index : Fin (quarterSource sources selected).2.geometry.parents.length) →
      (position : Flatten.Occurrence (blockWords sources selected)
        (blockFlattenedIndex sources selected index)) →
      FineOrigin sources selected index position → Fraction.Rational)
    (fun _index _position cached => (cached.origin.piece.span.lower - cached.origin.target.parameter) ^ 2)
    (fun second => Data.Fin.casesDependent
      (motive := fun selected : Fin 3 =>
        (index : Fin (quarterSource sources selected.succ).2.geometry.parents.length) →
        (position : Flatten.Occurrence (blockWords sources selected.succ)
          (blockFlattenedIndex sources selected.succ index)) →
        FineOrigin sources selected.succ index position → Fraction.Rational)
      (fun _index _position cached => (cached.origin.piece.span.lower - cached.origin.target.parameter) ^ 2)
      (fun third => Data.Fin.casesDependent
        (motive := fun selected : Fin 2 =>
          (index : Fin (quarterSource sources selected.succ.succ).2.geometry.parents.length) →
          (position : Flatten.Occurrence (blockWords sources selected.succ.succ)
            (blockFlattenedIndex sources selected.succ.succ index)) →
          FineOrigin sources selected.succ.succ index position → Fraction.Rational)
        (fun _index _position cached => (cached.origin.piece.span.lower - cached.origin.target.parameter) ^ 2)
        (fun _ : Fin 1 => fun _index _position cached =>
          (cached.origin.piece.span.lower - cached.origin.target.parameter) ^ 2) third) second)

/-- Actual scheduled depths pay the precise selected Block width in every original quarter branch. -/
theorem width_le (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth) (quarter : Fin 4)
    (index : Fin (quarterSource sources quarter).2.geometry.parents.length)
    (position : Flatten.Occurrence (blockWords sources quarter) (blockFlattenedIndex sources quarter index))
    (cached : FineOrigin sources quarter index position) :
    width quarter index position cached ≤ Geometric.Basic.quarterRadius 1 10 := by
  revert index position cached
  refine Data.Fin.cases_induction ?_ (fun second => ?_) quarter
  · intro index position cached
    exact FineOriginCache.width cached firstTen
  · refine Data.Fin.cases_induction ?_ (fun third => ?_) second
    · intro index position cached
      exact FineOriginCache.width cached secondTen
    · refine Data.Fin.cases_induction ?_ (fun _fourth => ?_) third
      · intro index position cached
        exact FineOriginCache.width cached thirdTen
      · intro index position cached
        exact FineOriginCache.width cached fourthTen

/-- Compare two literal fine-quarter source queries at an actual repeated physical point.

Both complete original origin caches remain inputs. Finite quarter dispatch
uses each original Layer depth payment and the retained half-open Route,
normalized-window and cofactor comparisons. Neither a source query nor an
observation is reacquired by this comparison.
-/
def queries_at_repeat (firstTen : 10 ≤ firstFine.numerical.depth)
    (secondTen : 10 ≤ secondFine.numerical.depth) (thirdTen : 10 ≤ thirdFine.numerical.depth)
    (fourthTen : 10 ≤ fourthFine.numerical.depth) (leftQuarter rightQuarter : Fin 4)
    (leftIndex : Fin (quarterSource sources leftQuarter).2.geometry.parents.length)
    (leftPosition : Flatten.Occurrence (blockWords sources leftQuarter)
      (blockFlattenedIndex sources leftQuarter leftIndex))
    (left : FineOrigin sources leftQuarter leftIndex leftPosition)
    (rightIndex : Fin (quarterSource sources rightQuarter).2.geometry.parents.length)
    (rightPosition : Flatten.Occurrence (blockWords sources rightQuarter)
      (blockFlattenedIndex sources rightQuarter rightIndex))
    (right : FineOrigin sources rightQuarter rightIndex rightPosition)
    (samePoint : (PreparedParent.startPoint (parent leftQuarter leftIndex leftPosition left)).coordinate =
      (PreparedParent.startPoint (parent rightQuarter rightIndex rightPosition right)).coordinate) :
    NamedEquivalent
      ((parent leftQuarter leftIndex leftPosition left).edge.rootName 0
        (parent leftQuarter leftIndex leftPosition left).edge.baseInside)
      ((parent rightQuarter rightIndex rightPosition right).edge.rootName 0
        (parent rightQuarter rightIndex rightPosition right).edge.baseInside) := by
  revert leftIndex leftPosition left rightIndex rightPosition right samePoint
  cases leftQuarter using Data.Fin.casesDependent with
  | first =>
    intro leftIndex leftPosition left
    cases rightQuarter using Data.Fin.casesDependent with
    | first =>
      intro rightIndex rightPosition right samePoint
      exact FineOriginCache.queries_at_repeat left right firstTen firstTen samePoint
    | following right1 =>
      cases right1 using Data.Fin.casesDependent with
      | first =>
        intro rightIndex rightPosition right samePoint
        exact FineOriginCache.queries_at_repeat left right firstTen secondTen samePoint
      | following right2 =>
        cases right2 using Data.Fin.casesDependent with
        | first =>
          intro rightIndex rightPosition right samePoint
          exact FineOriginCache.queries_at_repeat left right firstTen thirdTen samePoint
        | following right3 =>
          intro rightIndex rightPosition right samePoint
          exact FineOriginCache.queries_at_repeat left right firstTen fourthTen samePoint
  | following left1 =>
    cases left1 using Data.Fin.casesDependent with
    | first =>
      intro leftIndex leftPosition left
      cases rightQuarter using Data.Fin.casesDependent with
      | first =>
        intro rightIndex rightPosition right samePoint
        exact FineOriginCache.queries_at_repeat left right secondTen firstTen samePoint
      | following right1 =>
        cases right1 using Data.Fin.casesDependent with
        | first =>
          intro rightIndex rightPosition right samePoint
          exact FineOriginCache.queries_at_repeat left right secondTen secondTen samePoint
        | following right2 =>
          cases right2 using Data.Fin.casesDependent with
          | first =>
            intro rightIndex rightPosition right samePoint
            exact FineOriginCache.queries_at_repeat left right secondTen thirdTen samePoint
          | following right3 =>
            intro rightIndex rightPosition right samePoint
            exact FineOriginCache.queries_at_repeat left right secondTen fourthTen samePoint
    | following left2 =>
      cases left2 using Data.Fin.casesDependent with
      | first =>
        intro leftIndex leftPosition left
        cases rightQuarter using Data.Fin.casesDependent with
        | first =>
          intro rightIndex rightPosition right samePoint
          exact FineOriginCache.queries_at_repeat left right thirdTen firstTen samePoint
        | following right1 =>
          cases right1 using Data.Fin.casesDependent with
          | first =>
            intro rightIndex rightPosition right samePoint
            exact FineOriginCache.queries_at_repeat left right thirdTen secondTen samePoint
          | following right2 =>
            cases right2 using Data.Fin.casesDependent with
            | first =>
              intro rightIndex rightPosition right samePoint
              exact FineOriginCache.queries_at_repeat left right thirdTen thirdTen samePoint
            | following right3 =>
              intro rightIndex rightPosition right samePoint
              exact FineOriginCache.queries_at_repeat left right thirdTen fourthTen samePoint
      | following left3 =>
        intro leftIndex leftPosition left
        cases rightQuarter using Data.Fin.casesDependent with
        | first =>
          intro rightIndex rightPosition right samePoint
          exact FineOriginCache.queries_at_repeat left right fourthTen firstTen samePoint
        | following right1 =>
          cases right1 using Data.Fin.casesDependent with
          | first =>
            intro rightIndex rightPosition right samePoint
            exact FineOriginCache.queries_at_repeat left right fourthTen secondTen samePoint
          | following right2 =>
            cases right2 using Data.Fin.casesDependent with
            | first =>
              intro rightIndex rightPosition right samePoint
              exact FineOriginCache.queries_at_repeat left right fourthTen thirdTen samePoint
            | following right3 =>
              intro rightIndex rightPosition right samePoint
              exact FineOriginCache.queries_at_repeat left right fourthTen fourthTen samePoint

end FineOrigin

variable (index : Fin (assemble sources).geometry.parents.length)
variable (position : Flatten.Occurrence (parentWords sources) (flattenedIndex sources index))

/-- One exact original Block location and its SAME complete fine Entry/origin cache, with whole factory equations.

The supplied global location remains the original occurrence index.
Readonly finite descent runs once below that location and retains both
actual results; the original sources and paid execution are unchanged.
-/
@[expose] def OriginAt :=
  Σ inBlock : { value : Flatten.Occurrence (blockWords sources (quarter sources index position))
      (blockFlattenedIndex sources (quarter sources index position) (child sources index position)) //
    value = locateBlock sources (quarter sources index position) (child sources index position) },
    { cached : FineOrigin sources (quarter sources index position) (child sources index position) inBlock.val //
      cached = fineOrigin sources (quarter sources index position) (child sources index position) inBlock.val }

/-- Descend through the SAME original Block cache once, then retain its actual fine source origin once. -/
def keepOriginAt : OriginAt sources index position :=
  let inBlock := locateBlock sources (quarter sources index position) (child sources index position)
  let cached := fineOrigin sources (quarter sources index position) (child sources index position) inBlock
  ⟨⟨inBlock, rfl⟩, ⟨cached, rfl⟩⟩

namespace OriginAt

variable {sources index position} (retained : OriginAt sources index position)

/-- Read the literal original Block position retained below this SAME global source occurrence. -/
@[expose] def inBlock := retained.1.val

/-- The retained Block position is the WHOLE original finite locator output, with no source lookup replay. -/
theorem inBlock_eq : retained.inBlock =
    locateBlock sources (quarter sources index position) (child sources index position) := retained.1.property

/-- Read the SAME complete actual fine Entry/origin cache at that exact retained Block occurrence. -/
@[expose] def cached := retained.2.val

/-- The complete actual fine cache is the original readonly factory on the SAME retained Block position. -/
theorem cached_eq : retained.cached =
    fineOrigin sources (quarter sources index position) (child sources index position) retained.inBlock :=
  retained.2.property

/-- Read the SAME original complete parent carried by this literal globally selected fine source origin. -/
@[expose] def parent : CenteredEdge (Fibre.frameCurve frame) basis :=
  FineOrigin.parent (quarter sources index position) (child sources index position) retained.inBlock retained.cached

/-- Whole original quarter/global incidence identifies this literal source origin with the SAME global parent. -/
theorem parent_eq : retained.parent = (assemble sources).geometry.parents[index.val]'index.isLt :=
  (FineOrigin.parent_eq (quarter sources index position) (child sources index position)
    retained.inBlock retained.cached).trans (Execution.Cache.Sources.parent_eq sources index position).symm

/-- The actual fine origin below this global occurrence retains its original precise squared Route width. -/
@[expose] def width : Fraction.Rational :=
  FineOrigin.width (quarter sources index position) (child sources index position) retained.inBlock retained.cached

/-- Four genuine scheduled quarter depths pay this SAME retained global occurrence's repeat-window width. -/
theorem width_le (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth) :
    retained.width ≤ Geometric.Basic.quarterRadius 1 10 :=
  FineOrigin.width_le firstTen secondTen thirdTen fourthTen (quarter sources index position)
    (child sources index position) retained.inBlock retained.cached

end OriginAt

namespace Requested

variable {sources} {current freshFloor rootStage : Nat} {accuracy : AccuracyRequest}
variable (requested : Requested sources current freshFloor rootStage accuracy)
variable (sourceIndex : Fin (requested.shape.val.1 :: requested.shape.val.2).length)

/-- An actual visiting fresh-source position and original fine-origin descent retain both whole readonly results. -/
@[expose] def SourceOrigin :=
  Σ located : { value : Flatten.Occurrence (parentWords sources)
      (flattenedIndex sources (requested.originalIndex sourceIndex)) //
    value = locate sources (requested.originalIndex sourceIndex) },
      OriginAt sources (requested.originalIndex sourceIndex) located.val

/-- Read the SAME actual visiting source's retained fine origin through its original global incidence once. -/
def keepSourceOrigin : SourceOrigin requested sourceIndex :=
  let located := locate sources (requested.originalIndex sourceIndex)
  let cached := keepOriginAt sources (requested.originalIndex sourceIndex) located
  ⟨⟨located, rfl⟩, cached⟩

namespace SourceOrigin

variable {requested sourceIndex} (retained : SourceOrigin requested sourceIndex)

/-- Read the actual original global location of this SAME freshly prepared visiting source. -/
@[expose] def location := retained.1.val

/-- The retained source position is the WHOLE original structural locator result on this SAME global index. -/
theorem location_eq : retained.location = locate sources (requested.originalIndex sourceIndex) := retained.1.property

/-- Read the complete original fine-origin descent, retaining its actual BlockEntry, Sources and SourceOccurrence. -/
@[expose] def origin := retained.2

/-- The original fine origin and fresh source have the SAME whole centered parent, retaining different preparations. -/
theorem parent_eq : retained.origin.parent =
    (requested.shape.val.1 :: requested.shape.val.2)[sourceIndex.val]'sourceIndex.isLt := by
  have old := retained.origin.parent_eq
  have same := getElem_congr (i := (requested.assembledIndex sourceIndex).val)
    (j := (requested.assembledIndex sourceIndex).val) requested.parents_eq rfl
    (requested.assembledIndex sourceIndex).isLt
  exact old.trans (same.symm.trans (requested.parent_eq sourceIndex))

/-- Compare the actual queries at two retained visiting fresh-source occurrences of the same fine execution.

Both old fine-origin caches are retained at their literal global positions.
Whole parent incidence transports only query indices; the original fine
repeat comparison supplies the signed relation. The fresh preparations,
old requests, selected observations and visible radii stay distinct.
-/
def queries_at_repeat {leftIndex rightIndex : Fin (requested.shape.val.1 :: requested.shape.val.2).length}
    (left : SourceOrigin requested leftIndex) (right : SourceOrigin requested rightIndex)
    (firstTen : 10 ≤ firstFine.numerical.depth) (secondTen : 10 ≤ secondFine.numerical.depth)
    (thirdTen : 10 ≤ thirdFine.numerical.depth) (fourthTen : 10 ≤ fourthFine.numerical.depth)
    (samePoint :
      (PreparedParent.startPoint
        ((requested.shape.val.1 :: requested.shape.val.2)[leftIndex.val]'leftIndex.isLt)).coordinate =
      (PreparedParent.startPoint
        ((requested.shape.val.1 :: requested.shape.val.2)[rightIndex.val]'rightIndex.isLt)).coordinate) :
    NamedEquivalent
      (((requested.shape.val.1 :: requested.shape.val.2)[leftIndex.val]'leftIndex.isLt).edge.rootName 0
        ((requested.shape.val.1 :: requested.shape.val.2)[leftIndex.val]'leftIndex.isLt).edge.baseInside)
      (((requested.shape.val.1 :: requested.shape.val.2)[rightIndex.val]'rightIndex.isLt).edge.rootName 0
        ((requested.shape.val.1 :: requested.shape.val.2)[rightIndex.val]'rightIndex.isLt).edge.baseInside) := by
  have leftPoint := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    (PreparedParent.startPoint parent).coordinate) left.parent_eq
  have rightPoint := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    (PreparedParent.startPoint parent).coordinate) right.parent_eq
  let compared := FineOrigin.queries_at_repeat (sources := sources)
    firstTen secondTen thirdTen fourthTen
    (quarter sources (requested.originalIndex leftIndex) left.location)
    (quarter sources (requested.originalIndex rightIndex) right.location)
    (child sources (requested.originalIndex leftIndex) left.location) left.origin.inBlock left.origin.cached
    (child sources (requested.originalIndex rightIndex) right.location) right.origin.inBlock right.origin.cached
    (leftPoint.trans (samePoint.trans rightPoint.symm))
  have leftName := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) left.parent_eq
  have rightName := congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis =>
    parent.edge.rootName 0 parent.edge.baseInside) right.parent_eq
  exact NamedEquivalent.transport leftName rightName compared

end SourceOrigin

variable {point : LiftedPoint 2} {found : Vertex.Bank.Found requested.bank point}
variable (selected : Vertex.Bank.Position (.found found))

/-- The exact first Found's global location and actual fine-origin descent, retained once without another bank scan.

The selected bank Position remains the original stored first match. Only
structural source/Block locators run; fresh Stage preparations and all old
local SourceOccurrences remain distinct retained inputs.
-/
@[expose] def FoundOrigin :=
  Σ located : { value : Flatten.Occurrence (parentWords sources)
      (flattenedIndex sources (requested.foundAssembledIndex selected)) //
    value = requested.locateFound selected },
      OriginAt sources (requested.foundAssembledIndex selected) located.val

/-- Read the SAME first selected source occurrence, then retain its complete actual fine Block/origin caches. -/
def keepFoundOrigin : FoundOrigin requested selected :=
  let located := requested.locateFound selected
  let cached := keepOriginAt sources (requested.foundAssembledIndex selected) located
  ⟨⟨located, rfl⟩, cached⟩

namespace FoundOrigin

variable {requested selected} (retained : FoundOrigin requested selected)

/-- Read the exact globally selected original source location retained with the actual first Found. -/
@[expose] def location := retained.1.val

/-- This actual location is the original structural locator on THAT first retained bank occurrence. -/
theorem location_eq : retained.location = requested.locateFound selected := retained.1.property

/-- Read the SAME original complete fine source-origin cache below the literal first selected source occurrence. -/
@[expose] def origin := retained.2

/-- The exact original selected fine parent is the SAME actual fresh global source parent chosen by first Found.

This is equality of entire original centered parents and their query/Step
indices. Fresh and old preparations/observations are not identified. Their
original same-edge query comparisons remain the required operational bridge.
-/
theorem parent_eq : retained.origin.parent =
    (requested.shape.val.1 :: requested.shape.val.2)[(requested.foundSourceIndex selected).val]'
      (requested.foundSourceIndex selected).isLt := by
  have old := retained.origin.parent_eq
  have same := getElem_congr (i := (requested.assembledIndex (requested.foundSourceIndex selected)).val)
    (j := (requested.assembledIndex (requested.foundSourceIndex selected)).val) requested.parents_eq rfl
    (requested.assembledIndex (requested.foundSourceIndex selected)).isLt
  exact old.trans (same.symm.trans (requested.parent_eq (requested.foundSourceIndex selected)))

/-- The retained original selected parent has exactly the actual first Found's lifted source point and sheet. -/
theorem point_eq : PreparedParent.startPoint retained.origin.parent = point :=
  (congrArg (fun parent : CenteredEdge (Fibre.frameCurve frame) basis => PreparedParent.startPoint parent)
    retained.parent_eq).trans (requested.attempt.found_source_point selected)

end FoundOrigin

end Requested

end Steps.Acquisition.Quarter.Circuit.Execution.Cache.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
