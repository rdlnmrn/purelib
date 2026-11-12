module

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel.Steps.Acquisition.Observation.Source
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Trace.Physical.Spine.Assembly
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
import Purelib.Data.List.Flatten.Occurrence
import Purelib.Data.List.Append
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence
import Purelib.Approximation.Gaussian.Equivalence

/-! # Actual quarter source parents assembled from the same retained paid Blocks

The complete original Steps and paid Acquisition retain every source/target
Reading, geometric Route, physical acquisition and source product. The fold
reads those SAME nested Sources and joins their existing covered parents in
Block/Segment/child order. No new query, allocation or transport is executed.
-/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.Trace.Physical
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Factors.Segment.Reading.Payment
  (widthRequest)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision (Endpoint finalTarget)
open Purelib.Riemann.Meshes

variable {site : Fin 2} {parameter : Canonical} {unitQuarter : UnitCircuitQuarter}
variable {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 unitQuarter positive} {regular : parameter ≠ criticalValue site}
variable {frame : Paths.Frame parameter} {basis : Differential 1} {count floor : Nat} {sheet : Fin 2}
variable {baseStart baseFinish : LiftedPoint 2} {sourcePath : LiftedPath 2 baseStart baseFinish} {stage : Nat}
variable {sourceTargets : CellEndpoints.Targets sourcePath stage}

attribute [local irreducible] coordinate
attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt

namespace Steps.Acquisition.Observation.Blocks.Sources

/-- Assemble the exact actual Block/physical-Segment source parents without re-querying or preparing any source.

Every original paid head and actual unchanged tail are inputs. The stored
physical Sources provide their SAME centers, covering patches and complete
six-channel preparation products on the original supplied Targets.
-/
def assemble : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid →
    Spine.Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := sourceTargets) (coordinate site parameter 2 unitQuarter positive current.parameter)
      (coordinate site parameter 2 unitQuarter positive (finalTarget current targets).parameter)
  | [], _, _, _, _, _, _, _, _ => ⟨⟨[], .nil _⟩, .nil, PUnit.unit⟩
  | target :: targets, _, _, _, original, sourceOwner, _, paid, sources =>
      let first := Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
        original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine sources.1
      let following := assemble targets target original.nextReading original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
      first.append following
termination_by structural targets => targets

section Occurrences

open Purelib.Data.List
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)

attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Read one exact original physical source-parent word per retained paid Block, keeping empty Routes in order. -/
@[expose] def parentWords : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid →
    List (List (CenteredEdge (Curves.Legendre.Periods.Fibre.frameCurve frame) basis))
  | [] => fun _ _ _ _ _ _ _ _ => []
  | target :: targets => fun _ _ _ original sourceOwner _ paid sources =>
      (Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
        original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine
        sources.1).geometry.parents ::
      parentWords targets target original.nextReading original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
termination_by structural targets => targets

/-- The actual ordered Block assembly is the literal flattening of its same original cached parent words. -/
theorem assemble_parents : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (assemble targets current reading originalOwner original sourceOwner agreement paid sources).geometry.parents =
      (parentWords targets current reading originalOwner original sourceOwner agreement paid sources).flatten
  | [] => fun _ _ _ _ _ _ _ _ => rfl
  | target :: targets => fun _ _ _ original sourceOwner _ paid sources => by
      let first := Spine.Sources.assemble
        (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
        original.headGeometry.route.path original.headGeometry.route.within sourceOwner
            paid.head.paid.spine sources.1
      let following := assemble targets target original.nextReading original.headCovered.finishOwner original.tail
        paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
      change (first.append following).geometry.parents = _
      rewrite [Spine.Sources.Assembled.append_parents]
      exact congrArg (List.append first.geometry.parents)
        (assemble_parents targets target original.nextReading original.headCovered.finishOwner original.tail
          paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2)
termination_by structural targets => targets

/-- An exact view of one original retained Block and its complete original physical source family.

The family follows ONLY the same original target list and paid/source tails.
Its head retains the two existing parents and their whole input identity;
it introduces no new context record, root Owner, execution or observer.
-/
@[expose] def Entry : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    Fin (parentWords targets current reading originalOwner original sourceOwner agreement paid sources).length → Type 1
  | [] => fun _ _ _ _ _ _ _ _ index => Fin.elim0 index
  | target :: targets => fun _ _ _ original sourceOwner agreement paid sources index =>
      Fin.cases
        { retained : Block original.2.1 original.headGeometry sourceOwner agreement ×
            Spine.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
              (targets := sourceTargets)
              (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
              original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine //
          retained = (paid.head, sources.1) }
        (fun next => Entry targets target original.nextReading original.headCovered.finishOwner original.tail
          paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2 next) index
termination_by structural targets => targets

/-- Read the SAME complete original Block/source pair at one bounded original Block occurrence.

At a successor the getter follows literal original next Reading, paid
finishOwner and unchanged Sources tail. All cached factor budgets,
Geometry, comparisons, Endpoint, source requests and observations survive.
No original factory is called and no older Owner is retagged.
-/
@[expose] def entry : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (index : Fin
      (parentWords targets current reading originalOwner original sourceOwner agreement paid sources).length) →
    Entry targets current reading originalOwner original sourceOwner agreement paid sources index
  | [] => fun _ _ _ _ _ _ _ _ index => Fin.elim0 index
  | target :: targets => fun _ _ _ original _ _ paid sources index =>
      Fin.cases ⟨(paid.head, sources.1), rfl⟩
        (fun next => entry targets target original.nextReading original.headCovered.finishOwner original.tail
          paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2 next) index
termination_by structural targets => targets

/-- A complete original covering/preparation pair indexed by one exact original parent word. -/
@[expose] def SourcePair (parents : List (CenteredEdge (Curves.Legendre.Periods.Fibre.frameCurve frame) basis)) :=
  Σ covered : CoveredParents count parents, PreparedParents covered floor sourceTargets

namespace Entry

/-- Read the same complete actual source pair from a supplied original Block occurrence view.

The actual retained source input is consumed by the original assembler.
Its whole equality to the original input transports only that exact pair's
parent index. No source allocation, covering preparation or observation runs.
-/
@[expose] def sources : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (index : Fin
      (parentWords targets current reading originalOwner original sourceOwner agreement paid sources).length) →
    Entry targets current reading originalOwner original sourceOwner agreement paid sources index →
    SourcePair (frame := frame) (basis := basis) (count := count) (floor := floor)
      (sourceTargets := sourceTargets)
      ((parentWords targets current reading originalOwner original sourceOwner agreement paid sources)[
        index.val]'index.isLt)
  | [] => fun _ _ _ _ _ _ _ _ index => Fin.elim0 index
  | target :: targets => fun _ _ _ original sourceOwner _ paid sources index =>
      Fin.cases
        (fun retained =>
          let actual := Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
            original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine
            retained.val.2
          have same : actual.geometry.parents =
              (Spine.Sources.assemble
                (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
                original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine
                sources.1).geometry.parents :=
            congrArg (fun kept => (Spine.Sources.assemble
              (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
              original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.spine
              kept).geometry.parents) (congrArg Prod.snd retained.property)
          PreparedParents.castParents same actual.covered actual.prepared)
        (fun next retained => Entry.sources targets target original.nextReading
          original.headCovered.finishOwner original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail
          sources.2 next retained) index
termination_by structural targets => targets

end Entry

/-- Exact Block-prefix offsets retain the SAME whole original PreparedParent through the actual quarter assembly. -/
theorem assemble_entry_heq : (targets : List Endpoint) → (current : Endpoint) → (reading : ReadingAt actual current) →
    (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    (outer : Fin
      (parentWords targets current reading originalOwner original sourceOwner agreement paid sources).length) →
    (child : Fin ((parentWords targets current reading originalOwner original sourceOwner agreement paid sources)[
      outer.val]'outer.isLt).length) →
    (globalIndex : Fin
      (assemble targets current reading originalOwner original sourceOwner agreement paid
        sources).geometry.parents.length) →
    globalIndex.val =
      ((parentWords targets current reading originalOwner original sourceOwner agreement paid sources).take
        outer.val).flatten.length + child.val →
    HEq ((assemble targets current reading originalOwner original sourceOwner agreement paid sources).prepared.entry
      globalIndex)
      ((Entry.sources targets current reading originalOwner original sourceOwner agreement paid sources outer
        (entry targets current reading originalOwner original sourceOwner agreement paid sources outer)).2.entry child)
  | [] => fun _ _ _ _ _ _ _ _ outer => Fin.elim0 outer
  | target :: targets => fun _ _ _ original sourceOwner _ paid sources outer =>
      Fin.cases
        (fun child globalIndex offset => by
          let first := Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
            original.headGeometry.route.path original.headGeometry.route.within sourceOwner
            paid.head.paid.spine sources.1
          let following := assemble targets target original.nextReading original.headCovered.finishOwner original.tail
            paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
          have scalar : globalIndex.val = child.val := offset.trans (Nat.zero_add child.val)
          exact first.append_entry_left following child globalIndex scalar)
        (fun next child globalIndex offset => by
          let first := Spine.Sources.assemble
            (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
            original.headGeometry.route.path original.headGeometry.route.within sourceOwner
            paid.head.paid.spine sources.1
          let following := assemble targets target original.nextReading original.headCovered.finishOwner original.tail
            paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
          let words := parentWords targets target original.nextReading original.headCovered.finishOwner original.tail
            paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
          have prefixLength :
              ((parentWords (target :: targets) _ _ _ original sourceOwner _ paid sources).take
                next.succ.val).flatten.length =
                first.geometry.parents.length + (words.take next.val).flatten.length := by
            change (first.geometry.parents ++ (words.take next.val).flatten).length = _
            exact Append.length_append _ _
          let tailValue := (words.take next.val).flatten.length + child.val
          have scalar : globalIndex.val = first.geometry.parents.length + tailValue :=
            (offset.trans (congrArg (fun value => value + child.val) prefixLength)).trans (Nat.add_assoc _ _ _)
          have lengthEq : (first.append following).geometry.parents.length =
              first.geometry.parents.length + following.geometry.parents.length :=
            (congrArg List.length (Spine.Sources.Assembled.append_parents first following)).trans
              (Append.length_append first.geometry.parents following.geometry.parents)
          have fullBound : globalIndex.val < first.geometry.parents.length + following.geometry.parents.length :=
            Eq.mp (congrArg (fun length => globalIndex.val < length) lengthEq) globalIndex.isLt
          have tailBound : tailValue < following.geometry.parents.length := Nat.lt_of_add_lt_add_left
            (Eq.mp (congrArg (fun value => value <
              first.geometry.parents.length + following.geometry.parents.length) scalar) fullBound)
          let tailIndex : Fin following.geometry.parents.length := ⟨tailValue, tailBound⟩
          have inTail := first.append_entry_right following tailIndex globalIndex scalar
          exact inTail.trans
            (assemble_entry_heq targets target original.nextReading original.headCovered.finishOwner original.tail
              paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2 next child tailIndex rfl)) outer
termination_by structural targets => targets

section Located

variable (targets : List Endpoint) (current : Endpoint) (reading : ReadingAt actual current)
variable (originalOwner : OwnerAt site parameter unitQuarter positive current)
variable (original : Steps actual regular current reading originalOwner targets)
variable (sourceOwner : OwnerAt site parameter unitQuarter positive current)
variable (agreement : InitialAgreement current reading sourceOwner)
variable (paid : Acquisition original sourceOwner agreement)
variable (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
  (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid)
variable (index : Fin
  (assemble targets current reading originalOwner original sourceOwner agreement paid sources).geometry.parents.length)

/-- Read the SAME natural global source position in the exact flattened original Block words. -/
@[expose] def flattenedIndex : Fin
    (parentWords targets current reading originalOwner original sourceOwner agreement paid sources).flatten.length :=
  ⟨index.val, Eq.mp (congrArg (fun length => index.val < length)
    (congrArg List.length (assemble_parents targets current reading originalOwner original sourceOwner agreement
      paid sources))) index.isLt⟩

/-- Locate the actual global source's Block/child occurrence with the ORIGINAL finite flatten worker once. -/
def locate : Flatten.Occurrence
    (parentWords targets current reading originalOwner original sourceOwner agreement paid sources)
    (flattenedIndex targets current reading originalOwner original sourceOwner agreement paid sources index) :=
  Flatten.locate (parentWords targets current reading originalOwner original sourceOwner agreement paid sources)
    (flattenedIndex targets current reading originalOwner original sourceOwner agreement paid sources index)

/-- The actual complete global Block occurrence is the SAME original ordered flatten-locator factory value. -/
theorem locate_eq : locate targets current reading originalOwner original sourceOwner agreement paid sources index =
    Flatten.locate (parentWords targets current reading originalOwner original sourceOwner agreement paid sources)
      (flattenedIndex targets current reading originalOwner original sourceOwner agreement paid sources index) := by
  unfold locate
  rfl

variable (position : Flatten.Occurrence
  (parentWords targets current reading originalOwner original sourceOwner agreement paid sources)
  (flattenedIndex targets current reading originalOwner original sourceOwner agreement paid sources index))

/-- Read the original full Block/source cache at the SAME retained global occurrence, without another scan. -/
@[expose] def selected :=
  entry targets current reading originalOwner original sourceOwner agreement paid sources position.1

/-- Read the selected original physical covering/preparation pair with its whole source-cache transport. -/
@[expose] def selectedSources :=
  Entry.sources targets current reading originalOwner original sourceOwner agreement paid sources position.1
    (selected targets current reading originalOwner original sourceOwner agreement paid sources index position)

/-- The actual global parent is its exact original selected Block child, including all original query/Step data. -/
theorem parent_eq :
    (assemble targets current reading originalOwner original sourceOwner agreement paid sources).geometry.parents[
      index.val]'index.isLt =
    ((parentWords targets current reading originalOwner original sourceOwner agreement paid sources)[
      position.1.val]'position.1.isLt)[position.2.val.val]'position.2.val.isLt :=
  (getElem_congr (i := index.val) (j := index.val)
    (assemble_parents targets current reading originalOwner original sourceOwner agreement paid sources)
    rfl index.isLt).trans position.2.property.1

/-- The SAME global PreparedParent retains the complete original selected local Block cache heterogeneously. -/
theorem prepared_heq :
    HEq
      ((assemble targets current reading originalOwner original sourceOwner agreement paid sources).prepared.entry
        index)
      ((selectedSources targets current reading originalOwner original sourceOwner agreement paid sources index
        position).2.entry position.2.val) :=
  assemble_entry_heq targets current reading originalOwner original sourceOwner agreement paid sources position.1
    position.2.val index position.2.property.2

end Located
end Occurrences

section SignedRoots

open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology

/-- Read original physical root chains in the actual paid target-list order, keeping every literal Owner handoff.

An empty target list retains the same source Owner. Every nonempty head
consumes its SAME acquisition/source caches; empty Route parent words are
joined through their actual endpoint comparisons rather than dropped.
-/
private def rootChainWords : (targets : List Endpoint) → (current : Endpoint) →
    (reading : ReadingAt actual current) → (originalOwner : OwnerAt site parameter unitQuarter positive current) →
    (original : Steps actual regular current reading originalOwner targets) →
    (sourceOwner : OwnerAt site parameter unitQuarter positive current) →
    (agreement : InitialAgreement current reading sourceOwner) →
    (paid : Acquisition original sourceOwner agreement) →
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) →
    RootChain (parentWords targets current reading originalOwner original sourceOwner agreement paid sources).flatten
      (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName paid.finishOwner.parameterNonzero paid.finishOwner)
  | [] => fun _current _reading _originalOwner _original sourceOwner _agreement _paid _sources =>
      .nil (NamedEquivalent.refl (ownerRootName sourceOwner.parameterNonzero sourceOwner))
  | target :: targets => fun _current _reading _originalOwner original sourceOwner _agreement paid sources =>
      let first := Spine.Sources.acquiredRootChain
        (fun {_start _finish} segment => widthRequest paid.head.anchor segment)
        original.headGeometry.route.path original.headGeometry.route.within sourceOwner paid.head.paid.paid sources.1
      let following := rootChainWords targets target original.nextReading original.headCovered.finishOwner
        original.tail paid.head.finishOwner paid.head.nextAgreement paid.tail sources.2
      first.append following
termination_by structural targets => targets

/-- Derive the signed chain of the SAME assembled original paid Blocks without rebuilding a source.

Only the exact original parent-list equation reindexes the actual physical
chain. Empty Blocks and their ordered signed handoffs remain in the derived
RootChain; no adjacency or finishing comparison is supplied by a caller.
-/
def rootChain (targets : List Endpoint) (current : Endpoint) (reading : ReadingAt actual current)
    (originalOwner : OwnerAt site parameter unitQuarter positive current)
    (original : Steps actual regular current reading originalOwner targets)
    (sourceOwner : OwnerAt site parameter unitQuarter positive current)
    (agreement : InitialAgreement current reading sourceOwner)
    (paid : Acquisition original sourceOwner agreement)
    (sources : Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) targets current reading originalOwner original sourceOwner agreement paid) :
    RootChain (assemble targets current reading originalOwner original sourceOwner agreement paid sources
      ).geometry.parents
      (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName paid.finishOwner.parameterNonzero paid.finishOwner) :=
  PreparedBankRootChains.RootChain.castChildren
    (assemble_parents targets current reading originalOwner original sourceOwner agreement paid sources).symm
    (rootChainWords targets current reading originalOwner original sourceOwner agreement paid sources)

end SignedRoots

end Steps.Acquisition.Observation.Blocks.Sources

namespace Steps.Acquisition.Quarter.Sources

variable {current : Endpoint} {reading : ReadingAt actual current}
variable {originalOwner sourceOwner : OwnerAt site parameter unitQuarter positive current}
variable {givenQuarter : Steps.Quarter actual regular current reading originalOwner}
variable {agreement : InitialAgreement current reading sourceOwner}

/-- The whole actual paid quarter consumes its same nested stored source family without another source acquisition. -/
@[expose] def assemble (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter) :
    Spine.Sources.Assembled (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (targets := sourceTargets) (coordinate site parameter 2 unitQuarter positive current.parameter)
      (coordinate site parameter 2 unitQuarter positive
        (finalTarget current quarter.originalQuarter.cache.val).parameter) :=
  Observation.Blocks.Sources.assemble quarter.originalQuarter.cache.val current reading originalOwner
    quarter.originalQuarter.steps sourceOwner agreement quarter.receipt kept

section Occurrences

open Steps.Acquisition.Observation
open Purelib.Data.List

/-- Read the exact original retained Block parent words of the SAME completed paid quarter. -/
@[expose] def parentWords (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter) :=
  Blocks.Sources.parentWords quarter.originalQuarter.cache.val current reading originalOwner
    quarter.originalQuarter.steps
    sourceOwner agreement quarter.receipt kept

/-- The completed quarter's SAME original assembled parents are its actual retained Block-word flattening. -/
theorem assemble_parents (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter) :
    (assemble quarter kept).geometry.parents = (parentWords quarter kept).flatten :=
  Blocks.Sources.assemble_parents quarter.originalQuarter.cache.val current reading originalOwner
    quarter.originalQuarter.steps sourceOwner agreement quarter.receipt kept

/-- Locate one actual global quarter source in the SAME original Block flattening with no source preparation. -/
def locate (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter)
    (index : Fin (assemble quarter kept).geometry.parents.length) :=
  Blocks.Sources.locate quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps
    sourceOwner agreement quarter.receipt kept index

/-- Read a complete original Block/source cache from a supplied already retained quarter source position. -/
@[expose] def selected (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter)
    (index : Fin (assemble quarter kept).geometry.parents.length)
    (position : Flatten.Occurrence (parentWords quarter kept)
      (Blocks.Sources.flattenedIndex quarter.originalQuarter.cache.val current reading originalOwner
        quarter.originalQuarter.steps sourceOwner agreement quarter.receipt kept index)) :=
  Blocks.Sources.selected quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps
    sourceOwner agreement quarter.receipt kept index position

/-- Read the SAME selected physical covering/preparation pair, preserving original source models and observations. -/
@[expose] def selectedSources (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter)
    (index : Fin (assemble quarter kept).geometry.parents.length)
    (position : Flatten.Occurrence (parentWords quarter kept)
      (Blocks.Sources.flattenedIndex quarter.originalQuarter.cache.val current reading originalOwner
        quarter.originalQuarter.steps sourceOwner agreement quarter.receipt kept index)) :=
  Blocks.Sources.selectedSources quarter.originalQuarter.cache.val current reading originalOwner
    quarter.originalQuarter.steps sourceOwner agreement quarter.receipt kept index position

/-- The global quarter parent has exactly its selected original Block child's entire query/Step data. -/
theorem parent_eq (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter)
    (index : Fin (assemble quarter kept).geometry.parents.length)
    (position : Flatten.Occurrence (parentWords quarter kept)
      (Blocks.Sources.flattenedIndex quarter.originalQuarter.cache.val current reading originalOwner
        quarter.originalQuarter.steps sourceOwner agreement quarter.receipt kept index)) :
    (assemble quarter kept).geometry.parents[index.val]'index.isLt =
      ((parentWords quarter kept)[position.1.val]'position.1.isLt)[position.2.val.val]'position.2.val.isLt :=
  Blocks.Sources.parent_eq quarter.originalQuarter.cache.val current reading originalOwner quarter.originalQuarter.steps
    sourceOwner agreement quarter.receipt kept index position

/-- The global quarter's actual source preparation is the SAME whole original selected Block child cache. -/
theorem prepared_heq (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter)
    (index : Fin (assemble quarter kept).geometry.parents.length)
    (position : Flatten.Occurrence (parentWords quarter kept)
      (Blocks.Sources.flattenedIndex quarter.originalQuarter.cache.val current reading originalOwner
        quarter.originalQuarter.steps sourceOwner agreement quarter.receipt kept index)) :
    HEq ((assemble quarter kept).prepared.entry index)
      ((selectedSources quarter kept index position).2.entry position.2.val) :=
  Blocks.Sources.prepared_heq quarter.originalQuarter.cache.val current reading originalOwner
    quarter.originalQuarter.steps
    sourceOwner agreement quarter.receipt kept index position

end Occurrences

section SignedRoots

open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

/-- Read the signed chain of the SAME original paid Quarter and its complete source family.

The actual cached target list, paid receipt and source products are passed
unchanged to the original Block fold. No old covered execution or different
source Owner is substituted for the retained paid realization.
-/
def rootChain
    (quarter : Quarter givenQuarter sourceOwner agreement)
    (kept : Quarter.Sources (frame := frame) (basis := basis) (count := count) (floor := floor) (sheet := sheet)
      (sourceTargets := sourceTargets) quarter) :
    RootChain (assemble quarter kept).geometry.parents
      (ownerRootName sourceOwner.parameterNonzero sourceOwner)
      (ownerRootName quarter.finishOwner.parameterNonzero quarter.finishOwner) :=
  Observation.Blocks.Sources.rootChain quarter.originalQuarter.cache.val current reading originalOwner
    quarter.originalQuarter.steps sourceOwner agreement quarter.receipt kept

end SignedRoots

end Steps.Acquisition.Quarter.Sources

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Transport.Spatial.Parallel

end
