module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Queries
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Entries
public import Purelib.Riemann.Integration.PreparedConstantModels.Query
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Query
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Admission
import Purelib.Curves.Legendre.Periods.Jets.Source.Observations
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain.Occurrence
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic

/-! # Original stage completion from signed agreement of its actual queries

The original geometric chain pays endpoint membership. The actual cached
lookup and its own Position select the original first matching source.
Genuine all-query agreement supplies the signed comparison at unpaid
endpoints. Ready endpoints keep their original CommonRefinement; only an
unpaid endpoint materializes new query work and acquires another refinement.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

open Purelib
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedConstantModels (PreparedEdge)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {count floor : Nat} {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent)}
    {index rootStage : Nat} (attempt : StageAttempt covered chain index floor rootStage)

attribute [local irreducible] Purelib.Polynomial.Geometry.ClearPath.ClearSegment.pointAt
attribute [local irreducible] Purelib.Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence.ownerRootName

/-- Attach two retained related query samples to the exact selected original bank vertex.

The supplied Position belongs to this Found and this original bank. Both
observation bundles and direct Queries are consumed unchanged. The sample
relation proves the signed comparison; no observation, query, lookup or
source request is executed to reconstruct an occurrence.
-/
def sampleEquivalentToFound
    (sourceIndex : Fin (parent :: parents).length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    {point : LiftedPoint 2} {found : Vertex.Bank.Found attempt.2.2.1.val point}
    (position : Vertex.Bank.Position (.found found))
    (observed : CellModels.Observations frame
      (PreparedParent.liftedCell
        ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt))
      (attempt.2.1.entry sourceIndex).preparation.cell.models
      (attempt.2.1.entry sourceIndex).preparation.query.requests input)
    (selectedObserved : CellModels.Observations frame
      (PreparedParent.liftedCell
        ((parent :: parents)[(attempt.foundSourceIndex position).val]'(attempt.foundSourceIndex position).isLt))
      (attempt.2.1.entry (attempt.foundSourceIndex position)).preparation.cell.models
      (attempt.2.1.entry (attempt.foundSourceIndex position)).preparation.query.requests 0)
    (direct : PreparedEdge.Query ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge input inside)
    (selectedDirect : PreparedEdge.Query
      ((parent :: parents)[(attempt.foundSourceIndex position).val]'(attempt.foundSourceIndex position).isLt).edge
      0 (by decide +kernel))
    (related : NamedEquivalent observed.retained.sample.certificate.value.name
      selectedObserved.retained.sample.certificate.value.name) :
    NamedEquivalent (((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge.rootName input inside)
      found.original.sample.certificate.value.name := by
  let current := attempt.2.1.entry sourceIndex
  let selected := attempt.2.1.entry (attempt.foundSourceIndex position)
  let currentQuery := current.querySampleEquivalent input inside observed.retained.sample direct
  let selectedSample : NamedEquivalent selected.firstSample.certificate.value.name
      selectedObserved.retained.sample.certificate.value.name :=
    selected.firstQueryEquivalent.symm.trans
      (selected.querySampleEquivalent 0 (by decide +kernel) selectedObserved.retained.sample selectedDirect)
  let actualFound : NamedEquivalent selectedObserved.retained.sample.certificate.value.name
      found.original.sample.certificate.value.name :=
    NamedEquivalent.transport
      (first := selectedObserved.retained.sample.certificate.value.name)
      (second := selected.firstSample.certificate.value.name)
      (left := selectedObserved.retained.sample.certificate.value.name)
      (right := found.original.sample.certificate.value.name)
      rfl (attempt.found_source_name position).symm selectedSample.symm
  exact currentQuery.trans (related.trans actualFound)

/-- Materialize each needed query once and apply genuine agreement on the same prepared family.

The two new observation bundles and direct Queries are constructed in this
invocation only, then passed unchanged to the pure attachment operation.
The original preparation, bank and positional evidence remain cached inputs.
-/
private def queryEquivalentToFound
    (agreement : PreparedParents.QueryAgreement attempt.2.1)
    (sourceIndex : Fin (parent :: parents).length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    {point : LiftedPoint 2} {found : Vertex.Bank.Found attempt.2.2.1.val point}
    (position : Vertex.Bank.Position (.found found))
    (point_eq :
      PreparedParents.queryKey attempt.2.1 sourceIndex input = point) :
    NamedEquivalent (((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge.rootName input inside)
      found.original.sample.certificate.value.name := by
  let current := attempt.2.1.entry sourceIndex
  let selectedIndex := attempt.foundSourceIndex position
  let selected := attempt.2.1.entry selectedIndex
  let observed := current.preparation.query.observe frame input inside.1 inside.2
  let selectedObserved := selected.preparation.query.observe frame 0 (by decide +kernel) (by decide +kernel)
  let direct := PreparedEdge.Query.build ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge input inside
  let selectedDirect := PreparedEdge.Query.build ((parent :: parents)[selectedIndex.val]'selectedIndex.isLt).edge
    0 (by decide +kernel)
  have selectedKey :
      (⟨selected.preparation.cell.models.coordinate.point 0,
        ((parent :: parents)[selectedIndex.val]'selectedIndex.isLt).edge.sheet⟩ : LiftedPoint 2) = point :=
    (congrArg (fun coordinate => (⟨coordinate,
        ((parent :: parents)[selectedIndex.val]'selectedIndex.isLt).edge.sheet⟩ : LiftedPoint 2))
      ((selected.queryPoint_eq 0).trans
        ((parent :: parents)[selectedIndex.val]'selectedIndex.isLt).edge.point_zero)).trans
      (attempt.found_source_point position)
  let related := agreement sourceIndex selectedIndex input 0 inside (by decide +kernel)
    observed selectedObserved (point_eq.trans selectedKey.symm)
  exact attempt.sampleEquivalentToFound sourceIndex input inside position
    observed selectedObserved direct selectedDirect related

/-- Derive a checked endpoint's signed relation using its old Common or a genuinely new query pair.

The same RootCheck is matched together with its own Position. A successful
Common supplies the relation directly. Only an inconclusive containment
uses all-query agreement and new observations; an absent lookup contradicts
the erased membership proof. Neither branch performs a second lookup.
-/
private def checkedQueryEquivalent
    (agreement : PreparedParents.QueryAgreement attempt.2.1)
    (sourceIndex : Fin (parent :: parents).length) (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    {point : LiftedPoint 2} {endpointCount : Nat}
    {endpointPatch : ContinuedNeighborhood (Paths.polynomial parameter) endpointCount}
    (sample : ContinuedNeighborhood.Point endpointPatch point.coordinate)
    (queryEquivalent : NamedEquivalent
      (((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge.rootName input inside)
      sample.certificate.value.name)
    (point_eq :
      PreparedParents.queryKey attempt.2.1 sourceIndex input = point)
    (present : ∃ entry, entry ∈ attempt.2.2.1.val ∧ entry.point = point)
    (checked : Vertex.Bank.RootCheck sample attempt.2.2.1.val rootStage) :
    (found : Vertex.Bank.Found attempt.2.2.1.val point) →
      NamedEquivalent (((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge.rootName input inside)
        found.original.sample.certificate.value.name := by
  rcases checked with ⟨lookup, inspecting, position⟩
  cases lookup with
  | found actual =>
    cases inspecting with
    | ready common _ =>
      let related := queryEquivalent.trans (RootBranch.ofCommonRefinement common).equivalent
      exact fun found => NamedEquivalent.transport rfl
        (congrArg (fun vertex : Vertex parameter point => vertex.sample.certificate.value.name)
          (actual.original_eq found)) related
    | inconclusive _ _ _ _ =>
      let related := queryEquivalentToFound attempt agreement sourceIndex input inside position point_eq
      exact fun found => NamedEquivalent.transport rfl
        (congrArg (fun vertex : Vertex parameter point => vertex.sample.certificate.value.name)
          (actual.original_eq found)) related
  | absent missing =>
    exact False.elim (by
      have located := (show Vertex.Bank.Outcome attempt.2.2.1.val point from .absent missing).locate present
      have impossible := missing.symm.trans located.present
      cases impossible)

/-- Read the next global source occurrence, wrapping only the actual last occurrence to zero. -/
private def nextIndex (first : CenteredEdge (Fibre.frameCurve frame) basis)
    (remaining : List (CenteredEdge (Fibre.frameCurve frame) basis))
    (sourceIndex : Fin (first :: remaining).length) : Fin (first :: remaining).length :=
  if later : sourceIndex.val + 1 < (first :: remaining).length then
    ⟨sourceIndex.val + 1, later⟩
  else ⟨0, Nat.zero_lt_succ _⟩

/-- The actual closed centered chain identifies each successor source with the previous finish, including its sheet. -/
private theorem next_start_eq
    (chain : CenteredPathChain (parent :: parents)
      (start := PreparedParent.startPoint parent) (finish := PreparedParent.startPoint parent))
    (sourceIndex : Fin (parent :: parents).length) :
    PreparedParent.startPoint
      ((parent :: parents)[(nextIndex parent parents sourceIndex).val]'
        (nextIndex parent parents sourceIndex).isLt) =
      PreparedParent.finishPoint ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt) := by
  unfold nextIndex
  split
  · rename_i later
    exact CenteredPathChain.adjacent_eq (parent :: parents) chain sourceIndex later
  · rename_i notLater
    have atLast : sourceIndex.val + 1 = (parent :: parents).length :=
      Nat.le_antisymm (Nat.succ_le_of_lt sourceIndex.isLt) (Nat.le_of_not_gt notLater)
    have first := CenteredPathChain.startAt_eq (parent :: parents) chain
      (⟨0, Nat.zero_lt_succ _⟩ : Fin (parent :: parents).length) rfl
    have last := CenteredPathChain.finishAt_eq (parent :: parents) chain sourceIndex atLast
    exact first.trans last.symm

/-- The whole bank factory equation pays membership for every original source occurrence. -/
private theorem sourceMembers : SourceMembers covered attempt.2.1 attempt.2.2.1.val :=
  Eq.mp (congrArg (fun bank => SourceMembers covered attempt.2.1 bank) attempt.2.2.1.property.symm)
    (requestBank_sourceMembers covered attempt.2.1)

/-- Complete one original check using actual all-query agreement and geometric endpoint membership.

Ready checks retain their CommonRefinements and cached admission. Only
unpaid endpoints construct the additional query comparison and refinement.
All endpoint membership follows from this same ordered closed chain.
-/
private def completeQueriesAt (agreement : PreparedParents.QueryAgreement attempt.2.1)
    (sourceIndex : Fin (parent :: parents).length) :
    PreparedParent.Checked.Completion
      (DependentProduct.get (parent :: parents)
        (family := fun sourceIndex => PreparedParent.Checked
          (attempt.2.1.entry sourceIndex) attempt.2.2.1.val rootStage)
        attempt.2.2.2.2.1 sourceIndex) := by
  let current := attempt.2.1.entry sourceIndex
  let actual := (parent :: parents)[sourceIndex.val]'sourceIndex.isLt
  let checked := DependentProduct.get (parent :: parents)
    (family := fun sourceIndex => PreparedParent.Checked
      (attempt.2.1.entry sourceIndex) attempt.2.2.1.val rootStage)
    attempt.2.2.2.2.1 sourceIndex
  have firstPresent : ∃ entry, entry ∈ attempt.2.2.1.val ∧ entry.point = PreparedParent.startPoint actual :=
    ⟨Vertex.Entry.request current.firstVertex.val attempt.1.val.endpoint attempt.1.val.endpoint_positive,
      sourceMembers attempt sourceIndex, rfl⟩
  have lastPresent : ∃ entry, entry ∈ attempt.2.2.1.val ∧ entry.point = PreparedParent.finishPoint actual :=
    ⟨Vertex.Entry.request (attempt.2.1.entry (nextIndex parent parents sourceIndex)).firstVertex.val
        attempt.1.val.endpoint attempt.1.val.endpoint_positive,
      sourceMembers attempt (nextIndex parent parents sourceIndex), next_start_eq (chain := chain) sourceIndex⟩
  have firstKey :
      (⟨current.preparation.cell.models.coordinate.point 0, actual.edge.sheet⟩ : LiftedPoint 2) =
        PreparedParent.startPoint actual :=
    congrArg (fun coordinate => (⟨coordinate, actual.edge.sheet⟩ : LiftedPoint 2))
      ((current.queryPoint_eq 0).trans actual.edge.point_zero)
  have lastKey :
      (⟨current.preparation.cell.models.coordinate.point 1, actual.edge.sheet⟩ : LiftedPoint 2) =
        PreparedParent.finishPoint actual :=
    congrArg (fun coordinate => (⟨coordinate, actual.edge.sheet⟩ : LiftedPoint 2))
      ((current.queryPoint_eq 1).trans actual.edge.point_one)
  let firstQuery := checkedQueryEquivalent attempt agreement sourceIndex 0 (by decide +kernel)
    current.firstSample current.firstQueryEquivalent firstKey firstPresent checked.first
  let lastQuery := checkedQueryEquivalent attempt agreement sourceIndex 1 (by decide +kernel)
    current.lastSample current.lastQueryEquivalent lastKey lastPresent checked.last
  exact PreparedParent.Checked.complete checked firstPresent lastPresent firstQuery lastQuery

/-- Complete the same retained global StageAttempt from genuine signed agreement of its actual query family.

The original geometric chain supplies endpoint membership internally.
Every old lookup, Position, source preparation, model, bank, selected
Target and ready Common is retained. New query work and common-refinement
acquisitions occur only at originally inconclusive endpoints. No Distinct,
RootChain, desired successor comparison or replacement Stage is an input.
-/
def completeQueries (agreement : PreparedParents.QueryAgreement attempt.2.1) : Completion attempt :=
  let acquired := DependentProduct.ofFn (parent :: parents)
    (fun sourceIndex => completeQueriesAt attempt agreement sourceIndex)
  let result := Acquisitions.stage covered chain attempt.1.val attempt.1.property attempt.2.1
    attempt.2.2.1.val attempt.2.2.2.1 attempt.2.2.2.2.1 acquired
  ⟨acquired, ⟨result, rfl⟩⟩

/-- The old actual model's fraction-zero key is its same original starting lifted point, including sheet. -/
private theorem startKey_eq (index : Fin (parent :: parents).length) :
    PreparedParents.queryKey attempt.2.1 index 0 =
      PreparedParent.startPoint ((parent :: parents)[index.val]'index.isLt) :=
  congrArg₂ (fun coordinate sheet => (⟨coordinate, sheet⟩ : LiftedPoint 2))
    (((attempt.2.1.entry index).queryPoint_eq 0).trans
      ((parent :: parents)[index.val]'index.isLt).edge.point_zero) rfl

/-- The old actual model's fraction-one key is its same original finishing lifted point, including sheet. -/
private theorem finishKey_eq (index : Fin (parent :: parents).length) :
    PreparedParents.queryKey attempt.2.1 index 1 =
      PreparedParent.finishPoint ((parent :: parents)[index.val]'index.isLt) :=
  congrArg₂ (fun coordinate sheet => (⟨coordinate, sheet⟩ : LiftedPoint 2))
    (((attempt.2.1.entry index).queryPoint_eq 1).trans
      ((parent :: parents)[index.val]'index.isLt).edge.point_one) rfl

/-- Read the actual finishing Found and its own retained Position using the same chain's geometric membership.

The original cached Outcome supplies the Found unchanged. Its locate_eq
law transports only that same lookup's Position. Erased source membership
excludes absence; no endpoint lookup, observation or request is executed.
-/
private def terminalPosition (sourceIndex : Fin (parent :: parents).length)
    (checked : PreparedParent.Checked (attempt.2.1.entry sourceIndex) attempt.2.2.1.val rootStage) :
    (found : Vertex.Bank.Found attempt.2.2.1.val
      (PreparedParent.finishPoint ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt))) ×
      Vertex.Bank.Position (.found found) :=
  have present : ∃ entry, entry ∈ attempt.2.2.1.val ∧
      entry.point = PreparedParent.finishPoint ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt) :=
    ⟨Vertex.Entry.request (attempt.2.1.entry (nextIndex parent parents sourceIndex)).firstVertex.val
        attempt.1.val.endpoint attempt.1.val.endpoint_positive,
      sourceMembers attempt (nextIndex parent parents sourceIndex), next_start_eq (chain := chain) sourceIndex⟩
  let found := checked.last.1.locate present
  let position : Vertex.Bank.Position (.found found) :=
    Eq.mp (congrArg Vertex.Bank.Position (checked.last.1.locate_eq present)) checked.last.occurrence
  ⟨found, position⟩

/-- Two actual Found originals agree after equality of their WHOLE lifted keys, without identifying their Positions. -/
private def foundSamplesEquivalent {leftPoint rightPoint : LiftedPoint 2}
    (left : Vertex.Bank.Found attempt.2.2.1.val leftPoint) (right : Vertex.Bank.Found attempt.2.2.1.val rightPoint)
    (samePoint : leftPoint = rightPoint) :
    NamedEquivalent left.original.sample.certificate.value.name right.original.sample.certificate.value.name := by
  cases samePoint
  exact NamedEquivalent.transport rfl
    (congrArg (fun vertex : Vertex parameter leftPoint => vertex.sample.certificate.value.name)
      (left.original_eq right)) (NamedEquivalent.refl left.original.sample.certificate.value.name)

/-- A terminal fraction's original whole lifted key equals its actual finishing endpoint. -/
private theorem finishKey_eq_of_one (sourceIndex : Fin (parent :: parents).length)
    (fraction : Rational) (one : fraction = 1) :
    PreparedParents.queryKey attempt.2.1 sourceIndex fraction =
      PreparedParent.finishPoint ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt) :=
  (congrArg (fun input : Rational =>
    PreparedParents.queryKey attempt.2.1 sourceIndex input) one).trans
        (finishKey_eq attempt sourceIndex)

/-- Equal terminal fractions preserve the same edge root name with its original interval proof. -/
private theorem rootFraction_eq_one (sourceIndex : Fin (parent :: parents).length)
    (fraction : Rational) (inside : 0 ≤ fraction ∧ fraction ≤ 1) (one : fraction = 1) :
    ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge.rootName fraction inside =
      ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge.rootName 1 (by decide +kernel) := by
  cases one
  rfl

/-- The actual finishing lookup, its own Position and the same completed check's endpoint comparison. -/
private def TerminalSelection (sourceIndex : Fin (parent :: parents).length) :=
  (found : Vertex.Bank.Found attempt.2.2.1.val
    (PreparedParent.finishPoint ((parent :: parents)[sourceIndex.val]'sourceIndex.isLt))) ×
  Vertex.Bank.Position (.found found) ×
  NamedEquivalent (((parent :: parents)[sourceIndex.val]'sourceIndex.isLt).edge.rootName 1 (by decide +kernel))
    found.original.sample.certificate.value.name

/-- Read one original checked terminal and its completed comparison without matching or rebuilding the check. -/
private def terminalSelection (completed : Completion attempt) (sourceIndex : Fin (parent :: parents).length) :
    TerminalSelection attempt sourceIndex :=
  let checked := DependentProduct.get (parent :: parents) attempt.2.2.2.2.1 sourceIndex
  let acquired : PreparedParent.Checked.Completion checked :=
    DependentProduct.get (parent :: parents) completed.1 sourceIndex
  let selected := terminalPosition attempt sourceIndex checked
  ⟨selected.1, selected.2, acquired.2.1 selected.1⟩

/-- Exact root-query comparison type before attaching the independently retained observation bundles. -/
private def RootQueries :=
  (leftIndex rightIndex : Fin (parent :: parents).length) →
  (leftFraction rightFraction : Rational) →
  (leftInside : 0 ≤ leftFraction ∧ leftFraction ≤ 1) →
  (rightInside : 0 ≤ rightFraction ∧ rightFraction ≤ 1) →
  (_leftDirect : PreparedEdge.Query ((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge
    leftFraction leftInside) →
  (_rightDirect : PreparedEdge.Query ((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge
    rightFraction rightInside) →
  PreparedParents.queryKey attempt.2.1 leftIndex leftFraction =
      PreparedParents.queryKey attempt.2.1 rightIndex rightFraction →
  NamedEquivalent (((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge.rootName leftFraction leftInside)
    (((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge.rootName rightFraction rightInside)

/-- Exact dependent function type of the original strictTerminalRoots comparison. -/
private def StrictTerminalRoots :=
  (leftIndex rightIndex : Fin (parent :: parents).length) →
  (leftFraction rightFraction : Rational) →
  (leftInside : 0 ≤ leftFraction ∧ leftFraction ≤ 1) →
  (rightInside : 0 ≤ rightFraction ∧ rightFraction ≤ 1) →
  (leftDirect : PreparedEdge.Query ((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge leftFraction leftInside) →
  (_rightDirect : PreparedEdge.Query ((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge
    rightFraction rightInside) →
  (sameKey :
      PreparedParents.queryKey attempt.2.1 leftIndex leftFraction =
        PreparedParents.queryKey attempt.2.1 rightIndex rightFraction) →
  (leftBelow : leftFraction < 1) →
  (rightOne : rightFraction = 1) →
  NamedEquivalent (((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge.rootName leftFraction leftInside)
      (((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge.rootName rightFraction rightInside)

/-- Compare a strict query with the original terminal root through that same checked endpoint's selected source. -/
private def strictTerminalRoots (strictRoots : PreparedParents.QueryAgreement.StrictRoots attempt.2.1)
    (completed : Completion attempt) : StrictTerminalRoots attempt := by
  intro leftIndex rightIndex leftFraction rightFraction leftInside rightInside
    leftDirect _rightDirect sameKey leftBelow rightOne
  let selected := terminalSelection attempt completed rightIndex
  let selectedIndex := attempt.foundSourceIndex selected.2.1
  let selectedDirect := PreparedEdge.Query.build
    ((parent :: parents)[selectedIndex.val]'selectedIndex.isLt).edge
      0 (by decide +kernel)
  have selectedKey := sameKey.trans ((finishKey_eq_of_one attempt rightIndex rightFraction rightOne).trans
    ((attempt.found_source_point selected.2.1).symm.trans (startKey_eq attempt selectedIndex).symm))
  let roots := strictRoots
    leftIndex selectedIndex leftFraction 0 leftInside (by decide +kernel)
    leftBelow (by decide +kernel) leftDirect selectedDirect selectedKey
  exact NamedEquivalent.transport rfl
    (rootFraction_eq_one (parent := parent) (parents := parents) rightIndex rightFraction rightInside rightOne).symm
    (roots.trans ((attempt.foundQueryEquivalent selected.2.1).trans (selected.2.2).symm))

/-- Exact dependent function type of the original terminalStrictRoots comparison. -/
private def TerminalStrictRoots :=
  (leftIndex rightIndex : Fin (parent :: parents).length) →
  (leftFraction rightFraction : Rational) →
  (leftInside : 0 ≤ leftFraction ∧ leftFraction ≤ 1) →
  (rightInside : 0 ≤ rightFraction ∧ rightFraction ≤ 1) →
  (_leftDirect : PreparedEdge.Query ((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge leftFraction leftInside) →
  (rightDirect : PreparedEdge.Query ((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge
    rightFraction rightInside) →
  (sameKey :
      PreparedParents.queryKey attempt.2.1 leftIndex leftFraction =
        PreparedParents.queryKey attempt.2.1 rightIndex rightFraction) →
  (leftOne : leftFraction = 1) →
  (rightBelow : rightFraction < 1) →
  NamedEquivalent (((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge.rootName leftFraction leftInside)
      (((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge.rootName rightFraction rightInside)

/-- Compare the original terminal root with a strict query through its own retained first-match Position. -/
private def terminalStrictRoots (strictRoots : PreparedParents.QueryAgreement.StrictRoots attempt.2.1)
    (completed : Completion attempt) : TerminalStrictRoots attempt := by
  intro leftIndex rightIndex leftFraction rightFraction leftInside rightInside
    _leftDirect rightDirect sameKey leftOne rightBelow
  let selectedLeft := terminalSelection attempt completed leftIndex
  let selectedIndex := attempt.foundSourceIndex selectedLeft.2.1
  let selectedDirect := PreparedEdge.Query.build
    ((parent :: parents)[selectedIndex.val]'selectedIndex.isLt).edge
      0 (by decide +kernel)
  have selectedKey := (startKey_eq attempt selectedIndex).trans
    ((attempt.found_source_point selectedLeft.2.1).trans
      ((finishKey_eq_of_one attempt leftIndex leftFraction leftOne).symm.trans sameKey))
  let roots := strictRoots
    selectedIndex rightIndex 0 rightFraction (by decide +kernel) rightInside
    (by decide +kernel) rightBelow selectedDirect rightDirect selectedKey
  exact NamedEquivalent.transport
    (rootFraction_eq_one (parent := parent) (parents := parents) leftIndex leftFraction leftInside leftOne).symm rfl
    ((selectedLeft.2.2).trans
      ((attempt.foundQueryEquivalent selectedLeft.2.1).symm.trans roots))

/-- Exact dependent function type of the original terminalRoots comparison. -/
private def TerminalRoots :=
  (leftIndex rightIndex : Fin (parent :: parents).length) →
  (leftFraction rightFraction : Rational) →
  (leftInside : 0 ≤ leftFraction ∧ leftFraction ≤ 1) →
  (rightInside : 0 ≤ rightFraction ∧ rightFraction ≤ 1) →
  (_leftDirect : PreparedEdge.Query ((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge leftFraction leftInside) →
  (_rightDirect : PreparedEdge.Query ((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge
    rightFraction rightInside) →
  (sameKey :
      PreparedParents.queryKey attempt.2.1 leftIndex leftFraction =
        PreparedParents.queryKey attempt.2.1 rightIndex rightFraction) →
  (leftOne : leftFraction = 1) →
  (rightOne : rightFraction = 1) →
  NamedEquivalent (((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge.rootName leftFraction leftInside)
      (((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge.rootName rightFraction rightInside)

/-- Compare terminal roots through whole lifted-key incidence and original same-bank Found samples. -/
private def terminalRoots (completed : Completion attempt)
    : TerminalRoots attempt := by
  intro leftIndex rightIndex leftFraction rightFraction leftInside rightInside
    _leftDirect _rightDirect sameKey leftOne rightOne
  let selectedLeft := terminalSelection attempt completed leftIndex
  let selectedRight := terminalSelection attempt completed rightIndex
  have endpoints := (finishKey_eq_of_one attempt leftIndex leftFraction leftOne).symm.trans
    (sameKey.trans (finishKey_eq_of_one attempt rightIndex rightFraction rightOne))
  let originals := foundSamplesEquivalent attempt selectedLeft.1 selectedRight.1 endpoints
  exact NamedEquivalent.transport
    (rootFraction_eq_one (parent := parent) (parents := parents) leftIndex leftFraction leftInside leftOne).symm
    (rootFraction_eq_one (parent := parent) (parents := parents) rightIndex rightFraction rightInside rightOne).symm
    ((selectedLeft.2.2).trans (originals.trans (selectedRight.2.2).symm))

/-- Extend strict roots through the three original terminal cases, preserving both ordered query inputs. -/
private def queryRoots (strictRoots : PreparedParents.QueryAgreement.StrictRoots attempt.2.1)
    (completed : Completion attempt) : RootQueries attempt := by
  intro leftIndex rightIndex leftFraction rightFraction leftInside rightInside leftDirect rightDirect sameKey
  if leftBelow : leftFraction < 1 then
    if rightBelow : rightFraction < 1 then
      exact strictRoots leftIndex rightIndex leftFraction rightFraction leftInside rightInside leftBelow rightBelow
        leftDirect rightDirect sameKey
    else
      have rightOne : rightFraction = 1 := Fraction.Order.Basic.le_antisymm _ _ rightInside.2
        (Fraction.Order.Arithmetic.le_of_not_gt_direct rightBelow)
      exact strictTerminalRoots attempt strictRoots completed leftIndex rightIndex leftFraction rightFraction
        leftInside rightInside leftDirect rightDirect sameKey leftBelow rightOne
  else
    have leftOne : leftFraction = 1 := Fraction.Order.Basic.le_antisymm _ _ leftInside.2
      (Fraction.Order.Arithmetic.le_of_not_gt_direct leftBelow)
    if rightBelow : rightFraction < 1 then
      exact terminalStrictRoots attempt strictRoots completed leftIndex rightIndex leftFraction rightFraction
        leftInside rightInside leftDirect rightDirect sameKey leftOne rightBelow
    else
      have rightOne : rightFraction = 1 := Fraction.Order.Basic.le_antisymm _ _ rightInside.2
        (Fraction.Order.Arithmetic.le_of_not_gt_direct rightBelow)
      exact terminalRoots attempt completed leftIndex rightIndex leftFraction rightFraction
        leftInside rightInside leftDirect rightDirect sameKey leftOne rightOne

/-- Extend strict-query root agreement to every original observation using this same completed bank.

A terminal fraction reads its own old finishing Found and Position. Mixed
cases compare only with that Found's actual selected source at zero. Two
terminal cases use equality of the whole lifted keys and the original
Found.original_eq theorem. No lookup or endpoint request is repeated, and
independent Positions and source samples remain distinct.
-/
def queryAgreement (strictRoots : PreparedParents.QueryAgreement.StrictRoots attempt.2.1)
    (completed : Completion attempt) : PreparedParents.QueryAgreement attempt.2.1 := by
  intro leftIndex rightIndex leftFraction rightFraction leftInside rightInside leftObserved rightObserved sameKey
  let leftDirect := PreparedEdge.Query.build
    ((parent :: parents)[leftIndex.val]'leftIndex.isLt).edge leftFraction leftInside
  let rightDirect := PreparedEdge.Query.build
    ((parent :: parents)[rightIndex.val]'rightIndex.isLt).edge rightFraction rightInside
  let leftSample := (attempt.2.1.entry leftIndex).querySampleEquivalent
    leftFraction leftInside leftObserved.retained.sample leftDirect
  let rightSample := (attempt.2.1.entry rightIndex).querySampleEquivalent
    rightFraction rightInside rightObserved.retained.sample rightDirect
  exact leftSample.symm.trans
    ((queryRoots attempt strictRoots completed leftIndex rightIndex leftFraction rightFraction
      leftInside rightInside leftDirect rightDirect sameKey).trans rightSample)

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt

end
