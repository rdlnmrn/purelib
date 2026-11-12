module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Geometry
public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Strip.Endpoints
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Step.Source
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Comparison
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Accuracy
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered
import Purelib.Data.Gaussian.Field

/-! # Actual time-section endpoints of one retained local member

The same original Requested preparation and full factory select its actual
source endpoint Points. Each given zero/unit observation is continued once
at an admitted rational time; the original member's exact per-parent seed
budget is reused. At time one the existing source-Step comparison derives
agreement with the SAME stored block Steps. No source, member, Frame,
observation, acquisition or whole geometry is replayed or identified.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.List (DependentProduct)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1} {count : Nat}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis}
    {parents : List (CenteredEdge (Fibre.frameCurve frame) basis)}
    {covered : CoveredParents count (parent :: parents)}
    {chain : CenteredPathChain (parent :: parents) (start := startPoint parent) (finish := startPoint parent)}
    {current floor rootStage : Nat} {reference : AccuracyRequest}
    {source : Requested covered chain current floor rootStage reference}
    {ranges : ParameterRange covered} {allocation : ParameterRange.StripAllocation ranges}
    {root : Named} {roots : RootChain (parent :: parents) root root}
    {widths : Fin (parent :: parents).length → AccuracyRequest}
    {targetCurrent targetFloor targetRootStage : Nat} {offset : Canonical}
    {admitted : Norm.Basic.normSq offset ≤ allocation.bound}
    (cached : LocalMember source ranges allocation roots widths
      targetCurrent targetFloor targetRootStage offset admitted)
    (index : Fin (parent :: parents).length)
    (zeroInside : (0 : Rational) ≤ 0 ∧ (0 : Rational) ≤ 1)
    (firstObserved : CellModels.Observations frame (PreparedParent.liftedCell
        ((parent :: parents)[index.val]'index.isLt))
      (source.prepared.entry index).preparation.cell.models
      (source.prepared.entry index).preparation.query.requests 0)
    (firstFactory : firstObserved =
      (source.prepared.entry index).preparation.query.observe frame 0 zeroInside.1 zeroInside.2)
    (oneInside : (0 : Rational) ≤ 1 ∧ (1 : Rational) ≤ 1)
    (lastObserved : CellModels.Observations frame (PreparedParent.liftedCell
        ((parent :: parents)[index.val]'index.isLt))
      (source.prepared.entry index).preparation.cell.models
      (source.prepared.entry index).preparation.query.requests 1)
    (lastFactory : lastObserved =
      (source.prepared.entry index).preparation.query.observe frame 1 oneInside.1 oneInside.2)

/-- Both actual time-section caches reuse this member's identical original source and retained per-parent seed budget.

The two raw advance/reference factories and their original-endpoint Step
views are retained separately. This exact dependent pair contains no new
Frame, copied member context, source preparation or target geometry.
-/
@[expose] def EndpointSections (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) : Type _ :=
  let prepared := source.prepared.entry index
  let range := ranges.entry index
  let block := DependentProduct.get (parent :: parents) cached.member.blocks index
  PreparedParent.FirstStripEndpoint prepared range block.comparison.budget block.comparison.budget_eq
    zeroInside firstObserved firstFactory offset (admitted.trans (allocation.bound_le_entry index)) time timeInside ×
  PreparedParent.LastStripEndpoint prepared range block.comparison.budget block.comparison.budget_eq
    oneInside lastObserved lastFactory offset (admitted.trans (allocation.bound_le_entry index)) time timeInside

/-- Continue both supplied original endpoint bundles once using the actual retained member and source factory chain.

Requested.prepared_eq and prepareCovered_entry derive the original parent
factory before either transport. Only the two requested time-section
advances/reference comparisons execute; the given member's block, seed
budget, original source and both observation caches are reused unchanged.
-/
def endpointSections (time : Rational) (timeInside : 0 ≤ time ∧ time ≤ 1) :
    EndpointSections cached index zeroInside firstObserved firstFactory oneInside lastObserved lastFactory
      time timeInside :=
  let prepared := source.prepared.entry index
  let range := ranges.entry index
  let block := DependentProduct.get (parent :: parents) cached.member.blocks index
  have factory : prepared = prepareParent (frame := frame) (covered.entry index).val count floor
      (covered.entry index).property source.targets :=
    (congrArg (fun values : PreparedParents covered floor source.targets => values.entry index)
      source.prepared_eq).trans (prepareCovered_entry covered floor source.targets index)
  let first := prepared.firstStripAt range block.comparison.budget block.comparison.budget_eq factory
    zeroInside firstObserved firstFactory offset (admitted.trans (allocation.bound_le_entry index)) time timeInside
  let last := prepared.lastStripAt range block.comparison.budget block.comparison.budget_eq factory
    oneInside lastObserved lastFactory offset (admitted.trans (allocation.bound_le_entry index)) time timeInside
  ⟨first, last⟩

/-- The GIVEN time-one endpoint cache agrees with this SAME retained member's original block Steps.

The exact scalar one-times-offset identity reindexes only the parameter
increment. Both actual endpoint views and stored block Steps start at the
same original Point. Their signed agreement is derived by the existing
common-source comparison; no endpoint sign or desired relation is input.
-/
def endpointSigns
    (sections : EndpointSections cached index zeroInside firstObserved firstFactory
      oneInside lastObserved lastFactory 1 oneInside) :
    let block := DependentProduct.get (parent :: parents) cached.member.blocks index
    NamedEquivalent sections.1.2.val.root.value.name block.first.root.value.name ×
      NamedEquivalent sections.2.2.val.root.value.name block.last.root.value.name :=
  let block := DependentProduct.get (parent :: parents) cached.member.blocks index
  have scalar : (⟨(1 : Rational), 0⟩ : Canonical) * offset = offset := Basic.one_mul offset
  let first := Variation.Point.Step.equivalent_of_increment_eq (parameter := parameter)
    (source := (source.prepared.entry index).firstSample)
    (firstIncrement := (⟨(1 : Rational), 0⟩ : Canonical) * offset) (lastIncrement := offset)
    scalar sections.1.2.val block.first
  let last := Variation.Point.Step.equivalent_of_increment_eq (parameter := parameter)
    (source := (source.prepared.entry index).lastSample)
    (firstIncrement := (⟨(1 : Rational), 0⟩ : Canonical) * offset) (lastIncrement := offset)
    scalar sections.2.2.val block.last
  ⟨first, last⟩

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
