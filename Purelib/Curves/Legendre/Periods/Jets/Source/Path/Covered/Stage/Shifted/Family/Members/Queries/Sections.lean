module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members.Queries
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Strip.Sections
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.ShiftedOccurrence
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Occurrences
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.Linked
import Purelib.Data.List.DependentProduct
import Purelib.Approximation.AccuracyRequest
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh
import Purelib.Curves.Legendre.Paths
import Purelib.Curves.Legendre.Periods.Fibre
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Parameter.Strip
import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Covered.Stage.Shifted.Family.Members
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.CenteredPathChain
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Topology.PreparedRefinementRootChains
import Purelib.Riemann.RootContinuation.CertifiedSquareRoot
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction

/-! # Source anchoring of a GIVEN actual zero-member interior query

The original whole query result supplies both independent observations,
its actual QueryStep/reference and retained direct Query. The original
section comparison and zero-Step source law derive the anchor internally.
No query, numerical stage, source, member or root is reconstructed.
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
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.List (DependentProduct)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (Named RootChain)
open Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent (startPoint)

attribute [local irreducible] Riemann.RootContinuation.CertifiedSquareRoot.rawRoot
attribute [local irreducible] ShiftedGeometry.Occurrence.block PreparedParent.ShiftedAcquisition.Linked.first
  StripQueryCache.located StripQueryCache.aligned Shifted.requested
  ShiftedGeometry.Requested.request ShiftedGeometry.Request.shape

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
    (cache : StripQueryCache cached) (stage : Nat) (retained : QueryStage cached stage)
    (index : Fin (cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2).length)
    (input : Rational) (inside : 0 ≤ input ∧ input ≤ 1)
    (queried : StripQueryAt cached cache stage retained index input inside)

/-- Derive the actual zero-member query's original source anchor at its genuine supplied child/source fractions.

Both Frames, the GIVEN actual stage/cache, source and target observations,
direct Query, whole QueryStep and seed-reference factories stay original.
Only the original reference-to-Step comparison is requested again. No
arbitrary physical-fraction locator or whole-function cache is inferred.
-/
def querySourceAtZero (zero : offset = 0) :
    NamedEquivalent queried.2.1.val.retained.sample.certificate.value.name
      queried.1.val.retained.sample.certificate.value.name :=
  let located := StripQueryCache.located (cached := cached) cache index
  let prepared : PreparedParent (parameter := parameter) (frame := frame) (basis := basis)
      (parent := (parent :: parents)[located.block.val]'located.block.isLt)
      (covered.entry located.block).val count floor (covered.entry located.block).property source.targets :=
    PreparedParents.entry (parameter := parameter) (frame := frame) (basis := basis)
      (count := count) (parents := parent :: parents) (covered := covered) (floor := floor)
      (original := chain.path) (stage := source.selected.stage) (targets := source.targets)
      source.prepared located.block
  let selected : PreparedParent (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (parent := (cached.member.requested.request.shape.val.1 ::
        cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
      (cached.member.requested.request.covered.entry index).val count targetFloor
      (cached.member.requested.request.covered.entry index).property
      (CellEndpoints.Targets.build cached.member.requested.request.chain.path stage) :=
    PreparedParents.entry (parameter := parameter + offset) (frame := cached.targetFrame) (basis := basis)
      (count := count)
      (parents := cached.member.requested.request.shape.val.1 :: cached.member.requested.request.shape.val.2)
      (covered := cached.member.requested.request.covered) (floor := targetFloor)
      (original := cached.member.requested.request.chain.path) (stage := stage)
      (targets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
      retained.val.1.preparations index
  let range := ranges.entry located.block
  let block := DependentProduct.get (parent :: parents) cached.member.blocks located.block
  PreparedParent.ShiftedAcquisition.RootComparison.QuerySection.sourceAtZero
    (parameter := parameter) (frame := frame) (basis := basis)
    (parent := (parent :: parents)[located.block.val]'located.block.isLt)
    (patch := (covered.entry located.block).val) (count := count) (floor := floor)
    (covered := (covered.entry located.block).property) (original := chain.path)
    (stage := source.selected.stage) (targets := source.targets) (prepared := prepared) (range := range)
    (increment := offset) (target := cached.targetFrame)
    (shiftedPaid := admitted.trans ((allocation.bound_le_entry located.block).trans range.stripBound_le_shiftedBound))
    (firstSample := prepared.firstSample) (firstStep := block.first) (width := widths located.block)
    (retained := block.shifted) (strip := admitted.trans (allocation.bound_le_entry located.block))
    (actual := block.actual.val) (actual_eq := block.actual.property)
    (child := (cached.member.requested.request.shape.val.1 ::
      cached.member.requested.request.shape.val.2)[index.val]'index.isLt)
    (newPatch := (cached.member.requested.request.covered.entry index).val) (newCount := count)
    (newFloor := targetFloor) (newCovered := (cached.member.requested.request.covered.entry index).property)
    (newPath := cached.member.requested.request.chain.path) (newStage := stage)
    (newTargets := CellEndpoints.Targets.build cached.member.requested.request.chain.path stage)
    (comparison := block.comparison) (newPrepared := selected) (input := input) (inside := inside)
    (targetSample := queried.2.1.val.retained.sample) (queried := queried.2.2.2.val.2)
    queried.1.val queried.1.property queried.2.2.2.val.1 zero

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParents.StageAttempt.Requested.LocalMember

end
