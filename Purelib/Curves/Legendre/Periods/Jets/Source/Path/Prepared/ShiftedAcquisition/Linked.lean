module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.ShiftedAcquisition.RootComparison
public import Purelib.Riemann.Paths.PreparedPathPrimitiveCover.Acquisition.Parents.RootChain
import Purelib.Riemann.Topology.PreparedBankRootChains
import Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence

/-! # Linked actual shifted acquisitions at retained original endpoints

The two original parameter Steps, actual shifted acquisition, materialized
trace and original comparison cache are supplied unchanged. One actual
geometric chain and one cache-derived open RootChain are stored before the
global source request is allocated. This construction creates no source,
root, transport, center, subdivision, target allocation or acquisition.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Gaussian.Equivalence (NamedEquivalent)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedDirectDyadicRefinements (CenteredPathChain)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Paths.OwnerTracePath (OwnerPath)
open Purelib.Riemann.RootContinuation.SquareRootTrackEquivalence (ownerRootName)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)
open Purelib.Riemann.Topology

variable {parameter increment : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count floor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {baseStart baseFinish : LiftedPoint 2} {original : LiftedPath 2 baseStart baseFinish} {stage : Nat}
    {targets : CellEndpoints.Targets original stage}
    (source : PreparedParent patch count floor covered targets)
    (range : Variation.Point.Range (patch.neighborhood count)) (target : Paths.Frame (parameter + increment))
    (admitted : Norm.Basic.normSq increment ≤ range.shiftedBound)
    (strip : Norm.Basic.normSq increment ≤ range.stripBound) (width : AccuracyRequest)

/-- Actual endpoint Steps, shifted acquisition, trace and comparisons with their once-built geometric and root chains.

The source preparation and its exact old allocation remain nominal inputs.
All root Owners are the original retained occurrences. The new two chains
consume that same actual acquisition and comparison cache, preserving
complete factory equations without locally preparing any shifted sources.
-/
@[expose] def Linked :=
  (first : Variation.Point.Step source.firstSample increment) ×
  (_last : Variation.Point.Step source.lastSample increment) ×
  (shifted : ShiftedAcquisition (covered := covered) range target admitted first width) ×
  (actual : { path : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate first.owner
    (finishPoint parent).coordinate shifted.acquired.traced.finishOwner //
    path = shifted.acquired.traced.trace.get }) ×
  (comparison : RootComparison shifted strip actual.val actual.property) ×
  (_geometry : { value : CenteredPathChain shifted.parents.covered.parents
    (start := startPoint parent) (finish := finishPoint parent) // value = shifted.parents.covered.chain }) ×
  { roots : RootChain shifted.parents.covered.parents (ownerRootName first.owner.parameterNonzero first.owner)
    (ownerRootName shifted.acquired.traced.finishOwner.parameterNonzero shifted.acquired.traced.finishOwner) //
    roots = shifted.parents.rootChain comparison.paths.rootViews }

namespace Linked

variable {source range target admitted strip width}

/-- Retain the same supplied acquisition chain and derive/store its actual open root chain exactly once. -/
def ofRetained (first : Variation.Point.Step source.firstSample increment)
    (last : Variation.Point.Step source.lastSample increment)
    (shifted : ShiftedAcquisition (covered := covered) range target admitted first width)
    (actual : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate first.owner
      (finishPoint parent).coordinate shifted.acquired.traced.finishOwner)
    (actual_eq : actual = shifted.acquired.traced.trace.get)
    (comparison : RootComparison shifted strip actual actual_eq) : Linked source range target admitted strip width :=
  let geometry := shifted.parents.covered.chain
  let roots := shifted.parents.rootChain comparison.paths.rootViews
  ⟨first, last, shifted, ⟨actual, actual_eq⟩, comparison, ⟨geometry, rfl⟩, ⟨roots, rfl⟩⟩

variable (linked : Linked source range target admitted strip width)

/-- Read the same independently retained source-endpoint parameter Step. -/
@[expose] def first : Variation.Point.Step source.firstSample increment := linked.1

/-- Read the same independently retained finish-endpoint parameter Step. -/
@[expose] def last : Variation.Point.Step source.lastSample increment := linked.2.1

/-- Read the same original full shifted acquisition, including its actual centers and covering patches. -/
@[expose] def shifted : ShiftedAcquisition (covered := covered) range target admitted linked.first width :=
  linked.2.2.1

/-- Read the actual already materialized trace and its original complete factory identity. -/
@[expose] def actual :
    { path : OwnerPath (Fibre.frameCurve target).polynomial (startPoint parent).coordinate linked.first.owner
        (finishPoint parent).coordinate linked.shifted.acquired.traced.finishOwner //
      path = linked.shifted.acquired.traced.trace.get } := linked.2.2.2.1

/-- Read the same retained original strip/reference/root comparison cache. -/
@[expose] def comparison : RootComparison linked.shifted strip linked.actual.val linked.actual.property :=
  linked.2.2.2.2.1

/-- Read the once-retained geometric chain on the exact original covered centered list. -/
@[expose] def geometry : CenteredPathChain linked.shifted.parents.covered.parents
    (start := startPoint parent) (finish := finishPoint parent) := linked.2.2.2.2.2.1.val

/-- The whole cached geometric chain uses the identical actual acquired subdivision and covered centers. -/
theorem geometry_eq : linked.geometry = linked.shifted.parents.covered.chain := linked.2.2.2.2.2.1.property

/-- Read the once-retained cache-aware open root chain of those identical actual parents. -/
@[expose] def roots : RootChain linked.shifted.parents.covered.parents
    (ownerRootName linked.first.owner.parameterNonzero linked.first.owner)
    (ownerRootName linked.shifted.acquired.traced.finishOwner.parameterNonzero
      linked.shifted.acquired.traced.finishOwner) := linked.2.2.2.2.2.2.val

/-- The complete cached root chain consumes this SAME actual comparison cache and Parents centers. -/
theorem roots_eq : linked.roots = linked.shifted.parents.rootChain linked.comparison.paths.rootViews :=
  linked.2.2.2.2.2.2.property

/-- The SAME actual covered acquisition has at least one original centered parent, even for zero displacement. -/
theorem parents_ne_nil : linked.shifted.parents.covered.parents ≠ [] := by
  intro empty
  have sizes := linked.shifted.parents.covered.parents_length.trans
    linked.shifted.parents.covered.mesh.edgeCount_eq
  have zero : 0 = 2 ^ linked.shifted.parents.covered.mesh.depth := by
    rewrite [empty] at sizes
    exact sizes
  have powers : ∀ depth : Nat, 0 < (2 : Nat) ^ depth := by
    intro depth
    induction depth with
    | zero => exact Nat.zero_lt_succ 0
    | succ depth previous =>
        rewrite [Nat.pow_succ]
        exact Nat.mul_pos previous (by decide +kernel : 0 < (2 : Nat))
  have positive := powers linked.shifted.parents.covered.mesh.depth
  rewrite [← zero] at positive
  exact Nat.lt_irrefl 0 positive

/-- Attach the original endpoint Step names to the cached root chain using its derived actual finishing comparison.

The independent last Step is not identified by a coordinate or label.
Its actual source/seed refinements pay the original root comparison; all
existing acquisition and comparison cache data remain unchanged.
-/
def endpointRoots : RootChain linked.shifted.parents.covered.parents
    linked.first.root.value.name linked.last.root.value.name := by
  have firstName : ownerRootName linked.first.owner.parameterNonzero linked.first.owner =
      linked.first.root.value.name := by
    rewrite [linked.first.root_eq]
    rfl
  let roots := PreparedBankRootChains.RootChain.castNames firstName rfl linked.roots
  exact PreparedBankRootChains.RootChain.changeFinish roots (linked.comparison.finishEquivalent linked.last)

end Linked

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.ShiftedAcquisition

end
