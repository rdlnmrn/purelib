module

public import Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.PrimitiveCover.Refinement
import Purelib.Riemann.Integration.PreparedEndpointSafeRefinement
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints.Queries
import Purelib.Riemann.Topology.PreparedRefinementRootChains.Queries

/-! # Actual rooted primitive-cover geometry before observation requests

The existing Sum and dependent products retain one actual zero-width
comparison or one sufficiently refined and inspected child block. Original
bounds, mesh, query, neighborhood, cover and signed root-chain factories
remain attached to their same retained values. No primitive observation,
source target or numerical accuracy is selected by this acquisition.
-/

public section

namespace Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover

open Purelib
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Integration.Observation.UniformPreparedMesh (CoveredParents)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEndpointSafeRefinement (EndpointSafeBlock)
open Purelib.Riemann.RootContinuation.PreparedRefinementRootEndpoints (ParentBudget Queries)
open Purelib.Riemann.Topology.PreparedRefinementRootChains (RootChain)

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential : Differential genus}

namespace Acquisition

/-- The actual zero-width parent budget and query-root comparison, retaining both outer endpoint roles. -/
@[expose] def Stationary (parent : CenteredEdge curve differential) (queries : Queries parent.edge) :=
  Σ budget : {value : ParentBudget parent.edge // value = ParentBudget.acquire parent.edge ∧
      parent.edge.left.parameter = parent.edge.request.endpoint.parameter},
  {roots : RootChain (curve := curve) (differential := differential) []
      (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (of_decide_eq_true rfl)) //
    roots = PrimitiveCover.stationaryRootsFromQueries parent queries budget.property.2 budget.val}

/-- The same actual refined block, complete geometry, successful inspection, covered value and query-root chain.

The exact existing Refinement payload supplies the original bounds,
sufficient depth, checked mesh and whole block factory. Every remaining
field is a retained result of the original primitive-cover producer;
no source model or primitive reading occurs in this dependent product.
-/
@[expose] def Refined (parent : CenteredEdge curve differential) (queries : Queries parent.edge)
    (diameter : Rational) (positive : 0 < diameter) :=
  Σ safe : {value : EndpointSafeBlock parent // value.budget = ParentBudget.acquire parent.edge},
  Σ _geometry : Refinement parent diameter positive safe.val,
  Σ inspected : {value : CoveredParents.Inspection (count := count) safe.val.block.children //
    value = CoveredParents.Inspection.build safe.val.block.children ∧
      CoveredParents.Inspection.Ready safe.val.block.children value},
  Σ _covered : {value : CoveredParents.Inspection.Success inspected.val //
    value.val = CoveredParents.Inspection.coveredOfReady safe.val.block.children inspected.val inspected.property.2},
  {roots : RootChain safe.val.block.children
      (parent.edge.rootName 0 parent.edge.baseInside) (parent.edge.rootName 1 (of_decide_eq_true rfl)) //
    roots = Riemann.Topology.PreparedRefinementRootChains.EndpointSafeBlock.rootChainUsing safe.val queries}

end Acquisition

/-- One actual rooted primitive-cover geometry outcome, available before numerical request selection.

A zero-width parent has an empty inner word and a real retained root
comparison. Every strict parent keeps its actual checked children,
including physically stationary or repeated child occurrences.
-/
@[expose] def Acquisition (parent : CenteredEdge curve differential) (queries : Queries parent.edge)
    (diameter : Rational) (positive : 0 < diameter) :=
  Acquisition.Stationary parent queries ⊕ Acquisition.Refined (count := count) parent queries diameter positive

namespace Acquisition

variable (parent : CenteredEdge curve differential) (queries : Queries parent.edge)
variable (diameter : Rational) (positive : 0 < diameter)

/-- Retain the original stationary callback values without reconstructing its budget or query comparison. -/
private def collectStationary : StationaryConsumerFromQueries parent queries
    (Acquisition (count := count) parent queries diameter positive) :=
  fun same budget budgetFactory roots rootsFactory =>
    .inl ⟨⟨budget, budgetFactory, same⟩, ⟨roots, rootsFactory⟩⟩

/-- Retain the original successful refinement callback, including its complete checked-block factory. -/
private def collectRefined (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter) :
    ConsumerFromQueries (count := count) parent queries proper diameter positive
      (Acquisition (count := count) parent queries diameter positive) :=
  fun bounds boundsFactory chosenDepth depthFactory enough mesh meshFactory safe budgetFactory blockFactory
      inspected inspectedFactory ready covered coveredFactory roots rootsFactory =>
    .inr ⟨⟨safe, budgetFactory⟩,
      ⟨⟨diameter, rfl⟩, ⟨bounds, boundsFactory, proper⟩, ⟨chosenDepth, depthFactory⟩,
        ⟨enough⟩, ⟨mesh, meshFactory, blockFactory⟩⟩,
      ⟨inspected, inspectedFactory, ready⟩, ⟨covered, coveredFactory⟩, ⟨roots, rootsFactory⟩⟩

/-- Acquire original covered geometry once using the same supplied endpoint-query caches.

The original producer decides zero width, computes sufficient refinement
and checks each actual neighborhood. The exact callback values are retained
before a caller selects any source target or primitive-observation accuracy.
-/
def build : Acquisition (count := count) parent queries diameter positive :=
  withCoverOrStationaryFromQueries (count := count) parent queries diameter positive
    (collectStationary parent queries diameter positive) (collectRefined parent queries diameter positive)

variable {parent queries diameter positive}

/-- Read the actual retained child count without constructing any source, query, root or observation. -/
@[expose] def childCount : Acquisition (count := count) parent queries diameter positive → Nat
  | .inl _ => 0
  | .inr retained => retained.1.val.block.children.length

end Acquisition

end Purelib.Riemann.Integration.PreparedDirectDyadicRefinements.DirectParentBlock.PrimitiveCover

end
