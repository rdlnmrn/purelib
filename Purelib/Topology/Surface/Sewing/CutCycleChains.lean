module
import Purelib.Algebra.Ring.IntCast
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Vector.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Topology.Surface.Cut.JumpPaths
public import Purelib.Topology.Surface.Word.Pairing
import Mathlib.Algebra.Ring.Int.Defs
import Purelib.Tactic.Ring

open Purelib

open Purelib.Algebra

open Purelib.Topology.Chain

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Cut.JumpPaths

open Purelib.Topology.Surface.Cut.JumpPaths.CutPath

open Purelib.Topology.Surface.Word

public section

/-!
# Integer combinations of actual closed projected cut paths

Each component retains its cut path and surface path. Integer coefficients
combine these concrete cycles without identifying their distinct cut
vertices. The resulting finite chain is closed on the surface; its primitive
increment is evaluated on the cut paths and need not vanish.
-/

namespace Purelib.Topology.Surface.Sewing.CutCycleChains

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_zero)

variable {source target : Nat} {labels : Fin source → Fin target} {ambient : List (Stokes.OrientedEdge target)}

set_option genInjectivity false in
/-- An actual retained cut path whose projection is a supported closed surface path.

The original cut endpoints remain distinct data; only their projected labels are required to agree. -/
structure ClosedCutCycle (labels : Fin source → Fin target) (ambient : List (Stokes.OrientedEdge target)) where
  /-- Original start vertex in the retained cut bank. -/ start : Fin source
  /-- Original finish vertex in the retained cut bank. -/ finish : Fin source
  /-- Cached cut path, exact projected path and original endpoint certificate. -/ path : CutPath.Projected labels start
    finish
  /-- The original finish and start labels agree on the surface. -/ same : labels finish = labels start
  /-- The exact projected path uses only the original ambient unoriented support. -/ supported : CutPath.Supported
    ambient path.surfaceEdges

constructive_injectivity ClosedCutCycle

namespace ClosedCutCycle

/-- Build the empty cut cycle at the supplied original anchor. -/
@[expose] def empty (labels : Fin source → Fin target) (ambient : List (Stokes.OrientedEdge target)) (anchor : Fin
  source) :
    CutCycleChains.ClosedCutCycle labels ambient :=
  ⟨anchor, anchor, Projected.build labels [] (.nil _), rfl,
    fun _ member => (List.not_mem_nil member).elim⟩

/-- The retained projected edge list closes at its original projected start vertex. -/
theorem closed (cycle : CutCycleChains.ClosedCutCycle labels ambient) :
    PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish cycle.path.surfaceEdges (labels cycle.start)
      (labels cycle.start) :=
  cycle.path.closed cycle.same

/-- The original projected cycle has zero integer boundary at every surface vertex. -/
theorem boundary_zero (cycle : CutCycleChains.ClosedCutCycle labels ambient) (vertex : Fin target) :
    PathBoundary.wordBoundaryAt OrientedEdge.start OrientedEdge.finish cycle.path.surfaceEdges vertex = 0 :=
  cycle.path.boundary_zero cycle.same vertex

/-- Evaluate primitive increments along the retained original cut-edge path. -/
@[expose] def increment (cycle : CutCycleChains.ClosedCutCycle labels ambient) (primitive : Fin source →
  Stokes.PrimitivePoint) : PrimitivePoint :=
  CutPath.increment primitive cycle.path.cutEdges

/-- The original cut-path increment telescopes to its retained endpoint difference. -/
theorem increment_eq (cycle : CutCycleChains.ClosedCutCycle labels ambient) (primitive : Fin source →
  Stokes.PrimitivePoint) :
    cycle.increment primitive = (PrimitivePoint.sub (primitive cycle.finish)) (primitive cycle.start) :=
  CutPath.increment_eq primitive cycle.path.endpoints

end ClosedCutCycle

set_option genInjectivity false in
/-- A finite chain is a materialized bank of actual closed paths with integer multiplicities. Negative weights reverse
integration orientation; different base vertices do not require artificial connecting paths. -/
structure CutCycleChain (labels : Fin source → Fin target) (ambient : List (Stokes.OrientedEdge target)) where
  /-- Number of retained component cycles. -/ count : Nat
  /-- Original cached supported cycles, each with its own retained cut endpoints. -/ cycles : Data.Vector
    (CutCycleChains.ClosedCutCycle labels ambient) count
  /-- Integer multiplicity of each original retained cycle. -/ weights : Data.Vector Int count

constructive_injectivity CutCycleChain

namespace CutCycleChain

/-- Sum the integer-weighted boundaries of the retained actual projected cycles. -/
@[expose] def boundary (chain : CutCycleChains.CutCycleChain labels ambient) (vertex : Fin target) : Int :=
  FiniteSum.Fin.sumFin fun index => chain.weights index * PathBoundary.wordBoundaryAt
    OrientedEdge.start OrientedEdge.finish (chain.cycles index).path.surfaceEdges vertex

/-- Every finite integer combination of the retained closed cycles has zero surface boundary. -/
theorem boundary_zero (chain : CutCycleChains.CutCycleChain labels ambient) (vertex : Fin target) : chain.boundary
  vertex = 0 := by
  apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
  intro index
  rw [(chain.cycles index).boundary_zero, mul_zero]

/-- Combine the retained cut-cycle primitive increments using the original integer weights. -/
@[expose] def increment (chain : CutCycleChains.CutCycleChain labels ambient) (primitive : Fin source →
  Stokes.PrimitivePoint) : PrimitivePoint :=
  Pairing.linear chain.weights (fun index => (chain.cycles index).increment primitive)

/-- Evaluating a chain may consume previously checked component increments; the cut words are retained for provenance,
not summed afresh downstream. -/
theorem increment_cached (chain : CutCycleChains.CutCycleChain labels ambient) (primitive : Fin source →
  Stokes.PrimitivePoint)
    (values : Fin chain.count → Stokes.PrimitivePoint)
    (equal : ∀ index, (chain.cycles index).increment primitive = values index) :
    chain.increment primitive = Pairing.linear chain.weights values := by
  unfold CutCycleChain.increment Pairing.linear
  congr 1 <;> apply FiniteSum.Fin.sumFin_congr <;> intro index <;> dsimp only <;> rw [equal]

/-- Every retained component cycle is supported in the original ambient edge list. -/
theorem supported (chain : CutCycleChains.CutCycleChain labels ambient) (index : Fin chain.count) :
    CutPath.Supported ambient (chain.cycles index).path.surfaceEdges := (chain.cycles index).supported

/-- Negate the retained integer multiplicities while reusing the original cycle bank. -/
@[expose] def negate (chain : CutCycleChains.CutCycleChain labels ambient) : CutCycleChains.CutCycleChain labels ambient
  :=
  ⟨chain.count, chain.cycles, Data.Vector.Basic.vectorOfFn fun index => -chain.weights index⟩

/-- Negating cycle multiplicities negates the complete primitive increment. -/
theorem increment_negate (chain : CutCycleChains.CutCycleChain labels ambient) (primitive : Fin source →
  Stokes.PrimitivePoint) :
    chain.negate.increment primitive = (PrimitivePoint.sub PrimitivePoint.zero) (chain.increment primitive) := by
  unfold CutCycleChain.increment CutCycleChain.negate Pairing.linear
  change PrimitivePoint.mk _ _ = PrimitivePoint.mk (0 - _) (0 - _)
  congr 1 <;> rw [Data.Gaussian.Basic.zero_sub, ← FiniteSum.Fin.sumFin_neg] <;>
    apply FiniteSum.Fin.sumFin_congr <;> intro index <;> rw [vectorOfFn_apply]
  all_goals
    have castNeg : ((-chain.weights index : Int) : Data.Gaussian.Basic.Canonical) =
        -(chain.weights index : Data.Gaussian.Basic.Canonical) := Algebra.Ring.IntCast.neg _
    rw [castNeg]
    ring1

end CutCycleChain
end Purelib.Topology.Surface.Sewing.CutCycleChains
