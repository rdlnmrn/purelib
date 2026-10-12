module
public import Purelib.Algebra.Group.Negation
import Purelib.Algebra.Ring.IntCast
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex
public import Purelib.Topology.Surface.Sewing.SewingRetraction
import Mathlib.Algebra.Ring.Defs
import Purelib.Tactic.Ring

open Purelib.Algebra

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

public section

/-!
# Signed combinations of actual closed lifted vertex walks

Every operation retains the literal indexed path and the cached endpoint
transport. Reversed connectors cancel for every antisymmetric valuation.
Integer coefficients are realized by finite traversals of the same loops.
-/

section

open Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

attribute [local instance 2000] Group.Negation.subNegZeroMonoid

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames grid} {vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid}
    {edges : SquareRoot.Grid.RootEdgeBank frames}
  {first middle last : Fin vertices.count}

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

/-- Sum the supplied edge values along the original cached indexed edge word. -/
@[expose] def value (path : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last) (valuation :
  Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) : Gaussian :=
  Topology.Surface.Sewing.SewingRetraction.wordValue valuation path.indexed

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations

/-- Joining retained vertex walks adds their original cached edge-value sums. -/
theorem append_value (left : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first middle) (right :
  SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges middle last)
    (valuation : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    (left.append right).value valuation = left.value valuation + right.value valuation :=
  Topology.Surface.Sewing.SewingRetraction.wordValue_append valuation left.indexed right.indexed

/-- Reversing a retained vertex walk negates its antisymmetric edge-value sum. -/
theorem reverse_value (path : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (valuation : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      valuation edge.reverse = -valuation edge) :
    (path.reverse reference).value valuation = -path.value valuation :=
  Topology.Surface.Sewing.SewingRetraction.wordValue_reverse valuation anti path.indexed

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

/-- Base an original closed vertex walk at another vertex using a retained stem and its reverse. -/
@[expose] def conjugate (connector : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last) (loop :
  SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges last last)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first := connector.append (loop.append
      (connector.reverse reference))

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations

/-- Basing a retained loop along a stem preserves its antisymmetric edge-value sum. -/
theorem conjugate_value (connector : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first last) (loop :
  SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges last last)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (valuation : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) (anti : ∀ edge,
      valuation edge.reverse = -valuation edge) :
    (connector.conjugate loop reference).value valuation = loop.value valuation := by
  rw [SquareRoot.Grid.Walk.Vertex.VertexWalk.conjugate, SquareRoot.Grid.Walk.Combinations.append_value,
    SquareRoot.Grid.Walk.Combinations.append_value, SquareRoot.Grid.Walk.Combinations.reverse_value connector reference
    valuation anti]
  ring1

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

/-- Concatenate the original closed vertex walk the supplied finite number of times. -/
@[expose] def repetitions (loop : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first) : Nat →
  SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first
  | 0 => SquareRoot.Grid.Walk.Vertex.VertexWalk.nil vertices edges first
  | count + 1 => loop.append (Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk.repetitions loop count)

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations

/-- Finite repetition multiplies the original loop's edge-value sum by its natural repetition count. -/
theorem repetitions_value (loop : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first) (count : Nat)
    (valuation : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical) :
    (loop.repetitions count).value valuation = (count : Gaussian.Basic.Canonical) * loop.value valuation := by
  induction count with
  | zero => change 0 = (0 : Gaussian.Basic.Canonical) * loop.value valuation; exact (zero_mul _).symm
  | succ count ih =>
    rw [SquareRoot.Grid.Walk.Vertex.VertexWalk.repetitions, SquareRoot.Grid.Walk.Combinations.append_value, ih,
      Nat.cast_succ]; ring1

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

/-- Repeat the original closed walk for a nonnegative coefficient and its reverse for a negative coefficient. -/
@[expose] def integer (loop : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point) :
    Int → SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first
  | .ofNat count => loop.repetitions count
  | .negSucc count => (loop.repetitions (count + 1)).reverse reference

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Vertex.VertexWalk

namespace Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations

/-- Signed repetition multiplies the original loop's edge-value sum by the retained integer coefficient. -/
theorem integer_value (loop : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first)
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    (weight : Int) (valuation : Topology.Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (anti : ∀ edge, valuation edge.reverse = -valuation edge) :
    (loop.integer reference weight).value valuation = (weight : Gaussian.Basic.Canonical) * loop.value valuation := by
  cases weight with
  | ofNat count =>
      rw [SquareRoot.Grid.Walk.Vertex.VertexWalk.integer, SquareRoot.Grid.Walk.Combinations.repetitions_value]
      change (count : Gaussian.Basic.Canonical) * loop.value valuation = ((count : Int) : Gaussian.Basic.Canonical) *
        loop.value valuation
      rw [Int.cast_natCast]
  | negSucc count =>
    rw [SquareRoot.Grid.Walk.Vertex.VertexWalk.integer, SquareRoot.Grid.Walk.Combinations.reverse_value _ reference
      valuation anti, SquareRoot.Grid.Walk.Combinations.repetitions_value, Purelib.Algebra.Ring.IntCast.cast_negSucc,
      Nat.cast_succ]; ring1

/-- Concatenate a finite indexed family of retained loops with their signed integer coefficients.

The construction recurses through the original vector, preserving its shared base vertex and each original edge word. -/
@[expose] def combination (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
  Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {count : Nat} (loops : Data.Vector (SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first)
      count)
    (weights : Data.Vector Int count) : SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first
      :=
  let rec traverse : {size : Nat} →
      Data.Vector (SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first) size →
      {weightCount : Nat} → Data.Vector Int weightCount →
      size = weightCount → SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first
    | _, .nil, _, _, _ => SquareRoot.Grid.Walk.Vertex.VertexWalk.nil vertices edges first
    | _, .cons _ _, _, .nil, impossible => Nat.noConfusion impossible
    | _, .cons loop loops, _, .cons weight weights, same =>
        (loop.integer reference weight).append (traverse loops weights (Nat.succ.inj same))
  traverse loops weights rfl

/-- The edge-value sum of the retained loop combination is the finite sum of its original weighted loop values. -/
theorem combination_value
    (reference : ∀ point, Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point →
      Riemann.Paths.OwnerLoopMonodromy.WindingOneLoop polynomial point)
    {count : Nat} (loops : Data.Vector (SquareRoot.Grid.Walk.Vertex.VertexWalk vertices edges first first)
      count)
    (weights : Data.Vector Int count) (valuation : Topology.Polygon.Stokes.OrientedEdge vertices.count →
      Gaussian.Basic.Canonical)
    (anti : ∀ edge, valuation edge.reverse = -valuation edge) :
    (SquareRoot.Grid.Walk.Combinations.combination reference loops weights).value valuation =
      FiniteSum.Fin.sumFin (fun index => (weights index : Gaussian.Basic.Canonical) * (loops index).value valuation) :=
        by
  have all : ∀ {weightCount : Nat} (weights : Data.Vector Int weightCount)
      (same : count = weightCount),
      (SquareRoot.Grid.Walk.Combinations.combination reference loops (same.symm ▸ weights)).value valuation =
        FiniteSum.Fin.sumFin (fun index => ((same.symm ▸ weights) index : Gaussian.Basic.Canonical) * (loops
          index).value valuation) := by
    clear weights
    induction loops with
    | nil =>
        intro weightCount weights same
        cases weights with
        | nil => rfl
        | cons => exact Nat.noConfusion same
    | @cons size loop loops ih =>
        intro weightCount weights same
        cases weights with
        | nil => exact Nat.noConfusion same
        | @cons weightSize weight weights =>
            have sizes : size = weightSize := Nat.succ.inj same
            cases sizes
            change ((loop.integer reference weight).append
              (SquareRoot.Grid.Walk.Combinations.combination reference loops weights)).value valuation = _
            rw [SquareRoot.Grid.Walk.Combinations.append_value, SquareRoot.Grid.Walk.Combinations.integer_value _
              reference weight valuation anti, ih weights rfl, FiniteSum.Fin.sumFin_succ]
            rfl
  exact all weights rfl

end Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations

end
