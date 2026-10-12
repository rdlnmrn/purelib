module
public import Purelib.Topology.Chain.PathBoundary

import Purelib.Topology.Polygon.Stokes
public import Purelib.Topology.Surface.Cut.PrimitiveJumps
import Purelib.Topology.Surface.Cut.JumpPaths
import Purelib.Data.Gaussian.Basic
import Purelib.Tactic.Ring

@[expose] public section

/-!
# Exact recentering of primitive boundary area

Subtracting a constant changes an open path's area by an explicit endpoint
term. That term vanishes only for an actually closed cut path. No equality
of projected vertices is substituted for equality of cut endpoints.
-/

namespace Purelib.Integration.Path.CenteredPrimitiveArea

open Purelib
open Purelib.Topology.Polygon
/-- Centering all primitive values changes an ordered path's area by its exact endpoint correction.

The retained path-endpoint witness certifies the original edge order and endpoints; the origin is fixed throughout the
centering. -/
theorem edgeListArea_sub_constant {count : Nat} (primitive : Fin count → Stokes.PrimitivePoint) (origin :
  Stokes.PrimitivePoint) :
    ∀ {edges : List (Stokes.OrientedEdge count)} {start finish : Fin count},
      Topology.Chain.PathBoundary.PathEndpoints Stokes.OrientedEdge.start Stokes.OrientedEdge.finish edges start finish
        →
        Stokes.edgeListArea (fun vertex => (Stokes.PrimitivePoint.sub (primitive vertex)) origin) edges =
          Stokes.edgeListArea primitive edges -
          Stokes.edgeArea origin ((Stokes.PrimitivePoint.sub (primitive finish)) (primitive start))
  | _, _, _, .nil _ => by simp only [Stokes.edgeListArea, Stokes.edgeArea, Stokes.PrimitivePoint.sub]; ring1
  | _, _, _, .cons tail => by
      rw [Stokes.edgeListArea, Stokes.edgeListArea,
        Purelib.Integration.Path.CenteredPrimitiveArea.edgeListArea_sub_constant primitive origin tail]
      simp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
      ring1

/-- Centering the primitive values of a retained closed edge path preserves its exact area. -/
theorem edgeListArea_sub_constant_closed {count : Nat} (primitive : Fin count → Stokes.PrimitivePoint) (origin :
  Stokes.PrimitivePoint)
    {edges : List (Stokes.OrientedEdge count)} {anchor : Fin count}
    (closed : Topology.Chain.PathBoundary.PathEndpoints Stokes.OrientedEdge.start Stokes.OrientedEdge.finish edges
      anchor anchor) :
    Stokes.edgeListArea (fun vertex => (Stokes.PrimitivePoint.sub (primitive vertex)) origin) edges =
      Stokes.edgeListArea primitive edges := by
  rw [Integration.Path.CenteredPrimitiveArea.edgeListArea_sub_constant primitive origin closed]
  simp only [Stokes.edgeArea, Stokes.PrimitivePoint.sub]
  ring1

end Purelib.Integration.Path.CenteredPrimitiveArea
