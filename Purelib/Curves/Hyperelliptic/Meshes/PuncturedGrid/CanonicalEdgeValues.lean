module
import Purelib.Curves.Hyperelliptic.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TriangleCornerSources
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewnPrimitiveContacts
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.RouteChartContacts
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeWalks
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Topology.Surface.Sewing.VertexSewing
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
public import Purelib.Topology.Surface.Sewing.SewnPrimitivePaths

/-! A fixed chart is chosen in increasing vertex-index direction and used
with the opposite sign on reversal. This gives the antisymmetric edge
valuation required by the cut-coordinate identities. -/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues

open Purelib.Curves

open Purelib.Riemann

open Purelib.RootIsolation

open Purelib

public section

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames base.bank.grid} {vertices :
      SquareRoot.Grid.LiftedVertices.VertexBank
    base.bank.grid} {edges : SquareRoot.Grid.RootEdgeBank frames}
  {mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces}

/-- Reversing a retained route negates its source increment.

Both orientations read the same two endpoints from the same retained primitive
values; scalar subtraction establishes their opposite signs. -/
private theorem reverseRoute_increment {edge : Topology.Polygon.Stokes.OrientedEdge vertices.count}
    (route : Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge.reverse) (values : Fin
      mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.reverseRoute route).sourceEdge.increment values =
      -route.sourceEdge.increment values := by
  cases edge
  cases route with
  | forward location =>
    simp only [Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.reverseRoute,
      Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.sourceEdge,
      Topology.Surface.Sewing.SewnPrimitiveContacts.SourceEdge.increment]; ring1
  | backward location =>
    change (values location.sourceEdge.source location.sourceEdge.last - values location.sourceEdge.source
      location.sourceEdge.first) =
      -(values location.sourceEdge.source location.sourceEdge.first - values location.sourceEdge.source
        location.sourceEdge.last)
    ring1

/-- Choose the retained edge route in increasing vertex-index direction.

The order depends only on the two indexed vertices. Supported edges reuse the
original route and its chart, independently of primitive values or accuracy. -/
@[expose] def orderedRoute (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) (edge :
  Topology.Polygon.Stokes.OrientedEdge vertices.count)
    (supported : edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces) :
        Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute mesh edge :=
  Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.directedRoute mesh edge supported (decide (edge.start.val <
    edge.finish.val))

/-- Read the retained forward increment of a supported edge.

The original chart route supplies the primitive reading. Unsupported edges
return zero without constructing a route or choosing a second chart. -/
@[expose] def forwardValue (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) (edge :
      Topology.Polygon.Stokes.OrientedEdge vertices.count) : Gaussian :=
  if supported : edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces then
    (Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.build mesh edge supported).sourceEdge.increment values
  else 0

/-- Assign the canonical signed increment to an indexed edge.

Unsupported edges and loops have value zero. Supported edges reuse one directed
chart, so reversal never chooses a second primitive. -/
@[expose] def edgeValuation (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) (edge :
      Topology.Polygon.Stokes.OrientedEdge vertices.count) : Gaussian :=
  if edge.start.val < edge.finish.val then forwardValue mesh values edge
  else if edge.finish.val < edge.start.val then -forwardValue mesh values edge.reverse else 0

/-- Reversing an indexed edge negates its canonical retained value.

The two strict index orders are disjoint. Their scalar branches give opposite
signs, while loops and unsupported edges keep their zero values. -/
theorem edgeValuation_reverse (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) (edge :
      Topology.Polygon.Stokes.OrientedEdge vertices.count) :
    edgeValuation mesh values edge.reverse = -edgeValuation mesh values edge := by
  unfold edgeValuation
  change (if edge.finish.val < edge.start.val then forwardValue mesh values edge.reverse
    else if edge.start.val < edge.finish.val then -forwardValue mesh values edge.reverse.reverse else 0) =
      -(if edge.start.val < edge.finish.val then forwardValue mesh values edge
        else if edge.finish.val < edge.start.val then -forwardValue mesh values edge.reverse else 0)
  by_cases forward : edge.start.val < edge.finish.val
  · have backward : ¬ edge.finish.val < edge.start.val := Nat.lt_asymm forward
    rewrite [if_neg backward, if_pos forward, if_pos forward]
    exact Eq.refl _
  · by_cases backward : edge.finish.val < edge.start.val
    · rewrite [if_pos backward, if_neg forward, if_pos backward]
      ring1
    · rewrite [if_neg backward, if_neg forward, if_neg forward, if_neg backward]
      ring1

/-- The canonically oriented route reads the retained edge valuation.

A supported edge has distinct endpoints. Its index order selects the original
forward route or the reversal of the same retained route, with the stated sign. -/
theorem orderedRoute_value (mesh : Meshes.GridLiftedMesh.LiftedMesh vertices edges base.faces) (edge :
  Topology.Polygon.Stokes.OrientedEdge vertices.count)
    (supported : edge ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
      edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces)
    (values : Fin mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues 3) :
    (orderedRoute mesh edge supported).sourceEdge.increment values = edgeValuation mesh values edge := by
  have nonloop : edge.start ≠ edge.finish := supported.elim
    (Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop mesh
      edge)
    (fun member equal =>
      Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryPairs.ClearGrid.BranchCellBank.LiftedMesh.orientedEdges_nonloop
      mesh edge.reverse member equal.symm)
  have different : edge.start.val ≠ edge.finish.val := fun equal => nonloop (Fin.ext equal)
  by_cases forward : edge.start.val < edge.finish.val
  · have selected : decide (edge.start.val < edge.finish.val) = true := decide_eq_true forward
    unfold orderedRoute Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.directedRoute edgeValuation forwardValue
    rewrite [selected, if_pos forward, dif_pos supported]
    exact Eq.refl _
  · have backward : edge.finish.val < edge.start.val := by omega
    have selected : decide (edge.start.val < edge.finish.val) = false := decide_eq_false forward
    have reversed : edge.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces ∨
        edge.reverse.reverse ∈ Topology.Polygon.Stokes.triangleEdgeOccurrences mesh.triangulation.faces := by
      exact supported.symm
    unfold orderedRoute Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.directedRoute edgeValuation
    rewrite [selected, if_neg forward, if_pos backward]
    change (Hyperelliptic.Meshes.PuncturedGrid.Fragment.RouteWords.reverseRoute
      (Hyperelliptic.Meshes.PuncturedGrid.MeshPathWalks.EdgeRoute.build mesh edge.reverse
        reversed)).sourceEdge.increment values = _
    rewrite [reverseRoute_increment]
    unfold forwardValue
    rewrite [dif_pos reversed]
    exact Eq.refl _

end

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
