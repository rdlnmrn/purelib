module
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Gaussian.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Paths.OwnerLoopMonodromy
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Riemann.Meshes.GridLiftedConnections
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Tactic.Ring
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Polynomial.Geometry.Grid.FromStates (ContainsVertex)
open Purelib.Riemann.Paths.OwnerLoopMonodromy (WindingOneLoop)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank (LiftedWalk)

open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

@[expose] public section

/-!
# Based joining of actual root-lifted loops

Move a closed loop along a checked connector and return along its literal
reverse.  Both occurrences of the connector read the same lifted vertex
indices, so their area contributions cancel exactly.  Finite concatenation
then retains a single based walk with its actual endpoint-owner equation.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.LiftedWalk

open Purelib.Topology.Polygon.Stokes (PrimitivePoint edgeListArea edgeListArea_append)

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box} {grid :
  Polynomial.Geometry.Grid.ClearGrid polynomial ambient} {frames : RootIsolation.SquareRoot.Grid.RootFrames grid}
  {edges : RootEdgeBank frames} {start middle finish : Canonical}
    {firstSheet middleSheet lastSheet : Fin 2}

/-- Read the primitive edge-list area of the original lifted walk. -/
def area (path :
  LiftedWalk edges start firstSheet finish lastSheet) (vertices :
  VertexBank grid)
    (primitive : Fin vertices.count → PrimitivePoint) : Canonical :=
  edgeListArea primitive (edges.indexedEdges vertices path.walk firstSheet)

/-- Appending compatible retained lifted walks adds their primitive areas.

The shared middle sheet joins the original indexed edge lists, preserving their oriented occurrences and the supplied
primitive values. -/
theorem append_area (left :
  LiftedWalk edges start firstSheet middle middleSheet)
    (right : LiftedWalk edges middle middleSheet finish lastSheet) (vertices :
      VertexBank grid)
    (primitive : Fin vertices.count → PrimitivePoint) :
    (left.append right).area vertices primitive = left.area vertices primitive + right.area vertices primitive := by
  simp only [area,
    LiftedWalk.append, edges.indexedEdges_append, left.sheet_eq,
    edgeListArea_append, -eq_self, -iff_self]
  rfl

/-- Reversing the retained lifted walk negates its primitive area. -/
theorem reverse_area (path :
  LiftedWalk edges start firstSheet finish lastSheet)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    (vertices : VertexBank grid) (primitive : Fin vertices.count → PrimitivePoint) :
    (path.reverse reference).area vertices primitive = -path.area vertices primitive :=
  (congrArg (fun sheet => edgeListArea primitive (edges.indexedEdges vertices path.walk.reverse sheet))
    path.sheet_eq.symm).trans
    (edges.indexedEdges_reverse_area vertices reference primitive path.walk firstSheet)

/-- Join the original connector, loop and reversed connector into a loop at the original starting sheet. -/
def conjugate (connector :
  LiftedWalk edges start firstSheet finish lastSheet)
    (loop : LiftedWalk edges finish lastSheet finish lastSheet)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point) :
    LiftedWalk edges start firstSheet start firstSheet :=
  connector.append (loop.append (connector.reverse reference))

/-- Conjugating a retained lifted loop leaves its primitive area unchanged. -/
theorem conjugate_area (connector :
  LiftedWalk edges start firstSheet finish lastSheet)
    (loop : LiftedWalk edges finish lastSheet finish lastSheet)
    (reference : ∀ point, ContainsVertex grid point →
      WindingOneLoop polynomial point)
    (vertices : VertexBank grid) (primitive : Fin vertices.count → PrimitivePoint) :
    (connector.conjugate loop reference).area vertices primitive = loop.area vertices primitive := by
  rw [conjugate,
    append_area,
    append_area,
    reverse_area]
  ring1

/-- Right-associated concatenation traverses each retained loop once.
All joins are at the same coordinate and the same actual frame owner. -/
def concatenate (edges :
  RootEdgeBank frames) (base : Canonical) (member :
  ContainsVertex grid base) (sheet : Fin 2) :
    List (LiftedWalk edges base sheet base sheet) →
      LiftedWalk edges base sheet base sheet
  | [] => LiftedWalk.nil edges base member sheet
  | loop :: loops => loop.append (concatenate edges base member sheet loops)

/-- The area of the retained loop concatenation is the finite sum of the original loop areas. -/
theorem concatenate_area (edges :
  RootEdgeBank frames) (base : Canonical) (member :
  ContainsVertex grid base) (sheet : Fin 2)
    (vertices : VertexBank grid) (primitive : Fin vertices.count → PrimitivePoint) :
    (loops : List (LiftedWalk edges base sheet base sheet)) →
      (concatenate edges base member sheet loops).area vertices
        primitive = Geometry.Grid.CellBoundary.sumValues (fun loop => loop.area vertices primitive) loops
  | [] => rfl
  | loop :: loops => by
      rw [concatenate,
        append_area, concatenate_area edges base member sheet
        vertices primitive loops]
      rfl

end Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank.LiftedWalk
