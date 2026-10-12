module

meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Data.List.Flatten
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Topology.SquareRootContinuationChain
public import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Riemann.Paths.OwnerTraceReadings
import Purelib.Riemann.RootContinuation.RootOwnerFrames
import Purelib.Tactic.QuotientFreeOmega

public section

/-!
# Shared vertex indices for the two-sheeted grid

A base coordinate uses its first retained occurrence.  Its two root owners
have indices `2 * baseIndex + sheet`, so equal base coordinates are shared
without identifying the two sheets.  The coordinate bank is pure finite
geometry: constructing it never runs root isolation or path preparation.
-/

namespace Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
open Purelib.Data

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib

open Purelib.RootIsolation

open Purelib.Data.Gaussian.Basic (point)

namespace SheetIndex

/-- Encode a base vertex and sheet as the bounded index `2 * base + sheet`.

The supplied base and sheet bounds prove that the result lies in twice the
retained coordinate count, preserving both finite indices. -/
@[expose] def encode {count : Nat} (base : Fin count) (sheet : Fin 2) : Fin (2 * count) :=
  ⟨2 * base.val + sheet.val, by have := base.isLt; have := sheet.isLt; omega⟩

/-- Decode the retained base vertex index by division by two. -/
@[expose] def base {count : Nat} (index : Fin (2 * count)) : Fin count :=
  ⟨index.val / 2, by have := index.isLt; omega⟩

/-- Decode the retained sheet index by remainder modulo two. -/
@[expose] def sheet {count : Nat} (index : Fin (2 * count)) : Fin 2 :=
  ⟨index.val % 2, by omega⟩

/-- Decoding an encoded lifted index recovers its original base vertex. -/
theorem base_encode {count : Nat} (index : Fin count) (sheet : Fin 2) : base
  (SquareRoot.Grid.LiftedVertices.SheetIndex.encode index sheet) = index := by
  apply Fin.ext
  change (2 * index.val + sheet.val) / 2 = index.val
  have := sheet.isLt
  omega

/-- Decoding an encoded lifted index recovers its original sheet. -/
theorem sheet_encode {count : Nat} (index : Fin count) (sheet : Fin 2) : SquareRoot.Grid.LiftedVertices.SheetIndex.sheet
  (SquareRoot.Grid.LiftedVertices.SheetIndex.encode index sheet) = sheet := by
  apply Fin.ext
  change (2 * index.val + sheet.val) % 2 = sheet.val
  have := sheet.isLt
  omega

/-- Re-encoding the base and sheet of a lifted index recovers that exact index.

The quotient and remainder by two retain the supplied index's scalar value;
the original finite bound remains attached to the reconstructed index. -/
theorem encode_decode {count : Nat} (index : Fin (2 * count)) : SquareRoot.Grid.LiftedVertices.SheetIndex.encode (base
  index) (sheet index) = index := by
  apply Fin.ext
  change 2 * (index.val / 2) + index.val % 2 = index.val
  omega

end SheetIndex

variable {polynomial : Geometry.ClearPath.GaussianPolynomial} {ambient : Box}

set_option genInjectivity false in
/-- A finite coordinate bank with exact two-way grid coverage.

The retained coordinate list contains every grid vertex and only grid vertices.
Its order determines the first-occurrence index shared by the two sheets. -/
structure VertexBank (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) where
  /-- The retained finite list of Gaussian base coordinates. -/ coordinates : List Gaussian.Basic.Canonical
  /-- Every actual grid vertex occurs in the retained coordinate list. -/ covers : ∀ point,
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point → point ∈ coordinates
  /-- Every retained coordinate is an actual vertex of the original grid. -/ onGrid : ∀ point ∈ coordinates,
    Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point

constructive_injectivity VertexBank

namespace VertexBank

variable {grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient}

/-- Build a coordinate bank by traversing the Cartesian product of the original grid's vertical and horizontal lines.

The two coverage proofs retain this exact list; constructing the bank performs no root preparation. -/
@[expose] def build (grid : Polynomial.Geometry.Grid.ClearGrid polynomial ambient) :
  SquareRoot.Grid.LiftedVertices.VertexBank
  grid := by
  let coordinates := grid.vertical.flatMap fun vertical =>
    grid.horizontal.map fun horizontal => point vertical.coordinate horizontal.coordinate
  refine ⟨coordinates, ?_, ?_⟩
  · intro base member
    rcases Data.List.Map.mem_map.mp member.1 with ⟨vertical, verticalMember, verticalEq⟩
    rcases Data.List.Map.mem_map.mp member.2 with ⟨horizontal, horizontalMember, horizontalEq⟩
    exact Data.List.Flatten.mem_flatMap.mpr ⟨vertical, verticalMember,
      Data.List.Map.mem_map.mpr ⟨horizontal, horizontalMember, Gaussian.Basic.ext verticalEq horizontalEq⟩⟩
  · intro base member
    rcases Data.List.Flatten.mem_flatMap.mp member with ⟨vertical, verticalMember, member⟩
    rcases Data.List.Map.mem_map.mp member with ⟨horizontal, horizontalMember, equal⟩
    cases equal
    exact ⟨Data.List.Map.mem_map_of_mem verticalMember, Data.List.Map.mem_map_of_mem horizontalMember⟩

/-- Twice the retained coordinate-list length, accounting for both sheets at every base entry. -/
@[expose] def count (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) : Nat := 2 * vertices.coordinates.length

/-- Read the base coordinate stored at a lifted index. -/
@[expose] def coordinate (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (index : Fin vertices.count) :
  Gaussian.Basic.Canonical :=
  Topology.Mesh.CoordinateTriangulation.vertexAt vertices.coordinates (SquareRoot.Grid.LiftedVertices.SheetIndex.base
    index)

/-- Read the sheet retained by a lifted index. -/
@[expose] def sheet (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (index : Fin vertices.count) : Fin 2 :=
  SquareRoot.Grid.LiftedVertices.SheetIndex.sheet index

/-- Find the first retained occurrence of a grid point and pair it with its sheet.

The lookup consumes the cached coordinate list and its coverage witness.
Encoding its retained position preserves the separately supplied sheet. -/
@[expose] def index (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (point : Gaussian.Basic.Canonical)
  (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point) (sheet : Fin 2) : Fin vertices.count :=
  SquareRoot.Grid.LiftedVertices.SheetIndex.encode (Topology.Mesh.CoordinateTriangulation.lookupVertex point
    vertices.coordinates (vertices.covers point member)).index sheet

/-- The lifted index computed for a grid point reads back that exact point.

Decoding recovers the first retained base position, whose cached coordinate
is identified by the original lookup certificate. -/
theorem coordinate_index (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (point : Gaussian.Basic.Canonical)
  (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point) (sheet : Fin 2) :
    vertices.coordinate (vertices.index point member sheet) = point := by
  rw [SquareRoot.Grid.LiftedVertices.VertexBank.coordinate, SquareRoot.Grid.LiftedVertices.VertexBank.index,
    SquareRoot.Grid.LiftedVertices.SheetIndex.base_encode]
  exact (Topology.Mesh.CoordinateTriangulation.lookupVertex point vertices.coordinates (vertices.covers point
    member)).coordinate_eq

/-- The lifted index computed for a grid point retains the supplied sheet. -/
theorem sheet_index (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (point : Gaussian.Basic.Canonical)
  (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point) (sheet : Fin 2) :
    vertices.sheet (vertices.index point member sheet) = sheet :=
  SquareRoot.Grid.LiftedVertices.SheetIndex.sheet_encode _ _

/-- Distinct sheets remain distinct indices above the same rational base point.

Reading back the sheet from the retained lifted index identifies the supplied
sheet, so coordinate deduplication keeps the two sheet occurrences separate. -/
theorem index_same_sheet (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (point : Gaussian.Basic.Canonical)
  (member : Polynomial.Geometry.Grid.FromStates.ContainsVertex grid point)
    (first second : Fin 2) (equal : vertices.index point member first = vertices.index point member second) : first =
      second :=
  (vertices.sheet_index point member first).symm.trans ((congrArg vertices.sheet equal).trans (vertices.sheet_index
    point member second))

/-- The coordinate read at every lifted index is an actual original-grid vertex. -/
theorem coordinate_onGrid (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (index : Fin vertices.count) :
  Polynomial.Geometry.Grid.FromStates.ContainsVertex grid (vertices.coordinate index) :=
  vertices.onGrid _ (by
    change vertices.coordinates[(SquareRoot.Grid.LiftedVertices.SheetIndex.base
      index).val]'((SquareRoot.Grid.LiftedVertices.SheetIndex.base index).isLt) ∈ vertices.coordinates
    exact List.getElem_mem (SquareRoot.Grid.LiftedVertices.SheetIndex.base index).isLt)

/-- Every lifted index names its actual cached root occurrence.

The coordinate readback supplies the original grid-vertex witness to the
retained root frame, which selects the owner at the retained sheet. -/
@[expose] def owner (vertices : SquareRoot.Grid.LiftedVertices.VertexBank grid) (frames :
  RootFrames grid) (index : Fin vertices.count) :
    Riemann.Topology.SquareRootContinuationChain.Owner (polynomial.eval (vertices.coordinate index)) :=
  (frames.frameAt _ (vertices.coordinate_onGrid index)).owners (vertices.sheet index)

end VertexBank

end Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
