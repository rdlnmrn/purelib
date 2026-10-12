module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Riemann.Meshes.PuncturedFaceLookup

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.Walks
public import Purelib.Polynomial.Geometry.Grid.EdgeSides
import Purelib.Riemann.Meshes.FramedPuncturedGrid
public import Purelib.Riemann.Integration.PuncturedVertexConnections
import Purelib.Riemann.Integration.PuncturedVertexStars

@[expose] public section

/-!
# Automatic regular faces along actual punctured-grid edges

A frame edge's sole incident cell cannot be a strictly interior branch hole.
For an interior edge, its two distinct incident cells cannot both be holes,
because both contain its initial vertex and holes are positively separated.
Read the existing vertex-star tags and retain the selected regular-bank row,
its exact side orientation, and both incident endpoint certificates.
-/

namespace Purelib.Riemann.Meshes.PuncturedEdgeFaces

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Polynomial.Geometry.Grid.EdgeSides (EdgeCell)
open Purelib.Riemann.Meshes.GridLiftedDualSteps (GridSide)
open _root_.Purelib.Polynomial.Geometry.Grid (EdgeSides)
open Purelib.Riemann.Integration.PuncturedVertexConnections (RegularIncident)
open Purelib.Riemann.Integration.PuncturedVertexStars (VertexStar StarEntry)
open Purelib.Polynomial.Geometry.Grid.Walks (Edge)
open _root_.Purelib.Polynomial.Geometry.Grid renaming ClearGrid -> Grid

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {start finish : Purelib.Data.Gaussian.Basic.Canonical}

open Purelib.Riemann in
open Purelib.Data in
open Purelib.Polynomial in
set_option genInjectivity false in
/-- A geometric incident edge cell with its exact regular-face location.

The retained geometry preserves both endpoint corners and side orientation in the original framed grid. -/
structure RegularEdgeCell (base : FramedPuncturedGrid curve branches higher) (start finish : Gaussian.Basic.Canonical)
  where
  /-- The retained oriented edge-cell geometry. -/ geometry : Geometry.Grid.EdgeSides.EdgeCell base.bank.grid start
    finish
  /-- The exact location of this cell in the regular-face bank. -/ located : Meshes.PuncturedGridFaces.RegularLocation
    base.faces.regulars geometry.cell

constructive_injectivity RegularEdgeCell

namespace RegularEdgeCell

/-- Read the selected regular cell as an incident face at the starting endpoint. -/
def first (cell : RegularEdgeCell base start finish) : RegularIncident base start := ⟨cell.geometry.first, cell.located⟩
/-- Read the selected regular cell as an incident face at the finishing endpoint. -/
def last (cell : RegularEdgeCell base start finish) : RegularIncident base finish := ⟨cell.geometry.last, cell.located⟩

/-- Reverse the edge geometry while retaining its regular-face location. -/
def reverse (cell : RegularEdgeCell base start finish) : RegularEdgeCell base finish start := ⟨cell.geometry.reverse,
  cell.located⟩

open Purelib.Polynomial
/-- Select a regular incident cell from the actual edge-side candidates.

The cached starting vertex star supplies each classification. Strict hole interiority handles frame edges, and hole
separation prevents both interior candidates from being holes. -/
def select (star : VertexStar base start) : Polynomial.Geometry.Grid.EdgeSides base.bank.grid start finish →
  RegularEdgeCell base start finish
  | .single cell firstFrame _ =>
      match star.classify cell.first with
      | .regular located => ⟨cell, located⟩
      | .hole located =>
          (StarEntry.no_hole_on_frame
            (⟨cell.cell, .hole located, cell.first.corner.contains⟩ : StarEntry base start) located firstFrame).elim
  | .pair first second different =>
      match star.classify first.first with
      | .regular located => ⟨first, located⟩
      | .hole firstHole =>
          match star.classify second.first with
          | .regular located => ⟨second, located⟩
          | .hole secondHole =>
              (different (StarEntry.hole_cells_equal
                (⟨first.cell, .hole firstHole, first.first.corner.contains⟩ : StarEntry base start)
                (⟨second.cell, .hole secondHole, second.first.corner.contains⟩ : StarEntry base start) firstHole
                  secondHole)).elim

/-- Find a regular face along an actual grid edge using its cached starting vertex star.

Construct the finite geometric side candidates from the retained frame and select a certified regular-bank row. -/
def acquire (star : VertexStar base start) (edge : Geometry.Grid.Walks.Edge base.bank.grid start finish) :
  RegularEdgeCell base start finish :=
  select star (Polynomial.Geometry.Grid.EdgeSides.build base.bank.frame
    (Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox_proper curve.polynomial) edge)

end RegularEdgeCell

end Purelib.Riemann.Meshes.PuncturedEdgeFaces
