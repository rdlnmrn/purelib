module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Polynomial.Geometry.Grid.WindowBoundary
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
import Purelib.Topology.Mesh.IndexedQuadrilaterals
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits
public import Purelib.Riemann.Meshes.GridLiftedFaceLocations
public import Purelib.Data.Vector.Dependent
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Data.Int.Cast.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.WindowCircuitOrder
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedFaceLookup
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.QuadrilateralDual
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega

open Purelib

open Purelib.Curves.Hyperelliptic.Branches

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank

open Purelib.Polynomial.Geometry.Grid

open Purelib.Riemann.Meshes

open Purelib.Topology.Mesh

open Purelib.Topology.Mesh.IndexedQuadrilaterals

open Purelib.Topology.Polygon

open Purelib.Topology.Polygon.Stokes

open Purelib.Topology.Surface.Sewing

@[expose] public section

/-!
# Actual mesh faces omitted from an ordered branch word

Each retained regular occurrence locates its original cached quadrilateral
on the actual arriving sheet. The two existing mesh triangles provide the
finite face correction, with their diagonal cancelling exactly.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.CircuitPartition

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Mesh.IndexedQuadrilaterals (IndexedQuadrilateral)
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Topology.Surface.Sewing.SewingRetraction
open Purelib.Polynomial.Geometry.Grid.ClearGrid (Cell)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.BranchCellBank.CircuitPartition
  (RegularOccurrence)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {frames :
    RootIsolation.SquareRoot.Grid.RootFrames bank.grid}
  {vertices : Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices.VertexBank bank.grid} {edges :
    Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank frames}

/-- An antisymmetric edge value on a retained quadrilateral boundary equals the sum on its two original triangle
boundaries. -/
public theorem quad_value {count : Nat} (quad : IndexedQuadrilaterals.IndexedQuadrilateral count)
    (value : Stokes.OrientedEdge count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse = -value
      edge) :
    SewingRetraction.wordValue value quad.boundary =
      SewingRetraction.wordValue value quad.firstTriangle.boundary + SewingRetraction.wordValue value
        quad.secondTriangle.boundary := by
  have reversed := anti quad.diagonal
  simp only [IndexedQuadrilateral.diagonal, OrientedEdge.reverse] at reversed
  simp only [IndexedQuadrilateral.boundary, IndexedQuadrilateral.firstTriangle, IndexedQuadrilateral.secondTriangle,
    OrientedTriangle.boundary, SewingRetraction.wordValue]
  rw [reversed]
  ring1

namespace RegularOccurrence

variable (occurrence :
  OrderedBranchCircuits.BranchCellBank.CircuitPartition.RegularOccurrence
  faces vertices edges)

/-- The retained regular occurrence word is the actual indexed boundary of its original face at the arriving sheet. -/
public theorem original_word : occurrence.word =
    edges.indexedEdges vertices faces.regulars[occurrence.location.index.val].boundary occurrence.sheet := by
  rw [occurrence.word_eq, occurrence.location.indexed]
  have move (cell : ClearGrid.Cell curve.polynomial (Cuts.Ambient curve)) (member : cell ∈ bank.grid.cells)
      (equal : occurrence.location.face.cell = cell) :
      edges.indexedEdges vertices (CellBoundary.Cell.boundaryWalk cell member) occurrence.sheet =
        edges.indexedEdges vertices occurrence.location.face.boundary occurrence.sheet := by
    cases equal
    rfl
  exact move occurrence.cell occurrence.member occurrence.location.cell_eq

set_option genInjectivity false in
/-- The two original lifted mesh triangles accounting for one retained regular circuit occurrence.

The cached face location fixes the original arriving sheet and both signed triangle indices, with their exact word-value
identity. -/
structure FaceCorrection (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) (occurrence :
  CircuitPartition.RegularOccurrence faces vertices edges) where
  /-- The original cached lifted face at this occurrence's retained index and arriving sheet. -/ located :
    mesh.LocatedFace occurrence.location.index occurrence.sheet
  /-- The retained signed triangle indices contributing this face correction. -/ terms : List (SewingRetraction.FaceTerm
    mesh.triangles.length)
  /-- The correction consists exactly of the two original located triangle indices, each with coefficient one. -/
    terms_eq : terms = [(1, located.occurrence.first), (1, located.occurrence.second)]
  /-- Antisymmetric edge evaluation identifies the retained original regular words with these exact signed triangle
    corrections. -/ values : ∀ (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical), (∀ edge,
    value edge.reverse = -value edge) →
    SewingRetraction.wordValue value occurrence.word = SewingRetraction.faceValue mesh.triangulation.faces value terms

constructive_injectivity FaceCorrection

/-- Locate the retained regular occurrence's original lifted face and cache its two signed triangle terms. -/
def faceCorrection (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) :
  FaceCorrection
  mesh occurrence := by
  let located := mesh.locateFace occurrence.location.index occurrence.sheet
  refine ⟨located, [(1, located.occurrence.first), (1, located.occurrence.second)], rfl, ?_⟩
  intro value anti
  rw
    [original_word
    occurrence, ← located.lifted.boundary_eq]
  simp only [SewingRetraction.faceValue, Int.cast_one, one_mul, add_zero, located.occurrence.first_eq,
    located.occurrence.second_eq]
  exact Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.CircuitPartition.quad_value
    located.lifted.quad value anti

end RegularOccurrence

set_option genInjectivity false in
/-- The explanatory list and flattened face terms both use the same cached locations. No root transport or mesh triangle
is reconstructed. -/
structure FaceCorrections (mesh : GridLiftedMesh.LiftedMesh vertices edges faces)
    (regulars : List (CircuitPartition.RegularOccurrence faces vertices edges)) where
  /-- The dependent cache of face corrections indexed by the exact original occurrence list. -/ rows :
    Data.Vector.DependentVector (fun index : Fin regulars.length =>
    RegularOccurrence.FaceCorrection
    mesh regulars[index.val])
  /-- The retained signed triangle indices contributing this face correction. -/ terms : List (SewingRetraction.FaceTerm
    mesh.triangles.length)
  /-- Antisymmetric edge evaluation identifies the retained original regular words with these exact signed triangle
    corrections. -/ values : ∀ (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical), (∀ edge,
    value edge.reverse = -value edge) →
    CellBoundary.sumValues (fun occurrence => SewingRetraction.wordValue value occurrence.word) regulars =
      SewingRetraction.faceValue mesh.triangulation.faces value terms

constructive_injectivity FaceCorrections

/-- Cache face corrections in the exact original regular-occurrence order and concatenate their retained triangle terms.
-/
def faceCorrections (mesh : GridLiftedMesh.LiftedMesh vertices edges faces) :
    (regulars : List (CircuitPartition.RegularOccurrence faces vertices edges)) →
      FaceCorrections mesh
      regulars
  | [] => ⟨.nil, [], fun _ _ => rfl⟩
  | occurrence :: regulars =>
      let first :=
        RegularOccurrence.faceCorrection
        occurrence mesh
      let last :=
        faceCorrections
        mesh regulars
      ⟨.cons first last.rows, first.terms ++ last.terms, by
        intro value anti
        change SewingRetraction.wordValue value occurrence.word + CellBoundary.sumValues _ regulars = _
        rw [first.values value anti, last.values value anti, SewingRetraction.faceValue_append]⟩

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.CircuitPartition

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.OrderedBranches

open Purelib.Curves.Hyperelliptic.Branches (BranchCellBank)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Polygon.Stokes (OrientedEdge OrientedTriangle)
open Purelib.Topology.Surface.Sewing.SewingRetraction
open Purelib.Polynomial.Geometry.Grid.CellBoundary (sumValues)
open Purelib.Riemann.Meshes.PuncturedGridFaces (PuncturedFaces)
open _root_.Purelib.Polynomial.Geometry.Grid.WindowBoundary (Window)
open Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices (VertexBank)
open _root_.Purelib.RootIsolation.SquareRoot.Grid (RootFrames)
open Purelib.RootIsolation.SquareRoot.Grid (RootEdgeBank)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchCircuits.Window (OrderedBranches)

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : BranchCellBank curve branches
    higher}
  {faces : PuncturedFaces bank} {box :
    Purelib.Geometry.Rational.Box} {window : Polynomial.Geometry.Grid.WindowBoundary.Window
    bank.grid box}
  {frames : RootIsolation.SquareRoot.Grid.RootFrames bank.grid} {vertices :
    VertexBank bank.grid} {edges :
    RootEdgeBank frames} {sheet : Fin 2}

/-- Read the face corrections for the ordered branch compiler's actual retained regular occurrences. -/
def corrections (prepared : Window.OrderedBranches faces window edges vertices sheet) (mesh : GridLiftedMesh.LiftedMesh
  vertices edges faces) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.CircuitPartition.FaceCorrections mesh
      prepared.compiled.regulars :=
  Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.CircuitPartition.faceCorrections mesh
    prepared.compiled.regulars

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.OrderedBranches in
/-- The actual outer word is the ordered branch word modulo these explicit signed mesh-face terms. This is ready for the
existing finite Stokes API. -/
theorem face_values (prepared : Window.OrderedBranches faces window edges vertices sheet)
    {mesh : GridLiftedMesh.LiftedMesh vertices edges faces} (corrections :
      Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.CircuitPartition.FaceCorrections mesh
      prepared.compiled.regulars)
    (value : Stokes.OrientedEdge vertices.count → Data.Gaussian.Basic.Canonical) (anti : ∀ edge, value edge.reverse =
      -value edge) :
    edges.chainValue vertices value window.boundary sheet = SewingRetraction.wordValue value prepared.compiled.word +
      SewingRetraction.faceValue mesh.triangulation.faces value corrections.terms := by
  rw [prepared.values value anti, corrections.values value anti]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OrderedBranchFaceCorrections.OrderedBranches
