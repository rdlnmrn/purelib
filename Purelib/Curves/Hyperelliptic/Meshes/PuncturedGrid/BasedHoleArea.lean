module
import Purelib.Data.List.Append
import Purelib.RootIsolation.SquareRoot.Grid.Walk
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Polynomial.Geometry.Grid.FromStates

import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.BranchCutLifts
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.LoopMonodromy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
import Purelib.Integration.Path.BoundaryRibbon
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Polynomial.Geometry.Grid.Winding
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathWinding
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.RootEdgeBank
import Purelib.RootIsolation.SquareRoot.Grid.RootFrames
public import Purelib.RootIsolation.SquareRoot.Grid.Walk.ChainComparison
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WindowRootTransport
import Purelib.Topology.Surface.Boundary.PolarizedWordArea
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Data.Gaussian.Field
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.ClearGrid
import Purelib.Riemann.Meshes.GridLiftedFaces
import Purelib.Riemann.Meshes.PuncturedGridBoundary
import Purelib.Tactic.Ring

open Purelib.RootIsolation.SquareRoot.Grid.EdgeBank

open Purelib.Topology

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

open Purelib.Topology.Surface.Sewing

/-! The exact opposite-sheet stem defects for any retained based hole
circuit. The stem is supplied by its actual compiler leaf. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleArea
public section
open Purelib.Curves
open Purelib.Data
open Purelib.Integration
open Purelib.Polynomial
open Purelib.Riemann
open Purelib.RootIsolation
open Purelib
open Purelib.Data.List

open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue wordValue_append wordValue_reverse)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization
open Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization

open Purelib.Data.Gaussian.Basic.Canonical

variable {genus : Nat} {curve : Basic.HyperellipticCurve genus} {branches :
  Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {bank : Branches.BranchCellBank curve branches higher}
  {frames : SquareRoot.Grid.RootFrames bank.grid} (edges : SquareRoot.Grid.RootEdgeBank frames)
    (vertices : SquareRoot.Grid.LiftedVertices.VertexBank bank.grid)
  (hole : Meshes.PuncturedGridFaces.BranchHole bank) {start : Gaussian.Basic.Canonical} (member :
    Geometry.Grid.FromStates.ContainsVertex bank.grid start)
  (stem : Geometry.Grid.Walks.Walk bank.grid start hole.cell.box.anchor)

/-- The two original stem-and-hole cross areas combine into the explicit opposite-sheet remainder. -/
private theorem cross_remainder (stem hole other : Gaussian.Basic.Canonical) :
    Path.BoundaryRibbon.area stem hole + Path.BoundaryRibbon.area (stem + hole) (-other) =
      Path.BoundaryRibbon.area (stem + hole) (-(stem + other)) := by
  apply Gaussian.Basic.ext <;> simp only [Path.BoundaryRibbon.area, Gaussian.Basic.conj, Gaussian.Basic.add_re,
    Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
    Gaussian.Basic.neg_re, Gaussian.Basic.neg_im, Gaussian.Basic.mul_re, Gaussian.Basic.mul_im] <;> ring1

include member

/-- The original stem is returned on the other sheet. Both its polygon
difference and its total-increment defect remain explicit.

The concatenated lists retain their original order and multiplicities; the equality reassociates only the list boundary.
-/
theorem based_area (sheet : Fin 2) (value : Polygon.Stokes.OrientedEdge vertices.count →
  Gaussian.Basic.Canonical)
    (anti : ∀ edge, value edge.reverse = -value edge) :
    let outward := edges.indexedEdges vertices stem sheet
    let other := edges.indexedEdges vertices stem (Branches.BranchCutLifts.otherSheet sheet)
    let boundary := edges.indexedEdges vertices hole.boundary (RootEdgeBank.target edges stem
      sheet)
    Mesh.RetracingWords.wordArea value (edges.indexedEdges vertices (stem.based hole.boundary) sheet) =
      Mesh.RetracingWords.wordArea value boundary + (Mesh.RetracingWords.wordArea value outward -
        Mesh.RetracingWords.wordArea value other) +
        Path.BoundaryRibbon.area (SewingRetraction.wordValue value outward +
          SewingRetraction.wordValue value boundary)
          (-(SewingRetraction.wordValue value outward +
            SewingRetraction.wordValue value other)) := by
  intro outward other boundary
  let reference := fun point present =>
    (LoopMonodromy.BranchCellBank.referenceAt bank point present).toLoop
  have winding : Paths.PreparedPathWinding.ClearPath.rawWinding
      (stem.based hole.boundary).path = 4 * (2 * (0 : Int) + 1) := by
    rw [Geometry.Grid.Walks.Walk.based, Geometry.Grid.Winding.Walk.append_winding,
      Geometry.Grid.Winding.Walk.append_winding,
      Geometry.Grid.Winding.Walk.reverse_winding, hole.boundary_winding]
    ring1
  have returned := RootEdgeBank.target_odd edges (stem.based hole.boundary) member 0 winding
    sheet
  rw [Geometry.Grid.Walks.Walk.based, RootEdgeBank.target_append edges,
    RootEdgeBank.target_append edges] at returned
  have arrival : RootEdgeBank.target edges hole.boundary
    (RootEdgeBank.target edges stem sheet) =
      RootEdgeBank.target edges stem (Branches.BranchCutLifts.otherSheet sheet)
        := by
    apply edges.target_injective reference stem.reverse
    rw [returned, edges.target_reverse reference stem]
  rw [Geometry.Grid.Walks.Walk.based, edges.indexedEdges_append, edges.indexedEdges_append, arrival,
    edges.indexedEdges_reverse vertices reference, ← Append.append_assoc,
    Mesh.RetracingWords.wordArea_append, Mesh.RetracingWords.wordArea_append,
      SewingRetraction.wordValue_append]
  erw [Mesh.RetracingWords.wordArea_reverse value anti,
    SewingRetraction.wordValue_reverse value anti]
  change Mesh.RetracingWords.wordArea value outward + Mesh.RetracingWords.wordArea value boundary +
      Path.BoundaryRibbon.area (SewingRetraction.wordValue value outward)
        (SewingRetraction.wordValue value boundary) +
      -Mesh.RetracingWords.wordArea value other + Path.BoundaryRibbon.area
        (SewingRetraction.wordValue value outward +
        SewingRetraction.wordValue value boundary)
        (-SewingRetraction.wordValue value other) = _
  rw [← BasedHoleArea.cross_remainder
    (SewingRetraction.wordValue value outward)
    (SewingRetraction.wordValue value boundary)
    (SewingRetraction.wordValue value other)]
  ring1

/-- Polarize the actual based circuit. This exposes exactly the two stem
errors controlled by opposite-sheet polygon and increment requests. -/
theorem based_paired_area (sheet : Fin 2)
    (first second : Polygon.Stokes.OrientedEdge vertices.count → Gaussian.Basic.Canonical)
    (firstAnti : ∀ edge, first edge.reverse = -first edge) (secondAnti : ∀ edge, second edge.reverse = -second edge) :
    let outward := edges.indexedEdges vertices stem sheet
    let other := edges.indexedEdges vertices stem (Branches.BranchCutLifts.otherSheet sheet)
    let boundary := edges.indexedEdges vertices hole.boundary (RootEdgeBank.target edges stem
      sheet)
    let polygon := fun word => Path.PairedIncrementArea.area (word.map (fun edge => (⟨first edge, second edge⟩ :
      Polygon.Stokes.PrimitivePoint)))
    polygon (edges.indexedEdges vertices (stem.based hole.boundary) sheet) =
      polygon boundary + (polygon outward - polygon other) +
        Polygon.Stokes.edgeArea ⟨wordValue first outward + SewingRetraction.wordValue
          first boundary, SewingRetraction.wordValue second outward +
          SewingRetraction.wordValue second boundary⟩
          ⟨-(SewingRetraction.wordValue first outward +
            SewingRetraction.wordValue first other),
            -(SewingRetraction.wordValue second outward +
            SewingRetraction.wordValue second other)⟩ := by
  intro outward other boundary polygon
  have expanded := BilinearPolarization.extract_congr (fun
    coefficient => BasedHoleArea.based_area edges vertices hole member stem sheet
    (BilinearPolarization.mix first second coefficient)
      (BilinearPolarization.mix_reverse first second
      firstAnti secondAnti coefficient))
  have distribute : BilinearPolarization.extract (fun
    coefficient =>
      Mesh.RetracingWords.wordArea
        (BilinearPolarization.mix first second coefficient)
        boundary +
        (Mesh.RetracingWords.wordArea
          (BilinearPolarization.mix first second coefficient)
          outward - Mesh.RetracingWords.wordArea
          (BilinearPolarization.mix first second coefficient)
          other) +
        Path.BoundaryRibbon.area (SewingRetraction.wordValue
          (BilinearPolarization.mix first second coefficient)
          outward + SewingRetraction.wordValue
          (BilinearPolarization.mix first second coefficient)
          boundary)
          (-(SewingRetraction.wordValue
            (BilinearPolarization.mix first second
            coefficient) outward + SewingRetraction.wordValue
            (BilinearPolarization.mix first second
            coefficient) other))) =
      BilinearPolarization.extract (fun coefficient =>
        Mesh.RetracingWords.wordArea
        (BilinearPolarization.mix first second coefficient)
        boundary) +
        (BilinearPolarization.extract (fun coefficient =>
          Mesh.RetracingWords.wordArea
          (BilinearPolarization.mix first second coefficient)
          outward) -
          BilinearPolarization.extract (fun coefficient =>
            Mesh.RetracingWords.wordArea
            (BilinearPolarization.mix first second
            coefficient) other)) +
        BilinearPolarization.extract (fun coefficient =>
          Path.BoundaryRibbon.area
          (SewingRetraction.wordValue
            (BilinearPolarization.mix first second
            coefficient) outward + SewingRetraction.wordValue
            (BilinearPolarization.mix first second
            coefficient) boundary)
          (-(SewingRetraction.wordValue
            (BilinearPolarization.mix first second
            coefficient) outward + SewingRetraction.wordValue
            (BilinearPolarization.mix first second
            coefficient) other))) := by
    unfold BilinearPolarization.extract
    ring1
  have crossed : BilinearPolarization.extract (fun
    coefficient => Path.BoundaryRibbon.area
      (SewingRetraction.wordValue
        (BilinearPolarization.mix first second coefficient)
        outward + SewingRetraction.wordValue
        (BilinearPolarization.mix first second coefficient)
        boundary)
      (-(SewingRetraction.wordValue
        (BilinearPolarization.mix first second coefficient)
        outward + SewingRetraction.wordValue
        (BilinearPolarization.mix first second coefficient)
        other))) =
      Polygon.Stokes.edgeArea ⟨wordValue first outward + SewingRetraction.wordValue
        first boundary, SewingRetraction.wordValue second outward +
        SewingRetraction.wordValue second boundary⟩
        ⟨-(SewingRetraction.wordValue first outward +
          SewingRetraction.wordValue first other),
          -(SewingRetraction.wordValue second outward +
          SewingRetraction.wordValue second other)⟩ := by
    refine (BilinearPolarization.extract_congr (fun
      coefficient => ?_)).trans
      (BilinearPolarization.extract_area
        (SewingRetraction.wordValue first outward +
        SewingRetraction.wordValue first boundary)
        (-(SewingRetraction.wordValue first outward +
        SewingRetraction.wordValue first other))
        (SewingRetraction.wordValue second outward +
          SewingRetraction.wordValue second boundary)
          (-(SewingRetraction.wordValue second outward +
          SewingRetraction.wordValue second other)))
    rw [BilinearPolarization.word_mix,
      BilinearPolarization.word_mix,
      BilinearPolarization.word_mix]
    rw [Gaussian.Basic.conj_add, show Gaussian.Basic.conj (-(SewingRetraction.wordValue
      first outward + SewingRetraction.wordValue first other)) =
      -Gaussian.Basic.conj (SewingRetraction.wordValue first outward +
        SewingRetraction.wordValue first other) from rfl, Gaussian.Basic.conj_add]
    apply congrArg₂ Path.BoundaryRibbon.area <;> ring1
  have identity := expanded.trans distribute
  rw [Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_wordArea_mix,
    Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_wordArea_mix,
    Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_wordArea_mix,
    Surface.Boundary.PolarizedWordArea.BilinearPolarization.extract_wordArea_mix, crossed] at identity
  exact identity

end
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.BasedHoleArea
