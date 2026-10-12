module
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Topology.Polygon.Stokes

import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.IncrementArea
import Purelib.Topology.Mesh.RetracingWords
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.OwnedPuncturedMesh

public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.ValueWordLinearity
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Riemann.Meshes.FramedPuncturedGrid
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings.EdgeMagnitude
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Tactic.Ring

open Purelib

public section

/-! The polarized word area is the full two-differential increment area.
This readback keeps the internal area even for words with zero total. -/

namespace Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Topology.Surface.Sewing.SewingRetraction (wordValue)
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)

/-- Summing paired edge increments gives the two original ordered word totals. -/
private theorem paired_total {vertices : Nat}
    (first second : OrientedEdge vertices → Data.Gaussian.Basic.Canonical) (word : List (OrientedEdge vertices)) :
    Integration.Path.PairedIncrementArea.total (word.map (fun edge =>
      (⟨first edge, second edge⟩ : PrimitivePoint))) =
      ⟨wordValue first word, Purelib.Topology.Surface.Sewing.SewingRetraction.wordValue second word⟩ := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
    change (⟨first edge, second edge⟩ : PrimitivePoint).add
      (Integration.Path.PairedIncrementArea.total (rest.map (fun e => ⟨first e, second e⟩))) = _
    rw [ih]
    rfl

/-- This is an equality of full areas, with no closure or vanishing-total assumption. Its right side is the increment
area retained by Newton cut boundary comparisons. -/
theorem extract_wordArea_mix {vertices : Nat}
    (first second : OrientedEdge vertices → Data.Gaussian.Basic.Canonical) (word : List (OrientedEdge vertices)) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Topology.Mesh.RetracingWords.wordArea
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
      coefficient) word) =
      Integration.Path.PairedIncrementArea.area (word.map (fun edge =>
        (⟨first edge, second edge⟩ : PrimitivePoint))) := by
  induction word with
  | nil =>
    change (⟨1 / 4, 0⟩ : Data.Gaussian.Basic.Canonical) * (0 - 0 -
      Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary * (0 - 0)) = 0
    ring1
  | cons edge rest ih =>
    have split (coefficient : Data.Gaussian.Basic.Canonical) :
        Topology.Mesh.RetracingWords.wordArea
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
          coefficient) (edge :: rest) =
          Topology.Mesh.RetracingWords.wordArea
            (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient) rest +
          Integration.Path.BoundaryRibbon.area
            (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient edge)
            (Topology.Surface.Sewing.SewingRetraction.wordValue
              (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
              coefficient) rest) := by
      exact (Integration.Path.IncrementArea.pathArea_cons _ _).trans
        (congrArg (fun total => Topology.Mesh.RetracingWords.wordArea
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
          coefficient) rest +
          Integration.Path.BoundaryRibbon.area
            (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient edge) total)
          (Topology.Mesh.RetracingWords.sum_map_eq_wordValue _ rest))
    have distribute :
        Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient
          => Topology.Mesh.RetracingWords.wordArea
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
          coefficient) (edge :: rest)) =
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
            coefficient => Topology.Mesh.RetracingWords.wordArea
            (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient) rest) +
          Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
            coefficient => Integration.Path.BoundaryRibbon.area
            (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient edge)
            (Topology.Surface.Sewing.SewingRetraction.wordValue
              (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
              coefficient) rest)) := by
      refine (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr
        split).trans ?_
      unfold Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
      ring1
    rw [distribute, ih]
    have crossed : Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
      coefficient =>
        Integration.Path.BoundaryRibbon.area
          (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
          coefficient edge)
          (Topology.Surface.Sewing.SewingRetraction.wordValue
            (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient) rest)) =
        first edge * Topology.Surface.Sewing.SewingRetraction.wordValue second rest -
          Topology.Surface.Sewing.SewingRetraction.wordValue first rest * second edge := by
      refine (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
        coefficient => ?_)).trans
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_area (first
          edge) (Topology.Surface.Sewing.SewingRetraction.wordValue first rest) (second edge)
          (Topology.Surface.Sewing.SewingRetraction.wordValue second rest))
      rw [Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.word_mix]
      rfl
    rw [crossed]
    change _ = Topology.Polygon.Stokes.edgeArea (⟨first edge, second edge⟩ : PrimitivePoint)
      (Integration.Path.PairedIncrementArea.total (rest.map (fun e => ⟨first e, second e⟩))) +
      Integration.Path.PairedIncrementArea.area (rest.map (fun e => ⟨first e, second e⟩))
    rw [paired_total]
    unfold Topology.Polygon.Stokes.edgeArea
    ring1

end Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization

namespace Purelib.Topology.Surface.Boundary.PolarizedWordArea.ClearGrid

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid (OwnedPuncturedMesh)

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Topology.Surface.Sewing.PrimitiveSewing (PrimitiveValues)
open Purelib.Topology.Mesh.RetracingWords (wordArea)
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint triangleEdgeOccurrences)
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Riemann.Meshes (FramedPuncturedGrid)
open Purelib.Riemann.Meshes.GridLiftedMesh (LiftedMesh)
open _root_.Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Readings (EdgeMagnitude)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues (edgeValuation)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity

variable {genus : Nat} {curve : Curves.Hyperelliptic.Basic.HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}

/-- Read the polarized area of actual supported mixed face readings as the paired increment area used in the
physical-boundary estimates. -/
theorem extract_wordArea_mixValues
    (leftValues rightValues : Fin owner.mesh.triangles.length → Topology.Surface.Sewing.PrimitiveSewing.PrimitiveValues
      3)
    (source : List (OrientedEdge owner.vertices.count))
    (supported : ∀ edge ∈ source, edge ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
      edge.reverse ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces) :
    Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Topology.Mesh.RetracingWords.wordArea
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh (EdgeMagnitude.mixValues
        (owner := owner) leftValues rightValues coefficient)) source) =
      Integration.Path.PairedIncrementArea.area (source.map (fun edge =>
        (⟨Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues edge,
          Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues edge⟩ :
            PrimitivePoint))) := by
  refine (Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract_congr (fun
    coefficient => ?_)).trans
    (BilinearPolarization.extract_wordArea_mix
      (Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh leftValues)
        (Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation owner.mesh rightValues) source)
  apply congrArg Integration.Path.IncrementArea.pathArea
  induction source with
  | nil => rfl
  | cons edge rest ih =>
    exact congrArg₂ List.cons
      (EdgeMagnitude.edgeValuation_mixValues (owner := owner) coefficient (supported edge List.mem_cons_self))
      (ih (fun next member => supported next (List.mem_cons_of_mem edge member)))

end Purelib.Topology.Surface.Boundary.PolarizedWordArea.ClearGrid

public section
namespace Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization

open Purelib.Data
open Purelib.Curves
open Purelib.Polynomial

/-- Polarizing an ordered sum of word areas gives the sum of the paired word areas.

The two edge-value functions supply the original increments of each retained
word. Structural recursion preserves every word and repeated signed occurrence;
the pointwise polarization law identifies each head area and retains the tail. -/
theorem extract_word_sum {Item : Type} {vertices : Nat}
    (first second : Topology.Polygon.Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical) (words : Item → List
      (Topology.Polygon.Stokes.OrientedEdge vertices)) (items : List Item) :
    Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
      Purelib.Polynomial.Geometry.Grid.CellBoundary.sumValues (fun item => Topology.Mesh.RetracingWords.wordArea
      (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
      (words item)) items) =
      Purelib.Polynomial.Geometry.Grid.CellBoundary.sumValues (fun item =>
        Purelib.Integration.Path.PairedIncrementArea.area ((words item).map (fun edge =>
        (⟨first edge, second edge⟩ : Topology.Polygon.Stokes.PrimitivePoint)))) items := by
  induction items with
  | nil =>
      change (⟨1 / 4, 0⟩ : Gaussian.Basic.Canonical) * (0 - 0 -
        Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.imaginary * (0 - 0)) = 0
      ring1
  | cons item rest ih =>
      have split : Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun
        coefficient => Polynomial.Geometry.Grid.CellBoundary.sumValues (fun item =>
        Topology.Mesh.RetracingWords.wordArea
        (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second coefficient)
        (words item)) (item :: rest)) =
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
            Topology.Mesh.RetracingWords.wordArea
            (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient) (words item)) +
          Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract (fun coefficient =>
            Polynomial.Geometry.Grid.CellBoundary.sumValues (fun item => Topology.Mesh.RetracingWords.wordArea
            (Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.mix first second
            coefficient) (words item)) rest) := by
        unfold Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity.BilinearPolarization.extract
        dsimp only [Polynomial.Geometry.Grid.CellBoundary.sumValues]
        ring1
      rw [split, extract_wordArea_mix, ih]
      rfl

end Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization
