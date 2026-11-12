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

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Paired.BilinearIdentity
open Purelib.Integration.Path

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
    (first second : OrientedEdge vertices → Canonical) (word : List (OrientedEdge vertices)) :
    PairedIncrementArea.total (word.map (fun edge =>
      (⟨first edge, second edge⟩ : PrimitivePoint))) =
      ⟨wordValue first word, wordValue second word⟩ := by
  induction word with
  | nil => rfl
  | cons edge rest ih =>
    change (⟨first edge, second edge⟩ : PrimitivePoint).add
      (PairedIncrementArea.total (rest.map (fun e => ⟨first e, second e⟩))) = _
    rw [ih]
    rfl

/-- This is an equality of full areas, with no closure or vanishing-total assumption. Its right side is the increment
area retained by Newton cut boundary comparisons. -/
theorem extract_wordArea_mix {vertices : Nat}
    (first second : OrientedEdge vertices → Canonical) (word : List (OrientedEdge vertices)) :
    BilinearPolarization.extract (fun coefficient =>
      wordArea
      (BilinearPolarization.mix first second
      coefficient) word) =
      PairedIncrementArea.area (word.map (fun edge =>
        (⟨first edge, second edge⟩ : PrimitivePoint))) := by
  induction word with
  | nil =>
    change (⟨1 / 4, 0⟩ : Canonical) * (0 - 0 -
      BilinearPolarization.imaginary * (0 - 0)) = 0
    ring1
  | cons edge rest ih =>
    have split (coefficient : Canonical) :
        wordArea
          (BilinearPolarization.mix first second
          coefficient) (edge :: rest) =
          wordArea
            (BilinearPolarization.mix first second
            coefficient) rest +
          BoundaryRibbon.area
            (BilinearPolarization.mix first second
            coefficient edge)
            (wordValue
              (BilinearPolarization.mix first second
              coefficient) rest) := by
      exact (IncrementArea.pathArea_cons _ _).trans
        (congrArg (fun total => wordArea
          (BilinearPolarization.mix first second
          coefficient) rest +
          BoundaryRibbon.area
            (BilinearPolarization.mix first second
            coefficient edge) total)
          (Mesh.RetracingWords.sum_map_eq_wordValue _ rest))
    have distribute :
        BilinearPolarization.extract (fun coefficient
          => wordArea
          (BilinearPolarization.mix first second
          coefficient) (edge :: rest)) =
          BilinearPolarization.extract (fun
            coefficient => wordArea
            (BilinearPolarization.mix first second
            coefficient) rest) +
          BilinearPolarization.extract (fun
            coefficient => BoundaryRibbon.area
            (BilinearPolarization.mix first second
            coefficient edge)
            (wordValue
              (BilinearPolarization.mix first second
              coefficient) rest)) := by
      refine (BilinearPolarization.extract_congr
        split).trans ?_
      unfold BilinearPolarization.extract
      ring1
    rw [distribute, ih]
    have crossed : BilinearPolarization.extract (fun
      coefficient =>
        BoundaryRibbon.area
          (BilinearPolarization.mix first second
          coefficient edge)
          (wordValue
            (BilinearPolarization.mix first second
            coefficient) rest)) =
        first edge * wordValue second rest -
          wordValue first rest * second edge := by
      refine (BilinearPolarization.extract_congr (fun
        coefficient => ?_)).trans
        (BilinearPolarization.extract_area (first
          edge) (wordValue first rest) (second edge)
          (wordValue second rest))
      rw [BilinearPolarization.word_mix]
      rfl
    rw [crossed]
    change _ = Polygon.Stokes.edgeArea (⟨first edge, second edge⟩ : PrimitivePoint)
      (PairedIncrementArea.total (rest.map (fun e => ⟨first e, second e⟩))) +
      PairedIncrementArea.area (rest.map (fun e => ⟨first e, second e⟩))
    rw [paired_total]
    unfold Polygon.Stokes.edgeArea
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

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {owner : OwnedPuncturedMesh curve}

/-- Read the polarized area of actual supported mixed face readings as the paired increment area used in the
physical-boundary estimates. -/
theorem extract_wordArea_mixValues
    (leftValues rightValues : Fin owner.mesh.triangles.length → PrimitiveValues
      3)
    (source : List (OrientedEdge owner.vertices.count))
    (supported : ∀ edge ∈ source, edge ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces ∨
      edge.reverse ∈ triangleEdgeOccurrences owner.mesh.triangulation.faces) :
    BilinearPolarization.extract (fun coefficient =>
      wordArea
      (edgeValuation owner.mesh (EdgeMagnitude.mixValues
        (owner := owner) leftValues rightValues coefficient)) source) =
      PairedIncrementArea.area (source.map (fun edge =>
        (⟨edgeValuation owner.mesh leftValues edge,
          edgeValuation owner.mesh rightValues edge⟩ :
            PrimitivePoint))) := by
  refine (BilinearPolarization.extract_congr (fun
    coefficient => ?_)).trans
    (BilinearPolarization.extract_wordArea_mix
      (edgeValuation owner.mesh leftValues)
        (edgeValuation owner.mesh rightValues) source)
  apply congrArg IncrementArea.pathArea
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
    (first second : Polygon.Stokes.OrientedEdge vertices → Gaussian.Basic.Canonical) (words : Item → List
      (Polygon.Stokes.OrientedEdge vertices)) (items : List Item) :
    BilinearPolarization.extract (fun coefficient =>
      Geometry.Grid.CellBoundary.sumValues (fun item => Mesh.RetracingWords.wordArea
      (BilinearPolarization.mix first second coefficient)
      (words item)) items) =
      Geometry.Grid.CellBoundary.sumValues (fun item =>
        PairedIncrementArea.area ((words item).map (fun edge =>
        (⟨first edge, second edge⟩ : Polygon.Stokes.PrimitivePoint)))) items := by
  induction items with
  | nil =>
      change (⟨1 / 4, 0⟩ : Gaussian.Basic.Canonical) * (0 - 0 -
        BilinearPolarization.imaginary * (0 - 0)) = 0
      ring1
  | cons item rest ih =>
      have split : BilinearPolarization.extract (fun
        coefficient => Geometry.Grid.CellBoundary.sumValues (fun item =>
        Mesh.RetracingWords.wordArea
        (BilinearPolarization.mix first second coefficient)
        (words item)) (item :: rest)) =
          BilinearPolarization.extract (fun coefficient =>
            Mesh.RetracingWords.wordArea
            (BilinearPolarization.mix first second
            coefficient) (words item)) +
          BilinearPolarization.extract (fun coefficient =>
            Geometry.Grid.CellBoundary.sumValues (fun item => Mesh.RetracingWords.wordArea
            (BilinearPolarization.mix first second
            coefficient) (words item)) rest) := by
        unfold BilinearPolarization.extract
        dsimp only [Geometry.Grid.CellBoundary.sumValues]
        ring1
      rw [split, extract_wordArea_mix, ih]
      rfl

end Purelib.Topology.Surface.Boundary.PolarizedWordArea.BilinearPolarization
