module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary
public import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Full paired increment paths on the forward attachment words. Cross-edge
terms are retained until the certified word endpoints cancel them. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear

open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)

open Purelib.Data.Gaussian.Basic.Canonical

/-- The full finite dyadic paired increment path along the inverse of the original source edge. -/
def arcIncrements (values : Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat) (first last
  : Gaussian.Basic.Canonical) : List PrimitivePoint :=
  Path.Dyadic.DyadicPairedPrimitivePaths.increments (fun parameter => values
    (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source first last parameter)⁻¹) depth 0 1

/-- The original affine source path starts at its first endpoint. -/
private theorem source_zero (first last : Gaussian.Basic.Canonical) :
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source first last 0 = first := by
  apply Gaussian.Basic.ext <;> simp only [Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source,
    Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
    Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1

/-- The original affine source path ends at its last endpoint. -/
private theorem source_one (first last : Gaussian.Basic.Canonical) :
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source first last 1 = last := by
  apply Gaussian.Basic.ext <;> simp only [Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.source,
    Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im,
    Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1

/-- The complete inverse-arc increment path totals the difference of the original paired endpoint values. -/
theorem arcIncrements_total (values : Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat)
  (first last : Gaussian.Basic.Canonical) :
    Path.PairedIncrementArea.total (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements
      values depth first last) = (values last⁻¹).sub (values first⁻¹) := by
  rw [Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements,
    Path.Dyadic.DyadicPairedPrimitivePaths.increments_total,
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.source_zero,
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.source_one]

/-- The complete inverse-arc increment area equals the literal arc area minus its original endpoint chord. -/
theorem arcIncrements_area (values : Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat)
  (first last : Gaussian.Basic.Canonical) :
    Path.PairedIncrementArea.area (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements
      values depth first last) =
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values depth first last -
        Topology.Polygon.Stokes.edgeArea (values first⁻¹) (values last⁻¹) := by
  rw [Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements,
    Path.Dyadic.DyadicPairedPrimitivePaths.increments_area,
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.source_zero,
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.source_one]
  rfl

/-- Concatenate the complete original edge increment paths at their separately retained depths. -/
def adaptiveWordIncrements {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Topology.Polygon.Stokes.OrientedEdge count → Nat) (word : List (Topology.Polygon.Stokes.OrientedEdge
      count)) : List PrimitivePoint :=
  (word.map (fun edge => Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements values (depth
    edge) (coordinates edge.start) (coordinates edge.finish))).flatten

/-- The complete adaptive word increments telescope to the retained path endpoint difference. -/
theorem adaptiveWordIncrements_total {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Topology.Polygon.Stokes.OrientedEdge count → Nat) {word : List (Topology.Polygon.Stokes.OrientedEdge
      count)} {first last : Fin count}
    (path : Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish word first last) :
    Path.PairedIncrementArea.total
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements coordinates values depth
      word) =
      (values (coordinates last)⁻¹).sub (values (coordinates first)⁻¹) := by
  induction path with
  | nil =>
      simp only [Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements, List.map_nil,
        List.flatten_nil,
        Path.PairedIncrementArea.total, Data.Gaussian.Norm.Sum.Basic.gaussianSum,
          Topology.Polygon.Stokes.PrimitivePoint.sub, Gaussian.Basic.sub_self, -eq_self, -iff_self]
      try rfl
  | @cons edge tail last path ih =>
      change Path.PairedIncrementArea.total
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements _ _ _ _ ++
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements _ _ _ _) = _
      rw [Path.PairedAreaBlocks.total_append,
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements_total, ih]
      apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> dsimp only
        [Topology.Polygon.Stokes.PrimitivePoint.add, Topology.Polygon.Stokes.PrimitivePoint.sub] <;> ring1

/-- The adaptive word's full area is the original arc sum minus its endpoint chord, including every cross-edge
contribution. -/
theorem adaptiveWordIncrements_area {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Topology.Polygon.Stokes.OrientedEdge count → Nat) {word : List (Topology.Polygon.Stokes.OrientedEdge
      count)} {first last : Fin count}
    (path : Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish word first last) :
    Path.PairedIncrementArea.area
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements coordinates values depth
      word) =
      Geometry.Grid.CellBoundary.sumValues (fun edge =>
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values (depth edge) (coordinates
        edge.start) (coordinates edge.finish)) word -
        Topology.Polygon.Stokes.edgeArea (values (coordinates first)⁻¹) (values (coordinates last)⁻¹) := by
  induction path with
  | nil => change (0 : Gaussian.Basic.Canonical) = 0 - _; unfold Topology.Polygon.Stokes.edgeArea; ring1
  | @cons edge tail last path ih =>
      change Path.PairedIncrementArea.area
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements _ _ _ _ ++
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements _ _ _ _) = _
      rw [Path.PairedAreaBlocks.area_append,
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements_area, ih,
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcIncrements_total,
          Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements_total coordinates
          values depth path]
      change (_ - _) + (_ - _) + _ = (_ + _) - _
      simp only [Topology.Polygon.Stokes.edgeArea, Topology.Polygon.Stokes.PrimitivePoint.sub]
      ring1

/-- Uniform attachment requests are the constant-depth case. The adaptive
identity above also applies when retained covers require different depths. -/
def wordIncrements {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values : Gaussian.Basic.Canonical
  → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Nat) (word : List (Topology.Polygon.Stokes.OrientedEdge count)) : List PrimitivePoint :=
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements coordinates values (fun _ =>
    depth) word

/-- The constant-depth original word increments total the retained path endpoint difference. -/
theorem wordIncrements_total {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Nat) {word : List (Topology.Polygon.Stokes.OrientedEdge count)} {first last : Fin count}
    (path : Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish word first last) :
    Path.PairedIncrementArea.total (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.wordIncrements
      coordinates values depth word) =
      (values (coordinates last)⁻¹).sub (values (coordinates first)⁻¹) :=
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements_total coordinates values (fun
    _ => depth) path

/-- The constant-depth word's full area is the original arc sum minus its endpoint chord. -/
theorem wordIncrements_area {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Nat) {word : List (Topology.Polygon.Stokes.OrientedEdge count)} {first last : Fin count}
    (path : Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish word first last) :
    Path.PairedIncrementArea.area (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.wordIncrements
      coordinates values depth word) =
      Geometry.Grid.CellBoundary.sumValues (fun edge =>
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values depth (coordinates edge.start)
        (coordinates edge.finish)) word -
        Topology.Polygon.Stokes.edgeArea (values (coordinates first)⁻¹) (values (coordinates last)⁻¹) :=
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements_area coordinates values (fun
    _ => depth) path

/-- Concatenate all original word increment paths with their retained per-edge depths. -/
def adaptiveWordsIncrements {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Topology.Polygon.Stokes.OrientedEdge count → Nat) (words : List (List (Topology.Polygon.Stokes.OrientedEdge
      count))) : List PrimitivePoint :=
  (words.map (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements coordinates
    values depth)).flatten

/-- Closed components have zero displacement, so concatenating them adds
their full areas without an unaccounted cross-component term. -/
theorem adaptiveWordsIncrements_readback {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Topology.Polygon.Stokes.OrientedEdge count → Nat) (words : List (List (Topology.Polygon.Stokes.OrientedEdge
      count)))
    (closed : ∀ word ∈ words, ∃ anchor,
      Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
        Topology.Polygon.Stokes.OrientedEdge.finish word anchor anchor) :
    Path.PairedIncrementArea.total
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements coordinates values
      depth words) = Topology.Polygon.Stokes.PrimitivePoint.zero ∧
    Path.PairedIncrementArea.area
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements coordinates values
      depth words) =
      Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge =>
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values (depth edge)
        (coordinates edge.start) (coordinates edge.finish)) word) words := by
  induction words with
  | nil => exact ⟨rfl, rfl⟩
  | cons word words ih =>
      obtain ⟨anchor, path⟩ := closed word List.mem_cons_self
      have tail := ih (fun other member => closed other (List.mem_cons_of_mem _ member))
      have zeroTotal : Path.PairedIncrementArea.total
        (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements coordinates values
        depth word) = PrimitivePoint.zero := by
        rw [Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements_total coordinates
          values depth path]
        simp only [Topology.Polygon.Stokes.PrimitivePoint.sub, Gaussian.Basic.sub_self,
          Topology.Polygon.Stokes.PrimitivePoint.zero, -eq_self, -iff_self]
        try rfl
      constructor
      · change Path.PairedIncrementArea.total
          (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements _ _ _ _ ++
          Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements _ _ _ _) = _
        rw [Path.PairedAreaBlocks.total_append, zeroTotal, tail.1]
        simp only [Topology.Polygon.Stokes.PrimitivePoint.add, Topology.Polygon.Stokes.PrimitivePoint.zero,
          Gaussian.Basic.add_zero, -eq_self, -iff_self]
        try rfl
      · change Path.PairedIncrementArea.area
          (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements _ _ _ _ ++
          Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements _ _ _ _) = _
        rw [Path.PairedAreaBlocks.area_append, zeroTotal, tail.1, tail.2,
          Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordIncrements_area coordinates
            values depth path]
        change (_ - _) + _ + _ = _ + _
        simp only [Topology.Polygon.Stokes.edgeArea, Topology.Polygon.Stokes.PrimitivePoint.zero, -eq_self, -iff_self]
        try rfl
        ring1

/-- Concatenate all original word increment paths at one shared depth. -/
def wordsIncrements {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Nat) (words : List (List (Topology.Polygon.Stokes.OrientedEdge count))) : List PrimitivePoint :=
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements coordinates values (fun _ =>
    depth) words

/-- The full constant-depth closed-word family has zero total displacement and exactly its original arc-sum area. -/
theorem wordsIncrements_readback {count : Nat} (coordinates : Fin count → Gaussian.Basic.Canonical) (values :
  Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint)
    (depth : Nat) (words : List (List (Topology.Polygon.Stokes.OrientedEdge count)))
    (closed : ∀ word ∈ words, ∃ anchor,
      Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
        Topology.Polygon.Stokes.OrientedEdge.finish word anchor anchor) :
    Path.PairedIncrementArea.total (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.wordsIncrements
      coordinates values depth words) = Topology.Polygon.Stokes.PrimitivePoint.zero ∧
    Path.PairedIncrementArea.area (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.wordsIncrements
      coordinates values depth words) =
      Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge =>
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values depth
        (coordinates edge.start) (coordinates edge.finish)) word) words :=
  Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements_readback coordinates values
    (fun _ => depth) words closed

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {index otherIndex : Nat} {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other otherIndex otherBox}
  {left : Charts.Reciprocal.Cap.EnergyBounds sample} {right :
    Charts.Reciprocal.Cap.EnergyBounds otherSample}
  {target : Fraction.Rational} {minimum : Nat} {request :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached left right target minimum}
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached}

set_option genInjectivity false in
/-- The actual attachment words with independently chosen edge depths.
The retained summary includes all cross-edge and cross-component terms. -/
structure AdaptivePath (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  prepared)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other otherIndex otherBox)
    (depth : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Nat) where
  /-- The full original attached paired increment path. -/ path : List Topology.Polygon.Stokes.PrimitivePoint
  /-- The path is exactly the adaptive concatenation on the original attachment words. -/ path_eq : path =
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements
    lifted.vertices.coordinate (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) depth attached.words
  /-- The cached summary of this same complete path. -/ summary : Path.PairedIncrementArea.Summary path
  /-- The original closed attachment words give zero total displacement. -/ closed : summary.totalValue =
    Topology.Polygon.Stokes.PrimitivePoint.zero
  /-- The cached full path area equals the actual forward inverse-arc sum. -/ area_eq : summary.areaValue =
    Geometry.Grid.CellBoundary.sumValues (fun word =>
    Geometry.Grid.CellBoundary.sumValues (fun edge =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
      (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) (depth edge)
      (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)) word) attached.words

constructive_injectivity AdaptivePath

/-- Cache the full original attached increment path and its summary at the supplied edge depths, certifying closure and
exact arc readback. -/
def adaptivePath (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  prepared)
    (sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box)
    (otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other otherIndex otherBox)
    (depth : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Nat) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.AdaptivePath attached sample
      otherSample depth := by
  let path := Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements
    lifted.vertices.coordinate (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) depth attached.words
  let summary := Path.PairedIncrementArea.Summary.build path
  have readback := Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.adaptiveWordsIncrements_readback
    lifted.vertices.coordinate (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) depth attached.words
      attached.words_closed
  exact ⟨path, rfl, summary, summary.total_eq.trans readback.1, summary.area_eq.trans readback.2⟩

namespace PairedFamilyRequest.Evaluation

set_option genInjectivity false in
/-- Executable full forward path, not a list of endpoint chords or a sum of
independently reset areas. The summary is computed once and then reused. -/
structure ForwardPath (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation request geometry) where
  /-- The complete retained forward attachment path. -/ path : List Topology.Polygon.Stokes.PrimitivePoint
  /-- The path is exactly the original attachment-word increment family at the shared cap depth. -/ path_eq : path =
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.wordsIncrements lifted.vertices.coordinate
    (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample)
    request.localRequest.depth attached.words
  /-- The cached summary of this same complete forward path. -/ summary : Path.PairedIncrementArea.Summary path
  /-- The retained forward path has zero total displacement. -/ closed : summary.totalValue =
    Topology.Polygon.Stokes.PrimitivePoint.zero
  /-- The cached forward area cancels the actual retained cap area exactly. -/ cancellation : summary.areaValue +
    evaluated.area = 0
  /-- The cached forward area satisfies the original cap target. -/ accurate : Data.Gaussian.Norm.Basic.normSq
    summary.areaValue < target

constructive_injectivity ForwardPath

/-- Reuse the original adaptive path cache at the shared cap depth and certify its exact cancellation and retained
accuracy. -/
def forwardPath (evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation
  request geometry) :
  ForwardPath
  evaluated := by
  let retained := attached.adaptivePath sample otherSample (fun _ => request.localRequest.depth)
  exact ⟨retained.path, retained.path_eq, retained.summary, retained.closed,
    (congrArg (fun value => value + evaluated.area) retained.area_eq).trans

        (PairedCapBoundary.CapAttachment.PairedFamilyRequest.Evaluation.forward_arcs_cancel
        evaluated),
    (congrArg Data.Gaussian.Norm.Basic.normSq retained.area_eq).trans_lt

        (PairedCapBoundary.CapAttachment.PairedFamilyRequest.Evaluation.forward_arcs_small
        evaluated)⟩

end PairedFamilyRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
