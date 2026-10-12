module
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Geometry.Rectangle.Partition.PreparedBoxPartitions
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Periods.ReciprocalCapBilinearBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCaps
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily
public import Purelib.Riemann.Periods.DyadicBilinearBoundaryRibbon
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib.Riemann

open Purelib

@[expose] public section

/-! Exact inverse-arc readback of the full paired cap family. The retained
closed attachment words cancel every radial side at the common depth. -/
namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Gaussian.Basic.Canonical

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry (source point outer)

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
/-- The dyadic paired area along the radius from zero to the original inverse source point. -/
def radialArea (values : Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat) (source :
  Gaussian.Basic.Canonical) : Gaussian :=
  Periods.DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => values (Gaussian.Scale.scale parameter source⁻¹))
    depth 0 1

/-- The dyadic paired area along the inverse of the original source segment. -/
def arcArea (values : Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat) (first last :
  Gaussian.Basic.Canonical) : Gaussian :=
  Periods.DyadicBilinearBoundaryRibbon.dyadicArea (fun parameter => values (source first last parameter)⁻¹) depth 0 1

end

/-- Reversing the parameter endpoints negates the complete finite dyadic paired area. -/
private theorem dyadic_reverse (values : Fraction.Rational → Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat)
  (first last : Fraction.Rational) :
    Periods.DyadicBilinearBoundaryRibbon.dyadicArea values depth last first =
      -Periods.DyadicBilinearBoundaryRibbon.dyadicArea values depth first last := by
  induction depth generalizing first last with
  | zero => exact Topology.Polygon.Stokes.edgeArea_reverse _ _
  | succ depth ih =>
      have middle : Rectangle.Partition.PreparedBoxPartitions.midpoint last first =
        Rectangle.Partition.PreparedBoxPartitions.midpoint first last := by
        have doubled (a b : Fraction.Rational) : Rectangle.Partition.PreparedBoxPartitions.midpoint a b * 2 = a + b :=
          by
          calc
            _ = a * 2 + ((b - a) / 2) * 2 := by unfold Rectangle.Partition.PreparedBoxPartitions.midpoint; ring1
            _ = _ := by rw [Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)]; ring1
        apply Fraction.Field.mul_right_cancel_of_ne (c := 2) (by decide)
        rw [doubled, doubled]
        ring1
      rw [Periods.DyadicBilinearBoundaryRibbon.dyadicArea_succ, middle, ih
        (Rectangle.Partition.PreparedBoxPartitions.midpoint first last) last, ih first
        (Rectangle.Partition.PreparedBoxPartitions.midpoint first last),
        Periods.DyadicBilinearBoundaryRibbon.dyadicArea_succ]
      ring1

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry in
/-- Reversal follows the entire inverse arc, not just its endpoint chord. -/
theorem arcArea_reverse (values : Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat)
  (first last : Gaussian.Basic.Canonical) :
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values depth last first =
      -Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values depth first last := by
  have reversed (parameter : Fraction.Rational) : source last first parameter = source first last (1 + (-1) * parameter)
    := by
    apply Gaussian.Basic.ext <;> simp only [source, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im,
      Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  unfold Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
  rw [Periods.DyadicBilinearBoundaryRibbon.dyadicArea_congr
    (fun parameter => congrArg (fun point : Gaussian.Basic.Canonical => values point⁻¹) (reversed parameter)),
    Periods.DyadicBilinearBoundaryRibbon.dyadicArea_affine
      (fun parameter => values (source first last parameter)⁻¹) 1 (-1)]
  have firstEndpoint : (1 + (-1) * 0 : Fraction.Rational) = 1 := by ring1
  have lastEndpoint : (1 + (-1) * 1 : Fraction.Rational) = 0 := by ring1
  rw [firstEndpoint, lastEndpoint]
  exact Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.dyadic_reverse _ _ _ _

/-- A constant paired primitive value has zero dyadic area at every finite depth. -/
private theorem constant_area (value : Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat) (first last :
  Fraction.Rational) :
    Periods.DyadicBilinearBoundaryRibbon.dyadicArea (fun _ => value) depth first last = 0 := by
  induction depth generalizing first last with
  | zero => rw [Periods.DyadicBilinearBoundaryRibbon.dyadicArea_zero]; unfold Topology.Polygon.Stokes.edgeArea; ring1
  | succ depth ih => rw [Periods.DyadicBilinearBoundaryRibbon.dyadicArea_succ, ih, ih]; ring1

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry in
/-- The paired radial rectangle boundary is the first radial area plus the actual inverse arc minus the last radial
area. -/
theorem rectangle_boundary (values : Gaussian.Basic.Canonical → Topology.Polygon.Stokes.PrimitivePoint) (depth : Nat)
  (first last : Gaussian.Basic.Canonical) :
    Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary (fun parameter => values (point first last parameter))
      depth Path.Dyadic.RadialTriangles.unitBox =
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.radialArea values depth first +
          Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values depth first last -
          Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.radialArea values depth last := by
  have sourceZero : source first last 0 = first := by
    apply Gaussian.Basic.ext <;> simp only [source, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  have sourceOne : source first last 1 = last := by
    apply Gaussian.Basic.ext <;> simp only [source, Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im] <;> ring1
  have bottom (parameter : Fraction.Rational) : point first last ⟨parameter, 0⟩ = Gaussian.Scale.scale parameter first⁻¹
    := by
    change Gaussian.Scale.scale parameter (source first last 0)⁻¹ = _
    rw [sourceZero]
  have top (parameter : Fraction.Rational) : point first last ⟨parameter, 1⟩ = Gaussian.Scale.scale parameter last⁻¹ :=
    by
    change Gaussian.Scale.scale parameter (source first last 1)⁻¹ = _
    rw [sourceOne]
  have apex (parameter : Fraction.Rational) : point first last ⟨0, parameter⟩ = 0 := by
    change Gaussian.Scale.scale 0 (source first last parameter)⁻¹ = _
    apply Gaussian.Basic.ext <;> simp only [Gaussian.Scale.scale_re, Gaussian.Scale.scale_im, Gaussian.Basic.zero_re,
      Gaussian.Basic.zero_im] <;> ring1
  unfold Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary
  change Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary _ depth 0 1 0 +
    Rectangle.Partition.PreparedBoxBoundary.verticalBoundary _ depth 0 1 1 -
    Rectangle.Partition.PreparedBoxBoundary.horizontalBoundary _ depth 0 1 1 -
      Rectangle.Partition.PreparedBoxBoundary.verticalBoundary _ depth 0 1 0 = _
  rw [Periods.DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_dyadicArea,
    Periods.DyadicBilinearBoundaryRibbon.verticalBoundary_eq_dyadicArea,
    Periods.DyadicBilinearBoundaryRibbon.horizontalBoundary_eq_dyadicArea,
      Periods.DyadicBilinearBoundaryRibbon.verticalBoundary_eq_dyadicArea]
  rw [Periods.DyadicBilinearBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (bottom parameter)),
    Periods.DyadicBilinearBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values
      (Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.outer first last parameter)),
    Periods.DyadicBilinearBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (top parameter)),
    Periods.DyadicBilinearBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (apex parameter)),
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.constant_area]
  change Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.radialArea values depth first +
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea values depth first last -
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.radialArea values depth last - 0 = _
  ring1

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary.CapAttachment

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
  (ReciprocalGeometry vertex apex)

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Rat.Fraction.Compatibility

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

namespace PairedBoundary
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
/-- The original fan's radial terms telescope to its endpoint difference, leaving the actual reversed arc sum. -/
private theorem fan_radial_sum {count : Nat} (radial : Fin count → Gaussian)
    (arc : Fin count → Fin count → Gaussian) (apex : Fin count)
    {word : List (Topology.Polygon.Stokes.OrientedEdge count)} {first last : Fin count}
    (path : Purelib.Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish word first last) :
    Geometry.Grid.CellBoundary.sumValues (fun triangle => radial triangle.second + arc triangle.second triangle.third -
      radial triangle.third)
      (Purelib.Topology.Surface.Boundary.BoundaryCaps.fan apex word) =
    Geometry.Grid.CellBoundary.sumValues (fun edge => arc edge.finish edge.start) word + radial last - radial first :=
      by
  induction path with
  | nil => change (0 : Gaussian) = 0 + _ - _; ring1
  | @cons edge tail last path ih =>
      change (radial edge.finish + arc edge.finish edge.start - radial edge.start) +
        Geometry.Grid.CellBoundary.sumValues _ (Topology.Surface.Boundary.BoundaryCaps.fan apex tail) =
        arc edge.finish edge.start + Geometry.Grid.CellBoundary.sumValues _ tail + radial last - radial edge.start
      rw [ih]
      ring1

/-- Closed original attachment paths cancel all radial contributions of the retained fan family. -/
private theorem fans_radial_sum {count target : Nat} (vertex : Fin count → Fin target)
    (radial : Fin target → Gaussian) (arc : Fin target → Fin target → Gaussian)
    (words : List (List (Topology.Polygon.Stokes.OrientedEdge count))) (apices : Fin words.length → Fin target)
    (closed : ∀ word ∈ words, ∃ anchor,
      Purelib.Topology.Chain.PathBoundary.PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
        Topology.Polygon.Stokes.OrientedEdge.finish word anchor anchor) :
    Geometry.Grid.CellBoundary.sumValues (fun triangle => radial triangle.second + arc triangle.second triangle.third -
      radial triangle.third)
      (Purelib.Topology.Surface.Boundary.BoundaryCaps.fans vertex words apices) =
    Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge => arc (vertex
      edge.finish) (vertex edge.start)) word) words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      obtain ⟨anchor, path⟩ := closed word List.mem_cons_self
      rw [Topology.Surface.Boundary.BoundaryCaps.fans, Geometry.Grid.CellBoundary.sumValues_append,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary.CapAttachment.PairedBoundary.fan_radial_sum radial
        arc _ (Topology.Surface.Sewing.SewingProjection.pathEndpoints_map vertex path),
        ih _ (fun other member => closed other (List.mem_cons_of_mem _ member))]
      simp only [Geometry.Grid.CellBoundary.sumValues_map, Geometry.Grid.CellBoundary.sumValues,
        Topology.Surface.Sewing.VertexSewing.OrientedEdge.map]
      ring1
end PairedBoundary

variable {geometry :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry attached}
  {coarse : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {depth : Nat} {parameters : Path.Dyadic.RadialTriangles.Parameters depth}
  {refinement : Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement.Refinement geometry coarse parameters} {left :
    Charts.Reciprocal.Cap.EnergyBounds sample} {right :
    Charts.Reciprocal.Cap.EnergyBounds otherSample}

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment in
/-- The exact retained vertex-value cache identifies the sampled paired area with its actual radial rectangle boundary.
-/
theorem PairedPolynomialSample.boundary_eq_rectangle (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedPolynomialSample refinement left right) :
    evaluated.area = Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary
      (fun point => Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (geometry.point coarse point.re
        point.im)) depth Path.Dyadic.RadialTriangles.unitBox := by
  rw [evaluated.area_eq]
  calc
    _ = Topology.Polygon.Stokes.edgeListArea (fun vertex => Periods.ReciprocalCapBilinearBounds.pairedValue sample
      otherSample (geometry.point coarse
        (parameters.mesh.mesh.coordinate vertex).re (parameters.mesh.mesh.coordinate vertex).im))
        parameters.mesh.mesh.triangulation.boundary := by
      generalize parameters.mesh.mesh.triangulation.boundary = edges
      induction edges with
      | nil => rfl
      | cons edge edges ih =>
          change Topology.Polygon.Stokes.edgeArea (evaluated.values edge.start) (evaluated.values edge.finish) + _ = _
          rw [ih, evaluated.values_eq, evaluated.values_eq, refinement.coordinates_eq, refinement.coordinates_eq]
          rfl
    _ = Rectangle.Partition.PreparedBoxBoundary.rectangleBoundary
        (fun point => Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (geometry.point coarse point.re
          point.im))
        depth parameters.mesh.partition.parent :=
          Rectangle.Partition.PreparedBoxBoundary.TriangulatedPartition.boundaryArea_eq_rectangleBoundary
          parameters.mesh
          (fun point => Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample (geometry.point coarse
            point.re point.im))
    _ = _ := by rw [parameters.parent_eq]

/-- The retained paired cap face area equals its actual inverse arc plus the two signed radial contributions. -/
theorem PairedPolynomialSample.boundary_eq_arc (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear.PairedPolynomialSample refinement left right) :
    evaluated.area =
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.radialArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) depth (geometry.sourceCoordinates
        coarse.second) +
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) depth
        (geometry.sourceCoordinates coarse.second) (geometry.sourceCoordinates coarse.third) -
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.radialArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) depth (geometry.sourceCoordinates
        coarse.third) := by
  rw
    [PairedPolynomialSample.boundary_eq_rectangle
    evaluated]
  exact Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.rectangle_boundary
    (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) depth _ _

namespace PairedFamilyRequest.Evaluation
variable {target : Fraction.Rational} {minimum : Nat} {request :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached left right target minimum}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment in
/-- The cached complete family area is the inverse-arc sum with the cap
orientation. Every radial term cancels by the actual closed attachment paths. -/
theorem area_eq_arcs (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation request geometry) :
    evaluated.area = Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) request.localRequest.depth
        (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start)) word) attached.words := by
  let radial (vertex : Fin (lifted.vertices.count + attached.words.length)) :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.radialArea
      (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) request.localRequest.depth
      (geometry.sourceCoordinates vertex)
  let arc (first last : Fin (lifted.vertices.count + attached.words.length)) :=
    Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
      (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) request.localRequest.depth
      (geometry.sourceCoordinates first) (geometry.sourceCoordinates last)
  let contribution (triangle : Topology.Polygon.Stokes.OrientedTriangle (lifted.vertices.count + attached.words.length))
    :=
    radial triangle.second + arc triangle.second triangle.third - radial triangle.third
  have aggregate (entries : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Entry
    request geometry)) :
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.sampled.area)) =
        Geometry.Grid.CellBoundary.sumValues contribution (entries.map (fun entry => entry.coarse)) := by
    induction entries with
    | nil => rfl
    | cons head tail ih =>
        change head.evaluated.sampled.area + _ = contribution head.coarse + _
        rw
          [PairedPolynomialSample.boundary_eq_arc
          head.evaluated.sampled, ih]
  rw [evaluated.area_eq, aggregate, evaluated.coarses_eq, attached.caps_eq]
  change Geometry.Grid.CellBoundary.sumValues (fun triangle => radial triangle.second + arc triangle.second
    triangle.third - radial triangle.third)
    (Topology.Surface.Boundary.BoundaryCaps.fans vertex attached.words apex) = _
  rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary.CapAttachment.PairedBoundary.fans_radial_sum vertex
    radial arc attached.words apex attached.words_closed]
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro word _
  apply Geometry.Grid.CellBoundary.sumValues_congr
  intro edge _
  dsimp only [arc]
  rw [geometry.source_vertex_eq, geometry.source_vertex_eq]

/-- The complete actual inverse-arc sum satisfies the retained family target after exact closed-fan cancellation. -/
theorem arcs_small (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation request geometry) :
    Data.Gaussian.Norm.Basic.normSq (Geometry.Grid.CellBoundary.sumValues (fun word =>
      Geometry.Grid.CellBoundary.sumValues (fun edge =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) request.localRequest.depth
        (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start)) word) attached.words) < target
          := by
  rw [←
    area_eq_arcs
    evaluated]
  exact evaluated.accurate

/-- The actual forward outer word cancels the cached cap interface exactly.
This is a polynomial-arc identity; source ribbon corrections remain separate. -/
theorem forward_arcs_cancel (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation request geometry) :
    Geometry.Grid.CellBoundary.sumValues (fun word => Geometry.Grid.CellBoundary.sumValues (fun edge =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) request.localRequest.depth
        (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)) word) attached.words +
      evaluated.area = 0 := by
  rw
    [area_eq_arcs
    evaluated]
  have word_cancel (word : List (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)) :
      Geometry.Grid.CellBoundary.sumValues (fun edge =>
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample)
        request.localRequest.depth (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish))
          word +
      Geometry.Grid.CellBoundary.sumValues (fun edge =>
        Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample)
        request.localRequest.depth (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start))
          word = 0 := by
    induction word with
    | nil => exact Gaussian.Basic.add_zero (0 : Gaussian)
    | cons edge tail ih =>
        change (_ + _) + (_ + _) = 0
        dsimp only
        rw [Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea_reverse _ _
          (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)]
        have cancel (a b c : Gaussian) : (a + b) + (-a + c) = b + c := by ring1
        rw [cancel]
        exact ih
  generalize attached.words = words
  induction words with
  | nil => exact Gaussian.Basic.add_zero (0 : Gaussian)
  | cons word words ih =>
      change (_ + _) + (_ + _) = 0
      have rearrange (a b c d : Gaussian) : (a + b) + (c + d) = (a + c) + (b + d) := by ring1
      rw [rearrange, word_cancel word, ih, Gaussian.Basic.add_zero]

/-- The forward original outer arcs satisfy the retained target because they cancel the same cached cap area. -/
theorem forward_arcs_small (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation request geometry) :
    Data.Gaussian.Norm.Basic.normSq (Geometry.Grid.CellBoundary.sumValues (fun word =>
      Geometry.Grid.CellBoundary.sumValues (fun edge =>
      Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry.Bilinear.arcArea
        (Periods.ReciprocalCapBilinearBounds.pairedValue sample otherSample) request.localRequest.depth
        (lifted.vertices.coordinate edge.start) (lifted.vertices.coordinate edge.finish)) word) attached.words) < target
          := by
  have equal := eq_neg_of_add_eq_zero_left
    (forward_arcs_cancel
    evaluated)
  rw [equal, Gaussian.Norm.Basic.normSq_neg]
  exact evaluated.accurate

end PairedFamilyRequest.Evaluation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapBoundary.CapAttachment
