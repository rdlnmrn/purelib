module
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Data.Rat.Fraction
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Gaussian.Scale
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Integration.Energy.Polygon
import Purelib.Topology.Chain.PathBoundary

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapRefinement
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Geometry.Rectangle.Partition.PreparedBoxBoundary
import Purelib.Integration.Path.BoundaryRibbon
import Purelib.Integration.Path.Dyadic.RadialTriangles
import Purelib.Polynomial.Geometry.Grid.CellBoundary
import Purelib.Topology.Surface.Boundary.BoundaryCaps
import Purelib.Topology.Surface.Sewing.SewingProjection
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy
import Purelib.Integration.Path.Dyadic.DyadicBoundaryRibbon
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyRequest
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Geometry.Rectangle.Partition.PreparedBoxTriangulation
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Topology.PreparedSurfaceCoercivity
import Purelib.Riemann.Topology.PreparedSurfacePartitions
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Mesh.CoordinateTriangulation
import Purelib.Tactic.Ring

open Purelib.Geometry.Rectangle.Partition

open Purelib.Integration.Path.Dyadic

open Purelib.Polynomial.Geometry.Grid

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal

open Purelib.Curves

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Integration

open Purelib.Polynomial

open Purelib

@[expose] public section

/-!
# The actual inverse-arc boundary of the computed cap energy

The retained energy sample has the exact boundary of its radial parameter
mesh. Its outer side follows the inverse of the source edge, and its two
radial sides remain explicit until cancellation across the cap attachment.
-/

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Data.Gaussian.Basic.Canonical

section
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry
/-- The dyadic area of the retained value map along the radius from zero to the inverse source point. -/
def radialArea (values : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) (depth : Nat) (source :
  Gaussian.Basic.Canonical) : Gaussian :=
  DyadicBoundaryRibbon.dyadicArea (fun parameter => values (Gaussian.Scale.scale parameter source⁻¹)) depth
    0 1

/-- The dyadic area of the retained value map along the inverse of the original source segment. -/
def arcArea (values : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) (depth : Nat) (first last :
  Gaussian.Basic.Canonical) : Gaussian :=
  DyadicBoundaryRibbon.dyadicArea (fun parameter => values (source first last parameter)⁻¹) depth 0 1

end

/-- A constant Gaussian value map has zero dyadic area at every finite refinement depth. -/
private theorem constant_area (value : Gaussian.Basic.Canonical) (depth : Nat) (first last : Fraction.Rational) :
    DyadicBoundaryRibbon.dyadicArea (fun _ => value) depth first last = 0 := by
  induction depth generalizing first last with
  | zero => rw [DyadicBoundaryRibbon.dyadicArea_zero]; unfold Path.BoundaryRibbon.area; ring1
  | succ depth ih => rw [DyadicBoundaryRibbon.dyadicArea_succ, ih, ih]; ring1

open Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry in
/-- The actual radial rectangle boundary is the first radial area plus the inverse source-arc area minus the last radial
area.

All three terms use the same value map and refinement depth; the apex side is constant and contributes zero. -/
theorem rectangle_boundary (values : Gaussian.Basic.Canonical → Gaussian.Basic.Canonical) (depth : Nat) (first last :
  Gaussian.Basic.Canonical) :
    PreparedBoxBoundary.rectangleBoundary (fun parameter => Energy.Polygon.energyPrimitivePoint
      (values (point first last parameter)))
      depth RadialTriangles.unitBox =
        ReciprocalRadialGeometry.radialArea values depth first +
          ReciprocalRadialGeometry.arcArea values depth first last -
          ReciprocalRadialGeometry.radialArea values depth last := by
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
  unfold PreparedBoxBoundary.rectangleBoundary
  change PreparedBoxBoundary.horizontalBoundary _ depth 0 1 0 +
    PreparedBoxBoundary.verticalBoundary _ depth 0 1 1 -
    PreparedBoxBoundary.horizontalBoundary _ depth 0 1 1 -
      PreparedBoxBoundary.verticalBoundary _ depth 0 1 0 = _
  rw [DyadicBoundaryRibbon.horizontalBoundary_eq_dyadicArea,
    DyadicBoundaryRibbon.verticalBoundary_eq_dyadicArea,
    DyadicBoundaryRibbon.horizontalBoundary_eq_dyadicArea,
      DyadicBoundaryRibbon.verticalBoundary_eq_dyadicArea]
  rw [DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (bottom parameter)),
    DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values
      (ReciprocalRadialGeometry.outer first last parameter)),
    DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (top parameter)),
    DyadicBoundaryRibbon.dyadicArea_congr (fun parameter => congrArg values (apex parameter)),
      ReciprocalRadialGeometry.constant_area]
  change ReciprocalRadialGeometry.radialArea values depth first +
    ReciprocalRadialGeometry.arcArea values depth first last -
    ReciprocalRadialGeometry.radialArea values depth last - 0 = _
  ring1

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalRadialGeometry

namespace Purelib

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior

open Purelib.Topology.Polygon.Stokes

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment (vertex apex)

open Purelib.Riemann.Normalization
open Purelib.Topology.Surface.Boundary.BoundaryCaps

section
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment
/-- The radial contributions of one original fan telescope to its endpoint difference, leaving the reversed edge-arc
sum. -/
private theorem Riemann.Meshes.fan_radial_sum {count : Nat} (radial : Fin count → Gaussian)
    (arc : Fin count → Fin count → Gaussian) (apex : Fin count)
    {word : List (OrientedEdge count)} {first last : Fin count}
    (path : Topology.Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word first last) :
    CellBoundary.sumValues (fun triangle => radial triangle.second + arc triangle.second triangle.third -
      radial triangle.third)
      (Topology.Surface.Boundary.BoundaryCaps.fan apex word) =
    CellBoundary.sumValues (fun edge => arc edge.finish edge.start) word + radial last - radial first :=
      by
  induction path with
  | nil => change (0 : Gaussian) = 0 + _ - _; ring1
  | @cons edge tail last path ih =>
      change (radial edge.finish + arc edge.finish edge.start - radial edge.start) +
        CellBoundary.sumValues _ (Topology.Surface.Boundary.BoundaryCaps.fan apex tail) =
        arc edge.finish edge.start + CellBoundary.sumValues _ tail + radial last - radial edge.start
      rw [ih]
      ring1

/-- Closed original attachment words cancel all radial terms in the retained fans, leaving their actual reversed
edge-arc sums. -/
theorem Riemann.Meshes.fans_radial_sum {count target : Nat} (vertex : Fin count → Fin target)
    (radial : Fin target → Gaussian) (arc : Fin target → Fin target → Gaussian)
    (words : List (List (OrientedEdge count))) (apices : Fin words.length → Fin target)
    (closed : ∀ word ∈ words, ∃ anchor,
      Topology.Chain.PathBoundary.PathEndpoints OrientedEdge.start OrientedEdge.finish word anchor anchor) :
    CellBoundary.sumValues (fun triangle => radial triangle.second + arc triangle.second triangle.third -
      radial triangle.third)
      (Topology.Surface.Boundary.BoundaryCaps.fans vertex words apices) =
    CellBoundary.sumValues (fun word => CellBoundary.sumValues (fun edge => arc (vertex
      edge.finish) (vertex edge.start)) word) words := by
  induction words with
  | nil => rfl
  | cons word words ih =>
      obtain ⟨anchor, path⟩ := closed word List.mem_cons_self
      rw [Topology.Surface.Boundary.BoundaryCaps.fans, CellBoundary.sumValues_append, fan_radial_sum
        radial arc _ (Topology.Surface.Sewing.SewingProjection.pathEndpoints_map vertex path),
        ih _ (fun other member => closed other (List.mem_cons_of_mem _ member))]
      simp only [CellBoundary.sumValues_map, CellBoundary.sumValues,
        Topology.Surface.Sewing.VertexSewing.OrientedEdge.map]
      ring1

end

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : FramedPuncturedGrid curve branches higher}
  {lifted : LiftedPuncturedGrid base} {differential : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap :
    ReciprocalInnerInverse.Data curve collar}
  {regular : Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {prepared :

      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains differential} {attached :
    Caps.AllSurfacePreparation.CapAttachment prepared}
  {geometry : Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
    attached} {coarse : OrientedTriangle (lifted.vertices.count + attached.words.length)}
  {depth : Nat} {parameters : RadialTriangles.Parameters depth}
  {refinement : CapRefinement.Refinement geometry coarse parameters}
  {index : Nat} {box : Rational.Box} {sample : Cap.Primitives.Sample cap
    differential index box}
  {radius : Fraction.Rational}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment in
/-- Pointwise cache specifications identify the existing computed boundary
with the actual radial map; no equality of independently sampled values is
assumed. -/
theorem
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample.boundary_eq_rectangle
    (evaluated : CapEnergy.RegularPolynomialSample refinement sample radius)
      :
    evaluated.surface.boundaryArea = PreparedBoxBoundary.rectangleBoundary
      (fun point => Energy.Polygon.energyPrimitivePoint (sample.primitive.value.eval (geometry.point coarse point.re
        point.im)))
      depth RadialTriangles.unitBox := by
  rw [evaluated.surface_eq]
  change edgeListArea (fun vertex => Energy.Polygon.energyPrimitivePoint (evaluated.values vertex))
    parameters.mesh.mesh.triangulation.boundary = _
  calc
    _ = edgeListArea (fun vertex => Energy.Polygon.energyPrimitivePoint (sample.primitive.value.eval (geometry.point
      coarse
        (parameters.mesh.mesh.coordinate vertex).re (parameters.mesh.mesh.coordinate vertex).im)))
        parameters.mesh.mesh.triangulation.boundary := by
      generalize parameters.mesh.mesh.triangulation.boundary = edges
      induction edges with
      | nil => rfl
      | cons edge edges ih =>
          simp only [edgeListArea]
          rw [ih, evaluated.values_eq, evaluated.values_eq, refinement.coordinates_eq, refinement.coordinates_eq]
    _ = PreparedBoxBoundary.rectangleBoundary
        (fun point => Energy.Polygon.energyPrimitivePoint (sample.primitive.value.eval (geometry.point coarse point.re
          point.im)))
        depth parameters.mesh.partition.parent :=
          PreparedBoxBoundary.TriangulatedPartition.boundaryArea_eq_rectangleBoundary
          parameters.mesh
          (fun point => Energy.Polygon.energyPrimitivePoint (sample.primitive.value.eval (geometry.point coarse point.re
            point.im)))
    _ = _ := by rw [parameters.parent_eq]

/-- The actual sampled inverse arc and both radial contributions of this
retained cap face. Radial terms are paid by exact fan cancellation. -/
theorem
  Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularPolynomialSample.boundary_eq_arc
    (evaluated : CapEnergy.RegularPolynomialSample refinement sample radius)
      :
    evaluated.surface.boundaryArea =
      ReciprocalRadialGeometry.radialArea sample.primitive.value.eval depth
        (geometry.sourceCoordinates coarse.second) +
      ReciprocalRadialGeometry.arcArea sample.primitive.value.eval depth
        (geometry.sourceCoordinates coarse.second) (geometry.sourceCoordinates coarse.third) -
      ReciprocalRadialGeometry.radialArea sample.primitive.value.eval depth
        (geometry.sourceCoordinates coarse.third) := by
  rw [evaluated.boundary_eq_rectangle]
  exact ReciprocalRadialGeometry.rectangle_boundary sample.primitive.value.eval depth _
    _

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment in
/-- Closed attachment words cancel every sampled radial contribution. The
remaining paths are precisely inverse source edges with the cap orientation. -/
theorem Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapEnergy.RegularEnergy.area_eq_arcs
  (evaluated : CapEnergy.RegularEnergy geometry parameters sample radius) :
    evaluated.area = CellBoundary.sumValues (fun word => CellBoundary.sumValues (fun edge =>
      ReciprocalRadialGeometry.arcArea sample.primitive.value.eval depth
        (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start)) word) attached.words := by
  let radial (vertex : Fin (lifted.vertices.count + attached.words.length)) :=
    ReciprocalRadialGeometry.radialArea sample.primitive.value.eval depth
      (geometry.sourceCoordinates vertex)
  let arc (first last : Fin (lifted.vertices.count + attached.words.length)) :=
    ReciprocalRadialGeometry.arcArea sample.primitive.value.eval depth
      (geometry.sourceCoordinates first) (geometry.sourceCoordinates last)
  let contribution (triangle : OrientedTriangle (lifted.vertices.count + attached.words.length)) :=
    radial triangle.second + arc triangle.second triangle.third - radial triangle.third
  have aggregate (entries : List (CapEnergy.RegularFaceSample geometry
    parameters sample radius)) :
      Gaussian.Norm.Sum.Basic.gaussianSum (entries.map (fun entry => entry.evaluated.surface.boundaryArea)) =
        CellBoundary.sumValues contribution (entries.map (fun entry => entry.coarse)) := by
    induction entries with
    | nil => rfl
    | cons head tail ih =>
        change head.evaluated.surface.boundaryArea + _ = contribution head.coarse + _
        rw [head.evaluated.boundary_eq_arc, ih]
  rw [evaluated.area_eq, aggregate, evaluated.coarses_eq, attached.caps_eq]
  change CellBoundary.sumValues (fun triangle => radial triangle.second + arc triangle.second
    triangle.third - radial triangle.third)
    (Topology.Surface.Boundary.BoundaryCaps.fans vertex attached.words apex) = _
  rw [Riemann.Meshes.fans_radial_sum vertex radial arc attached.words apex attached.words_closed]
  apply CellBoundary.sumValues_congr
  intro word _
  apply CellBoundary.sumValues_congr
  intro edge _
  dsimp only [arc]
  rw [geometry.source_vertex_eq, geometry.source_vertex_eq]

/-- A requested regular cap controls the complete actual inverse-arc sum.
The boundary value is read from the already evaluated energy cache. -/
theorem Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapAccuracy.RequestedRegularEnergy.arcs_lower
  {target : Fraction.Rational} {minimum : Nat}
    (requested : CapAccuracy.RequestedRegularEnergy geometry sample target
      minimum) :
    -target < (CellBoundary.sumValues (fun word => CellBoundary.sumValues (fun edge =>
      ReciprocalRadialGeometry.arcArea sample.primitive.value.eval
        requested.request.depth
        (lifted.vertices.coordinate edge.finish) (lifted.vertices.coordinate edge.start)) word) attached.words).im / 4
          := by
  rw [← requested.evaluated.area_eq_arcs]
  exact requested.lower

end Purelib
