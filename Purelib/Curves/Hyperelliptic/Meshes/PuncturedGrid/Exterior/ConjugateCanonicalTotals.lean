module
import Purelib.Data.List.Membership
import Purelib.Data.List.Flatten
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings
import Purelib.Data.Rat.Fraction.Compatibility
public import Purelib.Integration.Path.ConjugateIncrementComparison
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.GridLiftedBoundaryLoops
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Readings.PrimitiveAreaBounds
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCapTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary
import Mathlib.Algebra.Ring.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapTotals
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceComparison
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Vector.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Topology.Surface.Sewing.PrimitiveSewing
import Purelib.Tactic.Ring

public section

/-! The paid cap-total comparison uses the literal canonical exterior
valuation. Keep the cross-component polygon when splitting its flattened word. -/
section

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Data.List

open Purelib.Riemann.Normalization

open _root_.Purelib.Data.Gaussian.Basic (conj)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
    domains} {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other stage domains}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals

/-- The retained conjugate source-increment list equals the literal canonical exterior-edge valuation.

Original physical source identities transport both differential readings in the complete exterior order. -/
private theorem source_values (prepared :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential)
    (first : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh) (last :
      Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared lifted.mesh) :
    prepared.sources.map (fun source => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨source.increment first.values, source.increment last.values⟩ : Topology.Polygon.Stokes.PrimitivePoint)) =
      lifted.exteriorBoundaries.flatten.map (fun edge =>
        (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh first.values edge),
          Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh last.values edge⟩ :
            Topology.Polygon.Stokes.PrimitivePoint)) := by
  let values := fun edge => (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
    first.values edge),
    Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh last.values edge⟩ :
      Topology.Polygon.Stokes.PrimitivePoint)
  have entries : prepared.sources.map (fun source => Path.ConjugateIncrementComparison.conjugateFirst
      (⟨source.increment first.values, source.increment last.values⟩ : Topology.Polygon.Stokes.PrimitivePoint)) =
      prepared.sources.map (fun source => values (source.project lifted.mesh.triangulation.faces)) := by
    apply Data.List.Map.map_congr_left
    intro source member
    have exterior : source.project lifted.mesh.triangulation.faces ∈ lifted.exteriorBoundaries.flatten :=
      prepared.sources_project ▸ Data.List.Map.mem_map_of_mem member
    have physical : source.project lifted.mesh.triangulation.faces ∈ lifted.boundaryLoops.flatten := by
      change _ ∈ (lifted.exteriorBoundaries ++ _).flatten
      rw [Flatten.flatten_append]
      exact Membership.mem_append.mpr (Or.inl exterior)
    exact congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
      (congrArg Data.Gaussian.Basic.conj
        (Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary.canonical_physical_source source physical
        first.values).symm)
      (Hyperelliptic.Meshes.PuncturedGrid.CanonicalPhysicalBoundary.canonical_physical_source source physical
        last.values).symm
  exact entries.trans ((Map.map_map ..).symm.trans (congrArg (List.map values) prepared.sources_project))

/-- A one-entry paired-increment polygon has zero internal area. -/
private theorem area_single (point : Topology.Polygon.Stokes.PrimitivePoint) : Path.PairedIncrementArea.area [point] = 0
  := by
  change Topology.Polygon.Stokes.edgeArea point ⟨0, 0⟩ + 0 = 0
  simp only [Topology.Polygon.Stokes.edgeArea, mul_zero, zero_mul, sub_self, add_zero, -eq_self, -iff_self]
  rfl

/-- A two-entry paired-increment polygon has the oriented edge area of its two entries. -/
private theorem area_pair (first last : Topology.Polygon.Stokes.PrimitivePoint) : Path.PairedIncrementArea.area [first,
  last] = Topology.Polygon.Stokes.edgeArea first last := by
  rw [Path.PairedAreaBlocks.area_cons, Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals.area_single]
  change Topology.Polygon.Stokes.edgeArea first ⟨last.left + 0, last.right + 0⟩ + 0 = _
  simp only [add_zero, -eq_self, -iff_self]
  rfl

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest in
/-- Odd degree has one closed component; even degree has two. Thus the
only cross-component term is one edge area, paid by the retained totals. -/
theorem conjugate_component_cross_bound
    (values : Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count → Topology.Polygon.Stokes.PrimitivePoint)
    {bound : Fraction.Rational}
    (bounded : ∀ word ∈ lifted.exteriorBoundaries,
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded (Path.PairedIncrementArea.total (word.map values)) bound) :
    Data.Gaussian.Norm.Basic.normSq (Path.PairedIncrementArea.area ((lifted.exteriorBoundaries.map (fun word =>
      word.map values)).map
      Path.PairedIncrementArea.total)) ≤ 4 * bound^2 := by
  cases shape : curve.degreeShape with
  | odd degree =>
      simp only [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape, List.map_cons, List.map_nil,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals.area_single,
        Gaussian.Norm.Basic.normSq_zero, -eq_self, -iff_self]
      exact Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Fraction.Order.Arithmetic.sq_nonneg_direct bound)
  | even degree =>
      have first := bounded (lifted.edges.indexedEdges lifted.vertices base.bank.exterior 0)
        (by rw [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape]; exact List.mem_cons_self)
      have last := bounded (lifted.edges.indexedEdges lifted.vertices base.bank.exterior 1)
        (by rw [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape]; exact List.mem_cons_of_mem _ List.mem_cons_self)
      simp only [Meshes.LiftedPuncturedGrid.exteriorBoundaries, shape, List.map_cons, List.map_nil,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals.area_pair, -eq_self, -iff_self]
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical, pow_two,
        Fraction.Field.mul_assoc, -eq_self, -iff_self] using
        Readings.PrimitiveAreaBounds.PrimitivePoint.area_bound first last

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals

end

public section

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest

open Purelib.Curves
open Purelib.Data
open Purelib.Data.Rat
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib
open Purelib.Data.List

open Purelib.Riemann.Normalization

open _root_.Purelib.Data.Gaussian.Basic (conj)

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {stage : Nat} {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential stage
    domains} {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other stage domains}

section PairedCapRequest
variable {first :
  SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
  regular domains differential}
  {last :
    SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.AllSurfacePreparation
    regular domains other} {target : Fraction.Rational} {floor depth otherDepth readingIndex : Nat}
  {box : Rational.Box} {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential
    stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage box}
  {allocated : PairedCapRequest first last target floor}

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
namespace Evaluation

/-- Component areas and their cross-component polygon together are the exact
canonical source polygon controlled by the retained numerical request. -/
theorem conjugate_canonical_accurate
    (evaluated : Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh) :
    let values := fun edge => (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh
      firstReadings.values edge),
      Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh lastReadings.values edge⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)
    let components := lifted.exteriorBoundaries.map (fun word => word.map values)
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (components.map
      Path.PairedIncrementArea.area) + Path.PairedIncrementArea.area (components.map Path.PairedIncrementArea.total) -
      Path.PairedIncrementArea.area ((evaluated.left.samples.pairedValues evaluated.right.samples).map (fun pair =>
        Path.ConjugateIncrementComparison.conjugateFirst pair.2))) < target := by
  intro values components
  have bound := evaluated.conjugate_accurate firstReadings lastReadings
  have entries := Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals.source_values first firstReadings
    lastReadings
  have flat : lifted.exteriorBoundaries.flatten.map values = components.flatten := Flatten.map_flatten ..
  have regrouped := (congrArg Path.PairedIncrementArea.area (entries.trans flat)).trans
    (Path.PairedAreaBlocks.area_flatten components)
  exact (congrArg (fun source => Data.Gaussian.Norm.Basic.normSq (source -
    Path.PairedIncrementArea.area ((evaluated.left.samples.pairedValues evaluated.right.samples).map (fun pair =>
      Path.ConjugateIncrementComparison.conjugateFirst pair.2))))
      regrouped).symm.trans_lt bound

/-- Pay the cross-component term with the actual canonical period totals,
leaving the sum of separate component polygons used by the Newton estimate. -/
theorem conjugate_components_accurate
    (evaluated : Evaluation allocated
      sample otherSample shared otherShared depth otherDepth readingIndex)
    (firstReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings shared lifted.mesh)
      (lastReadings : Hyperelliptic.Meshes.PuncturedGrid.TrianglePrimitiveReadings.TriangleReadings otherShared
      lifted.mesh)
    {bound : Fraction.Rational}
    (bounded : ∀ word ∈ lifted.exteriorBoundaries,
      Readings.PrimitiveAreaBounds.PrimitivePoint.Bounded
        (Path.PairedIncrementArea.total (word.map (fun edge =>
          (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh firstReadings.values
            edge),
            Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh lastReadings.values edge⟩ :
              Topology.Polygon.Stokes.PrimitivePoint)))) bound) :
    let components := lifted.exteriorBoundaries.map (fun word => word.map (fun edge =>
      (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh firstReadings.values
        edge),
        Hyperelliptic.Meshes.PuncturedGrid.CanonicalEdgeValues.edgeValuation lifted.mesh lastReadings.values edge⟩ :
          Topology.Polygon.Stokes.PrimitivePoint)))
    Data.Gaussian.Norm.Basic.normSq (Data.Gaussian.Norm.Sum.Basic.gaussianSum (components.map
      Path.PairedIncrementArea.area) -
      Path.PairedIncrementArea.area ((evaluated.left.samples.pairedValues evaluated.right.samples).map (fun pair =>
        Path.ConjugateIncrementComparison.conjugateFirst pair.2))) <
        2 * (target + 4 * bound^2) := by
  intro components
  let source := Data.Gaussian.Norm.Sum.Basic.gaussianSum (components.map Path.PairedIncrementArea.area)
  let cross := Path.PairedIncrementArea.area (components.map Path.PairedIncrementArea.total)
  let capArea := Path.PairedIncrementArea.area ((evaluated.left.samples.pairedValues evaluated.right.samples).map (fun
    pair => Path.ConjugateIncrementComparison.conjugateFirst pair.2))
  have whole := evaluated.conjugate_canonical_accurate firstReadings lastReadings
  have crossBound :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.ConjugateCanonicalTotals.conjugate_component_cross_bound _ bounded
  have sumBound : Data.Gaussian.Norm.Basic.normSq (source + cross - capArea) + Data.Gaussian.Norm.Basic.normSq
    cross < target + 4 * bound^2 :=
    (Fraction.Order.Arithmetic.add_lt_add_right_direct whole _).trans_le
      (Fraction.Order.Arithmetic.add_le_add_direct (le_refl _) crossBound)
  have paid := (Gaussian.Norm.Bounds.normSq_sub_le_two (source + cross - capArea) cross).trans_lt
    (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct (by decide : (0 : Fraction.Rational) < 2) sumBound)
  exact (congrArg Data.Gaussian.Norm.Basic.normSq (show source - capArea = (source + cross - capArea) - cross by
    ring1)).trans_lt paid

end Evaluation

end PairedCapRequest
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapRequest
