module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Topology.Chain.PathBoundary
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Geometry.ClearPath

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.EnergyBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapGeometry
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Integration.Path.Dyadic.DyadicPairedPrimitivePaths
import Purelib.Integration.Path.IncrementArea
import Purelib.Integration.Path.PairedAreaBlocks
import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Integration.PreparedPairedParentCapReadback
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Cut.PrimitiveJumps
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.PairedParentRequest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.PrimitiveBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.CapBilinear
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.EnteredPaths
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.MeshEdgeContainment
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.Riemann.Paths.PreparedPathDecomposition
import Purelib.Riemann.Paths.PreparedPathParentCaches
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

/-! The retained endpoint chords form exactly the polygon of the unsigned
cap totals. Closed components contribute no hidden cross-component term. -/
namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedIncrementArea
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)

open Purelib.Topology.Chain.PathBoundary (PathEndpoints)

/-- The paired increment total along an endpoint-certified edge path is its endpoint difference. -/
private theorem edge_total {count : Nat} (values : Fin count → Topology.Polygon.Stokes.PrimitivePoint)
    {edges : List (Topology.Polygon.Stokes.OrientedEdge count)} {first last : Fin count}
    (path : PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start Topology.Polygon.Stokes.OrientedEdge.finish edges
      first last) :
    Path.PairedIncrementArea.total (edges.map (fun edge => (values edge.finish).sub (values edge.start))) =
      (values last).sub (values first) := by
  induction path with
  | nil => apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> exact (sub_self _).symm
  | cons path ih =>
      change (_ : Topology.Polygon.Stokes.PrimitivePoint).add (Path.PairedIncrementArea.total _) = _
      rw [ih]
      apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> dsimp only
        [Topology.Polygon.Stokes.PrimitivePoint.add, Topology.Polygon.Stokes.PrimitivePoint.sub] <;> ring1

/-- The translated paired trace area equals the ordered sum of original edge areas. -/
private theorem edge_trace {count : Nat} (values : Fin count → Topology.Polygon.Stokes.PrimitivePoint)
    {edges : List (Topology.Polygon.Stokes.OrientedEdge count)} {first last : Fin count}
    (path : PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start Topology.Polygon.Stokes.OrientedEdge.finish edges
      first last) :
    Path.PairedIncrementArea.traceArea (values first) (edges.map (fun edge => (values edge.finish).sub (values
      edge.start))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => Topology.Polygon.Stokes.edgeArea (values
        edge.start) (values edge.finish))) := by
  induction path with
  | nil => rfl
  | @cons edge tail last path ih =>
      have step : (values edge.start).add ((values edge.finish).sub (values edge.start)) = values edge.finish := by
        apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> dsimp only
          [Topology.Polygon.Stokes.PrimitivePoint.add, Topology.Polygon.Stokes.PrimitivePoint.sub] <;> ring1
      change Topology.Polygon.Stokes.edgeArea (values edge.start) ((values edge.start).add _) +
        Path.PairedIncrementArea.traceArea ((values edge.start).add _) _ = _
      rw [step, ih]
      rfl

/-- A closed endpoint-certified edge path has zero increment total and exactly its original polygon area. -/
theorem closed_edge_polygon {count : Nat} (values : Fin count → Topology.Polygon.Stokes.PrimitivePoint)
    {edges : List (Topology.Polygon.Stokes.OrientedEdge count)} {anchor : Fin count}
    (path : PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start Topology.Polygon.Stokes.OrientedEdge.finish edges
      anchor anchor) :
    Path.PairedIncrementArea.total (edges.map (fun edge => (values edge.finish).sub (values edge.start))) =
      Topology.Polygon.Stokes.PrimitivePoint.zero ∧
    Path.PairedIncrementArea.area (edges.map (fun edge => (values edge.finish).sub (values edge.start))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (edges.map (fun edge => Topology.Polygon.Stokes.edgeArea (values
        edge.start) (values edge.finish))) := by
  have totalEq := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedIncrementArea.edge_total values
    path
  have zero : (values anchor).sub (values anchor) = PrimitivePoint.zero := by
    apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> exact sub_self _
  rw [zero] at totalEq
  have trace := Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedIncrementArea.edge_trace values
    path
  rw [Path.PairedIncrementArea.traceArea_eq, totalEq] at trace
  have zeroArea : Topology.Polygon.Stokes.edgeArea (values anchor) Topology.Polygon.Stokes.PrimitivePoint.zero = 0 := by
    simp only [-eq_self, -iff_self, Topology.Polygon.Stokes.edgeArea, Topology.Polygon.Stokes.PrimitivePoint.zero,
      mul_zero, zero_mul, sub_self]
    rfl
  rw [zeroArea, add_zero] at trace
  exact ⟨totalEq, trace⟩

/-- Flattening closed edge words retains zero total and the sum of all original edge areas.

No cross-component polygon term remains because each original word closes separately. -/
theorem closed_words_polygon {count : Nat} (values : Fin count → Topology.Polygon.Stokes.PrimitivePoint)
    (words : List (List (Topology.Polygon.Stokes.OrientedEdge count)))
    (closed : ∀ word ∈ words, ∃ anchor, PathEndpoints Topology.Polygon.Stokes.OrientedEdge.start
      Topology.Polygon.Stokes.OrientedEdge.finish word anchor anchor) :
    Path.PairedIncrementArea.total (words.flatten.map (fun edge => (values edge.finish).sub (values edge.start))) =
      Topology.Polygon.Stokes.PrimitivePoint.zero ∧
    Path.PairedIncrementArea.area (words.flatten.map (fun edge => (values edge.finish).sub (values edge.start))) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (words.flatten.map (fun edge => Topology.Polygon.Stokes.edgeArea (values
        edge.start) (values edge.finish))) := by
  induction words with
  | nil => exact ⟨rfl, rfl⟩
  | cons word words ih =>
      obtain ⟨anchor, path⟩ := closed word List.mem_cons_self
      have head :=
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedIncrementArea.closed_edge_polygon values
        path
      have tail := ih (fun other member => closed other (List.mem_cons_of_mem word member))
      constructor
      · rw [List.flatten_cons, Data.List.Map.map_append, Path.PairedAreaBlocks.total_append, head.1, tail.1]
        apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> exact add_zero _
      · rw [List.flatten_cons, Data.List.Map.map_append, Path.PairedAreaBlocks.area_append, head.1, tail.1, head.2,
          tail.2,
          Data.List.Map.map_append, Path.IncrementArea.sum_append]
        have zeroArea : Topology.Polygon.Stokes.edgeArea Topology.Polygon.Stokes.PrimitivePoint.zero
          Topology.Polygon.Stokes.PrimitivePoint.zero = 0 := by
          simp only [-eq_self, -iff_self, Topology.Polygon.Stokes.edgeArea, Topology.Polygon.Stokes.PrimitivePoint.zero,
            zero_mul, sub_self]
          rfl
        rw [zeroArea, add_zero]

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedIncrementArea

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest

open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian

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
    regular domains differential} {target : Fraction.Rational} {minimum stage depth : Nat}
  {box otherBox : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential stage box}
  {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other stage otherBox}
  {request : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest prepared other target minimum}

/-- The retained cap path total is the exact two-polynomial endpoint difference on its original occurrence. -/
theorem Entry.cap_total (entry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry
  request sample otherSample depth) :
    entry.cap.totalValue =
      (⟨sample.primitive.value.eval entry.plan.occurrence.finish⁻¹,
        otherSample.primitive.value.eval entry.plan.occurrence.finish⁻¹⟩ : Topology.Polygon.Stokes.PrimitivePoint).sub
      ⟨sample.primitive.value.eval entry.plan.occurrence.start⁻¹,
        otherSample.primitive.value.eval entry.plan.occurrence.start⁻¹⟩ := by
  rw [entry.cap.total_eq,
    Integration.PreparedPairedParentCapReadback.Request.Evaluation.cap_paths entry.compared
      entry.plan.occurrence.cap.path.bank,
    Hyperelliptic.Charts.Reciprocal.PreparedPairedReciprocalArc.pairedUniformPaths_segment
      entry.plan.occurrence.compared.entered.cache entry.plan.occurrence.cap.path.bank,
    Path.Dyadic.DyadicPairedPrimitivePaths.increments_total, Geometry.ClearPath.ClearSegment.pointAt_zero,
      Geometry.ClearPath.ClearSegment.pointAt_one]

/-- The stored chords are exactly the closed polygon of stored cap totals.
This keeps the original occurrence order and both sheet components. -/
public theorem endpoint_readback (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample otherSample
  depth) (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared) :
    Path.PairedIncrementArea.total (evaluated.retained.map (fun entry => entry.cap.totalValue)) =
      Topology.Polygon.Stokes.PrimitivePoint.zero ∧
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry => entry.chord)) =
      Path.PairedIncrementArea.area (evaluated.retained.map (fun entry => entry.cap.totalValue)) := by
  let values := fun vertex => (⟨sample.primitive.value.eval (lifted.vertices.coordinate vertex)⁻¹,
    otherSample.primitive.value.eval (lifted.vertices.coordinate vertex)⁻¹⟩ : Topology.Polygon.Stokes.PrimitivePoint)
  have indexed : evaluated.retained.map (fun entry => entry.plan.occurrence.placement.indexed) = attached.words.flatten
    := by
    have occurrences := (congrArg (List.map
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcPlan.occurrence) evaluated.plans_eq).trans
      request.occurrences_eq
    have edges := congrArg (List.map (fun occurrence => occurrence.placement.indexed)) occurrences
    simp only [Data.List.Map.map_map, Function.comp_def] at edges
    exact edges.trans (prepared.indexed_eq.trans attached.words_flatten.symm)
  have polygon :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedIncrementArea.closed_words_polygon values
    attached.words attached.words_closed
  rw [← indexed, Data.List.Map.map_map, Data.List.Map.map_map] at polygon
  have totals : evaluated.retained.map (fun entry => entry.cap.totalValue) =
      evaluated.retained.map (fun entry => (values entry.plan.occurrence.placement.indexed.finish).sub
        (values entry.plan.occurrence.placement.indexed.start)) := by
    apply Data.List.Map.map_congr_left
    intro entry _
    rw [Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest.Entry.cap_total entry]
    dsimp only [values]
    rw [entry.plan.occurrence.placement.start_eq, entry.plan.occurrence.placement.finish_eq]
  have chords : evaluated.retained.map (fun entry => entry.chord) =
      evaluated.retained.map (fun entry => Topology.Polygon.Stokes.edgeArea (values
        entry.plan.occurrence.placement.indexed.start)
        (values entry.plan.occurrence.placement.indexed.finish)) := by
    apply Data.List.Map.map_congr_left
    intro entry _
    rw [entry.chord_eq]
    unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.chordValue
    dsimp only [values]
    rw [entry.plan.occurrence.placement.start_eq, entry.plan.occurrence.placement.finish_eq]
  rw [totals, chords]
  exact ⟨polygon.1, polygon.2.symm⟩

set_option genInjectivity false in
/-- The cached closed polygon of the actual retained cap totals.

Its exact path identity and area summary identify the original endpoint chord contribution. -/
structure EndpointPolygon (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample otherSample
  depth) where
  /-- The cached ordered polygon of retained cap totals. -/ path : List Topology.Polygon.Stokes.PrimitivePoint
  /-- The cached path is exactly the retained evaluation's cap-total list. -/ path_eq : path = evaluated.retained.map
    (fun entry => entry.cap.totalValue)
  /-- The retained total and area summary of that exact polygon. -/ summary : Path.PairedIncrementArea.Summary path
  /-- The cached endpoint polygon has zero total. -/ closed : summary.totalValue =
    Topology.Polygon.Stokes.PrimitivePoint.zero
  /-- The original retained chord sum equals the cached endpoint polygon area. -/ chords_eq :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry => entry.chord)) = summary.areaValue

constructive_injectivity EndpointPolygon

/-- Reuse the retained segment totals; the polygon is summarized once. -/
def Evaluation.endpointPolygon (evaluated :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample otherSample
  depth) (attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared) :
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest.EndpointPolygon evaluated := by
  let path := evaluated.retained.map (fun entry => entry.cap.totalValue)
  let summary := Path.PairedIncrementArea.Summary.build path
  have readback :=
    Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest.endpoint_readback evaluated
    attached
  exact ⟨path, rfl, summary, summary.total_eq.trans readback.1, readback.2.trans summary.area_eq.symm⟩

/-- Summing retained source areas with endpoint chords separates into the two original ordered sums. -/
private theorem sum_parts (retained : List
  (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Entry request sample otherSample depth))
  :
    Data.Gaussian.Norm.Sum.Basic.gaussianSum (retained.map (fun entry => entry.source.areaValue + entry.chord)) =
      Data.Gaussian.Norm.Sum.Basic.gaussianSum (retained.map (fun entry => entry.source.areaValue)) +
        Data.Gaussian.Norm.Sum.Basic.gaussianSum (retained.map (fun entry => entry.chord)) := by
  induction retained with
  | nil => change (0 : Gaussian) = 0 + 0; ring1
  | cons head tail ih =>
      change (_ + _) + _ = (_ + _) + (_ + _)
      rw [ih]
      ring1

variable {attached : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment prepared}
  {geometry : Hyperelliptic.Meshes.PuncturedGrid.Exterior.Caps.AllSurfacePreparation.CapAttachment.ReciprocalGeometry
  attached}
  {left : Charts.Reciprocal.Cap.EnergyBounds sample} {right :
    Charts.Reciprocal.Cap.EnergyBounds otherSample}
  {capTarget : Fraction.Rational} {capFloor : Nat}
  {capRequest : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest attached left right
    capTarget capFloor}
  {evaluated : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation request sample
    otherSample capRequest.localRequest.depth}

/-- The requested error bound for the retained source-area sum, cached endpoint polygon and actual cap-area evaluation.
-/
def EndpointPolygon.CapError (polygon :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest.EndpointPolygon evaluated)
    (caps : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation capRequest
      geometry) : Prop :=
  Data.Gaussian.Norm.Basic.normSq
    (Data.Gaussian.Norm.Sum.Basic.gaussianSum (evaluated.retained.map (fun entry => entry.source.areaValue)) +
      polygon.summary.areaValue + caps.area) < target

/-- The endpoint contribution is now the actual closed cap-total polygon,
ready for the shared-boundary total comparison, not an unexplained chord sum. -/
theorem EndpointPolygon.cap_error (polygon :
  Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest.EndpointPolygon evaluated)
    (caps : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedCapFamily.PairedFamilyRequest.Evaluation capRequest
      geometry) : polygon.CapError caps := by
  have bound := evaluated.cap_error caps
  unfold Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedArcFamily.PairedArcRequest.Evaluation.CapError at bound
  rw [sum_parts, polygon.chords_eq] at bound
  exact bound

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest.EndpointPolygon

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PairedChordPolygon.PairedArcRequest.EndpointPolygon
