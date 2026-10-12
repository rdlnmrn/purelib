module
import Purelib.Data.Gaussian.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.List.Map
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Arithmetic

import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.Primitives
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar
import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData
import Purelib.Integration.Path.PairedAreaBlocks
public import Purelib.Integration.Path.PairedIncrementArea
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Topology.Polygon.Stokes
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentSignedTotals
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.ReciprocalAreaComparison
import Purelib.Data.Gaussian.Field
import Purelib.Integration.Path.IncrementArea
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Meshes.PuncturedGridFaces
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.Tactic.Ring

public section

/-! The polygon of retained occurrence totals on one actual exterior component. -/
section

open Purelib.Curves
open Purelib.Data
open Purelib.Geometry
open Purelib.Integration
open Purelib.Riemann
open Purelib

open Purelib.Data.List

open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial Gaussian Coordinate)

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram
  (SurfacePreparation)

open Purelib.Riemann.Normalization
open Purelib.Topology.Polygon.Stokes (OrientedEdge PrimitivePoint edgeArea)

open _root_.Purelib.Data.Gaussian.Basic (conj)

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon

/-- Negate both coordinates of a paired primitive point. -/
private def negate (point : Topology.Polygon.Stokes.PrimitivePoint) : PrimitivePoint := ⟨-point.left, -point.right⟩

/-- The total of pointwise negated paired increments is the negation of their original total. -/
private theorem total_negate (points : List Topology.Polygon.Stokes.PrimitivePoint) :
    Path.PairedIncrementArea.total (points.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.negate) =
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.negate (Path.PairedIncrementArea.total points) :=
      by
  induction points with
  | nil => apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> exact (neg_zero).symm
  | cons head tail ih =>
      change (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.negate head).add
        (Path.PairedIncrementArea.total (tail.map
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.negate)) =
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.negate (head.add (Path.PairedIncrementArea.total
          tail))
      rw [ih]
      apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk <;> dsimp only
        [Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.negate,
        Topology.Polygon.Stokes.PrimitivePoint.add] <;> ring1

/-- Simultaneously negating every paired increment preserves the original polygon area. -/
private theorem area_negate (points : List Topology.Polygon.Stokes.PrimitivePoint) : Path.PairedIncrementArea.area
  (points.map Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.negate) = Path.PairedIncrementArea.area
  points := by
  induction points with
  | nil => rfl
  | cons head tail ih =>
      rw [List.map_cons, Path.PairedAreaBlocks.area_cons,
        Path.PairedAreaBlocks.area_cons, Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.total_negate,
          ih]
      simp only [Topology.Polygon.Stokes.edgeArea,
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.negate, -eq_self, -iff_self]
      ring1

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon

variable {genus : Nat} {curve : Hyperelliptic.Basic.HyperellipticCurve genus} {branches :
  Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree} {base : Meshes.FramedPuncturedGrid curve branches higher}
  {lifted : Meshes.LiftedPuncturedGrid base} {differential other : Hyperelliptic.Differentials.Basic.Differential genus}
  {collar : Hyperelliptic.Charts.Reciprocal.ReciprocalExteriorCollar.Data curve} {cap :
    Hyperelliptic.Charts.Reciprocal.ReciprocalInnerInverse.Data curve collar}
  {regular : Hyperelliptic.Charts.Reciprocal.Disk.RegularBounds.Data cap} {domains :
    Hyperelliptic.Meshes.PuncturedGrid.Face.DomainBanks.FaceDomainBank lifted.frames base.faces.regulars}
  {index depth readingIndex floor : Nat} {box : Rational.Box}
  {sample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap differential index box}
  {shared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank differential index domains}
    {localTarget localArea : Normalization.InverseRootPolynomial.Coordinate}

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon

/-- The primitive polynomial increment between the inverse endpoints of the original indexed edge. -/
private def edgeIncrement (value : Normalization.InverseRootPolynomial.Polynomial) (edge :
  Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count) : Gaussian :=
  value.eval (lifted.vertices.coordinate edge.finish)⁻¹ - value.eval (lifted.vertices.coordinate edge.start)⁻¹

/-- The retained occurrence-order increments agree with the original program's indexed edge increments under the exact
occurrence readback. -/
private theorem occurrence_values {program : Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram
  lifted differential}
    (prepared :
      SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram.SurfacePreparation
      regular domains program)
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor))
    (occurrences : values.map (fun value => value.entry.occurrence) = prepared.occurrences) (primitive :
      Normalization.InverseRootPolynomial.Polynomial) :
    values.map (fun value => primitive.eval value.entry.occurrence.finish⁻¹ - primitive.eval
      value.entry.occurrence.start⁻¹) =
      program.indexed.map (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement primitive) :=
        by
  have indices := (congrArg (List.map (fun occurrence => occurrence.placement.indexed)) occurrences).trans
    prepared.occurrences_eq
  have pointwise : values.map (fun value => primitive.eval value.entry.occurrence.finish⁻¹ - primitive.eval
    value.entry.occurrence.start⁻¹) =
      (values.map (fun value => value.entry.occurrence)).map (fun occurrence =>
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement primitive
        occurrence.placement.indexed) := by
    rw [Map.map_map]
    apply Data.List.Map.map_congr_left
    intro value _
    dsimp only [Function.comp_def, Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement]
    rw [value.entry.occurrence.placement.start_eq, value.entry.occurrence.placement.finish_eq]
  have readback := congrArg (List.map (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement
    primitive)) indices
  rw [Map.map_map] at readback
  exact pointwise.trans readback

/-- Pairing two mapped Gaussian lists with conjugation equals one map over their shared original list. -/
private theorem zip_maps {A : Type u} (values : List A) (first last : A → Normalization.InverseRootPolynomial.Gaussian)
  :
    List.zipWith (fun left right => (⟨conj left, right⟩ : Topology.Polygon.Stokes.PrimitivePoint)) (values.map first)
      (values.map last) =
      values.map (fun value => (⟨conj (first value), last value⟩ : Topology.Polygon.Stokes.PrimitivePoint)) := by
  induction values with
  | nil => rfl
  | cons head tail ih => exact congrArg (List.cons _) ih

/-- Applying one common root sign to both original primitive polynomials preserves their paired edge polygon area. -/
private theorem polygon_signed (left right : Normalization.InverseRootPolynomial.Polynomial) (flip : Bool) (edges : List
  (Topology.Polygon.Stokes.OrientedEdge lifted.vertices.count)) :
    Path.PairedIncrementArea.area (edges.map (fun edge => (⟨conj
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement (if flip then -left else left)
      edge),
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement (if flip then -right else right)
        edge⟩ : Topology.Polygon.Stokes.PrimitivePoint))) =
    Path.PairedIncrementArea.area (edges.map (fun edge => (⟨conj
      (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement left edge),
      Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement right edge⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))) := open Purelib.Polynomial in by
  cases flip with
  | false => rfl
  | true =>
      have points : edges.map (fun edge => (⟨conj
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement (-left) edge),
        Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement (-right) edge⟩ :
        Topology.Polygon.Stokes.PrimitivePoint)) =
          (edges.map (fun edge => (⟨conj (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement
            left edge), Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.edgeIncrement right edge⟩ :
            Topology.Polygon.Stokes.PrimitivePoint))).map negate := by
        rw [Map.map_map]
        apply Data.List.Map.map_congr_left
        intro edge _
        apply congrArg₂ Topology.Polygon.Stokes.PrimitivePoint.mk
        · change Data.Gaussian.Basic.conj ((-left).eval _ - (-left).eval _) = -Data.Gaussian.Basic.conj
            (left.eval _ - left.eval _)
          rw [Dense.Basic.DensePolynomial.eval_neg, Dense.Basic.DensePolynomial.eval_neg]
          have equal (a b : Normalization.InverseRootPolynomial.Gaussian) : -a - -b = -(a - b) := by ring1
          rw [equal]
          rfl
        · change (-right).eval _ - (-right).eval _ = -(right.eval _ - right.eval _)
          rw [Dense.Basic.DensePolynomial.eval_neg, Dense.Basic.DensePolynomial.eval_neg]
          ring1
      exact (congrArg Path.PairedIncrementArea.area points).trans
        (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.area_negate _)

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid
namespace ExteriorProgram
namespace SurfacePreparation

/-- Coarsen directly to the actual occurrence totals using their common root
sign. No internal parent polygon is asserted to vanish. -/
theorem conjugate_occurrence_polygon
    {sheet : Fin 2}
    (first :
      ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted
      differential sheet))
    (last :
      ExteriorProgram.SurfacePreparation
      regular domains (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted other
      sheet))
    {otherDepth otherReadingIndex otherFloor : Nat} {otherBox : Rational.Box}
    {otherSample : Hyperelliptic.Charts.Reciprocal.Cap.Primitives.Sample cap other index otherBox}
    {otherShared : Hyperelliptic.Meshes.PuncturedGrid.Face.PrimitiveData.FacePrimitiveBank other index domains}
      {otherTarget otherArea : Normalization.InverseRootPolynomial.Coordinate}
    (values : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular) sample shared depth readingIndex localTarget localArea floor))
    (otherValues : List (Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceRequests.AllSurfacePreparation.SampledEntry
      (regular := regular)
      otherSample otherShared otherDepth otherReadingIndex otherTarget otherArea otherFloor))
    (occurrences : values.map (fun value => value.entry.occurrence) = first.occurrences)
    (otherOccurrences : otherValues.map (fun value => value.entry.occurrence) = last.occurrences)
    (degree : curve.polynomial.natDegree = 2 * genus + 2) :
    Path.PairedIncrementArea.area (List.zipWith (fun left right => (⟨conj left, right⟩ :
      Topology.Polygon.Stokes.PrimitivePoint))
      (values.map (fun value => value.evaluated.right.total)) (otherValues.map (fun value =>
        value.evaluated.right.total))) =
    Path.PairedIncrementArea.area ((Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build
      lifted differential sheet).indexed.map (fun edge =>
      (⟨conj (sample.primitive.value.eval (lifted.vertices.coordinate edge.finish)⁻¹ -
        sample.primitive.value.eval (lifted.vertices.coordinate edge.start)⁻¹),
        otherSample.primitive.value.eval (lifted.vertices.coordinate edge.finish)⁻¹ -
        otherSample.primitive.value.eval (lifted.vertices.coordinate edge.start)⁻¹⟩ :
          Topology.Polygon.Stokes.PrimitivePoint))) := by
  obtain ⟨flip, firstTotals, lastTotals⟩ := first.paired_occurrence_totals last values otherValues occurrences
    otherOccurrences degree
  have firstEq := firstTotals.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.occurrence_values
    first values occurrences _)
  have lastEq := lastTotals.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.occurrence_values
    last otherValues otherOccurrences _)
  have paired := congrArg₂ (List.zipWith (fun left right => (⟨conj left, right⟩ :
    Topology.Polygon.Stokes.PrimitivePoint))) firstEq lastEq
  have grouped := paired.trans (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.zip_maps
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.PeriodPrograms.ExteriorProgram.build lifted differential sheet).indexed
    _ _)
  exact (congrArg Path.PairedIncrementArea.area grouped).trans
    (Hyperelliptic.Meshes.PuncturedGrid.Exterior.ComponentCapPolygon.polygon_signed sample.primitive.value
    otherSample.primitive.value flip _)

end SurfacePreparation
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Exterior.SurfaceOccurrences.LiftedPuncturedGrid.ExteriorProgram

end
