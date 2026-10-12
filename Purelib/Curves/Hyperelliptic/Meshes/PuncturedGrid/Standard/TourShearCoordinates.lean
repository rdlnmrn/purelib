module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Gaussian.Basic
import Purelib.Algebra.FiniteSum.Fin
import Purelib.Algebra.Ring.IntCast
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Data.Vector.Basic

import Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration
import Purelib.Curves.Hyperelliptic.Branches.BranchIsolation
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection
import Purelib.Riemann.Meshes.FramedPuncturedGrid
import Purelib.Riemann.Meshes.LiftedPuncturedGrid
import Purelib.Topology.Polygon.Stokes
import Purelib.Topology.Surface.Boundary.BoundaryCoordinates
import Purelib.Topology.Surface.Cut.IntegralPairing
import Purelib.Topology.Surface.Cut.Spanning
import Purelib.Topology.Surface.Sewing.CutIntersection
import Purelib.Topology.Surface.Sewing.SewingRetraction
import Purelib.Topology.Surface.Sewing.VertexSewing
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations
import Init.Data.Bool
import Init.Data.Int.Basic
import Init.Prelude
import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Ring.Defs
import Mathlib.Algebra.Ring.Int.Defs
import Mathlib.Data.Int.Cast.Defs
import Purelib.Curves.Hyperelliptic.Branches.BranchCellBank
import Purelib.Curves.Hyperelliptic.Branches.Cuts
import Purelib.Curves.Hyperelliptic.Branches.FramedBranchCellBank
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.BoundaryWord
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Cut.Forest
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCoordinates
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourFaces
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourRetraction
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourSpanning
import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.WalkFaceAssignments
import Purelib.Data.Gaussian.Field
import Purelib.Data.Vector.Dependent
import Purelib.Geometry.Rational.Box.Sample
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Geometry.Grid.Walks
import Purelib.Riemann.Integration.PreparedOwnerClosedBridges
import Purelib.Riemann.Meshes.GridLiftedMesh
import Purelib.Riemann.Readings.PreparedBoundaryClosure
import Purelib.Riemann.Readings.PreparedBoundaryGluing
import Purelib.Riemann.Topology.PreparedCycleModels
import Purelib.RootIsolation.SquareRoot.Grid.LiftedVertices
import Purelib.RootIsolation.SquareRoot.Grid.Walk.Combinations
import Purelib.RootIsolation.State.WindingOne.Basic
import Purelib.Topology.Surface.Cut.BoundaryWord
import Purelib.Topology.Surface.Cut.Patch
import Purelib.Topology.Surface.Sewing.SewingConnected
import Purelib.Topology.Surface.Sewing.SewingTree
import Purelib.Tactic.Ring
open Purelib.Algebra.Ring

open Purelib

open Purelib.Algebra

open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours

open Purelib.Topology.Polygon

open Purelib.Topology.Surface.Boundary.BoundaryCoordinates

open Purelib.Topology.Surface.Cut.Spanning.CutBoundaryWord

open Purelib.Topology.Surface.Sewing

open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing

open Purelib.Topology.Surface.Sewing.VertexSewing

@[expose] public section

/-!
# Cached cut coordinates of the actual signed B-tour corrections

Combine the retained integer rows and their integral spans without routing
the longer corrected paths again. The valuation theorem identifies the
result with those actual paths, retaining the original signed face terms.
Intersection readback uses the same cached spans as the original tour table.
-/

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Data.Gaussian.Basic renaming Canonical -> Gaussian
open Purelib.Riemann.Meshes (FramedPuncturedGrid LiftedPuncturedGrid)
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourIntersection (IntersectionBank)
open Purelib.Topology.Surface.Sewing.CutIntersection.CutBoundaryWord.IntegralPairing.SpanningCoordinates
open _root_.Purelib.Topology.Surface.Cut.IntegralPairing renaming CutBoundaryWord -> IntegralPairing
open Purelib.Topology.Polygon.Stokes (OrientedEdge)
open Purelib.Topology.Surface.Boundary.BoundaryCoordinates (WordCoordinates)
open Purelib.Topology.Surface.Sewing.SewingRetraction (faceValue)
open Purelib.Data.Vector.Basic (vectorOfFn vectorOfFn_apply)
open Purelib.Algebra.FiniteSum.Fin (sumFin sumFin_congr sumFin_add sumFin_mul_left sumFin_mul_right sumFin_swap
  sumFin_succ)

/-- Evaluating a finite weighted row shear separates the original row value from the weighted row values. -/
public theorem sum_shear {K : Type} [CommRing K] {size count : Nat}
    (original : Fin size → K) (weights : Fin count → K) (rows : Fin count → Fin size → K)
    (values : Fin size → K) :
    sumFin (fun column => (original column + sumFin (fun index => weights index * rows index column)) * values column) =
      sumFin (fun column => original column * values column) +
        sumFin (fun index => weights index * sumFin (fun column => rows index column * values column)) := by
  calc
    _ = sumFin (fun column => original column * values column) +
        sumFin (fun column => sumFin (fun index => weights index * rows index column * values column)) := by
      rw [← FiniteSum.Fin.sumFin_add]
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [FiniteSum.Fin.sumFin_mul_right, add_mul]
    _ = sumFin (fun column => original column * values column) +
        sumFin (fun index => sumFin (fun column => weights index * rows index column * values column)) := by
      rw [FiniteSum.Fin.sumFin_swap (fun column index => weights index * rows index column * values column)]
    _ = _ := by
      congr 1
      apply FiniteSum.Fin.sumFin_congr
      intro index
      rw [← FiniteSum.Fin.sumFin_mul_left]
      exact FiniteSum.Fin.sumFin_congr (fun _ => _root_.mul_assoc _ _ _)

/-- Casting the actual finite integer sum to Gaussian rationals preserves its indexed summands. -/
private theorem cast_sum {count : Nat} (values : Fin count → Int) :
    ((sumFin values : Int) : Data.Gaussian.Basic.Canonical) = sumFin (fun index => (values index :
      Data.Gaussian.Basic.Canonical)) := by
  induction count with
  | zero => exact IntCast.cast_zero
  | succ count ih => rw [FiniteSum.Fin.sumFin_succ, FiniteSum.Fin.sumFin_succ, IntCast.add, ih]

/-- The Gaussian valuation of an integer row shear is the original valuation plus the weighted source-row valuations. -/
public theorem combine_shear {size count : Nat} (original : Fin size → Int)
    (weights : Fin count → Int) (rows : Fin count → Fin size → Int) (values : Fin size → Data.Gaussian.Basic.Canonical)
      :
    WordCoordinates.combine (fun column => original column + sumFin (fun index => weights index * rows index column))
      values =
      WordCoordinates.combine original values +
        sumFin (fun index => (weights index : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine (rows index)
          values) := by
  calc
    _ = sumFin (fun column => ((original column : Data.Gaussian.Basic.Canonical) +
        sumFin (fun index => (weights index : Data.Gaussian.Basic.Canonical) * (rows index column :
          Data.Gaussian.Basic.Canonical))) * values column) := by
      apply FiniteSum.Fin.sumFin_congr
      intro column
      rw [IntCast.add,
        cast_sum]
      congr 2
      exact FiniteSum.Fin.sumFin_congr (fun _ => Ring.IntCast.intCast_mul _ _)
    _ = _ :=
      sum_shear _ _ _
      _

variable {genus : Nat} {curve : HyperellipticCurve genus} {branches :
  Purelib.Curves.Hyperelliptic.Branches.BranchIsolation.Data curve}
  {higher : 1 < curve.polynomial.natDegree}
  {base : FramedPuncturedGrid curve
    (Purelib.Curves.Hyperelliptic.Branches.BranchConfiguration.configurationOfData curve branches).branches higher}
  {lifted : LiftedPuncturedGrid base} {integral :
    Topology.Surface.Cut.IntegralPairing.CutBoundaryWord lifted.cutBoundaryWord}
  {bank : IntersectionBank lifted integral}
    {target : Fin genus}
  {weights : Data.Vector Int genus}

namespace BShear

set_option genInjectivity false in
/-- The cached complete cut coordinates and integral span of an actual signed B-tour correction.

The original target row and weighted A rows retain their exact coefficient and signed face-correction readbacks. -/
structure CutCoordinates (shear : IntersectionBank.BShear bank target weights) where
  /-- The cached full integer row on the original retained cut alphabet. -/ row : Data.Vector Int
    lifted.cutBoundaryWord.alphabet.count
  /-- Each cached coordinate is the original B coordinate plus the weighted original A coordinates. -/ row_eq : ∀
    column, row column = (bank.rows.get target).coordinates.b.totals column +
    sumFin (fun index => weights index * (bank.rows.get index).coordinates.a.totals column)
  /-- The retained integral spanning certificate on this exact cached row. -/ span : IntegralPairing.SpanningCoordinates
    integral row
  /-- The span coefficients are exactly the original B coefficients plus the weighted original A coefficients. -/
    coefficients_eq : ∀ column, span.coefficients column = (bank.rows.get target).span.b.coefficients column +
    sumFin (fun index => weights index * (bank.rows.get index).span.a.coefficients column)
  /-- Every antisymmetric valuation of the actual corrected path agrees with the cached cut row and original signed face
    terms. -/ value_eq : ∀ (valuation : Stokes.OrientedEdge lifted.vertices.count → Data.Gaussian.Basic.Canonical),
    (∀ edge, valuation edge.reverse = -valuation edge) →
    shear.corrected.value valuation =
      WordCoordinates.combine row (fun column => valuation
        (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels (lifted.cutBoundaryWord.alphabet.generators column)))
          +
      (SewingRetraction.faceValue lifted.mesh.triangulation.faces valuation (bank.rows.get
        target).coordinates.routes.b.correction +
        sumFin (fun index => (weights index : Data.Gaussian.Basic.Canonical) *
          SewingRetraction.faceValue lifted.mesh.triangulation.faces valuation (bank.rows.get
            index).coordinates.routes.a.correction))

constructive_injectivity CutCoordinates

/-- Combine the original retained coordinate and spanning caches for the actual signed B-tour correction. -/
def cutCoordinates (shear : IntersectionBank.BShear bank target weights) :
  CutCoordinates
  shear := by
  let row := Data.Vector.Basic.vectorOfFn fun column => (bank.rows.get target).coordinates.b.totals column +
    sumFin (fun index => weights index * (bank.rows.get index).coordinates.a.totals column)
  let coefficients := Data.Vector.Basic.vectorOfFn fun column => (bank.rows.get target).span.b.coefficients column +
    sumFin (fun index => weights index * (bank.rows.get index).span.a.coefficients column)
  let physical := Data.Vector.Basic.vectorOfFn fun column => (bank.rows.get target).span.b.physical column +
    sumFin (fun index => weights index * (bank.rows.get index).span.a.physical column)
  have physicalEq (column : Fin lifted.cutBoundaryWord.alphabet.count) :
      physical column = if lifted.cutBoundaryWord.alphabet.oneSided column then row column else 0 := by
    dsimp only [physical, row]
    rw [Data.Vector.Basic.vectorOfFn_apply, (bank.rows.get target).span.b.physical_eq]
    cases side : lifted.cutBoundaryWord.alphabet.oneSided column
    · simp only [if_neg (show (false : Bool) ≠ true from fun h => Bool.noConfusion h), -eq_self, -iff_self]
      have zero : sumFin (fun index => weights index * (bank.rows.get index).span.a.physical column) = 0 := by
        apply (FiniteSum.Fin.sumFin_congr ?_).trans FiniteSum.Fin.sumFin_zero
        intro index
        rw [(bank.rows.get index).span.a.physical_eq, side]
        exact mul_zero _
      rw [zero, zero_add]
    · simp only [if_pos (rfl : true = true), Data.Vector.Basic.vectorOfFn_apply, -eq_self, -iff_self]
      congr 1
      exact FiniteSum.Fin.sumFin_congr (fun index => by rw [(bank.rows.get index).span.a.physical_eq, side]; rfl)
  have equation (column : Fin lifted.cutBoundaryWord.alphabet.count) :
      row column = sumFin (fun index => coefficients index * integral.paired index column) + physical column := by
    dsimp only [row, physical]
    rw [Data.Vector.Basic.vectorOfFn_apply, Data.Vector.Basic.vectorOfFn_apply]
    have paired : sumFin (fun index => coefficients index * integral.paired index column) =
        sumFin (fun index => (bank.rows.get target).span.b.coefficients index * integral.paired index column) +
        sumFin (fun index => weights index *
          sumFin (fun inner => (bank.rows.get index).span.a.coefficients inner * integral.paired inner column)) := by
      exact (FiniteSum.Fin.sumFin_congr (fun index => congrArg (· * integral.paired index column)
        (Data.Vector.Basic.vectorOfFn_apply _ index))).trans

          (sum_shear
          _ _ _ _)
    rw [paired, (bank.rows.get target).span.b.equation]
    have tails : sumFin (fun index => weights index * (bank.rows.get index).coordinates.a.totals column) =
        sumFin (fun index => weights index *
          sumFin (fun inner => (bank.rows.get index).span.a.coefficients inner * integral.paired inner column)) +
        sumFin (fun index => weights index * (bank.rows.get index).span.a.physical column) := by
      rw [← FiniteSum.Fin.sumFin_add]
      exact FiniteSum.Fin.sumFin_congr (fun index => by rw [(bank.rows.get index).span.a.equation, mul_add])
    rw [tails]
    ring1
  refine ⟨row, Data.Vector.Basic.vectorOfFn_apply _, ⟨coefficients, physical, physicalEq, equation⟩,
    Data.Vector.Basic.vectorOfFn_apply _, fun valuation anti => ?_⟩
  have combined : WordCoordinates.combine row
      (fun column => valuation (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
        (lifted.cutBoundaryWord.alphabet.generators column))) =
      WordCoordinates.combine (bank.rows.get target).coordinates.b.totals
        (fun column => valuation (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column))) +
      sumFin (fun index => (weights index : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine (bank.rows.get
        index).coordinates.a.totals
        (fun column => valuation (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)))) :=
    (FiniteSum.Fin.sumFin_congr (fun column => congrArg (fun coefficient : Int => (coefficient :
      Data.Gaussian.Basic.Canonical) * _)
      (Data.Vector.Basic.vectorOfFn_apply _ column))).trans
        (combine_shear
        _ _ _ _)
  rw [shear.value valuation anti, combined, (bank.rows.get target).coordinates.b_value valuation anti]
  have tails : sumFin (fun index => (weights index : Data.Gaussian.Basic.Canonical) *
      SewingRetraction.wordValue valuation (bank.rows.get index).pair.aFaces.geometry.indexed) =
      sumFin (fun index => (weights index : Data.Gaussian.Basic.Canonical) * WordCoordinates.combine (bank.rows.get
        index).coordinates.a.totals
        (fun column => valuation (OrientedEdge.map lifted.cutPolygon.patch.cut.vertexLabels
          (lifted.cutBoundaryWord.alphabet.generators column)))) +
      sumFin (fun index => (weights index : Data.Gaussian.Basic.Canonical) *
        SewingRetraction.faceValue lifted.mesh.triangulation.faces valuation (bank.rows.get
          index).coordinates.routes.a.correction) := by
    rw [← FiniteSum.Fin.sumFin_add]
    exact FiniteSum.Fin.sumFin_congr (fun index => by
        rw [(bank.rows.get index).coordinates.a_value valuation anti, mul_add])
  rw [tails]
  ring1

namespace CutCoordinates

variable {shear :
  Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank.BShear bank
  target weights}

/-- The actual integral spanning intersection equals the nested finite coefficient dot product. -/
private theorem intersection_eq_dot
    {firstRow lastRow : Data.Vector Int lifted.cutBoundaryWord.alphabet.count}
    (first : IntegralPairing.SpanningCoordinates integral firstRow)
    (last : IntegralPairing.SpanningCoordinates integral lastRow) :
    SpanningCoordinates.intersection first last = sumFin (fun row => first.coefficients row *
      sumFin (fun column => integral.paired row column * last.coefficients column)) := by
  apply FiniteSum.Fin.sumFin_congr
  intro row
  rw [← FiniteSum.Fin.sumFin_mul_left]
  exact FiniteSum.Fin.sumFin_congr (fun _ => _root_.mul_assoc _ _ _)

/-- Intersection with the corrected row is the original B intersection plus the weighted original A intersections. -/
theorem intersection_left (coordinates :
  BShear.CutCoordinates
  shear)
    {row : Data.Vector Int lifted.cutBoundaryWord.alphabet.count}
    (other : IntegralPairing.SpanningCoordinates integral row) :
    SpanningCoordinates.intersection coordinates.span other = SpanningCoordinates.intersection (bank.rows.get
      target).span.b other +
      sumFin (fun index => weights index * SpanningCoordinates.intersection (bank.rows.get index).span.a other) := by
  rw
    [intersection_eq_dot]
  have combined := (FiniteSum.Fin.sumFin_congr (fun column => congrArg
    (· * sumFin (fun inner => integral.paired column inner * other.coefficients inner))
    (coordinates.coefficients_eq column))).trans
      (sum_shear
      _ _ _ _)
  refine combined.trans (congrArg₂ (· + ·)
    (intersection_eq_dot
    (bank.rows.get target).span.b other).symm ?_)
  exact FiniteSum.Fin.sumFin_congr (fun index => congrArg (weights index * ·)

      (intersection_eq_dot
      (bank.rows.get index).span.a other).symm)

/-- The corrected row's intersection with an original A row reads the retained A/B and A/A table blocks. -/
theorem intersection_a (coordinates :
  BShear.CutCoordinates
  shear) (index : Fin genus) :
    SpanningCoordinates.intersection coordinates.span (bank.rows.get index).span.a = -bank.ab index target +
      sumFin (fun source => weights source * bank.aa source index) := by
  rw [coordinates.intersection_left, SpanningCoordinates.intersection_skew (bank.rows.get target).span.b (bank.rows.get
    index).span.a, ← bank.ab_eq]
  congr 1
  exact FiniteSum.Fin.sumFin_congr (fun source => by rw [bank.aa_eq])

/-- The corrected row's intersection with an original B row reads the retained B/B and A/B table blocks. -/
theorem intersection_b (coordinates :
  BShear.CutCoordinates
  shear) (index : Fin genus) :
    SpanningCoordinates.intersection coordinates.span (bank.rows.get index).span.b = bank.bb target index +
      sumFin (fun source => weights source * bank.ab source index) := by
  rw [coordinates.intersection_left, ← bank.bb_eq]
  congr 1
  exact FiniteSum.Fin.sumFin_congr (fun source => by rw [bank.ab_eq])

/-- An original A row's intersection with the corrected row reads the retained A/B and A/A table blocks. -/
theorem a_intersection (coordinates :
  BShear.CutCoordinates
  shear) (index : Fin genus) :
    SpanningCoordinates.intersection (bank.rows.get index).span.a coordinates.span = bank.ab index target +
      sumFin (fun source => weights source * bank.aa index source) := by
  rw [SpanningCoordinates.intersection_skew (bank.rows.get index).span.a coordinates.span, coordinates.intersection_a]
  have reversed : sumFin (fun source => weights source * bank.aa source index) =
      -sumFin (fun source => weights source * bank.aa index source) :=
    (FiniteSum.Fin.sumFin_congr (fun source => by rw [bank.aa_skew source index, mul_neg])).trans
      (FiniteSum.Fin.sumFin_neg _)
  rw [reversed]
  ring1

/-- The actual corrected-word pairing, with both source table blocks and the quadratic A-A term retained. No zero block
is presumed. -/
theorem intersection (first :
  BShear.CutCoordinates
  shear) {otherTarget : Fin genus}
    {otherWeights : Data.Vector Int genus}
    {otherShear : IntersectionBank.BShear bank otherTarget otherWeights} (last :
      BShear.CutCoordinates
      otherShear) :
    SpanningCoordinates.intersection first.span last.span = bank.bb target otherTarget -
      sumFin (fun index => otherWeights index * bank.ab index target) +
      sumFin (fun index => weights index *
        (bank.ab index otherTarget + sumFin (fun source => otherWeights source * bank.aa index source))) := by
  rw [first.intersection_left, SpanningCoordinates.intersection_skew (bank.rows.get target).span.b last.span,
    last.intersection_b,
    bank.bb_skew otherTarget target]
  have sums := FiniteSum.Fin.sumFin_congr (fun index => congrArg (weights index * ·) (last.a_intersection index))
  rw [sums]
  ring1

end CutCoordinates
end BShear
end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank

namespace Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank
namespace BShear

end Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Standard.TourCombinations.StandardTours.IntersectionBank.BShear
