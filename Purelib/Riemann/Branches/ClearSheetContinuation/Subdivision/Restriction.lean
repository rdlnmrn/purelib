module

public import Purelib.Integration.Polynomial.Gaussian.Cell.Restriction.Chain
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Refinement
public import Purelib.Data.List.DependentProduct
import Purelib.Data.List.OfFn.Basic
import Purelib.Integration.Partition.Interval.Chain.Map
import Purelib.Data.List.Flatten.Table
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Riemann.Paths.PreparedClearPathModels
import Purelib.Data.List.Map
public import Purelib.Data.Rat.Interval.ConvexCombination
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

/-! # Actual cached dyadic restrictions of one retained polynomial cell

The original coarse parameter edge and an additional dyadic depth determine
new subintervals in that cell's original unit parameter. Its polynomial is
not recompiled. One original Cached restriction is materialized for each
actual refined occurrence and retained in the existing dependent product.
The exact endpoint chain reassembles their actual integral samples.
-/

public section

namespace Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge

open Purelib
open Purelib.Algebra.FiniteSum.Fin (sumFin)
open Purelib.Data.Gaussian
open Purelib.Data.List
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Data.Rat.Interval.ConvexCombination
open Purelib.Integration.Partition (Interval)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Polynomial.Ascending.Gaussian.Restriction (Cached)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

/-- Read the original refined edge endpoints in their original coarse edge's exact local unit parameter. -/
@[expose] def intervals (coarse : ParameterEdge) (depth : Nat)
    (index : Fin (dyadicEdges depth coarse.left coarse.right).length) : Interval :=
  let fine := (dyadicEdges depth coarse.left coarse.right)[index.val]'index.isLt
  ⟨segmentParameter coarse.left.parameter coarse.right.parameter fine.left.parameter,
    segmentParameter coarse.left.parameter coarse.right.parameter fine.right.parameter⟩

/-- The actual new polynomial restriction cache at every retained dyadic subinterval of the SAME original cell. -/
@[expose] def Restrictions (cell : CellModel) (coarse : ParameterEdge) (depth : Nat) :=
  DependentProduct (dyadicEdges depth coarse.left coarse.right) (fun index =>
    Cached cell.polynomial (Cast.Path.ofCoordinate (intervals coarse depth index).start)
      (Cast.Path.ofCoordinate (intervals coarse depth index).finish))

namespace Restrictions

variable (cell : CellModel) (coarse : ParameterEdge) (depth : Nat)

/-- Materialize each genuinely new Cached subinterval table once in the original refined occurrence order. -/
def build : Restrictions cell coarse depth :=
  DependentProduct.ofFn (dyadicEdges depth coarse.left coarse.right) (fun index =>
    Cached.canonical cell.polynomial (Cast.Path.ofCoordinate (intervals coarse depth index).start)
      (Cast.Path.ofCoordinate (intervals coarse depth index).finish))

variable {cell coarse depth} (retained : Restrictions cell coarse depth)

/-- Read the SAME stored complete Cached restriction without executing its canonical factory again. -/
@[expose] def cache (index : Fin (dyadicEdges depth coarse.left coarse.right).length) :
    Cached cell.polynomial (Cast.Path.ofCoordinate (intervals coarse depth index).start)
      (Cast.Path.ofCoordinate (intervals coarse depth index).finish) :=
  DependentProduct.get (dyadicEdges depth coarse.left coarse.right) retained index

/-- Every stored cache retains its whole original canonical restriction factory, including its integral sample. -/
theorem build_cache (index : Fin (dyadicEdges depth coarse.left coarse.right).length) :
    (build cell coarse depth).cache index =
      Cached.canonical cell.polynomial (Cast.Path.ofCoordinate (intervals coarse depth index).start)
        (Cast.Path.ofCoordinate (intervals coarse depth index).finish) := by
  unfold build cache
  exact DependentProduct.get_ofFn _ _ index

/-- An actual refined occurrence's two normalized endpoints stay in the original coarse unit interval. -/
theorem endpoints_inside (ordered : coarse.left.parameter ≤ coarse.right.parameter)
    (index : Fin (dyadicEdges depth coarse.left coarse.right).length) :
    (0 ≤ (intervals coarse depth index).start ∧ (intervals coarse depth index).start ≤ 1) ∧
      (0 ≤ (intervals coarse depth index).finish ∧ (intervals coarse depth index).finish ≤ 1) := by
  have bounds := dyadicEdges_bounds depth coarse.left coarse.right ordered _ (List.getElem_mem index.isLt)
  constructor
  · exact segmentParameter_bounds _ _ _
      ⟨(Order.Basic.min_le_left _ _).trans bounds.1,
        (bounds.2.1.trans bounds.2.2).trans (Order.Basic.le_max_right _ _)⟩
  · exact segmentParameter_bounds _ _ _
      ⟨(Order.Basic.min_le_left _ _).trans (bounds.1.trans bounds.2.1),
        bounds.2.2.trans (Order.Basic.le_max_right _ _)⟩

/-- A strict coarse edge's normalized left endpoint is exactly zero. -/
private theorem normalized_left (strict : coarse.left.parameter < coarse.right.parameter) :
    segmentParameter coarse.left.parameter coarse.right.parameter coarse.left.parameter = 0 := by
  have actual := segmentParameter_interpolates coarse.left.parameter coarse.right.parameter coarse.left.parameter
    ⟨Order.Basic.min_le_left _ _, Order.Basic.le_max_left _ _⟩
  apply parameter_eq_of_interpolation strict.ne
  exact actual.trans (by ring1)

/-- A strict coarse edge's normalized right endpoint is exactly one. -/
private theorem normalized_right (strict : coarse.left.parameter < coarse.right.parameter) :
    segmentParameter coarse.left.parameter coarse.right.parameter coarse.right.parameter = 1 := by
  have actual := segmentParameter_interpolates coarse.left.parameter coarse.right.parameter coarse.right.parameter
    ⟨Order.Basic.min_le_right _ _, Order.Basic.le_max_right _ _⟩
  apply parameter_eq_of_interpolation strict.ne
  exact actual.trans (by ring1)

/-- The SAME original normalized dyadic intervals chain the coarse cell's unit zero to one exactly. -/
theorem interval_chain (strict : coarse.left.parameter < coarse.right.parameter) :
    Interval.Chain 0 1 (List.ofFn (intervals coarse depth)) := by
  let normalize := segmentParameter coarse.left.parameter coarse.right.parameter
  have original := Interval.Chain.map normalize (dyadicEdges_chain depth coarse.left coarse.right)
  let mapped : List Interval := ((dyadicEdges depth coarse.left coarse.right).map ParameterEdge.interval).map
    (fun interval : Interval => ⟨normalize interval.start, normalize interval.finish⟩)
  have normalized : Interval.Chain 0 1 mapped :=
    Eq.mp (congrArg₂ (fun start finish : Rational => Interval.Chain start finish mapped)
      (normalized_left (coarse := coarse) strict) (normalized_right (coarse := coarse) strict)) original
  have table : List.ofFn (intervals coarse depth) =
      ((dyadicEdges depth coarse.left coarse.right).map ParameterEdge.interval).map
        (fun interval => ⟨normalize interval.start, normalize interval.finish⟩) :=
    (OfFn.Basic.ofFn_map_cast (dyadicEdges depth coarse.left coarse.right) rfl
      (fun edge => (⟨normalize edge.left.parameter, normalize edge.right.parameter⟩ : Interval))).trans
        (Map.map_map (fun interval : Interval =>
          (⟨normalize interval.start, normalize interval.finish⟩ : Interval)) ParameterEdge.interval
            (dyadicEdges depth coarse.left coarse.right)).symm
  exact Eq.mpr (congrArg (Interval.Chain 0 1) table) normalized

/-- The actual SAME cached restriction models reassemble the original cell integral, with no new restriction factory. -/
theorem sample_sum (strict : coarse.left.parameter < coarse.right.parameter) :
    sumFin (fun index => (Cell.Restriction.model cell (retained.cache index)).integralSample) = cell.integralSample :=
  Cell.Restriction.integralSample_sum_unit cell (intervals coarse depth) retained.cache (interval_chain strict)

end Restrictions

end Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.ParameterEdge

namespace Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

open Purelib
open Purelib.Algebra
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Integration.Polynomial.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Riemann.Paths.PreparedClearPathModels.PreparedPath

/-- The SAME cached polynomial restriction bank at every original coarse dyadic occurrence.

The supplied cells are projections from retained actual preparations. The
existing dependent product stores each original cell's new fine restriction
bank once; the dyadic coarse/fine index spine remains nominal throughout.
-/
@[expose] def RefinementRestrictions (coarse additional : Nat) (left right : Endpoint)
    (cells : Fin (dyadicEdges coarse left right).length → CellModel) :=
  DependentProduct (dyadicEdges coarse left right) (fun index =>
    ParameterEdge.Restrictions (cells index)
      ((dyadicEdges coarse left right)[index.val]'index.isLt) additional)

namespace RefinementRestrictions

variable {coarse additional : Nat} {left right : Endpoint}
    {cells : Fin (dyadicEdges coarse left right).length → CellModel}

/-- Materialize each original coarse cell's complete new fine restriction bank once in the original order. -/
def build (coarse additional : Nat) (left right : Endpoint)
    (cells : Fin (dyadicEdges coarse left right).length → CellModel) :
    RefinementRestrictions coarse additional left right cells :=
  DependentProduct.ofFn (dyadicEdges coarse left right) (fun index =>
    ParameterEdge.Restrictions.build (cells index)
      ((dyadicEdges coarse left right)[index.val]'index.isLt) additional)

variable (retained : RefinementRestrictions coarse additional left right cells)

/-- Read the SAME stored original coarse occurrence's restriction bank without executing a canonical factory. -/
@[expose] def bank (index : Fin (dyadicEdges coarse left right).length) :
    ParameterEdge.Restrictions (cells index)
      ((dyadicEdges coarse left right)[index.val]'index.isLt) additional :=
  DependentProduct.get (dyadicEdges coarse left right) retained index

/-- Every stored coarse bank retains its whole original fine-bank factory equation. -/
theorem build_bank (index : Fin (dyadicEdges coarse left right).length) :
    (build coarse additional left right cells).bank index =
      ParameterEdge.Restrictions.build (cells index)
        ((dyadicEdges coarse left right)[index.val]'index.isLt) additional := by
  unfold build bank
  exact DependentProduct.get_ofFn _ _ index

/-- Read the actual fine cell consuming the SAME original retained coarse and fine cache coordinates. -/
@[expose] def fineCell {index : Fin (dyadicEdges (coarse + additional) left right).length}
    (found : Flatten.Occurrence (refinementBlocks coarse additional left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index)) : CellModel :=
  Cell.Restriction.model (cells (refinementOccurrence.coarseIndex found))
    ((retained.bank (refinementOccurrence.coarseIndex found)).cache (refinementOccurrence.localIndex found))

/-- The unchanged original coarse-cell order determines the original fine restriction-model word in each fiber. -/
@[expose] def words (outer : Fin (dyadicEdges coarse left right).length) : List CellModel :=
  List.ofFn (fun inner => Cell.Restriction.model (cells outer) ((retained.bank outer).cache inner))

/-- The SAME actual fine model table is the exact ordered flattening of its original stored coarse/fine banks.

The original full-prefix positions regroup the table. Existing row-major
code injectivity identifies the two retained occurrence outcomes at each
position, independently of edge/model values. Every restriction cache is
read from the supplied product; no canonical factory is executed here.
-/
theorem fineCells_eq_words
    (occurrences : (index : Fin (dyadicEdges (coarse + additional) left right).length) →
      Flatten.Occurrence (refinementBlocks coarse additional left right)
        (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index)) :
    List.ofFn (fun index => retained.fineCell (occurrences index)) = (List.ofFn retained.words).flatten := by
  let edges := dyadicEdges coarse left right
  let blocks := fun outer : Fin edges.length =>
    dyadicEdges additional (edges[outer.val]'outer.isLt).left (edges[outer.val]'outer.isLt).right
  have blocks_eq : List.ofFn blocks = refinementBlocks coarse additional left right :=
    OfFn.Basic.ofFn_map_cast edges rfl (fun edge => dyadicEdges additional edge.left edge.right)
  have length_eq : (dyadicEdges (coarse + additional) left right).length = (List.ofFn blocks).flatten.length :=
    (congrArg List.length (refinementBlocks_eq coarse additional left right)).trans
      (congrArg (fun table => table.flatten.length) blocks_eq.symm)
  let tableOuter := fun outer : Fin edges.length =>
    Fin.cast (Map.length_map (fun edge => dyadicEdges additional edge.left edge.right) edges).symm outer
  have block_eq (outer : Fin edges.length) :
      (refinementBlocks coarse additional left right)[(tableOuter outer).val]'(tableOuter outer).isLt =
        blocks outer :=
    Map.getElem_map _ _ outer.val outer.isLt (tableOuter outer).isLt
  let tableInner := fun outer : Fin edges.length => fun inner : Fin (blocks outer).length =>
    Fin.cast (congrArg List.length (block_eq outer)).symm inner
  let selected := fun outer : Fin edges.length => fun inner : Fin (blocks outer).length =>
    Flatten.position (refinementBlocks coarse additional left right) (tableOuter outer) (tableInner outer inner)
  let positions := fun outer : Fin edges.length => fun inner : Fin (blocks outer).length =>
    Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)).symm
      (selected outer inner).val
  let expected (outer : Fin edges.length) (inner : Fin (blocks outer).length) :
      Flatten.Occurrence (refinementBlocks coarse additional left right)
        (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right))
          (positions outer inner)) :=
    ⟨tableOuter outer, ⟨tableInner outer inner, (selected outer inner).property⟩⟩
  have offsets (outer : Fin edges.length) (inner : Fin (blocks outer).length) :
      (positions outer inner).val = ((List.ofFn blocks).take outer.val).flatten.length + inner.val :=
    (selected outer inner).property.2.trans
      (congrArg (fun table => (table.take outer.val).flatten.length + inner.val) blocks_eq.symm)
  have grouped := Flatten.ofFn_grouped blocks length_eq
    (fun index => retained.fineCell (occurrences index)) positions offsets
  have entries (outer : Fin edges.length) (inner : Fin (blocks outer).length) :
      retained.fineCell (occurrences (positions outer inner)) =
        Cell.Restriction.model (cells outer) ((retained.bank outer).cache inner) := by
    have same := refinementOccurrence.unique (occurrences (positions outer inner)) (expected outer inner)
    exact (congrArg (fun found => retained.fineCell found) same).trans (by rfl)
  have fibers : List.ofFn (fun outer : Fin edges.length =>
      List.ofFn (fun inner => retained.fineCell (occurrences (positions outer inner)))) =
        List.ofFn retained.words :=
    OfFn.Basic.ofFn_congr (fun outer => OfFn.Basic.ofFn_congr (fun inner => entries outer inner))
  exact grouped.trans (congrArg List.flatten fibers)

/-- A bounded original occurrence of a strict parameter-edge word has that same strict orientation. -/
private theorem strict_at : (edges : List ParameterEdge) → StrictParameterEdges edges →
    (index : Fin edges.length) →
      (edges[index.val]'index.isLt).left.parameter < (edges[index.val]'index.isLt).right.parameter
  | [], _proper, index => Fin.elim0 index
  | _first :: remaining, proper, index =>
      Fin.cases proper.1 (fun index => strict_at remaining proper.2 index) index

/-- Both original sums are exactly equal on the SAME retained fine restriction table and original coarse cells.

Original dyadic strict-progress evidence admits the local zero-to-one
restriction chain. Exact per-fiber integral reassembly and ordered flattening
preserve both actual sample words with no adaptive-count multiplier.
-/
theorem sample_sum
    (occurrences : (index : Fin (dyadicEdges (coarse + additional) left right).length) →
      Flatten.Occurrence (refinementBlocks coarse additional left right)
        (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) index))
    (strict : left.parameter < right.parameter) :
    FiniteSum.Fin.sumFin (fun index => (retained.fineCell (occurrences index)).integralSample) =
      FiniteSum.Fin.sumFin (fun index => (cells index).integralSample) := by
  have coarseProper := dyadicEdges_strictParameterEdges coarse left right strict
  calc
    _ = (Path.Basic.PathModel.mk (List.ofFn (fun index => retained.fineCell (occurrences index)))).integralSample :=
      (Path.Basic.PathModel.integralSample_ofFn_eq_sumFin _).symm
    _ = (Path.Basic.PathModel.mk (List.ofFn retained.words).flatten).integralSample :=
      congrArg (fun entries => (Path.Basic.PathModel.mk entries).integralSample)
        (retained.fineCells_eq_words occurrences)
    _ = FiniteSum.Fin.sumFin (fun outer => (Path.Basic.PathModel.mk (retained.words outer)).integralSample) :=
      Path.Basic.PathModel.integralSample_flatten_ofFn _
    _ = _ := FiniteSum.Fin.sumFin_congr (fun outer =>
      (Path.Basic.PathModel.integralSample_ofFn_eq_sumFin _).trans
        ((retained.bank outer).sample_sum (strict_at _ coarseProper outer)))

/-- Exact common-count transport retains the SAME whole fine cache table and original coarse integral sum.

Only a proven equality of finite dimensions changes the display index.
Neither selected observations nor request tolerances are altered.
-/
theorem sample_sum_cast {count : Nat}
    (same : count = (dyadicEdges (coarse + additional) left right).length)
    (occurrences : (index : Fin count) → Flatten.Occurrence (refinementBlocks coarse additional left right)
      (Fin.cast (congrArg List.length (refinementBlocks_eq coarse additional left right)) (Fin.cast same index)))
    (strict : left.parameter < right.parameter) :
    FiniteSum.Fin.sumFin (fun index => (retained.fineCell (occurrences index)).integralSample) =
      FiniteSum.Fin.sumFin (fun index => (cells index).integralSample) := by
  cases same
  exact retained.sample_sum occurrences strict

end RefinementRestrictions

end Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

end
