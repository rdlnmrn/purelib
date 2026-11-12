module

import Purelib.Data.List.DependentProduct
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Piece
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Layer
import Purelib.Data.List.Map
import Purelib.Data.List.Flatten
import Purelib.Data.List.Split
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Basic.Indexed
import Purelib.Data.List.OfFn.Basic
public import Purelib.Algebra.FiniteSum.Fin
import Purelib.Integration.Path.Dyadic.DyadicSteps

public import Purelib.Integration.Path.Dyadic.DyadicTrace
import Purelib.Data.Rat.Interval.Bisection
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Comparison
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Integration.Program.Gaussian.Sequential
public import Purelib.Integration.Program.Gaussian.Cached.Basic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Certified finite integral programs for original regular parallel spans -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib
open Purelib.Algebra
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Program.Gaussian
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Integration.Path.Dyadic
open Purelib.Approximation
open Purelib.Approximation.Rational
open Purelib.Riemann.RootContinuation

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : Waist.Differential.Bounds.Data site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

namespace Piece

open Purelib.Data.Rat.Fraction.Order

/-- Construct a whole original parallel-quarter piece from its identical cached starting query.

The supplied complete source is retained verbatim. Its actual cofactor
certificate supplies the paid root observation; containment of the original
unit span pays later queries of the same already prepared quarter.
-/
@[expose] def ofSource (data : Waist.Differential.Bounds.Data site parameter differential)
    (source : Transport.Reading actual 0 ⟨by decide +kernel, by decide +kernel⟩)
    (regular : parameter ≠ criticalValue site) (accuracy : AccuracyRequest) : Piece data actual accuracy :=
  let span : Interval.Bounds := ⟨0, 1, by decide +kernel⟩
  let cell := Cells.Model.build (span := span) data source regular accuracy
  ofCell (span := span) (fun _ contained => contained) cell

/-- The constructed original whole-quarter piece retains exactly the closed unit chart interval. -/
theorem ofSource_span (data : Waist.Differential.Bounds.Data site parameter differential)
    (source : Transport.Reading actual 0 ⟨by decide +kernel, by decide +kernel⟩)
    (regular : parameter ≠ criticalValue site) (accuracy : AccuracyRequest) :
    (ofSource data source regular accuracy).span = ⟨0, 1, by decide +kernel⟩ := rfl

/-- Construct each finite layer from the original piece, retaining every computed split before reading its children. -/
@[expose] def layerAt (initial : Piece data actual accuracy) : (depth : Nat) → Layer initial depth
  | 0 => Layer.ofPiece initial
  | depth + 1 =>
      let parent := layerAt initial depth
      let steps := Steps.build parent.pieces
      parent.next steps

/-- Reweighting one completed factory layer gives the complete original factory for the reweighted initial piece.

Both constructions have the same original mesh and complete accuracy. This
law additionally identifies the retained Readings, cofactor observations,
coefficients, allowances and numerical model, rather than only their spans.
-/
theorem layerAt_reweight (initial : Piece data actual accuracy)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : Waist.Differential.Bounds.Data site parameter nextDifferential) (depth : Nat) :
    (initial.layerAt depth).reweight nextData = (initial.reweight nextData).layerAt depth := by
  induction depth with
  | zero => exact Layer.reweight_ofPiece initial nextData
  | succ depth inductionHypothesis =>
      change ((initial.layerAt depth).next (Steps.build (initial.layerAt depth).pieces)).reweight nextData = _
      rewrite [Layer.reweight_next, Steps.reweight_build]
      exact congrArg (fun layer : Layer (initial.reweight nextData) depth =>
        layer.next (Steps.build layer.pieces)) inductionHypothesis

/-- Continuing a completed original scalar stage gives the complete original factory result at the summed depth.

The equality concerns the entire retained Layer, including the actual
source/cell observations and numerical model. Only the later Steps are
executed by advance; the original layerAt producer is unchanged.
-/
theorem layerAt_advance (initial : Piece data actual accuracy) (coarse extra : Nat) :
    (initial.layerAt coarse).advance extra = initial.layerAt (coarse + extra) := by
  induction extra with
  | zero => rfl
  | succ extra inductionHypothesis =>
      exact congrArg (fun layer : Layer initial (coarse + extra) =>
        layer.next (Steps.build layer.pieces)) inductionHypothesis

/-- Every actual original factory layer retains the exact ordered dyadic interval parts of its same initial span.

The proof follows the original once-retained midpoint Steps and next-layer
readback. It creates no replacement pieces, root observations or numerical
model and imposes no successful coverage premise on the producer.
-/
theorem layerAt_spans (initial : Piece data actual accuracy) (depth : Nat) :
    (initial.layerAt depth).pieces.map (fun piece => piece.span) =
      Interval.Bisection.parts depth initial.span := by
  induction depth with
  | zero => rfl
  | succ depth inductionHypothesis =>
      exact ((initial.layerAt depth).next_spans (Steps.build (initial.layerAt depth).pieces)).trans
        (congrArg Interval.Bisection.refine inductionHypothesis)

/-- The actual original scalar layer's upper times are the identical canonical dyadic vertex tail in original order. -/
theorem layerAt_uppers (initial : Piece data actual accuracy) (depth : Nat) :
    (initial.layerAt depth).pieces.map (fun piece => piece.span.upper) =
      DyadicTrace.tail depth initial.span.lower initial.span.upper := by
  have retained := congrArg (fun spans : List Interval.Bounds => spans.map (fun span => span.upper))
    (initial.layerAt_spans depth)
  rewrite [Data.List.Map.map_map] at retained
  exact retained.trans (DyadicTrace.tail_eq_parts_upper depth initial.span).symm

/-- Whole-quarter index transport preserves the complete original scalar-layer factory result. -/
theorem layerAt_transport (initial : Piece data actual accuracy) (depth : Nat)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    (initial.transport equal).layerAt depth = (initial.layerAt depth).transport equal := by
  cases equal
  rfl

/-- Construct the existing sequential refinement interface with internally proved consecutive sample bounds. -/
@[expose] def sequential (initial : Piece data actual accuracy) :
    Sequential.SequentialCompatibleConstantRefinementProgram :=
  { model depth := (initial.layerAt depth).model
    steps depth :=
      let parent := initial.layerAt depth
      let steps := Steps.build parent.pieces
      parent.compatible steps
    stepScale := 4 * initial.span.width ^ 2 * initial.cell.allowance
    stepScale_nonneg :=
      Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide +kernel)
          (Arithmetic.sq_nonneg_direct _)) initial.cell.allowance_nonnegative
    initialAllowance_le := by
      have bound := (Layer.ofPiece initial).aggregateAllowance_le
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct] at bound
      have scaleNonnegative := Arithmetic.mul_nonneg_direct
        (Arithmetic.sq_nonneg_direct initial.span.width) initial.cell.allowance_nonnegative
      have scaled := Arithmetic.mul_le_mul_of_nonneg_right_direct
        (show (1 : Fraction.Rational) ≤ 16 by decide +kernel) scaleNonnegative
      rewrite [Fraction.Field.one_mul] at scaled
      apply bound.trans
      apply scaled.trans_eq
      ring1
    comparisonAllowance_le depth :=
      (initial.layerAt depth).comparisonAllowance_le (Steps.build (initial.layerAt depth).pieces) }

/-- The retained regular parallel piece produces an actual certified Gaussian integral refinement program. -/
@[expose] def program (initial : Piece data actual accuracy) : Basic.RefinementProgram :=
  initial.sequential.toRefinementProgram

/-- Read the exact original layer model from the same constructed integral program. -/
theorem model_eq (initial : Piece data actual accuracy) (depth : Nat) :
    (initial.program.model depth) = (initial.layerAt depth).model := rfl

/-- The finite parallel integral has sixteen times the original squared-width-times-allowance error scale. -/
theorem errorScale_eq (initial : Piece data actual accuracy) :
    initial.program.errorScale = 16 * initial.span.width ^ 2 * initial.cell.allowance := by
  change 4 * (4 * initial.span.width ^ 2 * initial.cell.allowance) = _
  ring1

/-- Actual later regular parallel samples meet the earlier finite quarter-radius bound. -/
theorem later_close (initial : Piece data actual accuracy)
    {earlier later : Nat} (order : earlier ≤ later) :
    normSq ((initial.layerAt later).model.integralSample - (initial.layerAt earlier).model.integralSample) ≤
      Geometric.Basic.quarterRadius (16 * initial.span.width ^ 2 * initial.cell.allowance) earlier := by
  have bounded := initial.program.later_close order
  rewrite [initial.model_eq, initial.model_eq, initial.errorScale_eq] at bounded
  rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bounded

/-- Cache each requested original layer model with its actual integral sample and certified allowance. -/
@[expose] def cached (initial : Piece data actual accuracy) : Cached.Basic.CachedProgram :=
  initial.program.certifiedView.program

/-- The cached sample is the actual finite integral sample of the same original layer. -/
theorem cached_sample (initial : Piece data actual accuracy) (depth : Nat) :
    (initial.cached.stage depth).sample = (initial.layerAt depth).model.integralSample := rfl

/-- The internally selected finite refinement meets the supplied positive allowance request. -/
theorem requested_allowance (initial : Piece data actual accuracy) (current : Nat)
    (target : Fraction.Rational) (positive : 0 < target) :
    (initial.cached.stage (initial.cached.approximation.refineIndex current target positive)).allowance < target :=
  initial.cached.requested_allowance current target positive

end Piece

namespace Layer

/-- The original global advance and any original same-request parent factory keep identical complete requests.

Both procedures quarter the same initial request once per actual step.
The equality retains the complete positive AccuracyRequest, without
normalizing its tolerance or changing any scalar source/cache data.
-/
theorem advance_accuracy {initial : Piece data actual accuracy} {depth : Nat}
    (layer : Layer initial depth) (parent : Piece data actual layer.accuracy) (extra : Nat) :
    (layer.advance extra).accuracy = (parent.layerAt extra).accuracy := by
  induction extra with
  | zero => rfl
  | succ extra previous => exact congrArg AccuracyRequest.quarter previous

/-- The exact whole-piece factory decomposition of the same original completed layer.

Each original parent contributes its own original layerAt descendants.
Only exact request equality transports these pieces into the global
advance request; no source, child, cell or model is reconstructed.
-/
@[expose] def AdvancePieces {initial : Piece data actual accuracy} {depth : Nat}
    (layer : Layer initial depth) (extra : Nat) : Prop :=
  (layer.advance extra).pieces = layer.pieces.flatMap (fun parent =>
    Eq.mp (congrArg (fun request => List (Piece data actual request))
      (advance_accuracy layer parent extra).symm) (parent.layerAt extra).pieces)

/-- Advancing the actual global layer retains the ordered original per-parent factory descendants in full.

The proof follows the original Steps.build and advance recursion. Original
flat-map associativity combines the exact head/tail factory readbacks;
request transports are erased equalities, not another refinement builder.
-/
theorem advance_pieces {initial : Piece data actual accuracy} {depth : Nat}
    (layer : Layer initial depth) (extra : Nat) : AdvancePieces layer extra := by
  induction extra with
  | zero =>
      unfold AdvancePieces
      change layer.pieces = layer.pieces.flatMap (fun parent => [parent])
      have identical (pieces : List (Piece data actual layer.accuracy)) :
          pieces = pieces.flatMap (fun parent => [parent]) := by
        induction pieces with
        | nil => rfl
        | cons parent remaining previous => exact congrArg (List.cons parent) previous
      exact identical layer.pieces
  | succ extra previous =>
      unfold AdvancePieces at previous ⊢
      let localPieces := fun parent : Piece data actual layer.accuracy =>
        Eq.mp (congrArg (fun request => List (Piece data actual request))
          (advance_accuracy layer parent extra).symm) (parent.layerAt extra).pieces
      let children := fun parent : Piece data actual (layer.advance extra).accuracy =>
        parent.children (Split.build parent.cell parent.within)
      change (Steps.build (layer.advance extra).pieces).children = _
      calc
        _ = (layer.advance extra).pieces.flatMap children := Steps.children_build _
        _ = (layer.pieces.flatMap localPieces).flatMap children :=
          congrArg (fun pieces => pieces.flatMap children) previous
        _ = layer.pieces.flatMap (fun parent => (localPieces parent).flatMap children) :=
          Flatten.flatMap_assoc_direct localPieces children layer.pieces
        _ = _ := Flatten.flatMap_congr_direct _ _ layer.pieces (fun parent _ => by
          calc
            (localPieces parent).flatMap children = (Steps.build (localPieces parent)).children :=
              (Steps.children_build (localPieces parent)).symm
            _ = Eq.mp (congrArg (fun request => List (Piece data actual request))
                (congrArg AccuracyRequest.quarter (advance_accuracy layer parent extra).symm))
                  (Steps.build (parent.layerAt extra).pieces).children :=
              Steps.children_transport (advance_accuracy layer parent extra).symm (parent.layerAt extra).pieces
            _ = _ := rfl)

namespace Partition

/-- The exact original per-parent partition field with its supplied whole Piece and numerical-cell slices.

This is a named alias of the existing Sigma family. It retains the original
parent span, child request, full Piece list and its actual CellModel list;
no new nominal cache or alternative partition representation is introduced.
-/
@[expose] def Entry {parentAccuracy : AccuracyRequest} (extra : Nat)
    (parent : Piece data actual parentAccuracy) (childAccuracy : AccuracyRequest) : Type 1 :=
  Σ group : {pieces : List (Piece data actual childAccuracy) //
      pieces.map (fun piece => piece.span) = Interval.Bisection.parts extra parent.span},
    {cells : List CellModel // cells = Piece.models group.val}

namespace Entry

/-- The original partition field's span readback determines its actual unchanged dyadic descendant count.

This is the original count-field proof from Partition.layer. Both the
constructor and whole-row factory readback consume the same named law,
rather than repeating the retained dyadic length argument.
-/
theorem count {parentAccuracy childAccuracy : AccuracyRequest} {extra : Nat}
    {parent : Piece data actual parentAccuracy} (entry : Entry extra parent childAccuracy) :
    entry.1.val.length = 2 ^ extra := by
  have counts := congrArg List.length entry.1.property
  rewrite [Map.length_map] at counts
  have row := congrArg List.length (DyadicTrace.tail_eq_parts_upper extra parent.span)
  rewrite [DyadicSteps.tail_length, Map.length_map] at row
  exact counts.trans row.symm

end Entry

end Partition

/-- The actual ordered fine-piece and numerical-cell blocks indexed by the retained coarse scalar occurrences.

Each original dependent entry keeps both supplied cache slices, their exact
span/readback equations, and the original order. Both flattened banks equal
the supplied fine layer's actual lists; no numerical cell is reconstructed
from its equal Piece readback merely to populate this retained view.
-/
@[expose] def Partition {initial : Piece data actual accuracy} {coarse extra : Nat}
    (parents : Layer initial coarse) (fine : Layer initial (coarse + extra)) : Type 1 :=
  {blocks : DependentProduct parents.pieces (fun index =>
      Σ group : {pieces : List (Piece data actual fine.accuracy) //
          pieces.map (fun piece => piece.span) =
            Interval.Bisection.parts extra (parents.pieces[index.val]'index.isLt).span},
        {cells : List CellModel //
          cells = Piece.models group.val}) //
    (DependentProduct.mapToList parents.pieces blocks (fun _ block => block.1.val)).flatten = fine.pieces ∧
      (DependentProduct.mapToList parents.pieces blocks (fun _ block => block.2.val)).flatten = fine.model.cells}

/-- Split the actual piece and numerical-cell caches at the same original dyadic descendant counts.

The recursive call consumes the actual remaining suffixes. All span and
model equations are erased certificates; executable branches only split
the two supplied lists and retain their original entries in the product.
-/
private def partitionPieces {parentAccuracy childAccuracy : AccuracyRequest} (extra : Nat)
    (count : Nat) (count_eq : count = 2 ^ extra) :
    (parents : List (Piece data actual parentAccuracy)) →
    (pieces : List (Piece data actual childAccuracy)) →
    (cells : List CellModel) →
    cells = Piece.models pieces →
    pieces.map (fun piece => piece.span) =
      parents.flatMap (fun parent => Interval.Bisection.parts extra parent.span) →
    {blocks : DependentProduct parents (fun index =>
        Σ group : {pieces : List (Piece data actual childAccuracy) //
            pieces.map (fun piece => piece.span) =
              Interval.Bisection.parts extra (parents[index.val]'index.isLt).span},
          {stored : List CellModel //
            stored = Piece.models group.val}) //
      (DependentProduct.mapToList parents blocks (fun _ block => block.1.val)).flatten = pieces ∧
        (DependentProduct.mapToList parents blocks (fun _ block => block.2.val)).flatten = cells}
  | [], [], [], _, _ => ⟨PUnit.unit, ⟨rfl, rfl⟩⟩
  | [], _ :: _, _, _, impossible => nomatch impossible
  | [], [], _ :: _, impossible, _ => nomatch impossible
  | parent :: parents, pieces, cells, cells_eq, spans => by
      let divided := pieces.splitAt count
      let dividedCells := cells.splitAt count
      have headCount := congrArg List.length (DyadicTrace.tail_eq_parts_upper extra parent.span)
      rewrite [DyadicSteps.tail_length, Map.length_map] at headCount
      have actualCount : count = (Interval.Bisection.parts extra parent.span).length :=
        count_eq.trans headCount
      have firstSpans : divided.1.map (fun piece => piece.span) =
          Interval.Bisection.parts extra parent.span := by
        dsimp only [divided]
        rewrite [Split.at_eq, Map.map_take, spans, actualCount]
        exact Append.take_length_append _ _
      have laterSpans : divided.2.map (fun piece => piece.span) =
          parents.flatMap (fun parent => Interval.Bisection.parts extra parent.span) := by
        dsimp only [divided]
        rewrite [Split.at_eq, Map.map_drop, spans, actualCount]
        exact Append.drop_length_append _ _
      have firstCells : dividedCells.1 = Piece.models divided.1 := by
        calc
          _ = cells.take count := congrArg Prod.fst Split.at_eq
          _ = (Piece.models pieces).take count := congrArg (fun list => list.take count) cells_eq
          _ = Piece.models (pieces.take count) := (Map.map_take Piece.model pieces count).symm
          _ = _ := congrArg Piece.models (congrArg Prod.fst Split.at_eq).symm
      have laterCells : dividedCells.2 = Piece.models divided.2 := by
        calc
          _ = cells.drop count := congrArg Prod.snd Split.at_eq
          _ = (Piece.models pieces).drop count := congrArg (fun list => list.drop count) cells_eq
          _ = Piece.models (pieces.drop count) := (Map.map_drop Piece.model pieces count).symm
          _ = _ := congrArg Piece.models (congrArg Prod.snd Split.at_eq).symm
      let remaining := partitionPieces extra count count_eq parents divided.2 dividedCells.2 laterCells laterSpans
      refine ⟨⟨⟨⟨divided.1, firstSpans⟩, ⟨dividedCells.1, firstCells⟩⟩, remaining.1⟩, ?_, ?_⟩
      · change divided.1 ++
          (DependentProduct.mapToList parents remaining.1 (fun _ block => block.1.val)).flatten = pieces
        apply (congrArg (List.append divided.1) remaining.2.1).trans
        exact Split.append_parts pieces count
      · change dividedCells.1 ++
          (DependentProduct.mapToList parents remaining.1 (fun _ block => block.2.val)).flatten = cells
        apply (congrArg (List.append dividedCells.1) remaining.2.2).trans
        exact Split.append_parts cells count

/-- Group the supplied actual fine scalar caches under their identical original coarse occurrences.

Both factory equations are erased provenance. The operation computes one
finite descendant count and splits only the supplied Piece and numerical
cell lists. No initial layer, child numerical cell, cofactor observation,
source owner or scalar sample is rebuilt to obtain the ordered partition.
-/
def partition {initial : Piece data actual accuracy} {coarse extra : Nat}
    (parents : Layer initial coarse) (parent_eq : parents = initial.layerAt coarse)
    (fine : Layer initial (coarse + extra)) (fine_eq : fine = initial.layerAt (coarse + extra)) :
    Partition parents fine := by
  have sourceSpans := initial.layerAt_spans coarse
  have finalSpans := initial.layerAt_spans (coarse + extra)
  rewrite [← parent_eq] at sourceSpans
  rewrite [← fine_eq] at finalSpans
  have spans : fine.pieces.map (fun piece => piece.span) =
      parents.pieces.flatMap (fun parent => Interval.Bisection.parts extra parent.span) := by
    apply finalSpans.trans
    rewrite [Interval.Bisection.parts_add, ← sourceSpans]
    exact Flatten.flatMap_map (Interval.Bisection.parts extra) (fun parent => parent.span) parents.pieces
  let count := 2 ^ extra
  exact partitionPieces extra count rfl parents.pieces fine.pieces fine.model.cells fine.model_cells spans

namespace Partition

variable {initial : Piece data actual accuracy} {coarse extra : Nat}
variable {parents : Layer initial coarse} {fine : Layer initial (coarse + extra)}

/-- Read both complete actual cache slices at the same original bounded coarse occurrence. -/
@[expose] def get (partition : Partition parents fine) (index : Fin parents.pieces.length) :=
  DependentProduct.get parents.pieces partition.val index

/-- Retain one original local Layer using the same partitioned fine Piece and numerical-cell caches.

The original coarse/fine certificates derive the local accuracy, count,
width and allowance laws. The numerical model consumes its actual stored
cell slice; it is not reconstructed through equal Piece.model values.
An optional exact parent view changes only the dependent index while
retaining that supplied whole Piece. No reading, source, split,
coefficient or numerical sample is acquired.
-/
def layer (partition : Partition parents fine) (index : Fin parents.pieces.length)
    (parent : {kept : Piece data actual parents.accuracy //
        kept = parents.pieces[index.val]'index.isLt} :=
      ⟨parents.pieces[index.val]'index.isLt, rfl⟩) : Layer parent.val extra := by
  let original : Layer (parents.pieces[index.val]'index.isLt) extra := by
    let retained := partition.get index
    let pieces := retained.1.val
    let model : PathModel := ⟨retained.2.val⟩
    have radii : ∀ amount : Fraction.Rational,
        Geometric.Basic.quarterRadius (Geometric.Basic.quarterRadius amount coarse) extra =
          Geometric.Basic.quarterRadius amount (coarse + extra) := by
      intro amount
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow, pow_add]
      ring1
    have outer : pieces ∈
        DependentProduct.mapToList parents.pieces partition.val (fun _ block => block.1.val) := by
      have occurrence := DependentProduct.get_mapToList parents.pieces partition.val
        (fun _ block => block.1.val) index
      exact Eq.mp (congrArg (fun group => group ∈
        DependentProduct.mapToList parents.pieces partition.val (fun _ block => block.1.val)) occurrence)
          (List.getElem_mem ((DependentProduct.length_mapToList parents.pieces partition.val
            (fun _ block => block.1.val)).symm ▸ index.isLt))
    have original : ∀ piece, piece ∈ pieces → piece ∈ fine.pieces := by
      intro piece member
      exact Eq.mp (congrArg (fun list => piece ∈ list) partition.property.1)
        (mem_flatten_of_mem outer member)
    have parentMember : parents.pieces[index.val]'index.isLt ∈ parents.pieces := List.getElem_mem index.isLt
    exact
      { accuracy := fine.accuracy
        accuracy_eq := fine.accuracy_eq.trans ((radii accuracy.tolerance).symm.trans
          (congrArg (fun amount => Geometric.Basic.quarterRadius amount extra) parents.accuracy_eq.symm))
        pieces
        count := Entry.count (extra := extra) (parent := parents.pieces[index.val]'index.isLt)
          (childAccuracy := fine.accuracy) retained
        widths := by
          intro piece member
          exact (fine.widths piece (original piece member)).trans
            ((radii (initial.span.width ^ 2)).symm.trans
              (congrArg (fun amount => Geometric.Basic.quarterRadius amount extra)
                (parents.widths _ parentMember).symm))
        allowances := by
          intro piece member
          exact (fine.allowances piece (original piece member)).trans
            ((radii initial.cell.allowance).symm.trans
              (congrArg (fun amount => Geometric.Basic.quarterRadius amount extra)
                (parents.allowances _ parentMember).symm))
        model
        model_cells := retained.2.property }
  exact Eq.mp (congrArg (fun kept : Piece data actual parents.accuracy => Layer kept extra)
    parent.property.symm) original
/-- The local original Layer retains the same whole fine accuracy request after exact parent reindexing. -/
theorem layer_accuracy (partition : Partition parents fine) (index : Fin parents.pieces.length)
    (parent : {kept : Piece data actual parents.accuracy //
        kept = parents.pieces[index.val]'index.isLt} :=
      ⟨parents.pieces[index.val]'index.isLt, rfl⟩) :
    (partition.layer index parent).accuracy = fine.accuracy := by
  rcases parent with ⟨parent, equal⟩
  cases equal
  rfl

/-- Exact parent reindexing retains the complete same Piece entries with their original observations. -/
theorem layer_pieces (partition : Partition parents fine) (index : Fin parents.pieces.length)
    (parent : {kept : Piece data actual parents.accuracy //
        kept = parents.pieces[index.val]'index.isLt} :=
      ⟨parents.pieces[index.val]'index.isLt, rfl⟩) :
    HEq (partition.layer index parent).pieces (partition.get index).1.val := by
  rcases parent with ⟨parent, equal⟩
  cases equal
  exact HEq.rfl

/-- The local numerical model consumes the literal stored original CellModel slice after exact parent reindexing. -/
theorem layer_cells (partition : Partition parents fine) (index : Fin parents.pieces.length)
    (parent : {kept : Piece data actual parents.accuracy //
        kept = parents.pieces[index.val]'index.isLt} :=
      ⟨parents.pieces[index.val]'index.isLt, rfl⟩) :
    (partition.layer index parent).model.cells = (partition.get index).2.val := by
  rcases parent with ⟨parent, equal⟩
  cases equal
  rfl

/-- The local original Layer retains the ordered descendant spans of its exact retained parent. -/
theorem layer_spans (partition : Partition parents fine) (index : Fin parents.pieces.length)
    (parent : {kept : Piece data actual parents.accuracy //
        kept = parents.pieces[index.val]'index.isLt} :=
      ⟨parents.pieces[index.val]'index.isLt, rfl⟩) :
    (partition.layer index parent).pieces.map (fun piece => piece.span) =
      Interval.Bisection.parts extra parent.val.span := by
  rcases parent with ⟨parent, equal⟩
  cases equal
  exact (partition.get index).1.property

/-- The original produced partition slice retains the complete local factory's actual pieces.

Only the actual global advance and its fixed-width row decomposition are
used. Equal retained flattening and exact row counts recover the identical
supplied slice; the splitter, source observations and cell factory are not
executed again to obtain it.
-/
private theorem factory_pieces (parents : Layer initial coarse)
    (parent_eq : parents = initial.layerAt coarse) (fine : Layer initial (coarse + extra))
    (fine_eq : fine = initial.layerAt (coarse + extra)) (index : Fin parents.pieces.length) :
    HEq (((partition parents parent_eq fine fine_eq).get index).1.val)
      ((parents.pieces[index.val]'index.isLt).layerAt extra).pieces := by
  have advancing : parents.advance extra = fine :=
    (congrArg (fun layer : Layer initial coarse => layer.advance extra) parent_eq).trans
      ((initial.layerAt_advance coarse extra).trans fine_eq.symm)
  cases advancing
  let selected := partition parents parent_eq (parents.advance extra) fine_eq
  let rows := DependentProduct.mapToList parents.pieces selected.val (fun _ entry => entry.1.val)
  let localPieces := fun parent : Piece data actual parents.accuracy =>
    Eq.mp (congrArg (fun request => List (Piece data actual request))
      (advance_accuracy parents parent extra).symm) (parent.layerAt extra).pieces
  let expected := parents.pieces.map localPieces
  have transported {first last : AccuracyRequest} (same : first = last)
      (pieces : List (Piece data actual first)) :
      (Eq.mp (congrArg (fun request => List (Piece data actual request)) same) pieces).length = pieces.length ∧
        HEq (Eq.mp (congrArg (fun request => List (Piece data actual request)) same) pieces) pieces := by
    cases same
    exact ⟨rfl, HEq.rfl⟩
  have counts : rows.length = expected.length :=
    (DependentProduct.length_mapToList parents.pieces selected.val (fun _ entry => entry.1.val)).trans
      (Map.length_map localPieces parents.pieces).symm
  have rowsCount : ∀ row ∈ rows, row.length = 2 ^ extra :=
    DependentProduct.mapToList_all parents.pieces selected.val (fun _ entry => entry.1.val)
      (fun index entry => Entry.count (extra := extra)
        (parent := parents.pieces[index.val]'index.isLt)
        (childAccuracy := (parents.advance extra).accuracy) entry)
  have expectedCount : ∀ row ∈ expected, row.length = 2 ^ extra := by
    intro row member
    rcases Map.mem_map.mp member with ⟨parent, _member, same⟩
    have count : (localPieces parent).length = 2 ^ extra :=
      (transported (advance_accuracy parents parent extra).symm (parent.layerAt extra).pieces).1.trans
        (parent.layerAt extra).count
    exact same ▸ count
  have factories : (parents.advance extra).pieces = expected.flatten := advance_pieces parents extra
  have flattened : rows.flatten = expected.flatten := selected.property.1.trans factories
  have sameRows : rows = expected :=
    Flatten.eq_of_uniform_lengths (2 ^ extra) rows expected counts rowsCount expectedCount flattened
  have rowBound : index.val < rows.length :=
    (DependentProduct.length_mapToList parents.pieces selected.val (fun _ entry => entry.1.val)).symm ▸ index.isLt
  have expectedBound : index.val < expected.length := (congrArg List.length sameRows) ▸ rowBound
  have actualAt : rows[index.val]'rowBound = (selected.get index).1.val :=
    DependentProduct.get_mapToList parents.pieces selected.val (fun _ entry => entry.1.val) index
  have expectedAt : expected[index.val]'expectedBound = localPieces (parents.pieces[index.val]'index.isLt) :=
    Map.getElem_map localPieces parents.pieces index.val index.isLt expectedBound
  have samePieces : (selected.get index).1.val = localPieces (parents.pieces[index.val]'index.isLt) :=
    actualAt.symm.trans ((getElem_congr sameRows rfl rowBound).trans expectedAt)
  exact (heq_of_eq samePieces).trans
    (transported (advance_accuracy parents (parents.pieces[index.val]'index.isLt) extra).symm
      ((parents.pieces[index.val]'index.isLt).layerAt extra).pieces).2

/-- Whole factory readback of each actual partitioned local layer on the original supplied coarse/fine caches.

The exact quantified proposition retains both supplied Layer parents,
their whole original factory equations, actual bounded occurrence and
optional supplied parent view. It identifies the complete local Layer,
including all Piece sources, requested cells and numerical model.
-/
@[expose] def FactoryReadback {initial : Piece data actual accuracy} {coarse extra : Nat} : Prop :=
  ∀ (parents : Layer initial coarse) (parent_eq : parents = initial.layerAt coarse)
    (fine : Layer initial (coarse + extra)) (fine_eq : fine = initial.layerAt (coarse + extra))
    (index : Fin parents.pieces.length)
    (parent : {kept : Piece data actual parents.accuracy // kept = parents.pieces[index.val]'index.isLt}),
      (partition parents parent_eq fine fine_eq).layer index parent = parent.val.layerAt extra

/-- Every produced retained partition layer is the whole original parent-programme factory at the same extra depth.

The original Layer equality law consumes the same exact request and whole
Piece identities. This is a readback theorem: executable partitioning still
splits the supplied caches once and never rebuilds a local programme.
-/
theorem layer_factory : FactoryReadback (initial := initial) (coarse := coarse) (extra := extra) := by
  intro parents parent_eq fine fine_eq index parent
  rcases parent with ⟨parent, same⟩
  cases same
  let selected := partition parents parent_eq fine fine_eq
  have advancing : parents.advance extra = fine :=
    (congrArg (fun layer : Layer initial coarse => layer.advance extra) parent_eq).trans
      ((initial.layerAt_advance coarse extra).trans fine_eq.symm)
  apply Layer.eq_of_pieces
  · exact (selected.layer_accuracy index).trans
      ((congrArg (fun layer : Layer initial (coarse + extra) => layer.accuracy) advancing).symm.trans
        (advance_accuracy parents (parents.pieces[index.val]'index.isLt) extra))
  · exact (selected.layer_pieces index).trans (factory_pieces parents parent_eq fine fine_eq index)

/-- The original whole fine sample is the ordered finite sum of the same retained numerical cell slices.

The exact original partition flatten equation identifies the complete
supplied model. Original PathModel block additivity reads each stored slice
at its same bounded coarse occurrence without rebuilding any local model.
-/
theorem integralSample_eq_sum (partition : Partition parents fine) :
    fine.model.integralSample =
      FiniteSum.Fin.sumFin (fun index : Fin parents.pieces.length =>
        (PathModel.mk (partition.get index).2.val).integralSample) := by
  let cells := DependentProduct.mapToList parents.pieces partition.val (fun _ block => block.2.val)
  let blocks := fun index : Fin cells.length => cells[index.val]'index.isLt
  have enumeration : List.ofFn blocks = cells := Data.List.OfFn.Basic.ofFn_getElem cells
  have original := congrArg (fun cells : List CellModel => (PathModel.mk cells).integralSample)
    partition.property.2
  have materialized := congrArg (fun groups : List (List CellModel) =>
    (PathModel.mk groups.flatten).integralSample) enumeration
  have countEqual : parents.pieces.length = cells.length :=
    (DependentProduct.length_mapToList parents.pieces partition.val (fun _ block => block.2.val)).symm
  have readback : ∀ index : Fin parents.pieces.length,
      (PathModel.mk (blocks (Fin.cast countEqual index))).integralSample =
        (PathModel.mk (partition.get index).2.val).integralSample := by
    intro index
    exact congrArg (fun cells : List CellModel => (PathModel.mk cells).integralSample)
      (DependentProduct.get_mapToList parents.pieces partition.val (fun _ block => block.2.val) index)
  calc
    fine.model.integralSample = (PathModel.mk cells.flatten).integralSample := original.symm
    _ = (PathModel.mk (List.ofFn blocks).flatten).integralSample := materialized.symm
    _ = FiniteSum.Fin.sumFin (fun index => (PathModel.mk (blocks index)).integralSample) :=
      PathModel.integralSample_flatten_ofFn blocks
    _ = FiniteSum.Fin.sumFin (fun index : Fin parents.pieces.length =>
        (PathModel.mk (blocks (Fin.cast countEqual index))).integralSample) :=
      (FiniteSum.Fin.sumFin_cast countEqual
        (fun index => (PathModel.mk (blocks index)).integralSample)).symm
    _ = _ := FiniteSum.Fin.sumFin_congr readback

end Partition

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
