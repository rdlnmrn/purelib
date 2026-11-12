module

import Purelib.Data.Rat.Interval.Bisection
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Piece
public import Purelib.Data.List.DependentProduct
import Purelib.Algebra.Quadratic.Pair.Polynomial
public import Purelib.Integration.Polynomial.Gaussian.Path.Uniform
import Purelib.Data.List.Map
import Purelib.Data.Nat.BinaryNormalization
import Purelib.Data.Nat.Subtraction
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-! # Cached dyadic layers of an original regular parallel differential -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Data.List
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Approximation
open Purelib.Approximation.Rational

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : WaistBounds site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

set_option genInjectivity false in
/-- An ordered dyadic layer retaining its original regular parallel pieces and their cached numerical model.

The initial piece and finite depth remain indices. Exact count, squared-width
and allowance equations describe these same pieces; the model caches their
original readback without preparing their owners or observations again.
-/
structure Layer {initialAccuracy : AccuracyRequest}
    (initial : Piece data actual initialAccuracy) (depth : Nat) where
  /-- The actual common residual request at this layer. -/
  accuracy : AccuracyRequest
  /-- The request is the initial request divided by the original finite power of four. -/
  accuracy_eq : accuracy.tolerance = Geometric.Basic.quarterRadius initialAccuracy.tolerance depth
  /-- The actual retained ordered pieces at this residual request. -/
  pieces : List (Piece data actual accuracy)
  /-- The exact original dyadic piece count. -/
  count : pieces.length = 2 ^ depth
  /-- Every retained span has the original squared-width quarter radius. -/
  widths : ∀ piece ∈ pieces,
    piece.span.width ^ 2 = Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth
  /-- Every retained cell has the original allowance quarter radius. -/
  allowances : ∀ piece ∈ pieces,
    piece.cell.allowance = Geometric.Basic.quarterRadius initial.cell.allowance depth
  /-- The cached numerical model of these same original pieces. -/
  model : Basic.PathModel
  /-- The cache reads exactly the retained original cells in their same order. -/
  model_cells : model.cells = Piece.models pieces

constructive_injectivity Layer

namespace Layer

variable {initial : Piece data actual accuracy} {depth : Nat}

/-- Transport the same complete refinement layer along equality of its entire original prepared quarter.

The original initial piece, ordered sampled pieces, common accuracy and
cached numerical model remain literal. This changes only their quarter
indices and retains all source observations and refinement certificates.
-/
@[expose] def transport (layer : Layer initial depth)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    Layer (initial.transport equal) depth := by
  cases equal
  exact layer

/-- Whole-quarter transport retains the complete original refinement layer. -/
theorem transport_heq (layer : Layer initial depth)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    HEq (layer.transport equal) layer := by
  cases equal
  rfl

/-- Whole-quarter transport preserves the original complete accuracy request. -/
theorem transport_accuracy (layer : Layer initial depth)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    (layer.transport equal).accuracy = layer.accuracy := by
  cases equal
  rfl

/-- Whole-quarter transport preserves the exact original ordered numerical model. -/
theorem transport_model (layer : Layer initial depth)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    (layer.transport equal).model = layer.model := by
  cases equal
  rfl

/-- Whole-quarter transport retains every original ordered sampled piece and its certificates. -/
theorem transport_pieces (layer : Layer initial depth)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    HEq (layer.transport equal).pieces layer.pieces := by
  cases equal
  rfl

/-- Whole-quarter transport preserves the exact original ordered scalar span row. -/
theorem transport_spans (layer : Layer initial depth)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    (layer.transport equal).pieces.map (fun piece => piece.span) = layer.pieces.map (fun piece => piece.span) := by
  cases equal
  rfl

/-- Whole-quarter transport preserves the actual original piece count. -/
theorem transport_count (layer : Layer initial depth)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    (layer.transport equal).pieces.length = layer.pieces.length := by
  cases equal
  rfl

/-- The same bounded ordinal reads the identical original piece after whole-quarter transport. -/
theorem transport_get (layer : Layer initial depth)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target)
    (index : Fin layer.pieces.length) :
    HEq ((layer.transport equal).pieces[index.val]'(by
      rewrite [layer.transport_count equal]
      exact index.isLt)) (layer.pieces[index.val]'index.isLt) := by
  cases equal
  rfl

/-- A retained ordered piece bank with the complete original reweight-factory equation.

The supplied list may come from completed coefficient-request rows. Its
original source Readings, observations, intervals and coefficient Models
remain the actual data, with no second construction of those cache values.
-/
@[expose] def ReweightedPieces (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) : Type 1 :=
  {pieces : List (Piece nextData actual layer.accuracy) //
    pieces = layer.pieces.map (fun piece => piece.reweight nextData)}

/-- Complete cached coefficient Models and their actual original bounded scalar occurrences.

The dependent product retains each whole original Piece parent beside its
actual Model. The two equations certify the original ordinal and complete
reweight result without recovering the parent through a list-prefix lookup.
-/
@[expose] def ReweightedCells (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) : Type 1 :=
  DependentProduct layer.pieces (fun ordinal =>
    Σ original : {piece : Piece data actual layer.accuracy //
        piece = layer.pieces[ordinal.val]'ordinal.isLt},
      {model : Cells.Model (span := original.val.span) nextData original.val.source layer.accuracy //
        model = original.val.cell.reweight nextData})

/-- Attach retained actual coefficient Models to their original whole pieces in one ordered traversal.

Only Piece containers and a list spine are allocated. Each Model, source
Reading and cofactor observation is the same supplied cache; no coefficient
Model or original reweight factory is executed by this operation.
-/
def reweightedPieces (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential)
    (models : ReweightedCells layer nextData) : ReweightedPieces layer nextData := by
  let pieces := DependentProduct.mapToList layer.pieces models (fun _ entry =>
    Piece.ofCell entry.1.val.within entry.2.val)
  have same : pieces = DependentProduct.mapToList layer.pieces models
      (fun ordinal _entry => (layer.pieces[ordinal.val]'ordinal.isLt).reweight nextData) := by
    apply DependentProduct.mapToList_congr
    intro ordinal entry
    exact (congrArg (fun model => Piece.ofCell entry.1.val.within model) entry.2.property).trans
      (congrArg (fun original : Piece data actual layer.accuracy => original.reweight nextData) entry.1.property)
  exact ⟨pieces, same.trans (DependentProduct.mapToList_items layer.pieces models
    (fun piece => piece.reweight nextData))⟩

/-- Attaching retained Models preserves exactly the original bounded scalar occurrence count. -/
theorem reweightedPieces_count (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential)
    (models : ReweightedCells layer nextData) :
    (layer.reweightedPieces nextData models).val.length = layer.pieces.length := by
  exact DependentProduct.length_mapToList layer.pieces models (fun _ entry =>
    Piece.ofCell entry.1.val.within entry.2.val)

/-- The same bounded occurrence reads the actual whole Model cache attached to its retained original Piece. -/
theorem reweightedPieces_get (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential)
    (models : ReweightedCells layer nextData) (ordinal : Fin layer.pieces.length) :
    (layer.reweightedPieces nextData models).val[ordinal.val]'
        ((layer.reweightedPieces_count nextData models).symm ▸ ordinal.isLt) =
      Piece.ofCell (DependentProduct.get layer.pieces models ordinal).1.val.within
        (DependentProduct.get layer.pieces models ordinal).2.val := by
  exact DependentProduct.get_mapToList layer.pieces models
    (fun _ entry => Piece.ofCell entry.1.val.within entry.2.val) ordinal

/-- Reweight an actual completed layer while retaining its exact accuracy, spans, Readings and observations.

One ordered traversal constructs the new scalar coefficients and allowances.
No midpoint Reading, cofactor sample or geometric preparation is repeated;
the numerical model reads these same reweighted pieces.
-/
@[expose] def reweight (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential)
    (supplied : optParam (Option (ReweightedPieces layer nextData)) none) :
    Layer (initial.reweight nextData) depth :=
  let pieces := match supplied with
    | none => layer.pieces.map (fun piece => piece.reweight nextData)
    | some cached => cached.val
  have pieces_eq : pieces = layer.pieces.map (fun piece => piece.reweight nextData) := by
    cases supplied with
    | none => rfl
    | some cached => exact cached.property
  { accuracy := layer.accuracy
    accuracy_eq := layer.accuracy_eq
    pieces
    count := by
      rewrite [pieces_eq, Map.length_map]
      exact layer.count
    widths := by
      intro piece member
      rewrite [pieces_eq] at member
      rcases Map.mem_map.mp member with ⟨original, originalMember, equal⟩
      rewrite [← equal]
      exact layer.widths original originalMember
    allowances := by
      intro piece member
      rewrite [pieces_eq] at member
      rcases Map.mem_map.mp member with ⟨original, originalMember, equal⟩
      rewrite [← equal, (original.reweight nextData).cell.allowance_eq,
        (initial.reweight nextData).cell.allowance_eq]
      change Bounds.signedChartSlope nextData * original.span.width ^ 2 +
          2 * Bounds.residualSlope nextData * layer.accuracy.tolerance =
        Geometric.Basic.quarterRadius
          (Bounds.signedChartSlope nextData * initial.span.width ^ 2 +
            2 * Bounds.residualSlope nextData * accuracy.tolerance) depth
      rewrite [layer.widths original originalMember, layer.accuracy_eq]
      simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
      ring1
    model := ⟨Piece.models pieces⟩
    model_cells := rfl }

/-- Reweighting forwards the complete common accuracy request of the original completed layer. -/
theorem reweight_accuracy (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (layer.reweight nextData).accuracy = layer.accuracy := (rfl)

/-- The supplied-piece branch returns that complete same list cache as its actual Layer pieces. -/
theorem reweight_supplied_pieces (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential)
    (supplied : ReweightedPieces layer nextData) :
    (layer.reweight nextData (some supplied)).pieces = supplied.val := (rfl)

/-- Reweighting retains every complete original scalar piece through the existing piece operation in its same order. -/
theorem reweight_pieces (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (layer.reweight nextData).pieces = layer.pieces.map (fun piece => piece.reweight nextData) := (rfl)

/-- Reweighting retains the actual original ordered mesh rather than reconstructing a dyadic partition. -/
theorem reweight_spans (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (layer.reweight nextData).pieces.map (fun piece => piece.span) = layer.pieces.map (fun piece => piece.span) := by
  change (layer.pieces.map (fun piece => piece.reweight nextData)).map (fun piece => piece.span) = _
  exact Map.map_map (fun piece => piece.span) (fun piece => piece.reweight nextData) layer.pieces

/-- The same bounded occurrence reads the whole original piece after its differential is reweighted. -/
theorem reweight_get (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) (ordinal : Fin layer.pieces.length) :
    (layer.reweight nextData).pieces[ordinal.val]'(by
        change ordinal.val < (layer.pieces.map (fun piece => piece.reweight nextData)).length
        rewrite [Map.length_map]
        exact ordinal.isLt) =
      (layer.pieces[ordinal.val]'ordinal.isLt).reweight nextData :=
  Map.getElem_map (fun piece => piece.reweight nextData) layer.pieces ordinal.val ordinal.isLt _

/-- The actual retained scalar-root readings have a uniform geometric radius bound at this same original layer.

The original layer accuracy equation and each same cached cofactor sample
pay the bound. Neither chart-time geometry nor a new root observation is
chosen to establish decay.
-/
theorem rootReading_radius_le (layer : Layer initial depth)
    (piece : Piece data actual layer.accuracy) :
    piece.cell.rootReading.radius ≤ Geometric.Basic.quarterRadius
      (((25 / 4) * Data.Gaussian.Norm.Basic.normSq (halfGap site parameter)) * accuracy.tolerance) depth := by
  have bound := piece.cell.rootReading_radius_uniform
  rewrite [layer.accuracy_eq] at bound
  exact bound.trans_eq (by
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    ring1)

/-- The original dyadic count guarantees a nonempty retained piece list at every finite depth. -/
theorem nonempty (layer : Layer initial depth) : 0 < layer.pieces.length := by
  rewrite [layer.count]
  exact (Nat.zero_lt_succ depth).trans_le (Data.Nat.BinaryNormalization.succ_le_two_pow depth)

/-- Every actual factory-mesh source lies in the initial span and strictly before its upper endpoint.

The exact retained span row identifies its original dyadic partition.
Containment and strict positive child width follow from those same finite
parts, including the first occurrence without an independent domain input.
-/
theorem lower_within (layer : Layer initial depth)
    (spans : layer.pieces.map (fun piece => piece.span) = Interval.Bisection.parts depth initial.span)
    (proper : initial.span.lower < initial.span.upper)
    (piece : Piece data actual layer.accuracy) (member : piece ∈ layer.pieces) :
    initial.span.lower ≤ piece.span.lower ∧ piece.span.lower < initial.span.upper := by
  have partMember : piece.span ∈ Interval.Bisection.parts depth initial.span := by
    rewrite [← spans]
    exact Map.mem_map.mpr ⟨piece, member, rfl⟩
  have lower := Interval.Bisection.parts_subset depth initial.span partMember
    (show piece.span.Contains piece.span.lower from ⟨Fraction.Order.Basic.le_refl _, piece.span.valid⟩)
  have upper := Interval.Bisection.parts_subset depth initial.span partMember
    (show piece.span.Contains piece.span.upper from ⟨piece.span.valid, Fraction.Order.Basic.le_refl _⟩)
  have pieceProper := Interval.Bisection.parts_proper depth initial.span proper partMember
  exact ⟨lower.1, pieceProper.trans_le upper.2⟩

/-- Select the final retained original piece by its actual finite list index. -/
@[expose] def lastNode (layer : Layer initial depth) : Fin layer.pieces.length :=
  ⟨layer.pieces.length - 1, Nat.sub_lt layer.nonempty (by decide +kernel)⟩

/-- The selected final original piece's successor is exactly the actual retained piece count. -/
theorem lastNode_succ (layer : Layer initial depth) : (layer.lastNode).val + 1 = layer.pieces.length :=
  Data.Nat.Subtraction.sub_add_cancel layer.nonempty

/-- Retain the original singleton layer with its identical complete piece and numerical cell. -/
@[expose] def ofPiece (initial : Piece data actual accuracy) : Layer initial 0 :=
  { accuracy
    accuracy_eq := by
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
      rfl
    pieces := [initial]
    count := rfl
    widths := by
      intro piece member
      cases Membership.mem_singleton.mp member
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
      rfl
    allowances := by
      intro piece member
      cases Membership.mem_singleton.mp member
      rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, pow_zero, Fraction.Field.mul_one_direct]
      rfl
    model := ⟨[initial.model]⟩
    model_cells := rfl }

/-- Reweighting the original singleton layer gives the whole original singleton factory. -/
theorem reweight_ofPiece (initial : Piece data actual accuracy)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (ofPiece initial).reweight nextData = ofPiece (initial.reweight nextData) := (rfl)

/-- Assemble the next cached layer from these exact already completed midpoint splits.

The supplied steps retain each original split. Their child pieces and model
are computed once here, and all certificates consume those same caches.
-/
@[expose] def next (layer : Layer initial depth) (steps : Steps layer.pieces) : Layer initial (depth + 1) :=
  let pieces := steps.children
  let model : Basic.PathModel := ⟨Piece.models pieces⟩
  { accuracy := layer.accuracy.quarter
    accuracy_eq := by
      rewrite [AccuracyRequest.quarter_tolerance, layer.accuracy_eq,
        Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ, Fraction.Field.div_eq_mul_inv_direct]
      have quarter : (1 / 4 : Fraction.Rational) = (4 : Fraction.Rational)⁻¹ := by decide +kernel
      rewrite [quarter]
      ring1
    pieces
    count := by
      rewrite [Steps.children_length, layer.count, Nat.pow_succ]
      exact Nat.mul_comm _ _
    widths := by
      intro piece member
      have widths := steps.children_bounds
        (Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth)
        (Geometric.Basic.quarterRadius initial.cell.allowance depth)
        (fun parent parentMember => ⟨layer.widths parent parentMember, layer.allowances parent parentMember⟩)
        piece member
      rewrite [widths.1, Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ, Fraction.Field.div_eq_mul_inv_direct]
      have quarter : (1 / 4 : Fraction.Rational) = (4 : Fraction.Rational)⁻¹ := by decide +kernel
      rewrite [quarter]
      ring1
    allowances := by
      intro piece member
      have allowances := steps.children_bounds
        (Geometric.Basic.quarterRadius (initial.span.width ^ 2) depth)
        (Geometric.Basic.quarterRadius initial.cell.allowance depth)
        (fun parent parentMember => ⟨layer.widths parent parentMember, layer.allowances parent parentMember⟩)
        piece member
      rewrite [allowances.2, Geometric.Basic.quarterRadius_eq_mul_pow,
        Geometric.Basic.quarterRadius_eq_mul_pow, pow_succ, Fraction.Field.div_eq_mul_inv_direct]
      have quarter : (1 / 4 : Fraction.Rational) = (4 : Fraction.Rational)⁻¹ := by decide +kernel
      rewrite [quarter]
      ring1
    model
    model_cells := rfl }

/-- The original layer's numerical model is determined by its exact accuracy and complete piece bank. -/
theorem eq_of_pieces (first last : Layer initial depth)
    (sameAccuracy : first.accuracy = last.accuracy) (samePieces : HEq first.pieces last.pieces) :
    first = last := by
  cases first with
  | mk firstAccuracy firstAccuracyEq firstPieces firstCount firstWidths firstAllowances firstModel firstModelEq =>
      cases last with
      | mk lastAccuracy lastAccuracyEq lastPieces lastCount lastWidths lastAllowances lastModel lastModelEq =>
          cases sameAccuracy
          have same := eq_of_heq samePieces
          cases same
          cases firstModel with
          | mk firstCells =>
              cases lastModel with
              | mk lastCells =>
                  cases firstModelEq
                  cases lastModelEq
                  rfl

/-- Supplying a certified actual piece bank preserves the complete original omitted-cache reweight result. -/
theorem reweight_supplied (layer : Layer initial depth)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential)
    (supplied : ReweightedPieces layer nextData) :
    layer.reweight nextData (some supplied) = layer.reweight nextData := by
  apply eq_of_pieces (layer.reweight nextData (some supplied)) (layer.reweight nextData) rfl
  exact heq_of_eq supplied.property

/-- Reweighting a completed next layer consumes the same reweighted cached midpoint splits. -/
theorem reweight_next (layer : Layer initial depth) (steps : Steps layer.pieces)
    {nextRadicand : Pair.Polynomial.Coefficients} {nextDifferential : OddPowerDifferential nextRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (layer.next steps).reweight nextData = (layer.reweight nextData).next (steps.reweight nextData) := by
  apply eq_of_pieces ((layer.next steps).reweight nextData)
    ((layer.reweight nextData).next (steps.reweight nextData)) rfl
  change HEq (steps.children.map (fun piece => piece.reweight nextData)) (steps.reweight nextData).children
  exact heq_of_eq (steps.reweight_children nextData).symm

/-- The original next layer retains exactly the midpoint-bisected span bank of its supplied actual cached pieces. -/
theorem next_spans (layer : Layer initial depth) (steps : Steps layer.pieces) :
    (layer.next steps).pieces.map (fun piece => piece.span) =
      Interval.Bisection.refine (layer.pieces.map (fun piece => piece.span)) :=
  steps.children_spans

/-- Extend this same completed scalar layer using only its subsequent original midpoint splits.

The zero-step branch returns the literal supplied layer. Each successor
retains the previously completed layer before computing its actual Steps
once and passing those same splits to the original next constructor.
No earlier scalar Piece, source observation or preparation is rebuilt.
-/
@[expose] def advance (layer : Layer initial depth) : (extra : Nat) → Layer initial (depth + extra)
  | 0 => layer
  | extra + 1 =>
      let previous := advance layer extra
      let steps := Steps.build previous.pieces
      previous.next steps

/-- Extending by zero retains the complete supplied original layer literally. -/
theorem advance_zero (layer : Layer initial depth) : layer.advance 0 = layer := (rfl)

/-- The cached models carry the original compatible comparison of these same completed splits. -/
def compatible (layer : Layer initial depth) (steps : Steps layer.pieces) :
    Basic.PathModel.CompatibleConstantPathRefinement layer.model.cells (layer.next steps).model.cells := by
  rewrite [layer.model_cells]
  exact steps.compatible

/-- Transporting the model cache preserves the exact original ordered comparison cells. -/
theorem comparisonCells_eq (layer : Layer initial depth) (steps : Steps layer.pieces) :
    CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonCells (layer.compatible steps) =
      CompatibleRefinement.PathModel.CompatibleConstantPathRefinement.comparisonCells steps.compatible := by
  cases layer with
  | mk accuracy accuracy_eq pieces count widths allowances model model_cells =>
      cases model with
      | mk cells =>
          cases model_cells
          rfl

/-- The exact finite piece count is also the count of the same cached numerical cells. -/
theorem model_count (layer : Layer initial depth) : layer.model.cells.length = 2 ^ depth := by
  rewrite [layer.model_cells]
  exact (Map.length_map ..).trans layer.count

/-- The cached model's aggregate allowance is bounded by the original squared span width and decaying allowance. -/
theorem aggregateAllowance_le (layer : Layer initial depth) :
    layer.model.aggregateAllowance ≤ initial.span.width ^ 2 *
      Geometric.Basic.quarterRadius initial.cell.allowance depth := by
  apply Basic.PathModel.uniform_aggregateAllowance_le layer.model depth _ _
    (Fraction.Order.Arithmetic.sq_nonneg_direct _) layer.model_count
  intro model member
  rewrite [layer.model_cells] at member
  rcases Map.mem_map.mp member with ⟨piece, pieceMember, rfl⟩
  constructor
  · rewrite [piece.displacement_sq, layer.widths piece pieceMember]
    exact Fraction.Order.Basic.le_refl _
  · exact (layer.allowances piece pieceMember).le

end Layer

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
