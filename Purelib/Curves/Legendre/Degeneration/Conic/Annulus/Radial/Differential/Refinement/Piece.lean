module

import Purelib.Data.Rat.Interval.Bisection
import Purelib.Geometry.Gaussian.UnitCircle.Stereographic.Tangent
import Purelib.Polynomial.Dense.Gaussian.Basic

public import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement.Split
import Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Cells
import Purelib.Algebra.Quadratic.Pair.Polynomial
import Purelib.Data.List.Membership
import Purelib.Data.List.Map
import Purelib.Data.List.Append
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Data.Rat.Fraction.Field

/-! # Ordered actual chart cells on one retained regular parallel quarter -/

public section

namespace Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement

open Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Waist.Differential.Bounds renaming Data → WaistBounds

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat
open Purelib.Geometry.Gaussian.UnitCircle.Quarter (UnitCircuitQuarter)
open Purelib.Geometry.Gaussian
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.Riemann.RootContinuation
open Purelib.Integration.Polynomial.Gaussian.Path
open Purelib.Approximation

open Purelib.Algebra.Quadratic (Pair)

variable {radicand : Pair.Polynomial.Coefficients}
variable {targetRadicand : Pair.Polynomial.Coefficients}

set_option genInjectivity false in
/-- One actual retained scalar cell and its full requested-time source on an identical prepared parallel quarter.

The original quarter, differential budget and accuracy request remain
indices. The retained span containment pays all later midpoint queries of
that same preparation; the cell consumes this piece's identical source.
-/
structure Piece (data : WaistBounds site parameter differential)
    {positive : (0 : Fraction.Rational) < 2}
    (actual : Transport.Quarter site parameter 2 quarter positive) (accuracy : AccuracyRequest) where
  /-- The exact original closed rational chart span. -/
  span : Interval.Bounds
  /-- Every point of the original span lies in the same original prepared geometric quarter. -/
  within : ∀ time, span.Contains time → FixedRootBoxPath.Inside time
  /-- The actual complete requested-time source at the original lower chart endpoint. -/
  source : Transport.Reading actual span.lower (within span.lower ⟨Fraction.Order.Basic.le_refl _, span.valid⟩)
  /-- The paid original scalar cell consumes that same complete source and retained request. -/
  cell : Cells.Model data source accuracy

constructive_injectivity Piece

namespace Piece

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : WaistBounds site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

/-- Retain a supplied paid cell with its identical original chart span and complete requested-time geometric source. -/
@[expose] def ofCell {span : Interval.Bounds} {inside : FixedRootBoxPath.Inside span.lower}
    {source : Transport.Reading actual span.lower inside}
    (within : ∀ time, span.Contains time → FixedRootBoxPath.Inside time)
    (cell : Cells.Model data source accuracy) : Piece data actual accuracy :=
  { span, within, source, cell }

/-- Read the original cached scalar chart-integration container of the same retained piece. -/
@[expose] def model (piece : Piece data actual accuracy) := piece.cell.cell

/-- The original chart cell's displacement quadrance is exactly its retained squared chart width. -/
theorem displacement_sq (piece : Piece data actual accuracy) :
    normSq piece.model.displacement = piece.span.width ^ 2 := by
  rewrite [Purelib.Data.Gaussian.Norm.Basic.normSq_eq_canonical]
  change (piece.span.upper - piece.span.lower) * (piece.span.upper - piece.span.lower) +
    (0 - 0) * (0 - 0) = (piece.span.upper - piece.span.lower) ^ 2
  ring1

/-- Whole-span containment in the original quarter bounds the same retained squared chart width by one. -/
theorem width_sq_le_one (piece : Piece data actual accuracy) :
    piece.span.width ^ 2 ≤ 1 := by
  have first := piece.within piece.span.lower ⟨Fraction.Order.Basic.le_refl _, piece.span.valid⟩
  have last := piece.within piece.span.upper ⟨piece.span.valid, Fraction.Order.Basic.le_refl _⟩
  have timeEqual : piece.span.upper = piece.span.lower + piece.span.width := by
    change piece.span.upper = piece.span.lower + (piece.span.upper - piece.span.lower)
    ring1
  have shifted : FixedRootBoxPath.Inside (piece.span.lower + piece.span.width) := timeEqual ▸ last
  have unit := UnitCircle.Stereographic.Tangent.increment_unit first shifted
  rewrite [UnitCircle.Stereographic.Tangent.increment_normSq] at unit
  exact unit

/-- Transport this same complete scalar piece along equality of its whole original prepared quarter.

The exact original equality reindexes the actual retained source, sampled
cell and span certificate together. No geometric source, numerical sample
or replacement cell is constructed.
-/
@[expose] def transport (piece : Piece data actual accuracy)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    Piece data target accuracy := by
  cases equal
  exact piece

/-- Whole-quarter transport preserves the entire original piece heterogeneously. -/
theorem transport_heq (piece : Piece data actual accuracy)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    HEq (piece.transport equal) piece := by
  cases equal
  rfl

/-- Whole-quarter transport keeps the complete original sampled source. -/
theorem transport_source (piece : Piece data actual accuracy)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    HEq (piece.transport equal).source piece.source := by
  cases equal
  rfl

/-- Whole-quarter transport keeps the complete original paid scalar cell. -/
theorem transport_cell (piece : Piece data actual accuracy)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    HEq (piece.transport equal).cell piece.cell := by
  cases equal
  rfl

/-- Whole-quarter transport keeps the identical original closed span and its endpoint-validity certificate. -/
theorem transport_span (piece : Piece data actual accuracy)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    (piece.transport equal).span = piece.span := by
  cases equal
  rfl

/-- Whole-quarter transport preserves the identical original numerical model. -/
theorem transport_model (piece : Piece data actual accuracy)
    {target : Transport.Quarter site parameter 2 quarter positive} (equal : actual = target) :
    (piece.transport equal).model = piece.model := by
  cases equal
  rfl

/-- Read the exact original numerical cells in their retained piece order. -/
@[expose] def models (pieces : List (Piece data actual accuracy)) :
    List Purelib.Integration.Polynomial.Gaussian.Cell.Basic.CellModel := pieces.map model

/-- Retain the actual left and right children of the identical already completed midpoint split. -/
@[expose] def children (piece : Piece data actual accuracy) (split : Split piece.cell piece.within) :
    List (Piece data actual accuracy.quarter) :=
  [ofCell (fun time contained => piece.within time (Interval.Bisection.leftHalf_subset contained)) split.left,
    ofCell (fun time contained => piece.within time (Interval.Bisection.rightHalf_subset contained)) split.right]

/-- The retained child pieces read exactly the numerical cells of that same original split. -/
theorem children_models (piece : Piece data actual accuracy) (split : Split piece.cell piece.within) :
    models (children piece split) = split.children.cells := rfl

/-- The two retained actual child spans are exactly the original ordered midpoint halves. -/
theorem children_spans (piece : Piece data actual accuracy) (split : Split piece.cell piece.within) :
    (children piece split).map (fun child => child.span) =
      [Interval.Bisection.leftHalf piece.span, Interval.Bisection.rightHalf piece.span] := rfl

/-- Each actual midpoint child has exactly one quarter of the original squared width and paid local allowance. -/
theorem children_bounds (piece : Piece data actual accuracy) (split : Split piece.cell piece.within)
    (child : Piece data actual accuracy.quarter) (member : child ∈ children piece split) :
    child.span.width ^ 2 = piece.span.width ^ 2 / 4 ∧ child.cell.allowance = piece.cell.allowance / 4 := by
  have halfSquare : (piece.span.width / 2) ^ 2 = piece.span.width ^ 2 / 4 := by
    rewrite [Fraction.Field.div_eq_mul_inv_direct, Fraction.Field.div_eq_mul_inv_direct,
      Fraction.Field.mul_pow_direct]
    have inverseTwoSquare : ((2 : Fraction.Rational)⁻¹) ^ 2 = (4 : Fraction.Rational)⁻¹ := by decide +kernel
    rewrite [inverseTwoSquare]
    rfl
  cases member with
  | head =>
      constructor
      · change (Interval.Bisection.leftHalf piece.span).width ^ 2 = _
        rewrite [Interval.Bisection.leftHalf_width]
        exact halfSquare
      · exact split.left_allowance_eq
  | tail _ member =>
      cases member with
      | head =>
          constructor
          · change (Interval.Bisection.rightHalf piece.span).width ^ 2 = _
            rewrite [Interval.Bisection.rightHalf_width]
            exact halfSquare
          · exact split.right_allowance_eq
      | tail _ impossible => nomatch impossible

/-- Reweight a retained piece while consuming its complete identical source query and paid cofactor observation. -/
@[expose] def reweight (piece : Piece data actual accuracy) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : WaistBounds site parameter nextDifferential) : Piece nextData actual accuracy :=
  ofCell piece.within (piece.cell.reweight nextData)

/-- Reweighting by the identical original budget retains the complete Piece and its actual Model cache.

The original span, domain proof and Reading remain the same fields. The
whole retained Model identity uses its original center and allowance
certificates rather than identifying separately sampled observations.
-/
theorem reweight_self (piece : Piece data actual accuracy) : piece.reweight data = piece := by
  cases piece with
  | mk span within source cell =>
      change ofCell within (cell.reweight data) = ofCell within cell
      rewrite [cell.reweight_self]
      rfl

/-- Reweighting retains the full actual requested-time source of the original piece. -/
theorem reweight_source (piece : Piece data actual accuracy) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (piece.reweight nextData).source = piece.source := rfl

/-- Reweighting preserves the original complete interval and its occurrence in the prepared quarter. -/
theorem reweight_span (piece : Piece data actual accuracy) {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (piece.reweight nextData).span = piece.span := (rfl)

end Piece

set_option genInjectivity false in
/-- Actual cached midpoint splits following the original ordered scalar cells of one identical prepared quarter.

Each head retains the completed split of its exact original parent. The
tail retains the same original order; child readback and comparisons never
repeat geometric preparation or root sampling.
-/
inductive Steps {data : WaistBounds site parameter differential}
    {positive : (0 : Fraction.Rational) < 2}
    {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest} :
    List (Piece data actual accuracy) → Type 1
  /-- The empty original path needs no completed midpoint splits. -/
  | nil : Steps []
  /-- Retain the complete actual head split and completed tail steps in their original order. -/
  | cons {parent : Piece data actual accuracy} {parents}
      (split : Split parent.cell parent.within) (tail : Steps parents) : Steps (parent :: parents)

constructive_injectivity Steps

namespace Steps

variable {site : Fin 2} {parameter : Canonical} {differential : OddPowerDifferential radicand}
variable {data : WaistBounds site parameter differential}
variable {quarter : UnitCircuitQuarter} {positive : (0 : Fraction.Rational) < 2}
variable {actual : Transport.Quarter site parameter 2 quarter positive} {accuracy : AccuracyRequest}

/-- Compute and retain each original midpoint split once in the original parent order. -/
@[expose] def build : (parents : List (Piece data actual accuracy)) → Steps parents
  | [] => .nil
  | parent :: parents => .cons (Split.build parent.cell parent.within) (build parents)

/-- Read the ordered actual child pieces from these identical already completed splits. -/
@[expose] def children : {parents : List (Piece data actual accuracy)} →
    Steps parents → List (Piece data actual accuracy.quarter)
  | _, .nil => []
  | parent :: _, .cons split tail => Piece.children parent split ++ children tail

/-- The actual original split factory reads the ordered concatenation of its identical per-parent children.

The equality describes the whole retained child list. Structural recursion
uses the same original split at the supplied head and the literal parent
tail; the list-valued function is only this factory's readback specification.
-/
theorem children_build : (parents : List (Piece data actual accuracy)) →
    (build parents).children =
      parents.flatMap (fun parent => parent.children (Split.build parent.cell parent.within))
  | [] => rfl
  | parent :: parents =>
      congrArg (List.append (parent.children (Split.build parent.cell parent.within)))
        (children_build parents)

/-- Exact request transport commutes with the same original split factory's whole child list.

Both complete parent and child pieces retain their original sources,
coefficient caches and containment proofs. Only the supplied equality of
whole accuracy requests changes their dependent types.
-/
theorem children_transport {nextAccuracy : AccuracyRequest} (same : accuracy = nextAccuracy)
    (parents : List (Piece data actual accuracy)) :
    (build (Eq.mp (congrArg (fun request => List (Piece data actual request)) same) parents)).children =
      Eq.mp (congrArg (fun request => List (Piece data actual request))
        (congrArg AccuracyRequest.quarter same)) (build parents).children := by
  cases same
  rfl

/-- Derive the existing compatible refinement certificate on the exact original parent and child cells. -/
@[expose] def compatible : {parents : List (Piece data actual accuracy)} →
    (steps : Steps parents) → Basic.PathModel.CompatibleConstantPathRefinement
      (Piece.models parents) (Piece.models steps.children)
  | _, .nil => .nil
  | _, .cons split tail => .cons split.comparison (compatible tail)

/-- The spans of the actual retained child bank are the ordered bisection of the identical original parent spans. -/
theorem children_spans : {parents : List (Piece data actual accuracy)} → (steps : Steps parents) →
    steps.children.map (fun piece => piece.span) =
      Interval.Bisection.refine (parents.map (fun piece => piece.span))
  | _, .nil => rfl
  | parent :: _, .cons split tail => by
      change (Piece.children parent split ++ tail.children).map (fun piece => piece.span) = _
      rewrite [Data.List.Map.map_append, Piece.children_spans, children_spans tail]
      rfl

/-- Every completed midpoint split contributes exactly two original child pieces. -/
theorem children_length : {parents : List (Piece data actual accuracy)} →
    (steps : Steps parents) → steps.children.length = 2 * parents.length
  | _, .nil => rfl
  | _, .cons split tail => by
      change ([_, _] ++ children tail).length = 2 * (_ :: _).length
      rewrite [List.length_append, children_length]
      simp only [List.length_cons, List.length_nil]
      omega0

/-- The actual children contract uniform original squared widths and local allowances by exactly four. -/
theorem children_bounds : {parents : List (Piece data actual accuracy)} →
    (steps : Steps parents) → (width allowance : Fraction.Rational) →
    (∀ parent ∈ parents, parent.span.width ^ 2 = width ∧ parent.cell.allowance = allowance) →
    ∀ child ∈ steps.children, child.span.width ^ 2 = width / 4 ∧ child.cell.allowance = allowance / 4
  | _, .nil, _, _, _, _, impossible => nomatch impossible
  | parent :: parents, .cons split tail, width, allowance, bounds, child, member => by
      change child ∈ Piece.children parent split ++ tail.children at member
      cases Purelib.Data.List.Membership.mem_append.mp member with
      | inl head =>
          have childBounds := parent.children_bounds split child head
          have parentBounds := bounds parent (List.Mem.head parents)
          rewrite [parentBounds.1, parentBounds.2] at childBounds
          exact childBounds
      | inr remaining =>
          exact tail.children_bounds width allowance
            (fun value occurrence => bounds value (List.Mem.tail parent occurrence)) child remaining

/-- Reweight completed midpoint steps using their same cached source queries and cofactor observations.

Structural recursion visits the supplied original splits once. It does not
run the midpoint or residual-request factories again.
-/
@[expose] def reweight {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    {parents : List (Piece data actual accuracy)} → (steps : Steps parents) →
      Steps (parents.map (fun piece => piece.reweight nextData))
  | _, .nil => .nil
  | _, .cons split tail => .cons (split.reweight nextData) (reweight nextData tail)

/-- Reweighted completed steps retain the exact original ordered child bank under piece reweighting. -/
theorem reweight_children {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    {parents : List (Piece data actual accuracy)} → (steps : Steps parents) →
      (steps.reweight nextData).children = steps.children.map (fun piece => piece.reweight nextData)
  | _, .nil => rfl
  | _, .cons split tail => by
      change _ :: _ :: (tail.reweight nextData).children = _
      rewrite [reweight_children nextData tail]
      rfl

/-- Reweighting the retained steps factory gives its whole original result on the reweighted parents. -/
theorem reweight_build {nextDifferential : OddPowerDifferential targetRadicand}
    (nextData : WaistBounds site parameter nextDifferential) :
    (parents : List (Piece data actual accuracy)) →
      (build parents).reweight nextData = build (parents.map (fun piece => piece.reweight nextData))
  | [] => rfl
  | parent :: parents => by
      change Steps.cons (parent := parent.reweight nextData)
        ((Split.build parent.cell parent.within).reweight nextData)
        ((build parents).reweight nextData) = _
      rewrite [Split.reweight_build, reweight_build nextData parents]
      rfl

end Steps

end Purelib.Curves.Legendre.Degeneration.Conic.Annulus.Radial.Differential.Refinement
