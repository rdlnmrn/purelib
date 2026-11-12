module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Primitives
public import Purelib.Geometry.Path.Gaussian.Lifted.Basic
public import Purelib.Integration.Path.Lifted.Model
public import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Tactic.Ring
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Original lifted paths with shared Legendre cell sources

Each original lifted cell retains its selected regular-chart request and
six coefficient pullbacks. The ordered path keeps those owners cell by cell,
including the original sheet transports. All three relation-cell lists are
read from the same retained sources, so their actual integral samples are
the displayed combinations of the original six path samples.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source

open Purelib
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedCell LiftedPath)
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Curves.Legendre.PicardFuchs

set_option genInjectivity false in
/-- One original lifted cell with its actual shared source request and internally controlled relation primitives.

The original continued chart and lifted-cell index are retained. Endpoint
membership admits the whole original segment, while the selected source
request determines the six local coefficient tables and all three actual
primitive comparisons. -/
structure Cell {parameter : Canonical} {start finish : LiftedPoint 2}
    (liftedCell : LiftedCell start finish) where
  /-- The original continued-chart observation count. -/
  count : Nat
  /-- The original continued inverse-root chart owner. -/
  patch : ContinuedNeighborhood (Paths.polynomial parameter) count
  /-- The original cached relation and derivative budgets of that chart. -/
  cache : Cache patch
  /-- The original finite depth floor used for this source selection. -/
  floor : Nat
  /-- The actual original positive source-error target. -/
  target : Rational
  /-- The original finite source selection and all six polynomial caches constructed at its chosen depth. -/
  request : Request cache floor target
  /-- The retained allowance used by the six original differential cells. -/
  allowance : Rational
  /-- The literal original cell models consuming this source request. -/
  models : CellModels request start.coordinate finish.coordinate allowance
  /-- The original starting coordinate lies in this actual continued chart. -/
  startInside : patch.box.Contains start.coordinate
  /-- The original finishing coordinate lies in this actual continued chart. -/
  finishInside : patch.box.Contains finish.coordinate
  /-- The source-derived primitive comparisons of the three original relation cells. -/
  primitives : PrimitiveModels models

constructive_injectivity Cell

namespace Cell

/-- Attach the literal retained coefficient models to their original lifted segment and derive the primitive caches. -/
@[expose] def ofModels {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
    {floor : Nat} {target : Rational} (request : Request cache floor target)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish) {allowance : Rational}
    (models : CellModels request start.coordinate finish.coordinate allowance)
    (startInside : patch.box.Contains start.coordinate) (finishInside : patch.box.Contains finish.coordinate) :
    Cell (parameter := parameter) liftedCell :=
  let primitives := PrimitiveModels.build models startInside finishInside
  ⟨count, patch, cache, floor, target, request, allowance, models, startInside, finishInside, primitives⟩

/-- Attach a selected original regular source to one original lifted segment and construct its cell caches once. -/
@[expose] def ofRequest {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count} {cache : Cache patch}
    {floor : Nat} {target : Rational} (request : Request cache floor target)
    {start finish : LiftedPoint 2} (liftedCell : LiftedCell start finish)
    (allowance : Rational) (nonnegative : 0 ≤ allowance)
    (startInside : patch.box.Contains start.coordinate) (finishInside : patch.box.Contains finish.coordinate) :
    Cell (parameter := parameter) liftedCell :=
  let models := CellModels.build request start.coordinate finish.coordinate allowance nonnegative
  ofModels request liftedCell models startInside finishInside

end Cell

set_option genInjectivity false in
/-- An ordered source chain on an exact original lifted path.

Each original cell retains its original regular chart, chosen depth,
coefficient caches and sheet transport. Shared dependent lifted endpoints
preserve the original geometric path; algebraic endpoint-root transport
remains additional evidence when constructing a closed primitive telescope. -/
inductive Path (parameter : Canonical) : {start finish : LiftedPoint 2} → LiftedPath 2 start finish → Type 1
  /-- The original empty lifted path has no cell sources. -/
  | nil (point : LiftedPoint 2) : Path parameter (.nil point)
  /-- Retain the original head-cell source and the exact original remaining path. -/
  | cons {start middle finish : LiftedPoint 2} {liftedCell : LiftedCell start middle}
      {remaining : LiftedPath 2 middle finish} (head : Cell (parameter := parameter) liftedCell)
      (tail : Path parameter remaining) : Path parameter (.cons liftedCell remaining)

constructive_injectivity Path

namespace Path

open Purelib.Data.Rat.Fraction

variable {parameter : Canonical} {start finish : LiftedPoint 2} {original : LiftedPath 2 start finish}

/-- Concatenate original source chains using their retained geometry and cell caches. -/
@[expose] def append {start middle finish : LiftedPoint 2} {second : LiftedPath 2 middle finish} :
    (first : LiftedPath 2 start middle) → Path parameter first → Path parameter second →
      Path parameter (first.append second)
  | .nil _, .nil _, right => right
  | .cons actualHead actualTail, .cons head remaining, right =>
      .cons (liftedCell := actualHead) (remaining := actualTail.append second)
        head (append actualTail remaining right)

/-- The result of moving a retained first cell around an exactly closed lifted source path.

An empty chain has no head to move. A nonempty chain retains the original
closing endpoint equality and the source chain on the shifted closed path.
-/
@[expose] def HeadRotation {start finish : LiftedPoint 2} (original : LiftedPath 2 start finish) : Type 1 :=
  match original with
  | .nil _ => PUnit
  | .cons (middle := middle) head tail =>
      (closed : finish = start) →
        Path parameter ((closed ▸ tail).append (.cons head (.nil middle)))

/-- Move the retained source head using the actual constructor geometry and an exact lifted closure. -/
@[expose] def rotate (sources : Path parameter original) : HeadRotation (parameter := parameter) original :=
  Path.casesOn sources
    (fun _ => PUnit.unit)
    (fun {actualStart actualMiddle actualFinish cell tail} source remaining closed => by
      cases closed
      exact append tail remaining (.cons (start := actualStart) (middle := actualMiddle)
        (finish := actualMiddle) (liftedCell := cell) (remaining := .nil actualMiddle)
        source (.nil actualMiddle)))

/-- Move the original source head to the end of its closed path without rebuilding its actual geometry. -/
@[expose] def rotateHead {start middle : LiftedPoint 2} {head : LiftedCell start middle}
    {tail : LiftedPath 2 middle start} (sources : Path parameter (.cons head tail)) :
    Path parameter (tail.append (.cons head (.nil middle))) :=
  sources.rotate rfl

/-- Read the first original value-cell list in retained path order. -/
@[expose] def valueZero : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.valueZero.model :: valueZero tail

/-- Read the second original value-cell list in retained path order. -/
@[expose] def valueOne : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.valueOne.model :: valueOne tail

/-- Read the first original first-derivative-cell list in retained path order. -/
@[expose] def firstZero : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.firstZero.model :: firstZero tail

/-- Read the second original first-derivative-cell list in retained path order. -/
@[expose] def firstOne : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.firstOne.model :: firstOne tail

/-- Read the first original second-derivative-cell list in retained path order. -/
@[expose] def secondZero : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.secondZero.model :: secondZero tail

/-- Read the second original second-derivative-cell list in retained path order. -/
@[expose] def secondOne : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.secondOne.model :: secondOne tail

/-- Select the literal retained source-cell list for one of the original six differential specifications.

The same original list spine and cell occurrences are preserved. Selection
reads an existing value, first or second list without constructing a source.
-/
@[expose] def cells (sources : Path parameter original) : Fin 6 → List CellModel :=
  Fin.cases sources.valueZero (Fin.cases sources.valueOne
    (Fin.cases sources.firstZero (Fin.cases sources.firstOne
      (Fin.cases sources.secondZero (Fin.cases sources.secondOne Fin.elim0)))))

/-- A selected retained source list has the identical original head cell and selected unchanged tail. -/
theorem cells_cons {start middle finish : LiftedPoint 2} {liftedCell : LiftedCell start middle}
    {remaining : LiftedPath 2 middle finish} (head : Cell (parameter := parameter) liftedCell)
    (tail : Path parameter remaining) (index : Fin 6) :
    (Path.cons head tail).cells index = head.models.cell index :: tail.cells index := by
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  exact Fin.cases (Eq.refl _) (fun index => Fin.elim0 index) index

/-- Every selected source list is empty on the original empty lifted path. -/
theorem cells_nil (point : LiftedPoint 2) (index : Fin 6) :
    (Path.nil (parameter := parameter) point).cells index = [] := by
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  refine Fin.cases (Eq.refl _) ?_ index
  intro index
  exact Fin.cases (Eq.refl _) (fun index => Fin.elim0 index) index

/-- Read the first original relation-cell list from that same source chain. -/
@[expose] def zero : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.zero :: zero tail

/-- Read the second original relation-cell list from that same source chain. -/
@[expose] def one : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.one :: one tail

/-- Read the original scalar relation-cell list from that same source chain. -/
@[expose] def scalar : {start finish : LiftedPoint 2} → {original : LiftedPath 2 start finish} →
    Path parameter original → List CellModel
  | _, _, _, .nil _ => []
  | _, _, _, .cons head tail => head.models.scalar :: scalar tail

/-- The first value-cell list follows the exact original lifted path. -/
theorem valueZero_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.valueZero original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih => exact .cons head.models.valueZero.start_eq head.models.valueZero.finish_eq ih

/-- The second value-cell list follows the exact original lifted path. -/
theorem valueOne_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.valueOne original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih => exact .cons head.models.valueOne.start_eq head.models.valueOne.finish_eq ih

/-- The first derivative-cell list follows the exact original lifted path. -/
theorem firstZero_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.firstZero original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih => exact .cons head.models.firstZero.start_eq head.models.firstZero.finish_eq ih

/-- The second derivative-cell list follows the exact original lifted path. -/
theorem firstOne_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.firstOne original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih => exact .cons head.models.firstOne.start_eq head.models.firstOne.finish_eq ih

/-- The first second-derivative-cell list follows the exact original lifted path. -/
theorem secondZero_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.secondZero original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih => exact .cons head.models.secondZero.start_eq head.models.secondZero.finish_eq ih

/-- The second second-derivative-cell list follows the exact original lifted path. -/
theorem secondOne_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.secondOne original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih => exact .cons head.models.secondOne.start_eq head.models.secondOne.finish_eq ih

/-- The first relation-cell list follows the same exact original lifted path. -/
theorem zero_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.zero original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih =>
      exact .cons (by rw [head.models.zero_eq]; rfl) (by rw [head.models.zero_eq]; rfl) ih

/-- The second relation-cell list follows the same exact original lifted path. -/
theorem one_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.one original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih =>
      exact .cons (by rw [head.models.one_eq]; rfl) (by rw [head.models.one_eq]; rfl) ih

/-- The scalar relation-cell list follows the same exact original lifted path. -/
theorem scalar_follows (sources : Path parameter original) : LiftedPath.FollowedBy sources.scalar original := by
  induction sources with
  | nil point => exact .nil point
  | cons head tail ih =>
      exact .cons (by rw [head.models.scalar_eq]; rfl) (by rw [head.models.scalar_eq]; rfl) ih

/-- The first original relation path integrates the same first and value source paths. -/
theorem zero_integralSample (sources : Path parameter original) :
    (PathModel.mk sources.zero).integralSample =
      Clearance.connectionDenominator parameter * (PathModel.mk sources.firstZero).integralSample -
        (parameter * (PathModel.mk sources.valueZero).integralSample -
          (PathModel.mk sources.valueOne).integralSample) := by
  induction sources with
  | nil =>
      change (0 : Canonical) = Clearance.connectionDenominator parameter * 0 - (parameter * 0 - 0)
      ring1
  | cons head tail ih =>
      change head.models.zero.integralSample + (PathModel.mk tail.zero).integralSample = _
      rw [head.models.zero_integralSample, ih]
      change _ = Clearance.connectionDenominator parameter *
        (head.models.firstZero.model.integralSample + (PathModel.mk tail.firstZero).integralSample) -
          (parameter *
            (head.models.valueZero.model.integralSample + (PathModel.mk tail.valueZero).integralSample) -
              (head.models.valueOne.model.integralSample + (PathModel.mk tail.valueOne).integralSample))
      ring1

/-- The second original relation path integrates the same weighted first and original value source paths. -/
theorem one_integralSample (sources : Path parameter original) :
    (PathModel.mk sources.one).integralSample =
      Clearance.connectionDenominator parameter * (PathModel.mk sources.firstOne).integralSample -
        (parameter * (PathModel.mk sources.valueZero).integralSample -
          parameter * (PathModel.mk sources.valueOne).integralSample) := by
  induction sources with
  | nil =>
      change (0 : Canonical) = Clearance.connectionDenominator parameter * 0 - (parameter * 0 - parameter * 0)
      ring1
  | cons head tail ih =>
      change head.models.one.integralSample + (PathModel.mk tail.one).integralSample = _
      rw [head.models.one_integralSample, ih]
      change _ = Clearance.connectionDenominator parameter *
        (head.models.firstOne.model.integralSample + (PathModel.mk tail.firstOne).integralSample) -
          (parameter *
            (head.models.valueZero.model.integralSample + (PathModel.mk tail.valueZero).integralSample) -
              parameter *
                (head.models.valueOne.model.integralSample + (PathModel.mk tail.valueOne).integralSample))
      ring1

/-- The original scalar relation path integrates the same second, first and value source paths. -/
theorem scalar_integralSample (sources : Path parameter original) :
    (PathModel.mk sources.scalar).integralSample =
      4 * parameter * (1 - parameter) * (PathModel.mk sources.secondZero).integralSample +
        4 * (1 - 2 * parameter) * (PathModel.mk sources.firstZero).integralSample -
          (PathModel.mk sources.valueZero).integralSample := by
  induction sources with
  | nil =>
      change (0 : Canonical) = 4 * parameter * (1 - parameter) * 0 + 4 * (1 - 2 * parameter) * 0 - 0
      ring1
  | cons head tail ih =>
      change head.models.scalar.integralSample + (PathModel.mk tail.scalar).integralSample = _
      rw [head.models.scalar_integralSample, ih]
      change _ = 4 * parameter * (1 - parameter) *
        (head.models.secondZero.model.integralSample + (PathModel.mk tail.secondZero).integralSample) +
          4 * (1 - 2 * parameter) *
            (head.models.firstZero.model.integralSample + (PathModel.mk tail.firstZero).integralSample) -
              (head.models.valueZero.model.integralSample + (PathModel.mk tail.valueZero).integralSample)
      ring1

/-- The first relation's exact polynomial cells have zero total weighted allowance.

This concerns the retained polynomial combination only. The original
differential cells and the separate source-model residuals keep their
actual allowances and bounds. -/
theorem zero_totalWeightedAllowance (sources : Path parameter original) :
    (PathModel.mk sources.zero).totalWeightedAllowance = 0 := by
  induction sources with
  | nil => rfl
  | cons head tail ih =>
      change head.models.zero.weightedAllowance + (PathModel.mk tail.zero).totalWeightedAllowance = 0
      rw [ih, head.models.zero_eq]
      change _ * (0 : Rational) + 0 = 0
      rw [Field.mul_zero_direct, Field.zero_add]

/-- The second relation's exact polynomial cells have zero total weighted allowance. -/
theorem one_totalWeightedAllowance (sources : Path parameter original) :
    (PathModel.mk sources.one).totalWeightedAllowance = 0 := by
  induction sources with
  | nil => rfl
  | cons head tail ih =>
      change head.models.one.weightedAllowance + (PathModel.mk tail.one).totalWeightedAllowance = 0
      rw [ih, head.models.one_eq]
      change _ * (0 : Rational) + 0 = 0
      rw [Field.mul_zero_direct, Field.zero_add]

/-- The scalar relation's exact polynomial cells have zero total weighted allowance. -/
theorem scalar_totalWeightedAllowance (sources : Path parameter original) :
    (PathModel.mk sources.scalar).totalWeightedAllowance = 0 := by
  induction sources with
  | nil => rfl
  | cons head tail ih =>
      change head.models.scalar.weightedAllowance + (PathModel.mk tail.scalar).totalWeightedAllowance = 0
      rw [ih, head.models.scalar_eq]
      change _ * (0 : Rational) + 0 = 0
      rw [Field.mul_zero_direct, Field.zero_add]

/-- The first retained exact relation path has zero count-weighted polynomial allowance. -/
theorem zero_aggregateAllowance (sources : Path parameter original) :
    (PathModel.mk sources.zero).aggregateAllowance = 0 := by
  unfold PathModel.aggregateAllowance
  rw [sources.zero_totalWeightedAllowance, Field.mul_zero_direct]

/-- The second retained exact relation path has zero count-weighted polynomial allowance. -/
theorem one_aggregateAllowance (sources : Path parameter original) :
    (PathModel.mk sources.one).aggregateAllowance = 0 := by
  unfold PathModel.aggregateAllowance
  rw [sources.one_totalWeightedAllowance, Field.mul_zero_direct]

/-- The retained scalar relation path has zero count-weighted polynomial allowance. -/
theorem scalar_aggregateAllowance (sources : Path parameter original) :
    (PathModel.mk sources.scalar).aggregateAllowance = 0 := by
  unfold PathModel.aggregateAllowance
  rw [sources.scalar_totalWeightedAllowance, Field.mul_zero_direct]

end Path

end Purelib.Curves.Legendre.Periods.Jets.Source

end
