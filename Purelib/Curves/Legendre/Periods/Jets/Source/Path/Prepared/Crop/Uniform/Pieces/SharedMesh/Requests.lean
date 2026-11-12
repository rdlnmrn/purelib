module

public import Purelib.Curves.Legendre.Periods.Jets.Source.Path.Prepared.Bounds
public import Purelib.Riemann.Comparison.PrimitiveEdgeComparison.Powers.Rectangular
public import Purelib.Riemann.Integration.RectangularPrimitiveAccuracy.Floors
public import Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid.Face.Periods
public import Purelib.Riemann.Paths.RectangularSegmentSplitting
public import Purelib.Approximation.AccuracyRequest
import Purelib.Integration.Path.Primitive.Cells.Targets
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Approximation.Rational.Budget.Aggregate
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Bounds.Quarter
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Nat.Order
import Purelib.Tactic.Ring

/-! # Actual crop allocations before new source or grid model construction

The original prepared source and literal geometric split are fixed inputs.
The initial ratio, retained rectangular scale, binary occurrence count and
physical displacement precede both selections. Original Targets and a new
GridPrimitiveAccuracy at the residual floor pay all three actual shares.
No numerical model, Point, primitive or crop is acquired by this prefix.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

namespace UniformPieces.Chord.SharedMesh

open Purelib
open Purelib.Approximation (AccuracyRequest)
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric.Search (Selection)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Curves.Hyperelliptic.Branches
open Purelib.Curves.Hyperelliptic.Meshes.PuncturedGrid
open Face.InverseModels.BranchCellBank (FaceModels)
open Face.Periods (PeriodDomain)
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm.Basic (normSq)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Path.Gaussian.Lifted.Basic (LiftedPoint LiftedPath)
open Purelib.Integration.Path.Primitive.PrimitiveEdge
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison (PrimitiveOverlapBounds)
open Purelib.Riemann.Comparison.PrimitiveEdgeComparison.PrimitiveOverlapBounds (Rectangular)
open Purelib.Riemann.Normalization.InverseRootPolynomial (Polynomial)
open Purelib.Riemann.Integration.RectangularPrimitiveAccuracy (GridPrimitiveAccuracy)
open Purelib.Riemann.Paths.RectangularSegmentSplitting (SegmentSplit)
open Purelib.Riemann.Meshes.PuncturedGridFaces (RegularFace)
open Purelib.RootIsolation.SquareRoot.Grid (RootFrames)

universe u

variable {parameter : Canonical} {frame : Paths.Frame parameter} {basis : Differential 1}
    {parent : CenteredEdge (Fibre.frameCurve frame) basis} {patch : PreparedPatch parent} {count oldFloor : Nat}
    {covered : (patch.neighborhood count).box.Contains (parent.edge.point 1)}
    {start finish : LiftedPoint 2} {original : LiftedPath 2 start finish} {oldStage : Nat}
    {oldTargets : CellEndpoints.Targets original oldStage}
    (oldPrepared : PreparedParent patch count oldFloor covered oldTargets)
    {branches : BranchIsolation.Data (Fibre.frameCurve frame)}
    {higher : 1 < (Fibre.frameCurve frame).polynomial.natDegree}
    {bank : BranchCellBank (Fibre.frameCurve frame) branches higher}
    {frames : RootFrames bank.grid} {face : RegularFace bank} {models : FaceModels frames face} {sheet : Fin 2}
    (domain : PeriodDomain models sheet) (lower upper : Rational)
    (split : SegmentSplit domain.cuts (parent.edge.point lower) (parent.edge.point upper))
    {numerator : Polynomial}
    (cachedBounds : {value : Rectangular face.clearance domain.geometry domain.patch.cell_refines numerator //
      value = Rectangular.build face.clearance domain.geometry domain.patch.cell_refines numerator})
    (ambientBounds : PrimitiveOverlapBounds face.clearance numerator)
    (sourceFloor gridFloor : Nat) (accuracy : AccuracyRequest)

/-- The actual pre-acquisition selections, requests, Targets and internally paid finite crop formula.

Every let reads an original input cache or a literal geometric quantity.
The consumer gets complete original request records and their factories;
its arbitrary C/D arguments are paid only when the actual cost ceilings
hold. No final integral or primitive comparison is an input to the builder.
-/
abbrev AllocationConsumer (Result : Type u) : Type _ :=
  let ratio := PreparedParent.initialRatio oldPrepared
  let scale := Rectangular.powerScale cachedBounds.val 1
  let size := Budget.Aggregate.countCoordinate split.count
  let movement := normSq (parent.edge.point upper - parent.edge.point lower)
  let sourceScale := size * movement * (96 + 32 * ratio * scale)
  let residualScale := 128 * size * scale * movement / 256
  let share := accuracy.tolerance / 4
  let gluingTarget := Budget.Aggregate.perTerm share split.count / 32
  (source : Selection sourceScale sourceFloor share) →
  (_source_factory : source = Selection.build sourceScale source.scaleNonnegative sourceFloor
    share source.targetPositive) →
  (residual : Selection residualScale gridFloor share) →
  (_residual_factory : residual = Selection.build residualScale residual.scaleNonnegative gridFloor
    share residual.targetPositive) →
  (gluingPositive : 0 < gluingTarget) →
  (glue : GridPrimitiveAccuracy ambientBounds domain.steps gluingTarget) →
  (_glue_factory : glue = GridPrimitiveAccuracy.build ambientBounds domain.steps gluingTarget gluingPositive) →
  (actual : GridPrimitiveAccuracy ambientBounds domain.steps gluingTarget) →
  (_actual_factory : actual = glue.after residual.stage) →
  (_grid_floor : gridFloor ≤ actual.index) →
  (newTargets : CellEndpoints.Targets original source.stage) →
  (_targets_factory : newTargets = CellEndpoints.Targets.build original source.stage) →
  (_source_construction : 2 ≤ Nat.max 2 sourceFloor) →
  (_requested_source_floor : sourceFloor ≤ Nat.max 2 sourceFloor) →
  (_source_paid : sourceScale * newTargets.localBound < share) →
  (_residual_paid : 128 * size * scale * movement *
    Geometric.Basic.quarterRadius (1 / 256) actual.index < share) →
  (_gluing_paid : 32 * size ^ 2 * actual.globalBound < share) →
  (_costs_paid : ∀ displacementCost powerCost : Rational,
    displacementCost ≤ movement → powerCost ≤ scale * movement →
    newTargets.localBound * size * (96 * displacementCost + 32 * ratio * powerCost) +
      128 * size * powerCost * Geometric.Basic.quarterRadius (1 / 256) actual.index +
      32 * size ^ 2 * actual.globalBound < accuracy.tolerance) → Result

/-- The displayed source coefficient is nonnegative before stage selection. -/
private theorem source_scale_nonnegative {size movement ratio scale : Rational}
    (sizeNonnegative : 0 ≤ size) (movementNonnegative : 0 ≤ movement)
    (ratioNonnegative : 0 ≤ ratio) (scaleNonnegative : 0 ≤ scale) :
    0 ≤ size * movement * (96 + 32 * ratio * scale) :=
  Order.Arithmetic.mul_nonneg_direct (Order.Arithmetic.mul_nonneg_direct sizeNonnegative movementNonnegative)
    ((Field.zero_add (0 : Rational)).symm.trans_le
      (Order.Arithmetic.add_le_add_direct (by decide +kernel)
        (Order.Arithmetic.mul_nonneg_direct
          (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) ratioNonnegative) scaleNonnegative)))

/-- The separate grid residual coefficient is nonnegative before stage selection. -/
private theorem residual_scale_nonnegative {size movement scale : Rational}
    (sizeNonnegative : 0 ≤ size) (movementNonnegative : 0 ≤ movement) (scaleNonnegative : 0 ≤ scale) :
    0 ≤ 128 * size * scale * movement / 256 :=
  Order.Field.div_nonneg_direct
    (Order.Arithmetic.mul_nonneg_direct
      (Order.Arithmetic.mul_nonneg_direct
        (Order.Arithmetic.mul_nonneg_direct (by decide +kernel) sizeNonnegative) scaleNonnegative)
      movementNonnegative) (by decide +kernel)

/-- The actual grid-radius coefficient is exactly the retained residual selection scale at that SAME index. -/
private theorem residual_payment_eq (size scale movement : Rational) (index : Nat) :
    128 * size * scale * movement * Geometric.Basic.quarterRadius (1 / 256) index =
      Geometric.Basic.quarterRadius (128 * size * scale * movement / 256) index := by
  rewrite [Geometric.Basic.quarterRadius_eq_mul_pow, Geometric.Basic.quarterRadius_eq_mul_pow]
  simp only [Field.div_eq_mul_inv_direct]
  ring1

/-- The original per-term request pays the actual squared count gluing charge. -/
private theorem gluing_payment (size : Nat) {share bound : Rational} (positive : 0 < share)
    (accurate : bound < Budget.Aggregate.perTerm share size / 32) :
    32 * Budget.Aggregate.countCoordinate size ^ 2 * bound < share := by
  have scaled := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct accurate.le
    (show (0 : Rational) ≤ 32 by decide +kernel)
  have localBound : 32 * bound ≤ Budget.Aggregate.perTerm share size :=
    scaled.trans_eq ((Field.mul_comm 32 _).trans
      (Field.div_mul_cancel_of_ne _ 32 (by decide +kernel)))
  have paid := Budget.Aggregate.count_mul_allowance_lt (Nat.le_refl size) positive localBound
  have regroup : 32 * Budget.Aggregate.countCoordinate size ^ 2 * bound =
      Budget.Aggregate.countCoordinate size * (Budget.Aggregate.countCoordinate size * (32 * bound)) := by ring1
  exact regroup.trans_lt paid

/-- The genuine C/D ceilings substitute into the exact fixed-cache crop formula by direct nonnegative arithmetic. -/
private theorem coefficient_substitution_le {allowance size ratio scale movement displacementCost powerCost
    radius gluing : Rational} (allowanceNonnegative : 0 ≤ allowance) (sizeNonnegative : 0 ≤ size)
    (ratioNonnegative : 0 ≤ ratio) (radiusNonnegative : 0 ≤ radius)
    (displacementBound : displacementCost ≤ movement) (powerBound : powerCost ≤ scale * movement) :
    allowance * size * (96 * displacementCost + 32 * ratio * powerCost) +
        128 * size * powerCost * radius + 32 * size ^ 2 * gluing ≤
      (size * movement * (96 + 32 * ratio * scale)) * allowance +
        (128 * size * scale * movement) * radius + 32 * size ^ 2 * gluing := by
  have inside := Order.Arithmetic.add_le_add_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct displacementBound
      (show (0 : Rational) ≤ 96 by decide +kernel))
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct powerBound
      (Order.Arithmetic.mul_nonneg_direct (show (0 : Rational) ≤ 32 by decide +kernel) ratioNonnegative))
  have source := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct inside
    (Order.Arithmetic.mul_nonneg_direct allowanceNonnegative sizeNonnegative)
  have residual := Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct powerBound
      (Order.Arithmetic.mul_nonneg_direct (show (0 : Rational) ≤ 128 by decide +kernel)
        sizeNonnegative)) radiusNonnegative
  exact (Order.Arithmetic.add_le_add_direct (Order.Arithmetic.add_le_add_direct source residual)
    (Order.Basic.le_refl (32 * size ^ 2 * gluing))).trans_eq (by ring1)

/-- Three actual quarter-target payments leave a strict part of the original positive tolerance unspent. -/
private theorem three_shares_lt {target first second third : Rational} (positive : 0 < target)
    (firstPaid : first < target / 4) (secondPaid : second < target / 4) (thirdPaid : third < target / 4) :
    first + second + third < target := by
  have shares := Order.Arithmetic.add_lt_add_direct
    (Order.Arithmetic.add_lt_add_direct firstPaid secondPaid) thirdPaid
  have larger := Order.Arithmetic.mul_lt_mul_of_pos_right_direct
    (show (3 : Rational) < 4 by decide +kernel) (Data.Rat.Bounds.Quarter.quarter_pos positive)
  have whole : 4 * (target / 4) = target :=
    (Field.mul_comm 4 _).trans (Field.div_mul_cancel_of_ne target 4 (by decide +kernel))
  exact shares.trans ((show target / 4 + target / 4 + target / 4 = 3 * (target / 4) by ring1).trans_lt
    (larger.trans_eq whole))

/-- Select both actual numerical depths and construct their original source/grid allocations before any new model.

All four geometric coefficients are bound first from the GIVEN original
source/cache/split. One selection pays the new Targets through the owned
unit-scale law. A second selection sets a genuine minimum grid index;
one original gluing request is enlarged by after before models execute.
The complete records, factories, model-construction floor and derived
finite payments are forwarded to one consumer, without acquiring a Point.
-/
def withAllocation {Result : Type u}
    (consume : AllocationConsumer oldPrepared domain lower upper split cachedBounds ambientBounds
      sourceFloor gridFloor accuracy Result) : Result :=
  let ratio := PreparedParent.initialRatio oldPrepared
  let scale := Rectangular.powerScale cachedBounds.val 1
  let size := Budget.Aggregate.countCoordinate split.count
  let movement := normSq (parent.edge.point upper - parent.edge.point lower)
  let sourceScale := size * movement * (96 + 32 * ratio * scale)
  let residualScale := 128 * size * scale * movement / 256
  let share := accuracy.tolerance / 4
  let gluingTarget := Budget.Aggregate.perTerm share split.count / 32
  have ratioNonnegative := PreparedParent.initialRatio_nonnegative oldPrepared
  have scaleNonnegative := Rectangular.powerScale_nonnegative cachedBounds.val 1
  have sizeNonnegative : 0 ≤ size :=
    (Cast.Order.natCast_le_direct (Nat.zero_le split.count)).trans_eq
      (Budget.Aggregate.countCoordinate_eq split.count).symm
  have movementNonnegative := Norm.Basic.normSq_nonneg (parent.edge.point upper - parent.edge.point lower)
  have sourceNonnegative : 0 ≤ sourceScale :=
    source_scale_nonnegative sizeNonnegative movementNonnegative ratioNonnegative scaleNonnegative
  have residualNonnegative : 0 ≤ residualScale :=
    residual_scale_nonnegative sizeNonnegative movementNonnegative scaleNonnegative
  have sharePositive : 0 < share := Data.Rat.Bounds.Quarter.quarter_pos accuracy.positive
  let source := Selection.build sourceScale sourceNonnegative sourceFloor share sharePositive
  let residual := Selection.build residualScale residualNonnegative gridFloor share sharePositive
  have gluingPositive : 0 < gluingTarget :=
    Order.Field.div_pos_direct (Budget.Aggregate.perTerm_positive sharePositive split.count) (by decide +kernel)
  let glue := GridPrimitiveAccuracy.build ambientBounds domain.steps gluingTarget gluingPositive
  let actual := glue.after residual.stage
  let newTargets := CellEndpoints.Targets.build original source.stage
  have sourcePaid : sourceScale * newTargets.localBound < share :=
    (newTargets.mul_localBound_le_quarterRadius sourceScale sourceNonnegative).trans_lt
      (source.allowance_eq.symm.trans_lt source.accurate)
  have residualPaid : 128 * size * scale * movement *
      Geometric.Basic.quarterRadius (1 / 256) actual.index < share :=
    (residual_payment_eq size scale movement actual.index).trans_lt
      (residual.later_accurate (glue.floor_le_after residual.stage))
  have gluingPaid : 32 * size ^ 2 * actual.globalBound < share :=
    gluing_payment split.count sharePositive actual.accurate
  have costsPaid (displacementCost powerCost : Rational) (displacementBound : displacementCost ≤ movement)
      (powerBound : powerCost ≤ scale * movement) :
      newTargets.localBound * size * (96 * displacementCost + 32 * ratio * powerCost) +
        128 * size * powerCost * Geometric.Basic.quarterRadius (1 / 256) actual.index +
        32 * size ^ 2 * actual.globalBound < accuracy.tolerance :=
    (coefficient_substitution_le newTargets.localBound_positive.le sizeNonnegative ratioNonnegative
      (Geometric.Basic.quarterRadius_nonneg (by decide +kernel) actual.index)
      displacementBound powerBound).trans_lt
        (three_shares_lt accuracy.positive sourcePaid residualPaid gluingPaid)
  consume source rfl residual rfl gluingPositive glue rfl actual rfl
    (residual.lower.trans (glue.floor_le_after residual.stage)) newTargets rfl
    (Purelib.Data.Nat.Order.le_max_left 2 sourceFloor)
    (Purelib.Data.Nat.Order.le_max_right 2 sourceFloor)
    sourcePaid residualPaid gluingPaid costsPaid

/-- Retained source/residual selections and the actual after factory pay the full finite crop formula.

The scalar identities express the original pre-stage coefficients through
retained cache readbacks. They neither select a new stage nor replace a
model. Actual Targets use the source selection's SAME stage; the actual
grid request is the original after value. All three payments are derived
internally, including the genuine occurrence-count gluing request.
-/
theorem requested_costs_lt
    {pathStart pathFinish : LiftedPoint 2} (originalPath : LiftedPath 2 pathStart pathFinish)
    (accuracy : AccuracyRequest) (pieceCount : Nat) (ratio scale movement : Rational)
    (ratioNonnegative : 0 ≤ ratio) {sourceScale residualScale target : Rational}
    {initialSourceFloor residualFloor columns : Nat}
    (source : Selection sourceScale initialSourceFloor (accuracy.tolerance / 4))
    (residual : Selection residualScale residualFloor (accuracy.tolerance / 4))
    (sourceScale_eq : sourceScale = Budget.Aggregate.countCoordinate pieceCount * movement *
      (96 + 32 * ratio * scale))
    (residualScale_eq : residualScale = 128 * Budget.Aggregate.countCoordinate pieceCount * scale * movement / 256)
    (targets : CellEndpoints.Targets originalPath source.stage)
    {polynomial numerator : Polynomial} {ambient : Purelib.Riemann.Normalization.InverseRootPolynomial.Box}
    {clearance : Riemann.Comparison.PrimitiveEdgeComparison.RegionClearance polynomial ambient}
    {bounds : PrimitiveOverlapBounds clearance numerator}
    (glue actual : GridPrimitiveAccuracy bounds columns target)
    (actualFactory : actual = glue.after residual.stage)
    (target_eq : target = Budget.Aggregate.perTerm (accuracy.tolerance / 4) pieceCount / 32)
    {displacementCost powerCost : Rational}
    (displacementBound : displacementCost ≤ movement) (powerBound : powerCost ≤ scale * movement) :
    targets.localBound * Budget.Aggregate.countCoordinate pieceCount *
        (96 * displacementCost + 32 * ratio * powerCost) +
      128 * Budget.Aggregate.countCoordinate pieceCount * powerCost *
        Geometric.Basic.quarterRadius (1 / 256) actual.index +
      32 * Budget.Aggregate.countCoordinate pieceCount ^ 2 * actual.globalBound < accuracy.tolerance := by
  let size := Budget.Aggregate.countCoordinate pieceCount
  have sizeNonnegative : 0 ≤ size :=
    (Cast.Order.natCast_le_direct (Nat.zero_le pieceCount)).trans_eq
      (Budget.Aggregate.countCoordinate_eq pieceCount).symm
  have sourceNonnegative : 0 ≤ size * movement * (96 + 32 * ratio * scale) :=
    source.scaleNonnegative.trans_eq sourceScale_eq
  have sourceRadius := congrArg
    (fun value : Rational => Geometric.Basic.quarterRadius value source.stage) sourceScale_eq.symm
  have sourcePaid := (targets.mul_localBound_le_quarterRadius
    (size * movement * (96 + 32 * ratio * scale)) sourceNonnegative).trans_lt
      (sourceRadius.trans_lt (source.allowance_eq.symm.trans_lt source.accurate))
  have indexEq := congrArg (fun request : GridPrimitiveAccuracy bounds columns target => request.index) actualFactory
  have later : residual.stage ≤ actual.index := (glue.floor_le_after residual.stage).trans_eq indexEq.symm
  have residualRadius := congrArg
    (fun value : Rational => Geometric.Basic.quarterRadius value actual.index) residualScale_eq.symm
  have residualPaid := ((residual_payment_eq size scale movement actual.index).trans residualRadius).trans_lt
    (residual.later_accurate later)
  have gluingPaid := gluing_payment pieceCount (Data.Rat.Bounds.Quarter.quarter_pos accuracy.positive)
    (actual.accurate.trans_eq target_eq)
  exact (coefficient_substitution_le targets.localBound_positive.le sizeNonnegative ratioNonnegative
    (Geometric.Basic.quarterRadius_nonneg (show (0 : Rational) ≤ 1 / 256 by decide +kernel) actual.index)
    displacementBound powerBound).trans_lt
      (three_shares_lt accuracy.positive sourcePaid residualPaid gluingPaid)

end UniformPieces.Chord.SharedMesh

end Purelib.Curves.Legendre.Periods.Jets.Source.Cell.PreparedParent.Crop.Observation.Points

end
