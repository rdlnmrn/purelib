module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Partition
import Purelib.Integration.Polynomial.Gaussian.Path.Uniform
import Purelib.Integration.Polynomial.Gaussian.Path.ConstantRefinement
import Purelib.Data.List.Membership
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Compatible refinements of actual observed cap-form circle cells

The original whole banks supply their own requested coefficient readings.
The retained global coarse reading and original uniform polynomial/root
bounds pay each actual two-child integrand difference before the original
constant-path refinement certificates are assembled.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data
open Purelib.Data.List
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization
open Purelib.Geometry.Gaussian.UnitCircle
open Purelib.Integration.Polynomial.Gaussian.Cell.Basic (CellModel)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic
open Purelib.Approximation.Rational.Geometric
open Purelib.Integration.Polynomial.Gaussian.Path.CompatibleRefinement.PathModel.CompatibleConstantPathRefinement
  (comparisonCells comparisonCells_bounds comparisonCells_length comparisonAllowance)

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }}

/-- The actual cached coefficient and coarse-reading bounds determine one nonnegative cell refinement scale. -/
@[expose] def allowanceScale
    {data : Polynomials differential} (cached : data.Bounds base)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1) :
    Fraction.Rational :=
  8 * (32 * (1 + 1) + 4 * cached.separationCeiling bounds * (4 + 1)) +
    2 * (40 * magnitudeBound cached bounds anchor) + 1

/-- All retained magnitude and coefficient budgets give a nonnegative actual cell refinement scale. -/
theorem allowanceScale_nonnegative
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1) :
    0 ≤ allowanceScale cached bounds anchor := by
  have first : 0 ≤ 8 * (32 * (1 + 1) + 4 * cached.separationCeiling bounds * (4 + 1)) :=
    Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 8)
    (add_nonneg
      (Arithmetic.mul_nonneg_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le (by decide))
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
          (cached.separationCeiling_nonnegative nonzero bounds)) (by decide)))
  have last : 0 ≤ 2 * (40 * magnitudeBound cached bounds anchor) :=
    Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 2)
    (Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 40) (by decide)).le
      (magnitudeBound_nonnegative cached nonzero bounds anchor))
  exact add_nonneg (add_nonneg first last) (by decide)

/-- Two actual neighbouring-stage integrand readings meet their retained cell scale at the original precision.

The original banks have targets precision and precision divided by four.
Their actual left-parameter separation is certified separately by the
original dyadic geometry. Both whole bank identities and the global
coarse anchor remain actual inputs; no integrand comparison is assumed.
-/
theorem get_integrand_refinement_le
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight firstLeft firstRight lastLeft lastRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1)
    (anchorCanonical : anchor =
      readings differential cap base nonzero unitBound collarBound actual 0 anchorLeft anchorRight 1 (by decide))
    {firstDepth lastDepth : Nat} (precision : Fraction.Rational) (positive : 0 < precision)
    (unitPrecision : precision ≤ 1)
    (first : Readings differential cap base unitBound collarBound actual firstDepth firstLeft firstRight precision)
    (last : Readings differential cap base unitBound collarBound actual lastDepth lastLeft lastRight (precision / 4))
    (firstCanonical : first = readings differential cap base nonzero unitBound collarBound actual
      firstDepth firstLeft firstRight precision positive)
    (lastCanonical : last = readings differential cap base nonzero unitBound collarBound actual
      lastDepth lastLeft lastRight (precision / 4) (Fraction.Order.Field.div_pos_direct positive (by decide)))
    (firstIndex : Fin (dyadicEdges firstDepth firstLeft firstRight).length)
    (lastIndex : Fin (dyadicEdges lastDepth lastLeft lastRight).length)
    (movement :
      (((dyadicEdges lastDepth lastLeft lastRight)[lastIndex.val]'lastIndex.isLt).left.parameter -
        ((dyadicEdges firstDepth firstLeft firstRight)[firstIndex.val]'firstIndex.isLt).left.parameter) ^ 2 ≤
        precision) :
    let firstTime := ((dyadicEdges firstDepth firstLeft firstRight)[firstIndex.val]'firstIndex.isLt).left.parameter
    let lastTime := ((dyadicEdges lastDepth lastLeft lastRight)[lastIndex.val]'lastIndex.isLt).left.parameter
    Norm.Basic.normSq
      (velocity base lastTime * (last.get lastIndex).request.reading.value -
        velocity base firstTime * (first.get firstIndex).request.reading.value) ≤
      allowanceScale cached bounds anchor * precision := by
  have dividedPositive := Fraction.Order.Field.div_pos_direct positive (by decide : (0 : Fraction.Rational) < 4)
  have dividedOrder : precision / 4 ≤ precision := by
    exact Basic.quarterRadius_le_scale positive.le 1
  have estimate := get_integrand_distance_le cached nonzero pairs degreeBound bounds anchor anchorCanonical
    positive dividedPositive (dividedOrder.trans unitPrecision) first last firstCanonical lastCanonical
    firstIndex lastIndex precision positive
  let coefficient := cached.separationCeiling bounds
  let magnitude := magnitudeBound cached bounds anchor
  have coefficientNonnegative : 0 ≤ coefficient := cached.separationCeiling_nonnegative nonzero bounds
  have magnitudeNonnegative : 0 ≤ magnitude := magnitudeBound_nonnegative cached nonzero bounds anchor
  have targetPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct dividedOrder (Fraction.Order.Basic.le_refl precision))
    (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le
  have pointPayment := Arithmetic.add_le_add_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct movement (by decide : (0 : Fraction.Rational) ≤ 4))
    (Fraction.Order.Basic.le_refl precision)
  have coefficientPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct pointPayment
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4) coefficientNonnegative)
  have firstPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct targetPayment coefficientPayment)
    (by decide : (0 : Fraction.Rational) ≤ 8)
  have lastPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct movement
    (Arithmetic.mul_nonneg_direct
      (Fraction.Cast.Order.natCast_pos_direct (n := 80) (by decide)).le magnitudeNonnegative)
  have paid := estimate.trans (Arithmetic.add_le_add_direct firstPayment lastPayment)
  have reserve := Arithmetic.add_le_add_direct paid positive.le
  rewrite [_root_.add_zero] at reserve
  exact reserve.trans_eq (by
    change _ = (8 * (32 * (1 + 1) + 4 * coefficient * (4 + 1)) + 2 * (40 * magnitude) + 1) * precision
    ring1)

/-- Each actual mapped original cell retains its edge displacement bound and supplied allowance.

The property is independent of the retained numerical reading. It holds
for both total-form and reference-error cells without changing their
original observations, coefficients or bounded occurrences.
-/
theorem cells_bounds
    {depth : Nat} {left right : Endpoint} {target : Fraction.Rational} {factors : Canonical → Canonical}
    (stored : Readings differential cap base unitBound collarBound actual depth left right target factors)
    (reference : Option (Canonical → Canonical)) (allowance : { value : Fraction.Rational // 0 ≤ value })
    (movement : Fraction.Rational)
    (edgeBounds : ∀ edge ∈ dyadicEdges depth left right,
      (edge.right.parameter - edge.left.parameter) ^ 2 ≤ movement) :
    ∀ cell ∈ stored.cells reference (some allowance),
      Norm.Basic.normSq cell.displacement ≤ movement ∧ cell.localAllowance ≤ allowance.val := by
  rewrite [cells_eq]
  apply Data.List.DependentProduct.mapToList_all
  intro index reading
  constructor
  · rewrite [readingCell.displacement, Norm.Basic.normSq_eq_canonical]
    let edge := (dyadicEdges depth left right)[index.val]'index.isLt
    change (edge.right.parameter - edge.left.parameter) * (edge.right.parameter - edge.left.parameter) +
      0 * 0 ≤ movement
    exact (show (edge.right.parameter - edge.left.parameter) * (edge.right.parameter - edge.left.parameter) +
      0 * 0 = (edge.right.parameter - edge.left.parameter) ^ 2 by ring1).trans_le
      (edgeBounds edge (List.getElem_mem index.isLt))
  · exact (readingCell.allowance_value _ _ _ _ _ _ _ _ _ _).le

/-- Compare one actual coarse cell with both actual midpoint children using their original retained observations.

The coefficient differences are proved from the canonical numerical banks,
not supplied as successful comparisons. The same original cell allowances
pay both errors, and the actual signed displacements add exactly.
-/
def partitionZero
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1)
    (anchorCanonical : anchor =
      readings differential cap base nonzero unitBound collarBound actual 0 anchorLeft anchorRight 1 (by decide))
    (left right : Endpoint) (precision : Fraction.Rational) (positive : 0 < precision)
    (unitPrecision : precision ≤ 1) (width : (right.parameter - left.parameter) ^ 2 ≤ precision)
    (coarse : Readings differential cap base unitBound collarBound actual 0 left right precision)
    (fine : Readings differential cap base unitBound collarBound actual 1 left right (precision / 4))
    (coarseCanonical : coarse =
      readings differential cap base nonzero unitBound collarBound actual 0 left right precision positive)
    (fineCanonical : fine = readings differential cap base nonzero unitBound collarBound actual
      1 left right (precision / 4) (Fraction.Order.Field.div_pos_direct positive (by decide))) :
    let scale := allowanceScale cached bounds anchor
    let nonnegative := allowanceScale_nonnegative cached nonzero bounds anchor
    let parentAllowance : { value : Fraction.Rational // 0 ≤ value } :=
      ⟨scale * precision, Arithmetic.mul_nonneg_direct nonnegative positive.le⟩
    let childAllowance : { value : Fraction.Rational // 0 ≤ value } :=
      ⟨scale * (precision / 4), Arithmetic.mul_nonneg_direct nonnegative
        (Fraction.Order.Field.div_pos_direct positive (by decide)).le⟩
    PathModel.CompatibleConstantPathRefinement (coarse.cells none (some parentAllowance))
      (fine.cells none (some childAllowance)) := by
  let scale := allowanceScale cached bounds anchor
  have nonnegative := allowanceScale_nonnegative cached nonzero bounds anchor
  let parentAllowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨scale * precision, Arithmetic.mul_nonneg_direct nonnegative positive.le⟩
  let childAllowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨scale * (precision / 4), Arithmetic.mul_nonneg_direct nonnegative
      (Fraction.Order.Field.div_pos_direct positive (by decide)).le⟩
  let middle : Endpoint :=
    ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
  let parent := readingCell differential cap base unitBound collarBound actual precision
    ⟨left, right⟩ (coarse.get ⟨0, Nat.zero_lt_succ 0⟩) none (some parentAllowance)
  let first := readingCell differential cap base unitBound collarBound actual (precision / 4)
    ⟨left, middle⟩ (fine.get ⟨0, Nat.zero_lt_succ 1⟩) none (some childAllowance)
  let last := readingCell differential cap base unitBound collarBound actual (precision / 4)
    ⟨middle, right⟩ (fine.get ⟨1, Nat.lt_succ_self 1⟩) none (some childAllowance)
  let reference := velocity base left.parameter * (coarse.get ⟨0, Nat.zero_lt_succ 0⟩).request.reading.value
  let firstValue := velocity base left.parameter * (fine.get ⟨0, Nat.zero_lt_succ 1⟩).request.reading.value
  let lastValue := velocity base middle.parameter * (fine.get ⟨1, Nat.lt_succ_self 1⟩).request.reading.value
  have firstMovement : (left.parameter - left.parameter) ^ 2 ≤ precision := by
    rewrite [show left.parameter - left.parameter = 0 by ring1, pow_two, Fraction.Field.zero_mul_direct]
    exact positive.le
  have lastMovement : (middle.parameter - left.parameter) ^ 2 ≤ precision := by
    change (midpoint left.parameter right.parameter - left.parameter) ^ 2 ≤ precision
    rewrite [(midpoint_parameterSquares left.parameter right.parameter).1]
    exact (Basic.quarterRadius_le_scale
      (Arithmetic.sq_nonneg_direct (right.parameter - left.parameter)) 1).trans width
  have firstError := get_integrand_refinement_le cached nonzero pairs degreeBound bounds
    anchor anchorCanonical precision positive unitPrecision coarse fine coarseCanonical fineCanonical
    ⟨0, Nat.zero_lt_succ 0⟩ ⟨0, Nat.zero_lt_succ 1⟩ firstMovement
  have lastError := get_integrand_refinement_le cached nonzero pairs degreeBound bounds
    anchor anchorCanonical precision positive unitPrecision coarse fine coarseCanonical fineCanonical
    ⟨0, Nat.zero_lt_succ 0⟩ ⟨1, Nat.lt_succ_self 1⟩ lastMovement
  change Norm.Basic.normSq (firstValue - reference) ≤ scale * precision at firstError
  change Norm.Basic.normSq (lastValue - reference) ≤ scale * precision at lastError
  rewrite [Norm.Basic.normSq_eq_canonical] at firstError lastError
  have parentValue : parent.localAllowance = scale * precision :=
    readingCell.allowance_value _ _ _ _ _ _ _ _ _ _
  have firstPayment : scale * precision ≤ PathModel.parentChildAllowance parent first := by
    rewrite [← parentValue]
    exact PathModel.parentAllowance_le parent first
  have lastPayment : scale * precision ≤ PathModel.parentChildAllowance parent last := by
    rewrite [← parentValue]
    exact PathModel.parentAllowance_le parent last
  have parentPolynomial : parent.polynomial = Polynomial.Ascending.Gaussian.Basic.constant reference :=
    readingCell.polynomial _ _ _ _ _ _ _ _ _ _
  have firstPolynomial : first.polynomial = Polynomial.Ascending.Gaussian.Basic.constant firstValue :=
    readingCell.polynomial _ _ _ _ _ _ _ _ _ _
  have lastPolynomial : last.polynomial = Polynomial.Ascending.Gaussian.Basic.constant lastValue :=
    readingCell.polynomial _ _ _ _ _ _ _ _ _ _
  have firstBound : Canonical.normSq (firstValue - reference) ≤
      (PathModel.comparisonCell parent first).localAllowance := firstError.trans firstPayment
  have lastBound : Canonical.normSq (lastValue - reference) ≤
      (PathModel.comparisonCell parent last).localAllowance := lastError.trans lastPayment
  let remaining : PathModel.ConstantComparison reference [PathModel.comparisonCell parent last]
      [lastValue - reference] :=
    .cons lastValue (lastValue - reference) lastPolynomial rfl lastBound .nil
  let compared : PathModel.ConstantComparison reference
      [PathModel.comparisonCell parent first, PathModel.comparisonCell parent last]
      [firstValue - reference, lastValue - reference] :=
    .cons firstValue (firstValue - reference) firstPolynomial rfl firstBound remaining
  have certificate : PathModel.ConstantPartitionCertificate parent
      (PathModel.comparisonBlock parent ⟨[first, last]⟩) :=
    { reference := reference
      parent_polynomial_eq := parentPolynomial
      errors := [firstValue - reference, lastValue - reference]
      comparison := compared
      displacement_eq := by
        change (PathModel.comparisonCell parent first).displacement +
          ((PathModel.comparisonCell parent last).displacement + 0) = parent.displacement
        rewrite [PathModel.comparisonCell_displacement, PathModel.comparisonCell_displacement]
        dsimp only [first, last, parent]
        rewrite [readingCell.displacement, readingCell.displacement, readingCell.displacement]
        apply Purelib.Data.Gaussian.Basic.ext <;>
          simp only [Stereographic.Tangent.increment, Basic.add_re, Basic.add_im,
            Basic.zero_re, Basic.zero_im] <;> ring1 }
  change PathModel.CompatibleConstantPathRefinement
    (coarse.cells none (some parentAllowance)) (fine.cells none (some childAllowance))
  rewrite [cells_zero, cells_one]
  exact PathModel.CompatibleConstantPathRefinement.cons certificate .nil

/-- Assemble the original compatible refinement of two actual consecutive dyadic banks in their retained order.

Each leaf uses the proved comparison of its original coarse reading with
both actual midpoint children. Shared dependent-product splitting retains
every whole numerical entry; ordered append retains both literal halves.
-/
def compatible
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1)
    (anchorCanonical : anchor =
      readings differential cap base nonzero unitBound collarBound actual 0 anchorLeft anchorRight 1 (by decide))
    (precision : Fraction.Rational) (positive : 0 < precision) (unitPrecision : precision ≤ 1) :
    (depth : Nat) → (left right : Endpoint) →
    (∀ edge ∈ dyadicEdges depth left right, (edge.right.parameter - edge.left.parameter) ^ 2 ≤ precision) →
    (coarse : Readings differential cap base unitBound collarBound actual depth left right precision) →
    (fine : Readings differential cap base unitBound collarBound actual (depth + 1) left right (precision / 4)) →
    coarse = readings differential cap base nonzero unitBound collarBound actual
      depth left right precision positive →
    fine = readings differential cap base nonzero unitBound collarBound actual
      (depth + 1) left right (precision / 4) (Fraction.Order.Field.div_pos_direct positive (by decide)) →
    let scale := allowanceScale cached bounds anchor
    let nonnegative := allowanceScale_nonnegative cached nonzero bounds anchor
    let parentAllowance : { value : Fraction.Rational // 0 ≤ value } :=
      ⟨scale * precision, Arithmetic.mul_nonneg_direct nonnegative positive.le⟩
    let childAllowance : { value : Fraction.Rational // 0 ≤ value } :=
      ⟨scale * (precision / 4), Arithmetic.mul_nonneg_direct nonnegative
        (Fraction.Order.Field.div_pos_direct positive (by decide)).le⟩
    PathModel.CompatibleConstantPathRefinement (coarse.cells none (some parentAllowance))
      (fine.cells none (some childAllowance))
  | 0, left, right, widths, coarse, fine, coarseCanonical, fineCanonical =>
      partitionZero cached nonzero pairs degreeBound bounds anchor anchorCanonical
        left right precision positive unitPrecision (widths ⟨left, right⟩ (List.Mem.head []))
        coarse fine coarseCanonical fineCanonical
  | depth + 1, left, right, widths, coarse, fine, coarseCanonical, fineCanonical => by
      let middle : Endpoint :=
        ⟨midpoint left.parameter right.parameter, midpoint_inside left.inside right.inside⟩
      have coarseHalves := (congrArg split coarseCanonical).trans
        (split_readings differential cap base nonzero unitBound collarBound actual
          depth left right precision positive)
      have fineHalves := (congrArg split fineCanonical).trans
        (split_readings differential cap base nonzero unitBound collarBound actual
          (depth + 1) left right (precision / 4) (Fraction.Order.Field.div_pos_direct positive (by decide)))
      have firstWidths : ∀ edge ∈ dyadicEdges depth left middle,
          (edge.right.parameter - edge.left.parameter) ^ 2 ≤ precision := by
        intro edge member
        exact widths edge (Data.List.Membership.mem_append.mpr (Or.inl member))
      have lastWidths : ∀ edge ∈ dyadicEdges depth middle right,
          (edge.right.parameter - edge.left.parameter) ^ 2 ≤ precision := by
        intro edge member
        exact widths edge (Data.List.Membership.mem_append.mpr (Or.inr member))
      let first := compatible cached nonzero pairs degreeBound bounds anchor anchorCanonical
        precision positive unitPrecision depth left middle firstWidths (split coarse).1 (split fine).1
        (congrArg Prod.fst coarseHalves) (congrArg Prod.fst fineHalves)
      let last := compatible cached nonzero pairs degreeBound bounds anchor anchorCanonical
        precision positive unitPrecision depth middle right lastWidths (split coarse).2 (split fine).2
        (congrArg Prod.snd coarseHalves) (congrArg Prod.snd fineHalves)
      change PathModel.CompatibleConstantPathRefinement (coarse.cells none _) (fine.cells none _)
      rewrite [split_cells coarse none _, split_cells fine none _]
      exact PathModel.CompatibleConstantPathRefinement.append first last

/-- Every actual compatible consecutive bank comparison has the same computed geometric allowance bound.

The original child count cancels the original dyadic displacement square.
The retained parent and child cell budgets give a comparison allowance of
at most three times the original cached scale and coarse precision.
-/
theorem comparisonAllowance_le (scale : { value : Fraction.Rational // 0 ≤ value })
    (depth : Nat) (left right : Endpoint)
    (finePrecision : { value : Fraction.Rational // 0 ≤ value })
    (next : finePrecision.val = Basic.quarterRadius 1 depth / 4)
    {firstTarget lastTarget : Fraction.Rational}
    (coarse : Readings differential cap base unitBound collarBound actual depth left right firstTarget)
    (fine : Readings differential cap base unitBound collarBound actual (depth + 1) left right lastTarget) :
    let precision := Basic.quarterRadius 1 depth
    let positive := Basic.quarterRadius_pos (by decide : (0 : Fraction.Rational) < 1) depth
    let parentAllowance : { value : Fraction.Rational // 0 ≤ value } :=
      ⟨scale.val * precision, Arithmetic.mul_nonneg_direct scale.property positive.le⟩
    let childAllowance : { value : Fraction.Rational // 0 ≤ value } :=
      ⟨scale.val * finePrecision.val, Arithmetic.mul_nonneg_direct scale.property finePrecision.property⟩
    {parents children : List CellModel} →
    parents = coarse.cells none (some parentAllowance) →
    children = fine.cells none (some childAllowance) →
    (refinement : PathModel.CompatibleConstantPathRefinement parents children) →
    comparisonAllowance refinement ≤ 3 * scale.val * precision := by
  dsimp only
  let precision := Basic.quarterRadius 1 depth
  have positive := Basic.quarterRadius_pos (by decide : (0 : Fraction.Rational) < 1) depth
  let parentAllowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨scale.val * precision, Arithmetic.mul_nonneg_direct scale.property positive.le⟩
  let childAllowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨scale.val * finePrecision.val, Arithmetic.mul_nonneg_direct scale.property finePrecision.property⟩
  intro parents children parentsEq childrenEq refinement
  have parentBounds := cells_bounds coarse none parentAllowance precision
    (dyadicEdges_parameterSquare_le depth left right)
  have childBounds := cells_bounds fine none childAllowance (Basic.quarterRadius 1 (depth + 1))
    (dyadicEdges_parameterSquare_le (depth + 1) left right)
  have readback := comparisonCells_bounds refinement (Basic.quarterRadius 1 (depth + 1))
    parentAllowance.val childAllowance.val (fun cell member => (parentBounds cell (parentsEq ▸ member)).2)
    (fun cell member => childBounds cell (childrenEq ▸ member))
  have count := ((comparisonCells_length refinement).trans (congrArg List.length childrenEq)).trans
    (model_count fine (some childAllowance))
  have allowance := PathModel.uniform_aggregateAllowance_le ⟨comparisonCells refinement⟩ (depth + 1) 1
    (2 * (parentAllowance.val + childAllowance.val)) (by decide) count readback
  change comparisonAllowance refinement ≤ 1 * (2 * (scale.val * precision + scale.val * finePrecision.val))
    at allowance
  have scalar := congrArg (fun value => 1 * (2 * (scale.val * precision + scale.val * value))) next
  have allowance := allowance.trans_eq scalar
  have reserve := Arithmetic.mul_nonneg_direct
    (Arithmetic.mul_nonneg_direct scale.property positive.le)
    (by decide : (0 : Fraction.Rational) ≤ 1 / 2)
  have paid := Arithmetic.add_le_add_direct allowance reserve
  rewrite [_root_.add_zero] at paid
  exact paid.trans_eq (by
    simp only [Fraction.Field.div_eq_mul_inv_direct]
    have coefficients : 2 * (4 : Fraction.Rational)⁻¹ + (2 : Fraction.Rational)⁻¹ = 1 := by decide +kernel
    calc
      _ = scale.val * precision * (2 + (2 * (4 : Fraction.Rational)⁻¹ + (2 : Fraction.Rational)⁻¹)) := by ring1
      _ = 3 * scale.val * precision := by rewrite [coefficients]; ring1)

namespace EvenNegative

/-- One pair of whole original observations with their actual same-root coefficient comparison. -/
private abbrev Pair (differential reference : OddPowerDifferential curve.polynomial)
    (parameter : Canonical) (inside : collar.box.Contains (Primitives.point curve parameter))
    (target : Fraction.Rational) :=
  (source : Reading reference cap parameter inside target) ×
  (negative : Reading differential cap parameter inside target (-1)) ×
    Approximation.Gaussian.Equivalence.NamedEquivalent negative.2.1.channel.name source.2.1.channel.name

variable {reference : OddPowerDifferential curve.polynomial}
  {depth : Nat} {left right : Endpoint} {target : Fraction.Rational}
  {original : Readings reference cap base unitBound collarBound actual depth left right target}

/-- Pair the two retained banks' literal heads for cell construction without repeated prefix lookups. -/
private def pairs
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original) :=
  DependentProduct.zipWith (dyadicEdges depth left right) original retained
    (fun index =>
      let edge := (dyadicEdges depth left right)[index.val]'index.isLt
      Pair differential reference (actual.val.point edge.left.parameter)
        (point_inside base unitBound collarBound actual edge.left.parameter) target)
    (fun index source negative sameSource _ =>
      let same := sameSource.trans (Readings.get_eq original index).symm
      let compared := Approximation.Gaussian.Equivalence.NamedEquivalent.transport rfl
        (congrArg (fun value : Reading reference cap _ _ target => value.2.1.channel.name) same.symm) negative.2
      ⟨source, negative.1, compared⟩)

/-- The paired cache retains the complete original source reading at the same bounded occurrence. -/
private theorem pairs_source
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original)
    (index : Fin (dyadicEdges depth left right).length) :
    (DependentProduct.get (dyadicEdges depth left right) (pairs retained) index).1 = original.get index := by
  unfold pairs
  rewrite [DependentProduct.get_zipWith]
  exact (Readings.get_eq original index).symm

/-- The paired cache retains the complete actual negative reading at its original bounded occurrence. -/
private theorem pairs_negative
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original)
    (index : Fin (dyadicEdges depth left right).length) :
    (DependentProduct.get (dyadicEdges depth left right) (pairs retained) index).2.1 =
      (get retained index).1 := by
  unfold pairs
  rewrite [DependentProduct.get_zipWith]
  exact congrArg (fun entry => entry.1) (get_eq retained index).symm

/-- One actual same-edge pair supplies its original singleton constant partition with a computed uniform allowance. -/
private def partition (edge : ParameterEdge)
    (entry : Pair differential reference (actual.val.point edge.left.parameter)
      (point_inside base unitBound collarBound actual edge.left.parameter) target)
    (sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value }) :
    PathModel.ConstantPartitionCertificate
      (readingCell reference cap base unitBound collarBound actual target edge entry.1 none sourceAllowance)
      (PathModel.mk [readingCell differential cap base unitBound collarBound actual target edge entry.2.1 none
        (some ⟨272 * target, Arithmetic.mul_nonneg_direct
          (by decide +kernel : (0 : Fraction.Rational) ≤ 272)
      entry.1.request.positive.le⟩)]) := by
  let first := entry.1.request.reading.value
  let last := entry.2.1.request.reading.value
  let tangent := velocity base edge.left.parameter
  let error := tangent * (last - first)
  have positive := entry.1.request.positive
  let compared := entry.2.2.compare 0 0 target positive
  have distance := Approximation.Gaussian.Equivalence.Observation.Request.distance_le
    entry.2.1.request entry.1.request compared
  have speed : Norm.Basic.normSq tangent ≤ 4 :=
    (velocity_normSq_le base edge.left.parameter).trans
      ((Arithmetic.mul_le_mul_of_nonneg_left_direct unitBound (by decide)).trans_eq
        (Fraction.Field.mul_one_direct _))
  have errorBound : Norm.Basic.normSq error ≤ 272 * target := by
    change Norm.Basic.normSq (tangent * (last - first)) ≤ _
    rewrite [Norm.Basic.normSq_mul]
    exact ((Arithmetic.mul_le_mul_of_nonneg_right_direct speed
      (Norm.Basic.normSq_nonneg (last - first))).trans
        (Arithmetic.mul_le_mul_of_nonneg_left_direct distance (by decide))).trans_eq (by ring1)
  refine
    { reference := tangent * first
      parent_polynomial_eq := readingCell.polynomial _ _ _ _ _ _ _ _ _ _
      errors := [error]
      comparison := PathModel.ConstantComparison.cons (tangent * last) error
        (readingCell.polynomial _ _ _ _ _ _ _ _ _ _) ?_ ?_ .nil
      displacement_eq := ?_ }
  · change tangent * last - tangent * first = tangent * (last - first)
    ring1
  · rewrite [readingCell.allowance_value]
    change Canonical.normSq error ≤ 272 * target
    rewrite [← Norm.Basic.normSq_eq_canonical]
    exact errorBound
  · rewrite [PathModel.displacementSum_cons, PathModel.displacementSum_nil,
      readingCell.displacement, readingCell.displacement, Gaussian.Basic.add_zero]
    rfl

attribute [local irreducible] pairs

/-- The actual same-mesh source and negative banks form an ordered constant-path refinement.

Every singleton partition uses the two supplied whole observations and
their saved operational comparison. The original dependent products are
traversed together, retaining literal heads and tails rather than paying
observations or looking up prefixes again during cell construction.
-/
def refinement
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original)
    (sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value }) (positive : 0 < target) :
    PathModel.ConstantPathRefinement (original.cells none sourceAllowance)
      ((readings retained).cells none
        (some ⟨272 * target, Arithmetic.mul_nonneg_direct
          (by decide +kernel : (0 : Fraction.Rational) ≤ 272) positive.le⟩)) := by
  let allowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨272 * target, Arithmetic.mul_nonneg_direct
          (by decide +kernel : (0 : Fraction.Rational) ≤ 272) positive.le⟩
  let entries := pairs retained
  let parent := fun (index : Fin (dyadicEdges depth left right).length) (entry : Pair differential reference
      (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      (point_inside base unitBound collarBound actual
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) target) =>
    readingCell reference cap base unitBound collarBound actual target
      ((dyadicEdges depth left right)[index.val]'index.isLt) entry.1 none sourceAllowance
  let child := fun (index : Fin (dyadicEdges depth left right).length) (entry : Pair differential reference
      (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      (point_inside base unitBound collarBound actual
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) target) =>
    readingCell differential cap base unitBound collarBound actual target
      ((dyadicEdges depth left right)[index.val]'index.isLt) entry.2.1 none (some allowance)
  let certified := PathModel.ConstantPathRefinement.ofSingletons (dyadicEdges depth left right)
    entries parent child (fun index entry =>
      partition ((dyadicEdges depth left right)[index.val]'index.isLt) entry sourceAllowance)
  have parentEq : DependentProduct.mapToList (dyadicEdges depth left right) entries parent =
      original.cells none sourceAllowance := by
    rewrite [Readings.cells_eq]
    apply DependentProduct.mapToList_eq_of_get
    intro index
    exact congrArg (fun value : Reading reference cap
      (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      (point_inside base unitBound collarBound actual
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) target =>
      readingCell reference cap base unitBound collarBound actual target
      ((dyadicEdges depth left right)[index.val]'index.isLt) value none sourceAllowance)
      ((pairs_source retained index).trans (Readings.get_eq original index))
  have childEq : DependentProduct.mapToList (dyadicEdges depth left right) entries child =
      (readings retained).cells none (some allowance) := by
    rewrite [Readings.cells_eq]
    apply DependentProduct.mapToList_eq_of_get
    intro index
    exact congrArg (fun value : Reading differential cap
      (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      (point_inside base unitBound collarBound actual
        ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter) target (-1) =>
      readingCell differential cap base unitBound collarBound actual target
      ((dyadicEdges depth left right)[index.val]'index.isLt) value none (some allowance))
      ((pairs_negative retained index).trans
        ((get_readings retained index).symm.trans (Readings.get_eq (readings retained) index)))
  exact parentEq ▸ childEq ▸ certified

attribute [local semireducible] pairs

/-- The actual same-mesh negative and reference path samples differ by at most the computed uniform geometric budget.

The saved coefficient comparisons pay the two original observation
allowances. The original singleton refinement estimate and exact dyadic
count cancellation then bound the complete displacement-weighted path
sample difference; coefficient agreement alone is not used as an integral.
-/
theorem integralSample_distance_le
    (retained :
      EvenNegative differential reference cap base unitBound collarBound actual depth left right target original)
    (sourceAllowance : Option { value : Fraction.Rational // 0 ≤ value }) (positive : 0 < target) :
    let allowance : { value : Fraction.Rational // 0 ≤ value } :=
      ⟨272 * target, Arithmetic.mul_nonneg_direct
          (by decide +kernel : (0 : Fraction.Rational) ≤ 272) positive.le⟩
    Norm.Basic.normSq (((readings retained).model (some allowance)).integralSample -
      (original.model sourceAllowance).integralSample) ≤ 272 * target := by
  let allowance : { value : Fraction.Rational // 0 ≤ value } :=
    ⟨272 * target, Arithmetic.mul_nonneg_direct
          (by decide +kernel : (0 : Fraction.Rational) ≤ 272) positive.le⟩
  change Norm.Basic.normSq (((readings retained).model (some allowance)).integralSample -
    (original.model sourceAllowance).integralSample) ≤ 272 * target
  have compared := refinement retained sourceAllowance positive
  have distance :=
    Integration.Polynomial.Gaussian.Path.ConstantRefinement.PathModel.ConstantPathRefinement.integral_difference_le
      compared
  let path := (readings retained).model (some allowance)
  have count : path.cells.length = 2 ^ depth := Readings.model_count (readings retained) (some allowance)
  have localBounds := cells_bounds (readings retained) none allowance (Basic.quarterRadius 1 depth)
    (dyadicEdges_parameterSquare_le depth left right)
  have aggregate := PathModel.uniform_aggregateAllowance_le path depth 1 allowance.val (by decide) count localBounds
  rewrite [Norm.Basic.normSq_eq_canonical]
  exact distance.trans (aggregate.trans_eq (Fraction.Field.one_mul _))

end EvenNegative

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings

end
