module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip.Spatial
import Purelib.Approximation.Rational.Geometric.Search
public import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Refinement.Common
import Purelib.Curves.Legendre.Periods.Jets.Variation
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Curves.Legendre.Paths
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Vector.Dependent
import Purelib.Polynomial.Geometry.ClearPath
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision.Dyadic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.RationalEmbedding.Bounds
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Tactic.Ring

/-! # Joint radicand variation in one original signed strip budget

The same original segment and seed budget admit the entire rational
parameter/spatial rectangle. Two GIVEN endpoint spatial paths supply a
uniform spatial scale through the exact affine radicand identity. One
finite quarter search then pays a whole rectangular cell before root or
point observations are requested. No filled root cell is asserted here.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Geometry.Rational (Box)
open Purelib.Polynomial.Geometry.ClearPath (ClearSegment)
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation
open Purelib.Riemann.RootContinuation.FixedRootBoxPath (Inside PathData)
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision

/-- The Legendre radicand, rather than its roots, is the exact affine interpolation of its two parameter endpoints. -/
theorem interpolated_eval_affine (parameter increment point : Canonical) (time : Rational) :
    (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval point =
      (⟨1 - time, 0⟩ : Canonical) * (Paths.polynomial parameter).eval point +
        (⟨time, 0⟩ : Canonical) * (Paths.polynomial (parameter + increment)).eval point := by
  have complement : (⟨1 - time, 0⟩ : Canonical) = 1 - (⟨time, 0⟩ : Canonical) := by
    apply Basic.ext
    · rewrite [Basic.sub_re]
      rfl
    · rewrite [Basic.sub_im]
      change (0 : Rational) = 0 - 0
      ring1
  rewrite [radicand_eq, radicand_eq, radicand_eq,
    Variation.radicand_step parameter ((⟨time, 0⟩ : Canonical) * increment) point,
    Variation.radicand_step parameter increment point, complement]
  ring1

variable {parameter : Canonical} {count : Nat}
    {patch : ContinuedNeighborhood (Paths.polynomial parameter) count}
    (range : Range patch) (budget : FixedRootBoxBudget.Budget patch.base.seed.owner)
    (factory : budget = range.seedBudget)
    {ambient : Box} {start finish : Canonical}
    (segment : ClearSegment (Paths.polynomial parameter) ambient start finish)
    (firstInside : patch.box.Contains start) (lastInside : patch.box.Contains finish)
    (increment : Canonical) (admitted : Norm.Basic.normSq increment ≤ range.stripBound)

include range factory firstInside lastInside admitted in
/-- Every point of the whole parameter/spatial rectangle satisfies the SAME retained original movement budget. -/
theorem rectangle_movement (time fraction : Rational) (timeInside : Inside time) (fractionInside : Inside fraction) :
    Canonical.normSq ((Paths.polynomial parameter).eval patch.base.site.center -
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
        (segment.pointAt fraction)) ≤ budget.movement := by
  have paid := range.seed_movement_le
    (segment.pointAt_contains_of_endpoints firstInside lastInside fraction fractionInside)
    ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time timeInside increment admitted)
  rewrite [Norm.Basic.normSq_eq_canonical] at paid
  have movement := (congrArg (fun value : FixedRootBoxBudget.Budget patch.base.seed.owner => value.movement)
    factory).trans range.seedBudget_movement
  exact paid.trans_eq movement.symm

include range firstInside lastInside admitted in
/-- The original strip clearance proves nonvanishing at every point of that entire admitted rectangle. -/
theorem rectangle_nonzero (time fraction : Rational) (timeInside : Inside time) (fractionInside : Inside fraction) :
    (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval
      (segment.pointAt fraction) ≠ 0 :=
  range.strip_nonzero (segment.pointAt_contains_of_endpoints firstInside lastInside fraction fractionInside)
    ((⟨time, 0⟩ : Canonical) * increment) (range.interpolated_admitted time timeInside increment admitted)

variable (zeroInside : Inside 0) (oneInside : Inside 1)
    (firstPath lastPath : PathData budget budget)
    (firstFactory : firstPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 0 zeroInside)
    (lastFactory : lastPath =
      range.spatialPath budget factory segment firstInside lastInside increment admitted 1 oneInside)

include firstFactory in
/-- The given first spatial path reads the literal original polynomial on the SAME original segment. -/
theorem firstSpatial_point (fraction : Rational) :
    firstPath.point fraction = (Paths.polynomial parameter).eval (segment.pointAt fraction) := by
  have read := (congrArg (fun value : PathData budget budget => value.point fraction) firstFactory).trans
    (range.spatialPath_point budget factory segment firstInside lastInside increment admitted 0 zeroInside fraction)
  have scalar : parameter + (⟨(0 : Rational), 0⟩ : Canonical) * increment = parameter := by
    change parameter + 0 * increment = parameter
    exact (congrArg (fun value : Canonical => parameter + value) (Basic.zero_mul increment)).trans
      (Basic.add_zero parameter)
  exact read.trans (congrArg (fun value => (Paths.polynomial value).eval (segment.pointAt fraction)) scalar)

include lastFactory in
/-- The given last spatial path reads the shifted polynomial on that SAME oriented segment. -/
theorem lastSpatial_point (fraction : Rational) :
    lastPath.point fraction = (Paths.polynomial (parameter + increment)).eval (segment.pointAt fraction) := by
  have read := (congrArg (fun value : PathData budget budget => value.point fraction) lastFactory).trans
    (range.spatialPath_point budget factory segment firstInside lastInside increment admitted 1 oneInside fraction)
  have scalar : parameter + (⟨(1 : Rational), 0⟩ : Canonical) * increment = parameter + increment := by
    change parameter + 1 * increment = parameter + increment
    exact congrArg (fun value : Canonical => parameter + value) (Basic.one_mul increment)
  exact read.trans (congrArg (fun value => (Paths.polynomial value).eval (segment.pointAt fraction)) scalar)

/-- The same two retained endpoint spatial scales give a nonnegative uniform spatial scale. -/
@[expose] def spatialScale : Rational := 2 * (firstPath.scale + lastPath.scale)

/-- Both original endpoint scale certificates make their displayed uniform spatial scale nonnegative. -/
theorem spatialScale_nonnegative : 0 ≤ spatialScale (budget := budget) firstPath lastPath := by
  have sum : 0 ≤ firstPath.scale + lastPath.scale := by
    calc
      0 = 0 + 0 := by ring1
      _ ≤ _ := Order.Arithmetic.add_le_add_direct firstPath.scale_nonnegative lastPath.scale_nonnegative
  exact Order.Arithmetic.mul_nonneg_direct (by decide +kernel) sum

include firstFactory lastFactory in
/-- The exact affine radicand identity gives one spatial bound at every interpolation time.

Both endpoint paths retain the SAME segment, budget and increment factories.
Only their radicand values are interpolated; no interpolation or selection
of root Owners occurs in this estimate.
-/
theorem spatial_variation (time left right : Rational) (timeInside : Inside time)
    (leftInside : Inside left) (rightInside : Inside right) :
    Norm.Basic.normSq
      ((Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (segment.pointAt left) -
        (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (segment.pointAt right)) ≤
      spatialScale (budget := budget) firstPath lastPath * (right - left) ^ 2 := by
  have complementNonnegative := Order.Arithmetic.sub_nonneg_direct timeInside.2
  have complementUpper : 1 - time ≤ (1 : Rational) :=
    (Order.Arithmetic.sub_le_sub_left_direct timeInside.1 1).trans_eq (by ring1)
  have firstWeight : Norm.Basic.normSq (⟨1 - time, 0⟩ : Canonical) ≤ 1 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact RationalEmbedding.Bounds.unit_parameter complementNonnegative complementUpper
  have lastWeight : Norm.Basic.normSq (⟨time, 0⟩ : Canonical) ≤ 1 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact RationalEmbedding.Bounds.unit_parameter timeInside.1 timeInside.2
  have affine :
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (segment.pointAt left) -
          (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (segment.pointAt right) =
        (⟨1 - time, 0⟩ : Canonical) * (firstPath.point left - firstPath.point right) +
          (⟨time, 0⟩ : Canonical) * (lastPath.point left - lastPath.point right) := by
    rewrite [interpolated_eval_affine, interpolated_eval_affine,
      firstSpatial_point range budget factory segment firstInside lastInside increment admitted zeroInside
        firstPath firstFactory left,
      firstSpatial_point range budget factory segment firstInside lastInside increment admitted zeroInside
        firstPath firstFactory right,
      lastSpatial_point range budget factory segment firstInside lastInside increment admitted oneInside
        lastPath lastFactory left,
      lastSpatial_point range budget factory segment firstInside lastInside increment admitted oneInside
        lastPath lastFactory right]
    ring1
  have firstBound : Norm.Basic.normSq (firstPath.point left - firstPath.point right) ≤
      firstPath.scale * (right - left) ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact firstPath.variation left right leftInside rightInside
  have lastBound : Norm.Basic.normSq (lastPath.point left - lastPath.point right) ≤
      lastPath.scale * (right - left) ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    exact lastPath.variation left right leftInside rightInside
  have firstScaled := (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct firstWeight
    (Norm.Basic.normSq_nonneg (firstPath.point left - firstPath.point right))).trans_eq (Field.one_mul _)
  have lastScaled := (Order.Arithmetic.mul_le_mul_of_nonneg_right_direct lastWeight
    (Norm.Basic.normSq_nonneg (lastPath.point left - lastPath.point right))).trans_eq (Field.one_mul _)
  have estimate := Norm.Bounds.normSq_add_le_two
    ((⟨1 - time, 0⟩ : Canonical) * (firstPath.point left - firstPath.point right))
    ((⟨time, 0⟩ : Canonical) * (lastPath.point left - lastPath.point right))
  rewrite [← affine] at estimate
  rewrite [Norm.Basic.normSq_mul, Norm.Basic.normSq_mul] at estimate
  exact (estimate.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct (firstScaled.trans firstBound) (lastScaled.trans lastBound))
    (by decide +kernel))).trans_eq (by unfold spatialScale; ring1)

include firstInside lastInside in
/-- The original whole-box Legendre coefficient bounds temporal variation uniformly at every spatial fraction. -/
theorem temporal_variation (left right fraction : Rational) (fractionInside : Inside fraction) :
    Norm.Basic.normSq
      ((Paths.polynomial (parameter + (⟨left, 0⟩ : Canonical) * increment)).eval (segment.pointAt fraction) -
        (Paths.polynomial (parameter + (⟨right, 0⟩ : Canonical) * increment)).eval (segment.pointAt fraction)) ≤
      (Norm.Basic.normSq increment * range.coefficient) * (right - left) ^ 2 := by
  rewrite [interpolation_normSq]
  exact Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      (range.coefficient_upper (segment.pointAt_contains_of_endpoints firstInside lastInside fraction fractionInside))
      (Norm.Basic.normSq_nonneg increment)) (Order.Arithmetic.sq_nonneg_direct _)

include firstFactory lastFactory in
/-- Temporal and spatial variation give one squared-movement bound for the actual radicand rectangle. -/
theorem joint_variation (firstTime lastTime firstFraction lastFraction : Rational)
    (lastTimeInside : Inside lastTime) (firstInside' : Inside firstFraction) (lastInside' : Inside lastFraction) :
    Norm.Basic.normSq
      ((Paths.polynomial (parameter + (⟨firstTime, 0⟩ : Canonical) * increment)).eval (segment.pointAt firstFraction) -
        (Paths.polynomial (parameter + (⟨lastTime, 0⟩ : Canonical) * increment)).eval (segment.pointAt lastFraction)) ≤
      2 * ((Norm.Basic.normSq increment * range.coefficient) * (lastTime - firstTime) ^ 2 +
        spatialScale (budget := budget) firstPath lastPath * (lastFraction - firstFraction) ^ 2) := by
  let first := (Paths.polynomial (parameter + (⟨firstTime, 0⟩ : Canonical) * increment)).eval
    (segment.pointAt firstFraction)
  let middle := (Paths.polynomial (parameter + (⟨lastTime, 0⟩ : Canonical) * increment)).eval
    (segment.pointAt firstFraction)
  let last := (Paths.polynomial (parameter + (⟨lastTime, 0⟩ : Canonical) * increment)).eval
    (segment.pointAt lastFraction)
  have split : first - last = (first - middle) + (middle - last) := by ring1
  have estimate := Norm.Bounds.normSq_add_le_two (first - middle) (middle - last)
  rewrite [← split] at estimate
  exact estimate.trans (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (temporal_variation range segment firstInside lastInside increment firstTime lastTime firstFraction firstInside')
      (spatial_variation range budget factory segment firstInside lastInside increment admitted zeroInside oneInside
        firstPath lastPath firstFactory lastFactory lastTime firstFraction lastFraction
        lastTimeInside firstInside' lastInside')) (by decide +kernel))

/-- The uniform joint scale pays temporal and spatial widths at the same dyadic depth. -/
@[expose] def jointScale : Rational :=
  2 * (Norm.Basic.normSq increment * range.coefficient + spatialScale (budget := budget) firstPath lastPath)

/-- The original coefficient and both original endpoint scales make the joint scale nonnegative. -/
theorem jointScale_nonnegative : 0 ≤ jointScale (range := range) (budget := budget) increment firstPath lastPath := by
  have sum : 0 ≤ Norm.Basic.normSq increment * range.coefficient +
      spatialScale (budget := budget) firstPath lastPath := by
    calc
      0 = 0 + 0 := by ring1
      _ ≤ _ := Order.Arithmetic.add_le_add_direct
        (Order.Arithmetic.mul_nonneg_direct (Norm.Basic.normSq_nonneg increment) range.coefficient_nonnegative)
        (spatialScale_nonnegative (budget := budget) firstPath lastPath)
  exact Order.Arithmetic.mul_nonneg_direct (by decide +kernel) sum

/-- Select a genuine finite joint dyadic depth before requesting grid observations or root Owners.

The original budget's positive target clearance, not nonvanishing alone,
pays one eighth of the full cell movement. The two GIVEN endpoint path
scales and exact increment determine the retained executable search.
-/
def jointSelection :
    Search.Selection (jointScale (range := range) (budget := budget) increment firstPath lastPath)
      0 (budget.clearance / 8) :=
  Search.Selection.build _ (jointScale_nonnegative (range := range) (budget := budget) increment firstPath lastPath) 0 _
    (Order.Field.div_pos_direct budget.clearance_positive (by decide +kernel))

include firstFactory lastFactory in
/-- The selected joint depth pays the entire actual dyadic cell from its retained lower-left corner.

Both dyadic edges retain their original bounded occurrences and orientations.
Every point in their closed rectangle is covered by the same movement
estimate; no root query, root comparison or filled root cell is assumed.
-/
theorem cell_movement_lt
    (selected : Search.Selection (jointScale (range := range) (budget := budget) increment firstPath lastPath)
      0 (budget.clearance / 8))
    (timeDepth spatialDepth : Nat) (timeEnough : selected.stage ≤ timeDepth)
    (spatialEnough : selected.stage ≤ spatialDepth)
    (timeFirst timeLast spatialFirst spatialLast : Endpoint)
    (timeOrdered : timeFirst.parameter ≤ timeLast.parameter)
    (spatialOrdered : spatialFirst.parameter ≤ spatialLast.parameter)
    (timeIndex : Fin (dyadicEdges timeDepth timeFirst timeLast).length)
    (spatialIndex : Fin (dyadicEdges spatialDepth spatialFirst spatialLast).length)
    (time fraction : Rational)
    (timeBetween :
      ((dyadicEdges timeDepth timeFirst timeLast)[timeIndex.val]'timeIndex.isLt).left.parameter ≤ time ∧
        time ≤ ((dyadicEdges timeDepth timeFirst timeLast)[timeIndex.val]'timeIndex.isLt).right.parameter)
    (fractionBetween :
      ((dyadicEdges spatialDepth spatialFirst spatialLast)[spatialIndex.val]'spatialIndex.isLt).left.parameter ≤
          fraction ∧
        fraction ≤
          ((dyadicEdges spatialDepth spatialFirst spatialLast)[spatialIndex.val]'spatialIndex.isLt).right.parameter) :
    Norm.Basic.normSq
      ((Paths.polynomial (parameter +
          (⟨((dyadicEdges timeDepth timeFirst timeLast)[timeIndex.val]'timeIndex.isLt).left.parameter, 0⟩ :
            Canonical) * increment)).eval
          (segment.pointAt
            ((dyadicEdges spatialDepth spatialFirst spatialLast)[spatialIndex.val]'spatialIndex.isLt).left.parameter) -
        (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval (segment.pointAt fraction)) <
      budget.clearance / 8 := by
  let timeEdge := (dyadicEdges timeDepth timeFirst timeLast)[timeIndex.val]'timeIndex.isLt
  let spatialEdge := (dyadicEdges spatialDepth spatialFirst spatialLast)[spatialIndex.val]'spatialIndex.isLt
  have timeInside : Inside time :=
    ⟨timeEdge.left.inside.1.trans timeBetween.1, timeBetween.2.trans timeEdge.right.inside.2⟩
  have fractionInside : Inside fraction :=
    ⟨spatialEdge.left.inside.1.trans fractionBetween.1,
      fractionBetween.2.trans spatialEdge.right.inside.2⟩
  have timeSquared : (time - timeEdge.left.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 selected.stage :=
    (Order.Arithmetic.pow_le_pow_direct (Order.Arithmetic.sub_nonneg_direct timeBetween.1)
      (Order.Arithmetic.sub_le_sub_right_direct timeBetween.2 timeEdge.left.parameter) 2).trans
        (dyadicEdges_width_le timeDepth selected.stage timeEnough timeFirst timeLast timeOrdered timeEdge
          (List.getElem_mem timeIndex.isLt))
  have spatialSquared : (fraction - spatialEdge.left.parameter) ^ 2 ≤ Geometric.Basic.quarterRadius 1 selected.stage :=
    (Order.Arithmetic.pow_le_pow_direct (Order.Arithmetic.sub_nonneg_direct fractionBetween.1)
      (Order.Arithmetic.sub_le_sub_right_direct fractionBetween.2 spatialEdge.left.parameter) 2).trans
        (dyadicEdges_width_le spatialDepth selected.stage spatialEnough spatialFirst spatialLast spatialOrdered
          spatialEdge (List.getElem_mem spatialIndex.isLt))
  have temporalNonnegative := Order.Arithmetic.mul_nonneg_direct
    (Norm.Basic.normSq_nonneg increment) range.coefficient_nonnegative
  have varied := joint_variation range budget factory segment firstInside lastInside increment admitted
    zeroInside oneInside firstPath lastPath firstFactory lastFactory
    timeEdge.left.parameter time spatialEdge.left.parameter fraction
    timeInside spatialEdge.left.inside fractionInside
  have paid := Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Order.Arithmetic.add_le_add_direct
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct timeSquared temporalNonnegative)
      (Order.Arithmetic.mul_le_mul_of_nonneg_left_direct spatialSquared
        (spatialScale_nonnegative (budget := budget) firstPath lastPath)))
    (by decide +kernel : (0 : Rational) ≤ 2)
  have scalar :
      2 * ((Norm.Basic.normSq increment * range.coefficient) * Geometric.Basic.quarterRadius 1 selected.stage +
        spatialScale (budget := budget) firstPath lastPath * Geometric.Basic.quarterRadius 1 selected.stage) =
      Geometric.Basic.quarterRadius (jointScale (range := range) (budget := budget) increment firstPath lastPath)
        selected.stage := by
    simp only [Geometric.Basic.quarterRadius_eq_mul_pow]
    unfold jointScale
    ring1
  exact ((varied.trans paid).trans_eq scalar).trans_lt
    (selected.later_accurate (Nat.le_refl selected.stage))

/-- The exact selected search and both original coarse occurrence tables on its one common spatial grid. -/
@[expose] def JointGrid (firstDepth lastDepth : Nat) (left right : Endpoint) :=
  (selected : { value : Search.Selection
      (jointScale (range := range) (budget := budget) increment firstPath lastPath) 0 (budget.clearance / 8) //
      value = jointSelection (range := range) (budget := budget) increment firstPath lastPath }) ×
    { pairs : Data.Vector.DependentVector (fun index =>
        RefinementPairAbove firstDepth lastDepth selected.val.stage left right index) //
      pairs = refinementPairsAbove firstDepth lastDepth selected.val.stage left right }

include firstFactory lastFactory in
/-- Select the paid depth first, then retain both actual occurrence outcomes before any grid observations.

This construction calls one original finite search and one original common
occurrence-table builder. Its two lookup outcomes preserve both coarse
indices even for repeated or stationary physical parent occurrences.
-/
def jointGrid (firstDepth lastDepth : Nat) (left right : Endpoint) :
    JointGrid (range := range) (budget := budget) increment firstPath lastPath firstDepth lastDepth left right :=
  let selected := jointSelection (range := range) (budget := budget) increment firstPath lastPath
  let pairs := refinementPairsAbove firstDepth lastDepth selected.stage left right
  ⟨⟨selected, rfl⟩, ⟨pairs, rfl⟩⟩

namespace JointGrid

variable {range budget increment firstPath lastPath}

variable {firstDepth lastDepth : Nat} {left right : Endpoint}
    (grid : JointGrid (range := range) (budget := budget) increment firstPath lastPath
      firstDepth lastDepth left right)

/-- Read the SAME retained executable search outcome before requesting any grid root observation. -/
@[expose] def selection :
    Search.Selection (jointScale (range := range) (budget := budget) increment firstPath lastPath)
      0 (budget.clearance / 8) := grid.1.val

/-- The stored search keeps its whole original jointSelection factory, not merely its selected stage. -/
theorem selection_eq : grid.selection =
    jointSelection (range := range) (budget := budget) increment firstPath lastPath := grid.1.property

/-- Read both SAME original bounded occurrence outcomes at every common fine-grid index. -/
@[expose] def pairs : Data.Vector.DependentVector (fun index =>
    RefinementPairAbove firstDepth lastDepth grid.selection.stage left right index) := grid.2.val

/-- The entire stored occurrence table retains its original common-grid construction factory. -/
theorem pairs_eq : grid.pairs =
    refinementPairsAbove firstDepth lastDepth grid.selection.stage left right := grid.2.property

/-- The common spatial depth pays the selected joint minimum before either coarse mesh is queried. -/
theorem spatialMinimum : grid.selection.stage ≤ firstDepth + (lastDepth + grid.selection.stage) :=
  commonDepth_minimum firstDepth lastDepth grid.selection.stage

/-- The common spatial grid retains the first original mesh depth. -/
theorem firstMinimum : firstDepth ≤ firstDepth + (lastDepth + grid.selection.stage) :=
  commonDepth_first firstDepth lastDepth grid.selection.stage

/-- The same common spatial grid retains the second original mesh depth. -/
theorem lastMinimum : lastDepth ≤ firstDepth + (lastDepth + grid.selection.stage) :=
  commonDepth_last firstDepth lastDepth grid.selection.stage

end JointGrid

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
