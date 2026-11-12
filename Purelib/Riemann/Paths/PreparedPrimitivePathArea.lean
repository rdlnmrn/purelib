module
import Purelib.Data.List.Map
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Riemann.Integration.PreparedPrimitiveErrorBudget
import Purelib.Riemann.Integration.UniformPreparedPrimitives
import Purelib.Riemann.Paths.PreparedPrimitivePaths
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.DyadicCount
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Bounds
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Integration.Polynomial.Gaussian.Path.Primitive

import Purelib.Integration.Path.IncrementArea
public import Purelib.Riemann.Readings.UniformPreparedRequests
public import Purelib.Riemann.Paths.PathArea
import Purelib.Integration.Path.IncrementAreaComparison
import Purelib.Tactic.Ring

open Purelib.Data.Rat.Fraction.Order

public section

/-!
# Polynomial traces and actual prepared child-integral areas

Pair each retained child's polynomial increment with its actual integral
sample. All four powers of the subdivision count cancel. The polynomial
trace is evaluated at these actual child endpoints; it is not identified
with an independently chosen dyadic trace merely because totals agree.
-/

namespace Purelib.Riemann.Paths.PreparedPrimitivePathArea.PathArea

section
open Purelib.Data
/-- The canonical Gaussian rational scalar type. -/
private abbrev Gaussian := Gaussian.Basic.Canonical
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational

end

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg)

open Purelib.Integration in
open Purelib.Approximation in
open Purelib.Data in
/-- Compare the cumulative areas of two paired dyadic increment lists.

A bound on the actual samples and paired squared errors gives 32 times error times the sum of bound and error; all
powers of the retained subdivision count cancel. -/
theorem dyadic_comparison_bound (pairs : List (Gaussian.Basic.Canonical × Gaussian.Basic.Canonical)) (depth : Nat)
    (count : pairs.length = 2 ^ depth) {error bound : Rat.Fraction.Rational}
    (errorNonnegative : 0 ≤ error) (boundNonnegative : 0 ≤ bound)
    (errors : ∀ pair ∈ pairs, normSq (pair.1 - pair.2) ≤ quarterRadius error depth)
    (bounded : ∀ pair ∈ pairs, normSq pair.2 ≤ quarterRadius bound depth) :
    normSq (Path.IncrementArea.pathArea (pairs.map Prod.fst) - Path.IncrementArea.pathArea (pairs.map Prod.snd)) ≤
      32 * error * (bound + error) := by
  have eNonnegative := quarterRadius_nonneg errorNonnegative depth
  have bNonnegative := quarterRadius_nonneg boundNonnegative depth
  have leftBound (pair : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical) (member : pair ∈ pairs) :
      normSq pair.1 ≤ 2 * (quarterRadius bound depth + quarterRadius
        error depth) := by
    have estimate := Gaussian.Norm.Bounds.normSq_add_le_two (pair.1 - pair.2) pair.2
    rw [sub_add_cancel] at estimate
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
    exact estimate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add (errors pair member) (bounded pair member)) (by decide)).trans_eq (by ring1))
  have rightBound (pair : Gaussian.Basic.Canonical × Gaussian.Basic.Canonical) (member : pair ∈ pairs) :
      normSq pair.2 ≤ 2 * (quarterRadius bound depth + quarterRadius
        error depth) :=
    (bounded pair member).trans ((le_add_of_nonneg_right eNonnegative).trans
      ((le_add_of_nonneg_right (add_nonneg bNonnegative eNonnegative)).trans_eq (by ring1)))
  have estimate := Path.IncrementAreaComparison.pathArea_difference_bound pairs eNonnegative
    (Arithmetic.mul_nonneg_direct
      (by decide : (0 : Rat.Fraction.Rational) ≤ 2) (add_nonneg bNonnegative eNonnegative))
    (fun pair member => by
      have scalar := errors pair member
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar)
    (fun pair member => by
      have scalar := leftBound pair member
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar)
    (fun pair member => by
      have scalar := rightBound pair member
      simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar)
  rw [count] at estimate
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  apply estimate.trans_eq
  calc
    _ = 32 * ((((2 ^ depth : Nat) : Rat.Fraction.Rational) * (((2 ^ depth : Nat) : Rat.Fraction.Rational) *
      quarterRadius error depth))) *
      ((((2 ^ depth : Nat) : Rat.Fraction.Rational) * (((2 ^ depth : Nat) : Rat.Fraction.Rational) *
        quarterRadius bound depth)) +
        (((2 ^ depth : Nat) : Rat.Fraction.Rational) * (((2 ^ depth : Nat) : Rat.Fraction.Rational) *
          quarterRadius error depth))) := by ring1
    _ = _ := by
      rw [Rational.Geometric.DyadicCount.dyadic_count_cancel, Rational.Geometric.DyadicCount.dyadic_count_cancel]

end Purelib.Riemann.Paths.PreparedPrimitivePathArea.PathArea

namespace Purelib.Riemann.Paths.PreparedPrimitivePathArea.LocalRequest

open Purelib.Data.List

open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Data.Gaussian.Basic.Canonical
open _root_.Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianSum)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement movement_nonnegative)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_nonneg quarterRadius_eq_mul_pow)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
section
open Purelib.Data
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational
/-- The canonical Gaussian rational scalar type. -/
private abbrev Gaussian := Gaussian.Basic.Canonical

end

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {target : Data.Rat.Fraction.Rational}

section
open Purelib.Approximation
open Purelib.Data
/-- The count-paid area comparison error from retained spatial and polynomial budgets.

The scalar uses the original parent movement, primitive remainder and inverse/model errors independently of the number
of fine children. -/
@[expose] def areaComparisonError (request : LocalRequest parent count target) : Rat.Fraction.Rational :=
  2 * request.request.model.primitive.remainderBound * movement parent * quarterRadius
    (movement parent) request.request.budget.depth +
    (4 * request.request.numeratorBound * quarterRadius request.neighborhood.inverseErrorScale
      request.request.index +
      40 * request.request.budget.error) * movement parent

/-- The retained area-comparison error is nonnegative. -/
theorem areaComparisonError_nonnegative (request : LocalRequest parent count target) : 0 ≤ (areaComparisonError request)
  :=
  add_nonneg
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide)
          request.request.model.primitive.remainderBound_nonnegative)
        (movement_nonnegative parent)) (quarterRadius_nonneg (movement_nonnegative parent) _))
    (Arithmetic.mul_nonneg_direct
      (add_nonneg (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide) request.request.numerator_nonnegative)
        (quarterRadius_nonneg request.neighborhood.inverseErrorScale_positive.le _))
        (Arithmetic.mul_nonneg_direct (by decide +kernel) request.request.budget.error_positive.le))
      (movement_nonnegative parent))

end

open Purelib.Riemann in
open Purelib.Data in
/-- The retained area-comparison error is strictly below the positive requested target. -/
theorem areaComparisonError_lt (request : LocalRequest parent count target) (positive : 0 < target) :
    (areaComparisonError request) < target := by
  have estimate := Integration.PreparedPrimitiveErrorBudget.Request.operational_bound_lt request.request
    (Field.div_pos_direct positive (by decide))
  exact estimate.trans_eq ((by ring1 : 8 * (target / 8) = (target / 8) * 8).trans
    (Rat.Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)))

open Purelib.Data in
/-- Pair each actual child's polynomial increment with its retained integral sample.

Both readings use the same ordered child list and its original endpoints. -/
@[expose] def areaPairs (request : LocalRequest parent count target) : List (Gaussian.Basic.Canonical ×
  Gaussian.Basic.Canonical) :=
  request.request.block.children.map fun child =>
    (request.request.model.primitive.value.eval (child.edge.point 1) - request.request.model.primitive.value.eval
      (child.edge.point 0),
      child.model.integralSample)

open Purelib.Riemann in
open Purelib.Integration in
/-- The right paired readings are exactly the actual prepared child-path increments.

Mapping the retained paired list reads each original child sample.
The resulting ordered path is the same prepared child increment list. -/
theorem areaPairs_right (request : LocalRequest parent count target) :
    (areaPairs request).map Prod.snd = PathArea.increments (PathModel.mk
      (request.request.block.children.map CenteredEdge.model)) := by
  dsimp only [areaPairs, PathArea.increments]
  rw [Map.map_map, Map.map_map]
  rfl

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- The retained polynomial increments telescope to the original parent's endpoint difference.

The ordered child polynomial increments use their exact retained endpoints.
Their chain certificate telescopes to the original parent endpoint difference. -/
theorem areaPairs_left_total (request : LocalRequest parent count target) :
    gaussianSum ((areaPairs request).map Prod.fst) =
      request.request.model.primitive.value.eval (parent.edge.point 1) - request.request.model.primitive.value.eval
        (parent.edge.point 0) := by
  let value := request.request.model.primitive.value.eval
  have sumEq (children : List (CenteredEdge curve differential)) :
      gaussianSum (children.map (fun child => value (child.edge.point 1) - value
        (child.edge.point 0))) =
        Polynomial.Gaussian.Path.Primitive.incrementSum value (children.map CenteredEdge.model) := by
    induction children with
    | nil => rfl
    | cons child children ih =>
        exact congrArg (fun tail => value (child.edge.point 1) - value (child.edge.point 0) +
          tail) ih
  dsimp only [areaPairs]
  rw [Map.map_map]
  have telescope := (sumEq request.request.block.children).trans
    (PreparedPrimitivePaths.incrementSum_eq value request.request.block.chain)
  rw [← parent.edge.point_one, ← parent.edge.point_zero] at telescope
  exact telescope

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Every retained polynomial/sample pair satisfies the count-paid dyadic error bound. -/
theorem areaPairs_errors (request : LocalRequest parent count target) :
    ∀ pair ∈ (areaPairs request), normSq (pair.1 - pair.2) ≤ quarterRadius (areaComparisonError
      request) request.request.block.depth := by
  rcases request with ⟨patch, neighborhood, neighborhoodEq, request, finishInside⟩
  subst neighborhood
  have starts := PreparedPrimitivePaths.block_starts_inside request.block (patch.neighborhood count).box
    (patch.start_inside count) finishInside
  have finishes := PreparedPrimitivePaths.block_finishes_inside request.block (patch.neighborhood count).box
    (patch.start_inside count) finishInside
  intro pair member
  obtain ⟨child, inChildren, equal⟩ := List.Map.mem_map.mp member
  rw [← equal]
  have estimate := Integration.UniformPreparedPrimitives.children_bounded patch request.model request.block.roots
    request.numeratorBound request.budget.error
    (quarterRadius (movement parent) request.block.depth) child inChildren (starts child
      inChildren) (finishes child inChildren)
    (request.numerator_le _ (starts child inChildren)) (request.child_modelError_le inChildren)
    (PreparedPrimitivePaths.block_movement_le request.block inChildren)
  apply estimate.trans_eq
  simp only [areaComparisonError, request.block_depth, quarterRadius_eq_mul_pow]
  ring1

open Purelib.Riemann
open Purelib.Integration
open Purelib.Approximation
open Purelib.Data
/-- Compare complete cumulative areas on the actual prepared child list.

The supplied sample-density bound and retained comparison error control the squared area difference while preserving the
original child endpoints. -/
theorem area_error (request : LocalRequest parent count target) {density : Rat.Fraction.Rational}
    (densityNonnegative : 0 ≤ density)
    (bounded : ∀ child ∈ request.request.block.children,
      normSq child.model.integralSample ≤ density * quarterRadius (movement parent)
        request.request.block.depth) :
    normSq (Path.IncrementArea.pathArea ((areaPairs request).map Prod.fst) -
      Path.IncrementArea.pathArea (PathArea.increments (PathModel.mk
        (request.request.block.children.map CenteredEdge.model)))) ≤
        32 * (areaComparisonError request) * (density * movement parent + (areaComparisonError request)) := by
  rw [← areaPairs_right request]
  apply PathArea.dyadic_comparison_bound (areaPairs request) request.request.block.depth
    ((Map.length_map ..).trans request.request.block.childCount) (areaComparisonError_nonnegative request)
    (Arithmetic.mul_nonneg_direct densityNonnegative (movement_nonnegative parent)) (areaPairs_errors
      request)
  intro pair member
  obtain ⟨child, inChildren, equal⟩ := List.Map.mem_map.mp member
  rw [← equal]
  exact (bounded child inChildren).trans_eq (by simp only [quarterRadius_eq_mul_pow]; ring1)

/-- A positive target gives the strict density-weighted area-comparison bound.

The original nonnegative sample density and positive target give the strict
bound after paying the retained comparison error at the same child depth. -/
theorem area_error_lt (request : LocalRequest parent count target) (positive : 0 < target) {density :
  Rat.Fraction.Rational}
    (densityNonnegative : 0 ≤ density)
    (bounded : ∀ child ∈ request.request.block.children,
      normSq child.model.integralSample ≤ density * quarterRadius (movement parent)
        request.request.block.depth) :
    normSq (Path.IncrementArea.pathArea ((areaPairs request).map Prod.fst) -
      Path.IncrementArea.pathArea (PathArea.increments (PathModel.mk
        (request.request.block.children.map CenteredEdge.model)))) <
        32 * target * (density * movement parent + target) := by
  have paid := areaComparisonError_lt request positive
  apply (area_error request densityNonnegative bounded).trans_lt
  calc
    _ ≤ 32 * (areaComparisonError request) * (density * movement parent + target) :=
      Arithmetic.mul_le_mul_of_nonneg_left_direct (add_le_add le_rfl paid.le)
        (Arithmetic.mul_nonneg_direct (by decide +kernel) (areaComparisonError_nonnegative request))
    _ = (32 * (density * movement parent + target)) * (areaComparisonError request) := by ring1
    _ < (32 * (density * movement parent + target)) * target :=
      Arithmetic.mul_lt_mul_of_pos_left_direct
        (Arithmetic.mul_pos_direct (by decide +kernel)
          (Arithmetic.add_pos_of_nonneg_of_pos_direct
            (Arithmetic.mul_nonneg_direct densityNonnegative (movement_nonnegative parent))
            positive)) paid
    _ = _ := by ring1

/-- Retain local area, total-error and magnitude bounds for the paired child lists.

The actual sample density controls both totals; internal cumulative excursions remain in the separate area comparison.
-/
theorem prepared_area_bounds (request : LocalRequest parent count target) (positive : 0 < target) {density :
  Rat.Fraction.Rational}
    (densityNonnegative : 0 ≤ density)
    (bounded : ∀ child ∈ request.request.block.children, normSq child.model.integralSample ≤ density *
      child.edge.pointMovement) :
    let left := (areaPairs request).map Prod.fst
    let right := (areaPairs request).map Prod.snd
    normSq (Path.IncrementArea.pathArea left - Path.IncrementArea.pathArea right) ≤ 32 * target * (density * movement
      parent + target) ∧
    normSq (gaussianSum left - gaussianSum right) ≤ target ∧
    normSq (gaussianSum left) ≤ 2 * (density * movement parent + target) ∧
    normSq (gaussianSum right) ≤ 2 * (density * movement parent + target) := by
  have cellsBound (child : CenteredEdge curve differential) (member : child ∈ request.request.block.children) :
      normSq child.model.integralSample ≤ density * quarterRadius (movement parent)
        request.request.block.depth :=
    (bounded child member).trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (PreparedPrimitivePaths.block_movement_le request.request.block member) densityNonnegative)
  have rightBound : normSq (gaussianSum ((areaPairs request).map Prod.snd)) ≤ density *
    movement parent := by
    rw [areaPairs_right request]
    have estimate := Gaussian.Norm.Sum.Bounds.normSq_sum_le
      (PathArea.increments (PathModel.mk (request.request.block.children.map
        CenteredEdge.model)))
      (density * quarterRadius (movement parent) request.request.block.depth) (by
        intro value member
        obtain ⟨cell, inCells, equal⟩ := List.Map.mem_map.mp member
        obtain ⟨child, inChildren, cellEq⟩ := List.Map.mem_map.mp inCells
        rw [← equal, ← cellEq]
        have scalar := cellsBound child inChildren
        simpa only [Gaussian.Norm.Basic.normSq_eq_canonical] using scalar)
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical, PathArea.increments, Map.length_map,
      request.request.block.childCount] at estimate
    apply estimate.trans_eq
    calc
      _ = density * ((((2 ^ request.request.block.depth : Nat) : Rat.Fraction.Rational) *
        (((2 ^ request.request.block.depth : Nat) : Rat.Fraction.Rational) * quarterRadius
          (movement parent) request.request.block.depth))) := by ring1
      _ = _ := by rw [Rational.Geometric.DyadicCount.dyadic_count_cancel]
  have totalBound : normSq (gaussianSum ((areaPairs request).map Prod.fst) -
    gaussianSum ((areaPairs request).map Prod.snd)) ≤ target := by
    rw [(areaPairs_left_total request), (areaPairs_right request), PathArea.increments_sum]
    exact (request.accurate positive).le
  refine ⟨?_, totalBound, ?_, ?_⟩
  · rw [areaPairs_right request]
    exact (area_error_lt request positive densityNonnegative cellsBound).le
  · have estimate := Gaussian.Norm.Bounds.normSq_add_le_two
      (gaussianSum ((areaPairs request).map Prod.fst) -
        gaussianSum ((areaPairs request).map Prod.snd))
      (gaussianSum ((areaPairs request).map Prod.snd))
    rw [sub_add_cancel] at estimate
    simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
    exact estimate.trans ((Arithmetic.mul_le_mul_of_nonneg_left_direct
      (add_le_add totalBound rightBound) (by decide)).trans_eq (by ring1))
  · exact rightBound.trans ((le_add_of_nonneg_right positive.le).trans
      ((le_add_of_nonneg_right (add_nonneg
        (Arithmetic.mul_nonneg_direct densityNonnegative (movement_nonnegative parent))
          positive.le)).trans_eq (by ring1)))

end Purelib.Riemann.Paths.PreparedPrimitivePathArea.LocalRequest
