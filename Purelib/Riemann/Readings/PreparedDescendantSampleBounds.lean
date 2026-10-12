module
import Purelib.Riemann.Comparison.PreparedNestedPrimitiveComparison
import Purelib.Riemann.Integration.PreparedPrimitiveEquivalence
import Purelib.Riemann.Normalization.InverseRootPolynomial
import Purelib.Riemann.Readings.SeededPrimitiveBounds
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Gaussian.Norm.Sum.Basic
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Integration.Polynomial.Gaussian.Cell.Allowance
import Purelib.Integration.Polynomial.Gaussian.Cell.Basic
import Purelib.Integration.Polynomial.Gaussian.Cell.Constant
import Purelib.Integration.Polynomial.Gaussian.Path.Allowance
import Purelib.Integration.Polynomial.Gaussian.Path.Basic
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Normalization.ContinuedInverseRoot
public import Purelib.Riemann.Paths.PathArea

import Purelib.Riemann.Readings.PreparedRefinementPrimitiveArea
import Purelib.Tactic.Ring
public import Purelib.Riemann.Readings.UniformPreparedRequests
import Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries
public import Purelib.Riemann.Integration.PreparedRefinementMovement
import Purelib.Data.List.Map
import Purelib.Data.Rat.Fraction.Order.Basic

open Purelib.Integration.Polynomial.Gaussian

open Purelib.Data.Rat

@[expose] public section

/-!
# Sample bounds from retained patches and actual aggregate allowances

The fixed patch bounds the inverse polynomial at every refinement index.
Prepared-centre errors are charged through their actual weighted allowances,
so no uniform upper bound on individual descendant model errors is required.
-/

namespace Purelib.Riemann.Readings.PreparedDescendantSampleBounds.LocalRequest

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedge)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples

open Purelib.Data in
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus}
  {parent : CenteredEdge curve differential} {target : Purelib.Data.Rat.Fraction.Rational}

section
open Purelib.Riemann
open Purelib.Data
/-- The retained patch's uniform sample-density ceiling from its numerator and inverse bounds. -/
def sampleDensity (request : LocalRequest parent count target) : Rat.Fraction.Rational :=
  2 * (request.request.numeratorBound * (Readings.SeededPrimitiveBounds.derivativeBounds
    request.neighborhood.base).inverseUpper +
    2 * request.request.numeratorBound * request.neighborhood.inverseErrorScale)

/-- The retained sample-density ceiling is nonnegative. -/
theorem sampleDensity_nonnegative (request : LocalRequest parent count target) : 0 ≤ sampleDensity request :=
  Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide) (add_nonneg
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct request.request.numerator_nonnegative
      (Readings.SeededPrimitiveBounds.derivativeBounds request.neighborhood.base).inverseUpper_positive.le)
    (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      request.request.numerator_nonnegative)
      request.neighborhood.inverseErrorScale_positive.le))

end

open Purelib.Riemann in
open Purelib.Approximation in
open Purelib.Data in
/-- Bound a descendant's actual center value using its original retained patch.

The density ceiling is fixed across refinement indices, while forty times the descendant's actual model-error allowance
pays the center discrepancy. -/
private theorem center_bound (localRequest : LocalRequest parent count target)
    {child : CenteredEdge curve differential} (relation : RootSubedge parent child) :
    normSq child.center.value ≤ sampleDensity localRequest + 40 * child.edge.modelErrorAllowance := by
  rcases localRequest with ⟨patch, neighborhood, neighborhoodEq, request, finishInside⟩
  subst neighborhood
  let retained : LocalRequest parent count target := ⟨patch, patch.neighborhood count, rfl, request, finishInside⟩
  have inside := Comparison.PreparedNestedPrimitiveComparison.LocalRequest.child_inside retained relation 0
    child.edge.baseInside
  let sample := Normalization.ContinuedInverseRoot.ContinuedNeighborhood.Point.acquire
    (patch.neighborhood count) (child.edge.point 0) inside
  let location := relation.location 0 child.edge.baseInside
  let equivalent := (relation.equivalent 0 child.edge.baseInside).symm.trans
    (patch.point_equivalent_at count location.fraction location.inside location.point_eq inside sample)
  have discrepancy := Integration.PreparedPrimitiveEquivalence.coefficient_center_le
    child.edge child.center sample inside request.index equivalent
  have numerator := request.numerator_le _ inside
  have inverse := (Readings.SeededPrimitiveBounds.derivativeBounds (patch.neighborhood count).base).value_le
    ((patch.neighborhood count).base.refine request.index) ((patch.neighborhood count).box_refines.contains inside)
  have coefficient := Rat.Fraction.Order.Arithmetic.mul_le_mul_direct numerator inverse
    (Gaussian.Basic.Canonical.normSq_nonneg (((patch.neighborhood count).base.refine request.index).value.eval
    (child.edge.point 0))) request.numerator_nonnegative
  rw [← Gaussian.Basic.Canonical.normSq_mul] at coefficient
  have inverseError := Rational.Geometric.Basic.quarterRadius_le_scale
    (patch.neighborhood count).inverseErrorScale_positive.le request.index
  have discrepancyLe := discrepancy.trans (Rat.Fraction.Order.Arithmetic.add_le_add_direct
    (Rat.Fraction.Order.Arithmetic.mul_le_mul_direct (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
      numerator (by decide : (0 : Rat.Fraction.Rational) ≤ 2)) inverseError
      (Rational.Geometric.Basic.quarterRadius_nonneg (patch.neighborhood count).inverseErrorScale_positive.le
        request.index)
      (Rat.Fraction.Order.Arithmetic.mul_nonneg_direct (by decide : (0 : Rat.Fraction.Rational) ≤ 2)
        request.numerator_nonnegative)) le_rfl)
  have estimate := Gaussian.Norm.Bounds.normSq_sub_le_via child.center.value
    ((PreparedPrimitiveSamples.differentialNumerator differential).eval (child.edge.point 0) *
      ((patch.neighborhood count).base.refine request.index).value.eval (child.edge.point 0)) 0
  rw [Gaussian.Basic.sub_zero, Gaussian.Basic.sub_zero] at estimate
  simp only [Gaussian.Norm.Basic.normSq_eq_canonical] at estimate
  have reverse (first last : Normalization.InverseRootPolynomial.Gaussian) : normSq (first - last) = normSq (last -
    first) := by
    rw [show first - last = -(last - first) by ring1, Gaussian.Basic.Canonical.normSq_neg]
  rw [reverse child.center.value] at estimate
  exact (estimate.trans (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Rat.Fraction.Order.Arithmetic.add_le_add_direct discrepancyLe coefficient)
    (by decide : (0 : Rat.Fraction.Rational) ≤ 2))).trans_eq (by unfold sampleDensity; ring1)

open Purelib.Riemann in
open Purelib.Integration in
open Purelib.Data in
/-- Bound a descendant's integral sample using its actual weighted allowance.

The estimate is density times movement plus five halves of the weighted allowance, including zero-displacement cells
without division by their movement. -/
theorem descendant_sample_bound (request : LocalRequest parent count target)
    {child : CenteredEdge curve differential} (relation : RootSubedge parent child) :
    normSq child.model.integralSample ≤ sampleDensity request * child.edge.pointMovement +
      (5 / 2) * child.model.weightedAllowance := by
  rw [Cell.Basic.CellModel.integralSample_constant
    child.model child.center.value rfl, Gaussian.Basic.Canonical.normSq_mul]
  rw [← Gaussian.Norm.Basic.normSq_eq_canonical child.model.displacement]
  have bound := Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (center_bound request relation)
    (show 0 ≤ child.edge.pointMovement from Gaussian.Norm.Basic.normSq_nonneg _)
  have weighted : child.model.weightedAllowance = child.edge.pointMovement * (16 * child.edge.modelErrorAllowance) := by
    unfold Integration.PreparedSubdivisionModelCore.CenteredEdge.model
      Polynomial.Gaussian.Cell.Basic.CellModel.weightedAllowance
      Polynomial.Gaussian.Cell.Basic.CellModel.displacement
        Integration.PreparedConstantModels.PreparedEdge.centeredModel
      Integration.PreparedConstantModels.PreparedEdge.pointMovement
    rw [Gaussian.Norm.Basic.normSq_eq_canonical]
  exact bound.trans_eq (by
    rw [weighted, show (5 / 2 : Rat.Fraction.Rational) * (child.edge.pointMovement * (16 *
      child.edge.modelErrorAllowance)) =
      ((5 / 2) * 16) * child.edge.pointMovement * child.edge.modelErrorAllowance by ring1,
      show (5 / 2 : Rat.Fraction.Rational) * 16 = 40 by decide +kernel]
    ring1)

end Purelib.Riemann.Readings.PreparedDescendantSampleBounds.LocalRequest

namespace Purelib.Riemann.Readings.PreparedDescendantSampleBounds.PreparedPrimitiveChargeBounds

open Purelib.Riemann.Readings.PreparedDescendantSampleBounds.LocalRequest (sampleDensity descendant_sample_bound)

open Purelib.Data.Gaussian.Basic.Canonical
open Purelib.Data.Rat.Fraction.Compatibility
open Purelib.Data.Gaussian.Norm.Sum.Basic (gaussianNormSqSum)
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.RootContinuation.PreparedSubedgeRootQueries (RootSubedgeBlock RootSubedgeRefinement)
open Purelib.Riemann.Readings.UniformPreparedRequests (LocalRequest RequestedParents)
open Purelib.Riemann.Integration.PreparedRefinementMovement (movementSum movementSum_nonnegative movementMass
  movementMass_eq)
open Purelib.Integration.Polynomial.Gaussian.Path.Basic (PathModel)

open Purelib.Data in
/-- The exact rational coordinate type. -/
private abbrev Coordinate := Rat.Fraction.Rational

variable {genus count : Nat} {curve : HyperellipticCurve genus} {differential :
  Differential genus} {target : Purelib.Data.Rat.Fraction.Rational}

open Purelib.Data in
/-- The maximum retained sample-density ceiling over the original parent requests, with zero for an empty list. -/
def sampleDensityMaximum : {parents : List (CenteredEdge curve differential)} → RequestedParents count target parents →
  Rat.Fraction.Rational
  | _, .nil => 0
  | _, .cons head tail => max (sampleDensity head) (sampleDensityMaximum tail)

/-- The maximum retained sample-density ceiling is nonnegative. -/
theorem sampleDensityMaximum_nonnegative : ∀ {parents : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents), 0 ≤ sampleDensityMaximum requests
  | _, .nil => le_rfl
  | _, .cons _ tail => (sampleDensityMaximum_nonnegative tail).trans (Fraction.Order.Basic.le_max_right _ _)

section
open Purelib.Riemann
open Purelib.Integration
open Purelib.Data
/-- Sum the descendant sample bounds within one original parent's retained root-subedge block. -/
private theorem block_samples_le {parent : CenteredEdge curve differential} (request : LocalRequest parent count target)
    {children : List (CenteredEdge curve differential)} (roots : RootSubedgeBlock parent children) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments (Polynomial.Gaussian.Path.Basic.PathModel.mk
      (children.map CenteredEdge.model))) ≤
      sampleDensity request * movementSum children +
        (5 / 2) * (Polynomial.Gaussian.Path.Basic.PathModel.mk (children.map CenteredEdge.model)).totalWeightedAllowance
          := by
  induction roots with
  | nil =>
    change (0 : Rat.Fraction.Rational) ≤ _ * 0 + (5 / 2) * 0; rw [Rat.Fraction.Field.mul_zero_direct,
      Rat.Fraction.Field.mul_zero_direct, _root_.zero_add]
  | cons head tail ih =>
      exact (Rat.Fraction.Order.Arithmetic.add_le_add_direct (descendant_sample_bound request head) ih).trans_eq (by
        simp only [movementSum, List.map_cons, Polynomial.Gaussian.Path.Basic.PathModel.totalWeightedAllowance,
          List.foldr_cons]
        ring1)

/-- The sum of squared samples splits over the exact concatenated child lists. -/
private theorem samples_append (first last : List (CenteredEdge curve differential)) :
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments (Polynomial.Gaussian.Path.Basic.PathModel.mk
      ((first ++ last).map CenteredEdge.model))) =
      Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments (Polynomial.Gaussian.Path.Basic.PathModel.mk
        (first.map CenteredEdge.model))) +
        Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments
          (Polynomial.Gaussian.Path.Basic.PathModel.mk (last.map CenteredEdge.model))) := by
  induction first with
  | nil =>
      change Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments
        (Polynomial.Gaussian.Path.Basic.PathModel.mk (last.map CenteredEdge.model))) =
        0 + Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments
          (Polynomial.Gaussian.Path.Basic.PathModel.mk (last.map CenteredEdge.model)))
      rw [_root_.zero_add]
  | cons child first ih =>
      change normSq child.model.integralSample +
        Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments
          (Polynomial.Gaussian.Path.Basic.PathModel.mk ((first ++ last).map CenteredEdge.model))) = _
      rw [ih]
      change _ = (normSq child.model.integralSample +
        Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments
          (Polynomial.Gaussian.Path.Basic.PathModel.mk (first.map CenteredEdge.model)))) +
          Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments
            (Polynomial.Gaussian.Path.Basic.PathModel.mk (last.map CenteredEdge.model)))
      ring1

end

open Purelib.Integration in
open Purelib.Data in
/-- The movement-and-weighted-allowance budget is additive over concatenated child lists. -/
private theorem budget_append (density : Rat.Fraction.Rational) (first last : List (CenteredEdge curve differential)) :
    density * movementSum (first ++ last) + (5 / 2) * (Polynomial.Gaussian.Path.Basic.PathModel.mk ((first ++ last).map
      CenteredEdge.model)).totalWeightedAllowance =
      (density * movementSum first + (5 / 2) * (Polynomial.Gaussian.Path.Basic.PathModel.mk (first.map
        CenteredEdge.model)).totalWeightedAllowance) +
        (density * movementSum last + (5 / 2) * (Polynomial.Gaussian.Path.Basic.PathModel.mk (last.map
          CenteredEdge.model)).totalWeightedAllowance) := by
  induction first with
  | nil =>
      simp only [-eq_self, -iff_self, List.nil_append, List.map_nil, movementSum,
        Polynomial.Gaussian.Path.Basic.PathModel.totalWeightedAllowance, List.foldr_nil,
        Rat.Fraction.Field.mul_zero_direct, _root_.zero_add]
      rfl
  | cons child first ih =>
      change density * (child.edge.pointMovement + movementSum (first ++ last)) +
        (5 / 2) * (child.model.weightedAllowance + (Polynomial.Gaussian.Path.Basic.PathModel.mk ((first ++ last).map
          CenteredEdge.model)).totalWeightedAllowance) =
        (density * (child.edge.pointMovement + movementSum first) +
          (5 / 2) * (child.model.weightedAllowance + (Polynomial.Gaussian.Path.Basic.PathModel.mk (first.map
            CenteredEdge.model)).totalWeightedAllowance)) +
        (density * movementSum last + (5 / 2) * (Polynomial.Gaussian.Path.Basic.PathModel.mk (last.map
          CenteredEdge.model)).totalWeightedAllowance)
      calc
        _ = density * child.edge.pointMovement + (5 / 2) * child.model.weightedAllowance +
          (density * movementSum (first ++ last) + (5 / 2) *
            (Polynomial.Gaussian.Path.Basic.PathModel.mk ((first ++ last).map
              CenteredEdge.model)).totalWeightedAllowance) := by ring1
        _ = _ := by rw [ih]; ring1

open Purelib.Riemann
open Purelib.Integration
open Purelib.Data
/-- Bound all actual descendant samples by a common density ceiling and their retained weighted allowances. -/
private theorem samples_le : ∀ {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (_refinement : RootSubedgeRefinement parents children)
    {density : Rat.Fraction.Rational}, sampleDensityMaximum requests ≤ density →
    Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments (Polynomial.Gaussian.Path.Basic.PathModel.mk
      (children.map CenteredEdge.model))) ≤
      density * movementSum children + (5 / 2) * (Polynomial.Gaussian.Path.Basic.PathModel.mk (children.map
        CenteredEdge.model)).totalWeightedAllowance
  | _, _, .nil, .nil, _, _ => by
      change (0 : Rat.Fraction.Rational) ≤ _ * 0 + (5 / 2) * 0; rw [Rat.Fraction.Field.mul_zero_direct,
        Rat.Fraction.Field.mul_zero_direct, _root_.zero_add]
  | _, _, .cons head tail, .cons (block := block) _ roots remaining, _, upper => by
      rw [samples_append, budget_append]
      exact Rat.Fraction.Order.Arithmetic.add_le_add_direct
        ((block_samples_le head roots).trans (Rat.Fraction.Order.Arithmetic.add_le_add_direct
          (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct ((Fraction.Order.Basic.le_max_left _ _).trans
            upper) (movementSum_nonnegative block)) le_rfl))
        (samples_le tail remaining ((Fraction.Order.Basic.le_max_right _ _).trans upper))

/-- Bound the count-weighted sample mass of the actual descendant bank.

The original request maximum multiplies the actual movement mass, and five halves of the scheduler's retained aggregate
allowance pays all center errors. -/
theorem refinement_sample_mass_bound {parents children : List (CenteredEdge curve differential)}
    (requests : RequestedParents count target parents) (refinement : RootSubedgeRefinement parents children) :
    (children.length : Rat.Fraction.Rational) * Gaussian.Norm.Sum.Basic.gaussianNormSqSum (Paths.PathArea.increments
      (Polynomial.Gaussian.Path.Basic.PathModel.mk (children.map CenteredEdge.model))) ≤
      sampleDensityMaximum requests * movementMass children +
        (5 / 2) * (Polynomial.Gaussian.Path.Basic.PathModel.mk (children.map CenteredEdge.model)).aggregateAllowance :=
          by
  exact (Rat.Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (samples_le requests refinement le_rfl)
    (Rat.Fraction.Cast.Order.natCast_le_direct (Nat.zero_le children.length))).trans_eq (by
      rw [movementMass_eq, Polynomial.Gaussian.Path.Basic.PathModel.aggregateAllowance]
      dsimp only [Polynomial.Gaussian.Path.Basic.PathModel.cells]
      rw [Data.List.Map.length_map]
      ring1)

end Purelib.Riemann.Readings.PreparedDescendantSampleBounds.PreparedPrimitiveChargeBounds
