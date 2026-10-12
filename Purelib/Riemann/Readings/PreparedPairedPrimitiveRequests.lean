module
meta import Purelib.Elab.ConstructiveInjectivity
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box
import Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility
import Purelib.Riemann.Integration.PreparedSubdivisionModelCore
import Purelib.Riemann.Readings.PreparedPrimitiveRequests
import Purelib.Approximation.Rational.Budget.Weighted
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Curves.Hyperelliptic.Basic
import Purelib.Curves.Hyperelliptic.Differentials.Basic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives

public import Purelib.Riemann.RootContinuation.PreparedNewtonPrimitiveIncrementArea
import Purelib.Riemann.Integration.PreparedEdgeRecasting
import Purelib.Riemann.Branches.PreparedSheetContinuationCore
import Purelib.Riemann.Normalization.InverseRootPrimitive
import Purelib.Riemann.Integration.PreparedPairedModelAccuracy
import Purelib.Riemann.Readings.PreparedPrimitiveSamples
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Gaussian.Primitive.Certificate
import Purelib.Riemann.Integration.PreparedConstantModels
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Riemann.Normalization.ContinuedInverseRoot
import Purelib.Riemann.Integration.PreparedDirectDyadicRefinementsCore
import Purelib.Riemann.Branches.ClearSheetContinuation
import Purelib.Riemann.Integration.PreparedModelAccuracy
import Mathlib.Order.Basic
import Purelib.Tactic.Ring

public section

/-! Models are selected before one shared numerical and root-safe mesh. -/
namespace Purelib.Riemann.Readings.PreparedPairedPrimitiveRequests

open Purelib
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Differentials.Basic (Differential)
open Purelib.Riemann.Integration.PreparedSubdivisionModelCore (CenteredEdge)
open Purelib.Riemann.Integration.PreparedEdgeRecasting (recastCenteredEdge)
open Purelib.Riemann.Branches.UniformPrimitiveSheetCompatibility (PreparedPatch)
open Purelib.Riemann.Normalization.InverseRootPrimitive (PrimitiveModel)
open Purelib.Riemann.Readings.PreparedPrimitiveSamples (differentialNumerator)
open Purelib.Riemann.Readings.PreparedPrimitiveRequests (movement)
open Purelib.Riemann.Integration.PreparedModelAccuracy (Coordinate)
open Purelib.Riemann.Integration.PreparedPairedModelAccuracy (PairedRequest)
open Purelib.Riemann.RootContinuation.PreparedNewtonPairedPrimitives.Request (PrimitiveComparison)
open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius quarterRadius_antitone)
open Purelib.Approximation.Rational.Geometric.Search (firstQuarterBelow)

open Purelib.Approximation.Rational in
/-- A scalar weight moves into the scale of the original quarter-radius sequence. -/
theorem quarter_weight (weight scale : Coordinate) (index : Nat) :
    weight * Geometric.Basic.quarterRadius scale index = Geometric.Basic.quarterRadius (weight * scale) index := by
  simp only [Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
  ring1

open Purelib.Approximation.Rational in
open Purelib.Data.Rat in
/-- Quarter-radius values preserve the original ordering of their scales. -/
theorem quarter_scale {first second : Coordinate} (order : first ≤ second) (index : Nat) :
    Geometric.Basic.quarterRadius first index ≤ Geometric.Basic.quarterRadius second index := by
  simp only [Geometric.Basic.quarterRadius_eq_mul_pow, -eq_self, -iff_self]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct order
    (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) index)

open Purelib.Approximation.Rational in
set_option genInjectivity false in
/-- One retained quarter-radius index paying two original scalar scales.

Both bounds use the same selected index and target, preserving separate first and second scale witnesses. -/
structure IndexBudget (first second target : Coordinate) where
  /-- The selected common index in the original quarter-radius sequences. -/ index : Nat
  /-- The first original scale meets the target at the retained index. -/ firstPaid : Geometric.Basic.quarterRadius
    first index ≤ target
  /-- The second original scale meets the target at the same index. -/ secondPaid : Geometric.Basic.quarterRadius second
    index ≤ target

constructive_injectivity IndexBudget

open Purelib.Approximation.Rational in
/-- Choose a shared index paying both original nonnegative scales.

The constructive search uses their sum from index zero; monotonicity transports its bound to each retained scale. -/
@[expose] def IndexBudget.build (first second target : Coordinate)
    (firstNonnegative : 0 ≤ first) (secondNonnegative : 0 ≤ second) (positive : 0 < target) :
    IndexBudget first second target := by
  let index := Geometric.Search.firstQuarterBelow (first + second) 0 target
  have paid := (Geometric.Search.firstQuarterBelow_accurate (first + second)
    (add_nonneg firstNonnegative secondNonnegative) 0 target positive).le
  exact ⟨index, (Riemann.Readings.PreparedPairedPrimitiveRequests.quarter_scale (le_add_of_nonneg_right
    secondNonnegative) index).trans paid,
    (Riemann.Readings.PreparedPairedPrimitiveRequests.quarter_scale (le_add_of_nonneg_left firstNonnegative)
      index).trans paid⟩

variable {genus count : Nat} {curve : Purelib.Curves.Hyperelliptic.Basic.HyperellipticCurve genus} {source :
  Purelib.Curves.Hyperelliptic.Differentials.Basic.Differential genus}

open Purelib.Curves.Hyperelliptic in
/-- A shared paired request with both original primitive error densities paid.

The same model index indexes separate first and recast second comparisons, while the original parent, upper accuracy and
target remain explicit. -/
@[expose] def PaidPrimitivePair (parent : CenteredEdge curve source) (other : Differentials.Basic.Differential genus)
    (count : Nat) (upper target : Coordinate) :=
  (shared : PairedRequest parent other upper) × (index : Nat) ×
  (first : PrimitiveComparison shared.first count index) ×
    { second : PrimitiveComparison shared.second count index //
      first.errorDensity ≤ target ∧ second.errorDensity ≤ target }

open Purelib.Approximation.Rational in
open Purelib.Curves.Hyperelliptic in
open Purelib.Data.Rat in
open Purelib.Polynomial.Dense.Gaussian in
open Purelib.Riemann.Readings in
open Purelib.Riemann.RootContinuation in
/-- Prepare both original primitive rows with separate polynomial, spatial and numerical payments.

Shared polynomial and spatial indices pay one third of the target each; the positive accuracy cap pays the remaining
factor-40 term. The exact original patch and recast patch retain their selected models and common geometry. -/
@[expose] def PaidPrimitivePair.build (parent : CenteredEdge curve source) (other : Differentials.Basic.Differential
  genus)
    (patch : PreparedPatch parent) (count : Nat)
    (finishInside : (patch.neighborhood count).box.Contains (parent.edge.point 1))
    (proper : parent.edge.left.parameter < parent.edge.request.endpoint.parameter)
    (upper target : Coordinate) (upperPositive : 0 < upper) (positive : 0 < target) :
    PaidPrimitivePair parent other count upper target := by
  let otherPatch := PreparedNewtonPairedPrimitives.NewtonBandBounds.recastPrimitivePatch patch other
  let firstNumerator := Bounds.Box.denseEvalNormBound (differentialNumerator source) (patch.neighborhood count).box
  let secondNumerator := Bounds.Box.denseEvalNormBound (differentialNumerator other) (otherPatch.neighborhood count).box
  have firstNumeratorNonnegative : 0 ≤ firstNumerator :=
    (Bounds.Box.denseHornerNormBounds_nonneg (differentialNumerator source) (patch.neighborhood count).box).1
  have secondNumeratorNonnegative : 0 ≤ secondNumerator :=
    (Bounds.Box.denseHornerNormBounds_nonneg (differentialNumerator other) (otherPatch.neighborhood count).box).1
  have thirdPositive : 0 < target / 3 := Fraction.Order.Field.div_pos_direct positive (by decide)
  let polynomial := IndexBudget.build
    (4 * firstNumerator * (patch.neighborhood count).inverseErrorScale)
    (4 * secondNumerator * (otherPatch.neighborhood count).inverseErrorScale) (target / 3)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      firstNumeratorNonnegative) (patch.neighborhood count).inverseErrorScale_positive.le)
    (Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      secondNumeratorNonnegative) (otherPatch.neighborhood count).inverseErrorScale_positive.le)
    thirdPositive
  let firstModel := PrimitiveModel.ofIndex (patch.neighborhood count) polynomial.index (differentialNumerator source)
  let secondModel := PrimitiveModel.ofIndex (otherPatch.neighborhood count) polynomial.index (differentialNumerator
    other)
  have firstTaylorNonnegative : 0 ≤ 2 * firstModel.primitive.remainderBound * movement parent :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      firstModel.primitive.remainderBound_nonnegative)
      (PreparedPrimitiveRequests.movement_nonnegative parent)
  have secondTaylorNonnegative : 0 ≤ 2 * secondModel.primitive.remainderBound * movement parent :=
    Fraction.Order.Arithmetic.mul_nonneg_direct (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
      secondModel.primitive.remainderBound_nonnegative)
      (PreparedPrimitiveRequests.movement_nonnegative parent)
  let spatial := IndexBudget.build (2 * firstModel.primitive.remainderBound * movement parent)
    (2 * secondModel.primitive.remainderBound * movement parent) (target / 3)
    firstTaylorNonnegative secondTaylorNonnegative thirdPositive
  let accuracy := min upper (Budget.Weighted.allowance (target / 3) 40)
  have fortyNonnegative : (0 : Coordinate) ≤ 40 := by decide +kernel
  have accuracyPositive : 0 < accuracy := Fraction.Order.Basic.lt_min upperPositive
    (Budget.Weighted.allowance_positive thirdPositive fortyNonnegative)
  let shared := PairedRequest.build parent other proper upper accuracy accuracyPositive
    (Fraction.Order.Basic.min_le_left _ _) spatial.index
  let first := PrimitiveComparison.ofModel shared.first count polynomial.index patch firstModel finishInside
  let second := PrimitiveComparison.ofModel shared.second count polynomial.index otherPatch secondModel finishInside
  have numerical : 40 * shared.accuracy ≤ target / 3 :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct (Fraction.Order.Basic.min_le_right _ _)
      fortyNonnegative).trans
      (Budget.Weighted.mul_allowance_le thirdPositive.le fortyNonnegative)
  have firstTaylor : 2 * firstModel.primitive.remainderBound * Geometric.Basic.quarterRadius (movement parent)
    shared.first.block.depth ≤ target / 3 := by
    rw [Riemann.Readings.PreparedPairedPrimitiveRequests.quarter_weight]
    exact ((quarterRadius_antitone firstTaylorNonnegative shared.first_depth_ge).trans
      spatial.firstPaid)
  have secondTaylor : 2 * secondModel.primitive.remainderBound * Geometric.Basic.quarterRadius (movement parent)
    shared.second.block.depth ≤ target / 3 := by
    rw [Riemann.Readings.PreparedPairedPrimitiveRequests.quarter_weight]
    exact ((quarterRadius_antitone secondTaylorNonnegative shared.second_depth_ge).trans
      spatial.secondPaid)
  have firstPolynomial : 4 * firstNumerator * Geometric.Basic.quarterRadius (patch.neighborhood count).inverseErrorScale
    polynomial.index ≤ target / 3 := by
    rw [Riemann.Readings.PreparedPairedPrimitiveRequests.quarter_weight]
    exact polynomial.firstPaid
  have secondPolynomial : 4 * secondNumerator * Geometric.Basic.quarterRadius (otherPatch.neighborhood
    count).inverseErrorScale polynomial.index ≤ target / 3 := by
    rw [Riemann.Readings.PreparedPairedPrimitiveRequests.quarter_weight]
    exact polynomial.secondPaid
  have thirds : target / 3 + (target / 3 + target / 3) = target := by
    calc
      _ = (target / 3) * 3 := by ring1
      _ = target := Fraction.Field.div_mul_cancel_of_ne _ _ (by decide)
  refine ⟨shared, polynomial.index, first, second, ?_, ?_⟩
  · exact (add_le_add firstTaylor (add_le_add firstPolynomial numerical)).trans_eq thirds
  · exact (add_le_add secondTaylor (add_le_add secondPolynomial numerical)).trans_eq thirds

end Purelib.Riemann.Readings.PreparedPairedPrimitiveRequests
