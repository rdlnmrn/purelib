module

public import Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # Derived uniform bounds for actual retained circle observations

Both whole reading banks retain their original dyadic occurrences and
canonical numerical caches. The same stored observations are compared by
their actual semantic payments and the retained uniform coefficient bound.
-/

public section

namespace Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings

open Purelib.Data.Rat.Fraction.Order

open Purelib
open Purelib.Data
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian
open Purelib.Data.Rat
open Purelib.Curves.Hyperelliptic.Basic (HyperellipticCurve)
open Purelib.Curves.Hyperelliptic.Charts.Reciprocal
open Purelib.Curves.Hyperelliptic.Differentials.OddPower.Basic (OddPowerDifferential)
open Purelib.RationalFunctions.Curve (RationalCurve)
open Purelib.RationalFunctions.Curve.Canonical.Circle
open Purelib.Riemann.Branches.ClearSheetContinuation.Subdivision
open Purelib.Riemann.Normalization
open Purelib.Approximation.Gaussian
open Polynomials.Bounds

variable {genus : Nat} {curve : HyperellipticCurve genus}
  {collar : ReciprocalExteriorCollar.Data curve} {cap : ReciprocalInnerInverse.Data curve collar}
  {differential : OddPowerDifferential curve.polynomial} {base : Canonical}
  {unitBound : Norm.Basic.normSq base ≤ 1}
  {collarBound : Norm.Basic.normSq base ≤ ReciprocalExteriorCollar.innerRadius curve ^ 2}
  {actual : { value : RationalCurve // value = circle base }}
  {left right : Endpoint}

/-- Two actual canonical stored observations satisfy the retained uniform coefficient variation bound.

The complete bank equalities identify the supplied caches with the
original materialization at their own targets and depths. Their original
whole entries supply both root floors and the actual sampler ceiling;
no comparison or regularity premise is supplied by the caller.
-/
theorem get_distance_uniform_le
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {firstLeft firstRight lastLeft lastRight : Endpoint}
    {firstDepth lastDepth : Nat} {firstTarget lastTarget : Fraction.Rational}
    (firstPositive : 0 < firstTarget) (lastPositive : 0 < lastTarget)
    (first : Readings differential cap base unitBound collarBound actual firstDepth firstLeft firstRight firstTarget)
    (last : Readings differential cap base unitBound collarBound actual lastDepth lastLeft lastRight lastTarget)
    (firstCanonical : first =
      readings differential cap base nonzero unitBound collarBound actual
        firstDepth firstLeft firstRight firstTarget firstPositive)
    (lastCanonical : last =
      readings differential cap base nonzero unitBound collarBound actual
        lastDepth lastLeft lastRight lastTarget lastPositive)
    (firstIndex : Fin (dyadicEdges firstDepth firstLeft firstRight).length)
    (lastIndex : Fin (dyadicEdges lastDepth lastLeft lastRight).length)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    Norm.Basic.normSq ((last.get lastIndex).request.reading.value - (first.get firstIndex).request.reading.value) ≤
      32 * (lastTarget + firstTarget) + 4 * cached.separationCeiling bounds *
        (Norm.Basic.normSq
          (actual.val.point ((dyadicEdges lastDepth lastLeft lastRight)[lastIndex.val]'lastIndex.isLt).left.parameter -
            actual.val.point
              ((dyadicEdges firstDepth firstLeft firstRight)[firstIndex.val]'firstIndex.isLt).left.parameter) +
              accuracy) := by
  have firstFloor : rootLower (cap := cap) ≤
      (first.get firstIndex).1.1.prepared.apart.certificate.lowerSq := by
    rewrite [firstCanonical]
    exact get_lower_bound _ _ _ _ _ _ _ _ _ _ _ _ _
  have lastFloor : rootLower (cap := cap) ≤
      (last.get lastIndex).1.1.prepared.apart.certificate.lowerSq := by
    rewrite [lastCanonical]
    exact get_lower_bound _ _ _ _ _ _ _ _ _ _ _ _ _
  have samplerBound : (Name.Sampling.approximation (first.get firstIndex).1.1.certificate.value.name).centerBound ≤
      rootCeiling bounds := by
    rewrite [firstCanonical]
    have bounded := get_samplerBound differential cap base nonzero unitBound collarBound actual
      firstDepth firstLeft firstRight firstTarget firstPositive firstIndex
    exact bounded.trans_eq (by unfold rootCeiling; rewrite [bounds.numeratorUpper_eq]; rfl)
  have separation := cached.separation_le nonzero unitBound degreeBound bounds actual _ _
    (first.get firstIndex).2.1 (last.get lastIndex).2.1 firstFloor lastFloor samplerBound accuracy positive.le
  have estimate := distance_le bounds nonzero pairs first last firstIndex lastIndex accuracy positive
  exact estimate.trans ((Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl _) (Arithmetic.mul_le_mul_of_nonneg_left_direct
      separation (by decide : (0 : Fraction.Rational) ≤ 4))).trans_eq (by ring1))

/-- The retained coarse bank's actual reading gives one finite magnitude ceiling for every later canonical bank.

The same original whole form is observed at the coarse left endpoint once.
Its actual reading is retained as the anchor. The uniform coefficient
variation and both original request payments bound all other readings;
no additional observer, quotient or root is constructed.
-/
@[expose] def magnitudeBound
    {data : Polynomials differential} (cached : data.Bounds base)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (anchor : Readings differential cap base unitBound collarBound actual 0 left right 1) : Fraction.Rational :=
  2 * (64 + 4 * cached.separationCeiling bounds * (4 * Norm.Basic.normSq base + 1) +
    Norm.Basic.normSq (anchor.get ⟨0, Nat.zero_lt_succ 0⟩).request.reading.value)

/-- The actual retained coarse reading and nonnegative uniform bounds give a nonnegative magnitude ceiling. -/
theorem magnitudeBound_nonnegative
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    (anchor : Readings differential cap base unitBound collarBound actual 0 left right 1) :
    0 ≤ magnitudeBound cached bounds anchor :=
  Arithmetic.mul_nonneg_direct (by decide)
    (add_nonneg (add_nonneg (Fraction.Cast.Order.natCast_pos_direct (n := 64) (by decide)).le
      (Arithmetic.mul_nonneg_direct
        (Arithmetic.mul_nonneg_direct (by decide)
          (cached.separationCeiling_nonnegative nonzero bounds))
        (add_nonneg (Arithmetic.mul_nonneg_direct (by decide) (Norm.Basic.normSq_nonneg base))
          (by decide)))) (Norm.Basic.normSq_nonneg _))

/-- Every actual canonical reading at a target at most one meets the same retained coarse-anchor magnitude bound. -/
theorem get_normSq_le
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1)
    (anchorCanonical : anchor =
      readings differential cap base nonzero unitBound collarBound actual 0 anchorLeft anchorRight 1 (by decide))
    {depth : Nat} {target : Fraction.Rational} (positive : 0 < target) (targetBound : target ≤ 1)
    (stored : Readings differential cap base unitBound collarBound actual depth left right target)
    (canonical : stored =
      readings differential cap base nonzero unitBound collarBound actual depth left right target positive)
    (index : Fin (dyadicEdges depth left right).length) :
    Norm.Basic.normSq (stored.get index).request.reading.value ≤ magnitudeBound cached bounds anchor := by
  let first := (anchor.get ⟨0, Nat.zero_lt_succ 0⟩).request.reading.value
  let last := (stored.get index).request.reading.value
  have estimate := get_distance_uniform_le cached nonzero pairs degreeBound bounds (by decide) positive
    anchor stored anchorCanonical canonical ⟨0, Nat.zero_lt_succ 0⟩ index 1 (by decide)
  have pointDistance :
      Norm.Basic.normSq
        (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter -
          actual.val.point ((dyadicEdges 0 anchorLeft anchorRight)[0]'(Nat.zero_lt_succ 0)).left.parameter) ≤
      4 * Norm.Basic.normSq base := by
    have estimated := Norm.Bounds.normSq_sub_le_two
      (actual.val.point ((dyadicEdges depth left right)[index.val]'index.isLt).left.parameter)
      (actual.val.point ((dyadicEdges 0 anchorLeft anchorRight)[0]'(Nat.zero_lt_succ 0)).left.parameter)
    have actualNorm (time : Fraction.Rational) :
        Norm.Basic.normSq (actual.val.point time) = Norm.Basic.normSq base := by
      rewrite [actual.property]
      exact point_normSq base time
    rewrite [actualNorm, actualNorm] at estimated
    exact estimated.trans_eq (by ring1)
  have targetPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct targetBound
      (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)))
    (Fraction.Cast.Order.natCast_pos_direct (n := 32) (by decide)).le
  have targetPayment' : 32 * (target + 1) ≤ (64 : Fraction.Rational) := targetPayment.trans_eq (by ring1)
  have movementPayment := Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct pointDistance
      (Fraction.Order.Basic.le_refl (1 : Fraction.Rational)))
    (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
      (cached.separationCeiling_nonnegative nonzero bounds))
  have difference : Norm.Basic.normSq (last - first) ≤
      64 + 4 * cached.separationCeiling bounds * (4 * Norm.Basic.normSq base + 1) :=
    estimate.trans (Arithmetic.add_le_add_direct targetPayment' movementPayment)
  have triangle := Norm.Bounds.normSq_add_le_two (last - first) first
  rewrite [show last - first + first = last by ring1] at triangle
  exact triangle.trans (Arithmetic.mul_le_mul_of_nonneg_left_direct
    (Arithmetic.add_le_add_direct difference (Fraction.Order.Basic.le_refl _)) (by decide))

/-- Two actual whole-form integrand readings satisfy a uniform finite parameter-distance and request bound.

The same retained coarse observation bounds the last actual reading.
The original circle tangent supplies both its magnitude and variation;
the complete canonical banks supply the actual requested coefficients.
-/
theorem get_integrand_distance_le
    {data : Polynomials differential} (cached : data.Bounds base) (nonzero : base ≠ 0)
    (pairs : differential.denominatorPairs = 0) (degreeBound : differential.numerator.natDegree ≤ 2 * genus)
    {root : InverseModelDerivativeBounds.DerivativeBounds cap.clearance cap.model}
    (bounds : InverseModelPrimitiveBounds.PrimitiveDerivativeBounds root cap.polynomial)
    {anchorLeft anchorRight firstLeft firstRight lastLeft lastRight : Endpoint}
    (anchor : Readings differential cap base unitBound collarBound actual 0 anchorLeft anchorRight 1)
    (anchorCanonical : anchor =
      readings differential cap base nonzero unitBound collarBound actual 0 anchorLeft anchorRight 1 (by decide))
    {firstDepth lastDepth : Nat} {firstTarget lastTarget : Fraction.Rational}
    (firstPositive : 0 < firstTarget) (lastPositive : 0 < lastTarget) (lastTargetBound : lastTarget ≤ 1)
    (first : Readings differential cap base unitBound collarBound actual firstDepth firstLeft firstRight firstTarget)
    (last : Readings differential cap base unitBound collarBound actual lastDepth lastLeft lastRight lastTarget)
    (firstCanonical : first =
      readings differential cap base nonzero unitBound collarBound actual
        firstDepth firstLeft firstRight firstTarget firstPositive)
    (lastCanonical : last =
      readings differential cap base nonzero unitBound collarBound actual
        lastDepth lastLeft lastRight lastTarget lastPositive)
    (firstIndex : Fin (dyadicEdges firstDepth firstLeft firstRight).length)
    (lastIndex : Fin (dyadicEdges lastDepth lastLeft lastRight).length)
    (accuracy : Fraction.Rational) (positive : 0 < accuracy) :
    let firstTime := ((dyadicEdges firstDepth firstLeft firstRight)[firstIndex.val]'firstIndex.isLt).left.parameter
    let lastTime := ((dyadicEdges lastDepth lastLeft lastRight)[lastIndex.val]'lastIndex.isLt).left.parameter
    Norm.Basic.normSq
      (velocity base lastTime * (last.get lastIndex).request.reading.value -
        velocity base firstTime * (first.get firstIndex).request.reading.value) ≤
      8 * (32 * (lastTarget + firstTarget) + 4 * cached.separationCeiling bounds *
        (4 * (lastTime - firstTime) ^ 2 + accuracy)) +
          80 * magnitudeBound cached bounds anchor * (lastTime - firstTime) ^ 2 := by
  let firstTime := ((dyadicEdges firstDepth firstLeft firstRight)[firstIndex.val]'firstIndex.isLt).left.parameter
  let lastTime := ((dyadicEdges lastDepth lastLeft lastRight)[lastIndex.val]'lastIndex.isLt).left.parameter
  let firstValue := (first.get firstIndex).request.reading.value
  let lastValue := (last.get lastIndex).request.reading.value
  have readingDifference := get_distance_uniform_le cached nonzero pairs degreeBound bounds
    firstPositive lastPositive first last firstCanonical lastCanonical firstIndex lastIndex accuracy positive
  have magnitude := get_normSq_le cached nonzero pairs degreeBound bounds anchor anchorCanonical
    lastPositive lastTargetBound last lastCanonical lastIndex
  have pointMovement : Norm.Basic.normSq (actual.val.point lastTime - actual.val.point firstTime) ≤
      4 * (lastTime - firstTime) ^ 2 := by
    have estimated := movement_normSq_le base firstTime (lastTime - firstTime)
    rewrite [show firstTime + (lastTime - firstTime) = lastTime by ring1] at estimated
    have aligned : actual.val.point lastTime - actual.val.point firstTime =
        (circle base).point lastTime - (circle base).point firstTime := by rewrite [actual.property]; rfl
    rewrite [aligned]
    exact estimated.trans ((Arithmetic.mul_le_mul_of_nonneg_right_direct
      (Arithmetic.mul_le_mul_of_nonneg_left_direct unitBound
        (by decide : (0 : Fraction.Rational) ≤ 4))
      (Arithmetic.sq_nonneg_direct (lastTime - firstTime))).trans_eq (by ring1))
  have readingPayment := readingDifference.trans (Arithmetic.add_le_add_direct
    (Fraction.Order.Basic.le_refl _) (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct pointMovement (Fraction.Order.Basic.le_refl accuracy))
      (Arithmetic.mul_nonneg_direct (by decide : (0 : Fraction.Rational) ≤ 4)
        (cached.separationCeiling_nonnegative nonzero bounds))))
  have firstFactor := Arithmetic.mul_le_mul_of_nonneg_right_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct unitBound
      (Fraction.Cast.Order.natCast_pos_direct (n := 40) (by decide)).le)
    (Arithmetic.sq_nonneg_direct (lastTime - firstTime))
  have firstTerm := Arithmetic.mul_le_mul_direct firstFactor magnitude
    (Norm.Basic.normSq_nonneg lastValue)
    (Arithmetic.mul_nonneg_direct
      (Arithmetic.mul_nonneg_direct
        (Fraction.Cast.Order.natCast_pos_direct (n := 40) (by decide)).le (by decide))
      (Arithmetic.sq_nonneg_direct (lastTime - firstTime)))
  have secondTerm := Arithmetic.mul_le_mul_direct
    (Arithmetic.mul_le_mul_of_nonneg_left_direct unitBound (by decide : (0 : Fraction.Rational) ≤ 4))
    readingPayment (Norm.Basic.normSq_nonneg (lastValue - firstValue))
    (Arithmetic.mul_nonneg_direct (by decide) (by decide))
  have estimate := (integrand_distance_le base firstTime lastTime firstValue lastValue).trans
    (Arithmetic.mul_le_mul_of_nonneg_left_direct
      (Arithmetic.add_le_add_direct firstTerm secondTerm) (by decide))
  exact estimate.trans_eq (by ring1)

end Purelib.Curves.Hyperelliptic.Charts.Reciprocal.Cap.FormReadings.Circle.Readings

end
