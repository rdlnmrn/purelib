module
import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Cast.Order
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Geometry.Rational.Box.Separation.Norm
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Residual.Radius
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Basic
public import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Uniqueness
import Purelib.Polynomial.Dense.Gaussian.GCD
import Purelib.RootIsolation.State.WindingOne.Basic
public import Purelib.RootIsolation.Track.Basic
import Purelib.RootIsolation.Track.Residual
import Purelib.Polynomial.Dense.Gaussian.Bounds.Box.Taylor
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Geometry.Rational.Box.Bounds
import Purelib.Geometry.Rational.Box.Refinement
public import Purelib.Geometry.Rational.Box.Separation
import Purelib.Polynomial.Dense.Basic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

open Purelib.RootIsolation

/-!
# Incompatibility of separated tracks in a small box

Retained coordinate gaps, residual requests and finite Taylor error bounds
exclude support of two separated winding-one tracks below the same threshold.
-/

namespace Purelib.RootIsolation.Track.Separation.Separated

/-- Separated winding-one states cannot share a box below the uniqueness threshold.

The original two tracks refine their supplied states at the same computed
residual request. Their coordinate gap and the retained derivative/Taylor
certificates contradict simultaneous support in that smaller common box. -/
public theorem separated_tracks_not_supported_in_small_common_box_of_separation
    {p : Polynomial.Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (degreePositive : 0 < p.natDegree)
    (separation : Dense.Gaussian.Derivative.Separation.Basic.Certificate p ambient)
    (leftTrack rightTrack : Basic.WindingOneTrack p ambient)
    (leftState rightState : State.WindingOne.Basic.WindingOneState p ambient)
    (separated : leftState.box.Separated rightState.box)
    (common : Box)
    (leftCommon : leftState.box.Refines common)
    (rightCommon : rightState.box.Refines common)
    (small : common.diagonalSq <
      Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold ambient separation) : False
        := by
  obtain ⟨gap, gapPositive, gapLower⟩ := Box.Separation.Norm.separated_normSq_lower separated
  let threshold := Dense.Gaussian.Derivative.Separation.Uniqueness.separatedPairResidualThreshold ambient separation gap
  have thresholdPositive := Dense.Gaussian.Derivative.Separation.Uniqueness.separatedPairResidualThreshold_pos ambient
    separation gapPositive
  let radius := Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius p ambient threshold
  let radiusPositive := Dense.Gaussian.Bounds.Box.Residual.Radius.residualRefinementRadius_pos p ambient
    thresholdPositive
  let leftRefined := leftTrack.refine leftState radius radiusPositive
  let rightRefined := rightTrack.refine rightState radius radiusPositive
  let u := leftRefined.box.anchor
  let v := rightRefined.box.anchor
  have leftResidual : Data.Gaussian.Norm.Basic.normSq (p.eval u) ≤ threshold := by
    simpa only [radius, radiusPositive, leftRefined, u] using
      Track.Residual.refined_anchor_residual_le degreePositive leftTrack leftState
        thresholdPositive
  have rightResidual : Data.Gaussian.Norm.Basic.normSq (p.eval v) ≤ threshold := by
    simpa only [radius, radiusPositive, rightRefined, v] using
      Track.Residual.refined_anchor_residual_le degreePositive rightTrack rightState
        thresholdPositive
  have uLeft : leftState.box.Contains u :=
    (leftTrack.nested leftState radius radiusPositive).contains
      leftRefined.box.contains_anchor
  have vRight : rightState.box.Contains v :=
    (rightTrack.nested rightState radius radiusPositive).contains
      rightRefined.box.contains_anchor
  have uAmbient : ambient.Contains u := leftState.refinesAmbient.contains uLeft
  have vAmbient : ambient.Contains v := rightState.refinesAmbient.contains vRight
  have uCommon : common.Contains u := leftCommon.contains uLeft
  have vCommon : common.Contains v := rightCommon.contains vRight
  let distance := Data.Gaussian.Norm.Basic.normSq (v - u)
  have distanceLower : gap ^ 2 ≤ distance := by
    have raw := gapLower uLeft vRight
    calc
      gap ^ 2 ≤ Data.Gaussian.Norm.Basic.normSq (u - v) := raw
      _ = Data.Gaussian.Norm.Basic.normSq (v - u) := by
        simp only [Data.Gaussian.Norm.Basic.normSq, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im]
        ring1
  have distancePositive : 0 < distance :=
    (Fraction.Order.Arithmetic.pow_pos_direct gapPositive 2).trans_le
      distanceLower
  have distanceUpper : distance ≤ common.diagonalSq :=
    common.normSq_sub_le_diagonalSq vCommon uCommon
  have distanceSmall : distance <
      Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold ambient separation :=
    distanceUpper.trans_lt small
  have derivativeLower : separation.margin ≤
      Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval u) := by
    exact separation.lower uAmbient
      (leftResidual.trans (Fraction.Order.Basic.min_le_left _ _))
  let error := p.eval v - p.eval u -
    (Dense.Gaussian.GCD.derivative p).eval u * (v - u)
  have errorBound : Data.Gaussian.Norm.Basic.normSq error ≤
      Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * distance ^ 2 := by
    exact Dense.Gaussian.Bounds.Box.Taylor.normSq_dense_taylor_remainder_le_denseTaylorRemainderBound
      p vAmbient uAmbient
  have distanceScaled :
      distance * (8 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient) ≤
        separation.margin :=
    (Fraction.Order.Field.le_div_iff_pos
      (Fraction.Order.Arithmetic.mul_pos_direct
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 8) (by decide))
        (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound_pos p ambient))).mp distanceSmall.le
  have errorScaled : 8 * Data.Gaussian.Norm.Basic.normSq error ≤
      separation.margin * distance := by
    have eightNonnegative : (0 : Fraction.Rational) ≤ 8 :=
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by decide)).le
    calc
      8 * Data.Gaussian.Norm.Basic.normSq error ≤ 8 *
          (Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient * distance ^ 2) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct errorBound
          eightNonnegative
      _ = (distance *
          (8 * Dense.Gaussian.Bounds.Box.Taylor.denseTaylorRemainderBound p ambient)) * distance := by ring1
      _ ≤ separation.margin * distance :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          distanceScaled distancePositive.le
  have differenceBound : Data.Gaussian.Norm.Basic.normSq (p.eval v - p.eval u) ≤ 4 * threshold := by
    calc
      Data.Gaussian.Norm.Basic.normSq (p.eval v - p.eval u) ≤
          2 * (Data.Gaussian.Norm.Basic.normSq (p.eval v) + Data.Gaussian.Norm.Basic.normSq (p.eval u)) :=
        Gaussian.Norm.Bounds.normSq_sub_le_two _ _
      _ ≤ 2 * (threshold + threshold) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (add_le_add rightResidual leftResidual)
          (Fraction.Cast.Order.natCast_pos_direct
            (n := 2) (by decide)).le
      _ = 4 * threshold := by ring1
  have inverseThirtyTwo :
      (32 : Fraction.Rational) * (1 / 32) = 1 := by
    calc
      (32 : Fraction.Rational) * (1 / 32) = (1 / 32) * 32 := by ring1
      _ = 1 := Fraction.Field.div_mul_cancel_of_ne 1 32
        (Fraction.Cast.Order.natCast_pos_direct
          (n := 32) (by decide)).ne'
  have differenceScaled : 8 * Data.Gaussian.Norm.Basic.normSq (p.eval v - p.eval u) ≤
      separation.margin * distance := by
    have eightNonnegative : (0 : Fraction.Rational) ≤ 8 :=
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 8) (by decide)).le
    have thirtyTwoNonnegative : (0 : Fraction.Rational) ≤ 32 :=
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 32) (by decide)).le
    calc
      8 * Data.Gaussian.Norm.Basic.normSq (p.eval v - p.eval u) ≤ 8 * (4 * threshold) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          differenceBound eightNonnegative
      _ = 32 * threshold := by ring1
      _ ≤ 32 * ((1 / 32 : Fraction.Rational) *
          (separation.margin * gap ^ 2)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          (Fraction.Order.Basic.min_le_right _ _) thirtyTwoNonnegative
      _ = separation.margin * gap ^ 2 := by
        rw [show 32 * ((1 / 32 : Fraction.Rational) *
            (separation.margin * gap ^ 2)) =
              (32 * (1 / 32 : Fraction.Rational)) *
                (separation.margin * gap ^ 2) by ring1,
          inverseThirtyTwo]
        ring1
      _ ≤ separation.margin * distance :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
          distanceLower separation.margin_pos.le
  let linear := (Dense.Gaussian.GCD.derivative p).eval u * (v - u)
  have linearIdentity : linear = (p.eval v - p.eval u) - error := by
    apply Gaussian.Basic.ext <;>
      simp only [linear, error, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im, Gaussian.Basic.mul_re,
        Gaussian.Basic.mul_im] <;>
      ring1
  have linearUpper : Data.Gaussian.Norm.Basic.normSq linear ≤
      2 * (Data.Gaussian.Norm.Basic.normSq (p.eval v - p.eval u) + Data.Gaussian.Norm.Basic.normSq error) := by
    rw [linearIdentity]
    exact Gaussian.Norm.Bounds.normSq_sub_le_two _ _
  have fourLinearUpper : 4 * Data.Gaussian.Norm.Basic.normSq linear ≤
      2 * (separation.margin * distance) := by
    have fourNonnegative : (0 : Fraction.Rational) ≤ 4 :=
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 4) (by decide)).le
    calc
      4 * Data.Gaussian.Norm.Basic.normSq linear ≤
          4 * (2 * (Data.Gaussian.Norm.Basic.normSq (p.eval v - p.eval u) + Data.Gaussian.Norm.Basic.normSq
            error)) :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct linearUpper
          fourNonnegative
      _ = 8 * Data.Gaussian.Norm.Basic.normSq (p.eval v - p.eval u) + 8 * Data.Gaussian.Norm.Basic.normSq error
        := by
        ring1
      _ ≤ separation.margin * distance +
          separation.margin * distance :=
        add_le_add differenceScaled errorScaled
      _ = 2 * (separation.margin * distance) := by ring1
  have linearLower : separation.margin * distance ≤
      Data.Gaussian.Norm.Basic.normSq linear := by
    calc
      separation.margin * distance ≤
          Data.Gaussian.Norm.Basic.normSq ((Dense.Gaussian.GCD.derivative p).eval u) * distance :=
        Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
          derivativeLower distancePositive.le
      _ = Data.Gaussian.Norm.Basic.normSq linear := by
        dsimp only [linear, distance]
        rw [Gaussian.Norm.Basic.normSq_mul]
  have impossible : 4 * (separation.margin * distance) ≤
      2 * (separation.margin * distance) :=
    (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct linearLower
      (Fraction.Cast.Order.natCast_pos_direct
        (n := 4) (by decide)).le).trans fourLinearUpper
  have basePositive : 0 < separation.margin * distance :=
    Fraction.Order.Arithmetic.mul_pos_direct
      separation.margin_pos distancePositive
  have strict : 2 * (separation.margin * distance) <
      4 * (separation.margin * distance) := by
    calc
      2 * (separation.margin * distance) =
          0 + 2 * (separation.margin * distance) := by ring1
      _ < 2 * (separation.margin * distance) +
          2 * (separation.margin * distance) :=
        Fraction.Order.Arithmetic.add_lt_add_right_direct
          (Fraction.Order.Arithmetic.mul_pos_direct
            (Fraction.Cast.Order.natCast_pos_direct
              (n := 2) (by decide)) basePositive)
          (2 * (separation.margin * distance))
      _ = 4 * (separation.margin * distance) := by ring1
  exact (not_le_of_gt strict impossible).elim

end Purelib.RootIsolation.Track.Separation.Separated
