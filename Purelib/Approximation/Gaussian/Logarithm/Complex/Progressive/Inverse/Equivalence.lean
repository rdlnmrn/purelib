module
import Purelib.Data.Nat.Order
import Purelib.Data.Rat.Fraction
public import Purelib.Data.Rat.Bounds.Fraction
import Purelib.Approximation.Gaussian.Equivalence
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Diagonal
public import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Reconstruction
import Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local.Domain
import Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial.Error
import Purelib.Approximation.Gaussian.Name.Basic
import Purelib.Approximation.Gaussian.Sequence.Name.Equivalence
import Purelib.Approximation.Rational.Geometric.Basic
import Purelib.Approximation.Rational.Geometric.Search
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Gaussian.Norm.Bounds
import Purelib.Data.Rat.Fraction.Compatibility
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Order.Field

import Purelib.Tactic.QuotientFreeOmega
import Init.Data.Nat.MinMax
import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Int.Cast.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Cast.Defs
import Mathlib.Data.Nat.Init
import Mathlib.Order.Defs.PartialOrder
import Purelib.Approximation.Gaussian.Sequence
import Purelib.Approximation.Gaussian.Sequence.Name
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Tactic.Ring

open Purelib.Approximation.Rational.Geometric.Basic (quarterRadius_scale_mono)

public section

/-!
# Finite coherence of progressive transcendental outputs

The local exponential and logarithm algorithms first build limit-free
`Approximation` sidechannels.  Their CCL processes are therefore coherent by
construction.  This module propagates that certificate through global dyadic
range reduction, repeated squaring, and the finite correction arithmetic.

These are statements about every finite rational process branch.  They do not
assert that a completed exponential or logarithm value has been selected.
-/

namespace Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Equivalence

open Purelib
open Purelib.Approximation
open Purelib.Approximation.Gaussian.Equivalence
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse
open Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Local
open Purelib.Approximation.Gaussian.Logarithm.Local.Inverse.Polynomial
open Purelib.Approximation.Gaussian.Sequence.Name
open Purelib.Approximation.Rational
open Purelib.Approximation.Rational.Geometric
open Purelib.CCL.Transcendental
open Purelib.Data.Rat

/-- The combined scale for diagonal sample movement, reconstructed-chart movement and finite inverse error. -/
@[expose] public def dynamicLocalExpLogChartEquivalentMasterScale : Fraction.Rational :=
  Diagonal.dynamicLocalExpLogErrorScale +
    Reconstruction.dynamicLocalExpLogChartApproximationScale +
      Error.expLogErrorScale

/-- The combined diagonal-to-chart comparison scale is nonnegative. -/
theorem dynamicLocalExpLogChartEquivalentMasterScale_nonneg :
    0 ≤
      dynamicLocalExpLogChartEquivalentMasterScale
      :=
  add_nonneg
    (add_nonneg Diagonal.dynamicLocalExpLogErrorScale_nonneg
      Reconstruction.dynamicLocalExpLogChartApproximationScale_nonneg)
    Error.expLogErrorScale_nonnegative

/-- The combined comparison scale bounds the diagonal exponential–logarithm movement scale. -/
private theorem dynamicLocalExpLogScale_le_chartEquivalentMaster :
    Diagonal.dynamicLocalExpLogErrorScale ≤

        dynamicLocalExpLogChartEquivalentMasterScale
        := by
  unfold
    dynamicLocalExpLogChartEquivalentMasterScale
  calc
    Diagonal.dynamicLocalExpLogErrorScale ≤
        Diagonal.dynamicLocalExpLogErrorScale +
          Reconstruction.dynamicLocalExpLogChartApproximationScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        Reconstruction.dynamicLocalExpLogChartApproximationScale_nonneg
    _ ≤ Diagonal.dynamicLocalExpLogErrorScale +
          Reconstruction.dynamicLocalExpLogChartApproximationScale +
            Error.expLogErrorScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        Error.expLogErrorScale_nonnegative

/-- The combined comparison scale bounds the reconstructed-chart movement scale. -/
private theorem dynamicLocalExpLogChartScale_le_chartEquivalentMaster :
    Reconstruction.dynamicLocalExpLogChartApproximationScale ≤

        dynamicLocalExpLogChartEquivalentMasterScale
        := by
  unfold
    dynamicLocalExpLogChartEquivalentMasterScale
  calc
    Reconstruction.dynamicLocalExpLogChartApproximationScale ≤
        Diagonal.dynamicLocalExpLogErrorScale +
          Reconstruction.dynamicLocalExpLogChartApproximationScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_left _ _
        Diagonal.dynamicLocalExpLogErrorScale_nonneg
    _ ≤ Diagonal.dynamicLocalExpLogErrorScale +
          Reconstruction.dynamicLocalExpLogChartApproximationScale +
            Error.expLogErrorScale :=
      Fraction.Compatibility.coordinate_le_add_of_nonneg_right _ _
        Error.expLogErrorScale_nonnegative

/-- The combined comparison scale bounds the finite exponential–logarithm inverse error coefficient. -/
private theorem finiteExpLogScale_le_chartEquivalentMaster :
    Error.expLogErrorScale ≤

        dynamicLocalExpLogChartEquivalentMasterScale
        := by
  unfold
    dynamicLocalExpLogChartEquivalentMasterScale
  exact Fraction.Compatibility.coordinate_le_add_of_nonneg_left _ _
    (add_nonneg Diagonal.dynamicLocalExpLogErrorScale_nonneg
      Reconstruction.dynamicLocalExpLogChartApproximationScale_nonneg)

/-- The dynamic finite exp-log computation is operationally equal to exact Möbius reconstruction of the same finite
reduced readings. -/
@[expose] public def dynamicLocalExpLog_chart_equivalent (input : Gaussian.Name.Basic.Named)
    (disk : Domain.Disk input) :
    Gaussian.Equivalence.Equivalent
      (Diagonal.dynamicLocalExpLogApproximation input disk)
      (Reconstruction.dynamicLocalExpLogChartApproximation input disk) where
  compare := by
    intro leftStart rightStart target positive
    let smallTarget := target / 16
    have smallPositive : 0 < smallTarget :=
      Fraction.Order.Field.div_pos_direct positive (by decide)
    let start := max leftStart rightStart
    let index := Search.firstQuarterBelow

        dynamicLocalExpLogChartEquivalentMasterScale
        start smallTarget
    have indexGe : start ≤ index :=
      Search.firstQuarterBelow_ge

          dynamicLocalExpLogChartEquivalentMasterScale
          start smallTarget
    have masterSmall :
        Geometric.Basic.quarterRadius

              dynamicLocalExpLogChartEquivalentMasterScale
              index < smallTarget :=
      Search.firstQuarterBelow_accurate

          dynamicLocalExpLogChartEquivalentMasterScale

            dynamicLocalExpLogChartEquivalentMasterScale_nonneg
            start smallTarget smallPositive
    exact
      { leftIndex := index
        rightIndex := index
        left_ge := (Purelib.Data.Nat.Order.le_max_left _ _).trans indexGe
        right_ge := (Purelib.Data.Nat.Order.le_max_right _ _).trans indexGe
        close := by
          intro leftLater rightLater leftOrder rightOrder
          have leftTail :=
            (Diagonal.dynamicLocalExpLogApproximation input disk).later_close leftOrder
          have leftTailSmall := leftTail.trans_lt
            ((quarterRadius_scale_mono

                  dynamicLocalExpLogScale_le_chartEquivalentMaster
                  index).trans_lt
              masterSmall)
          have rightTail :=
            (Reconstruction.dynamicLocalExpLogChartApproximation input disk).later_close
              rightOrder
          have rightTailSmall := rightTail.trans_lt
            ((quarterRadius_scale_mono

                  dynamicLocalExpLogChartScale_le_chartEquivalentMaster
                index).trans_lt masterSmall)
          have rightTailReverse :
              Data.Gaussian.Norm.Basic.normSq
                  ((Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                      index -
                    (Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                      rightLater) < smallTarget := by
            have identity :
                (Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                      index -
                    (Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                      rightLater =
                  -((Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                      rightLater -
                    (Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                      index) := by
              apply Data.Gaussian.Basic.ext <;>
                simp only [Purelib.Data.Gaussian.Basic.sub_re, Purelib.Data.Gaussian.Basic.sub_im,
                  Purelib.Data.Gaussian.Basic.neg_re, Purelib.Data.Gaussian.Basic.neg_im] <;> ring1
            rw [identity, Data.Gaussian.Norm.Basic.normSq_neg]
            exact rightTailSmall
          have direct := Reconstruction.dynamicLocalExpLog_chart_error input disk index
          have directSmall :
              Data.Gaussian.Norm.Basic.normSq
                  ((Diagonal.dynamicLocalExpLogApproximation input disk).sample index -
                    (Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                      index) < smallTarget := by
            change Data.Gaussian.Norm.Basic.normSq
                ((Diagonal.dynamicLocalExpLogApproximation input disk).sample index -
                  Reconstruction.dynamicLocalExpLogChartSample input index) < smallTarget
            have directRadius :
                Error.expLogErrorScale *
                    (1 / 4 : Fraction.Rational) ^ index ≤
                  Geometric.Basic.quarterRadius

                      dynamicLocalExpLogChartEquivalentMasterScale
                      index := by
              rw [Geometric.Basic.quarterRadius_eq_mul_pow]
              exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct

                  finiteExpLogScale_le_chartEquivalentMaster
                (Fraction.Order.Arithmetic.pow_nonneg_direct (by decide) _)
            exact direct.trans_lt (directRadius.trans_lt masterSmall)
          have middle := (Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _).trans_lt
            (Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
              (by decide)
              (Fraction.Order.Arithmetic.add_lt_add_direct
                directSmall rightTailReverse))
          calc
            Data.Gaussian.Norm.Basic.normSq
                ((Diagonal.dynamicLocalExpLogApproximation input disk).sample
                    leftLater -
                  (Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                    rightLater) ≤
              2 *
                (Data.Gaussian.Norm.Basic.normSq
                    ((Diagonal.dynamicLocalExpLogApproximation input disk).sample
                        leftLater -
                      (Diagonal.dynamicLocalExpLogApproximation input disk).sample
                        index) +
                  Data.Gaussian.Norm.Basic.normSq
                    ((Diagonal.dynamicLocalExpLogApproximation input disk).sample
                        index -
                      (Reconstruction.dynamicLocalExpLogChartApproximation input disk).sample
                        rightLater)) :=
              Data.Gaussian.Norm.Bounds.normSq_sub_le_via _ _ _
            _ < 2 *
                (smallTarget + 2 * (smallTarget + smallTarget)) :=
              Fraction.Order.Arithmetic.mul_lt_mul_of_pos_left_direct
                (by decide)
                (Fraction.Order.Arithmetic.add_lt_add_direct
                  leftTailSmall middle)
            _ = 10 * smallTarget := by ring1
            _ < target := by
              dsimp only [smallTarget]
              exact Purelib.Data.Rat.Bounds.Fraction.ten_sixteenths_lt positive }

/-- The productive diagonal exponential–logarithm and reconstructed-chart names are operationally equivalent for the
same certified reduced input. -/
@[expose] public def dynamicLocalExpLog_chart_named_equivalent (input : Gaussian.Name.Basic.Named)
    (disk : Domain.Disk input) :
    Gaussian.Equivalence.NamedEquivalent
      (Diagonal.dynamicLocalExpLogApproximation input disk).toNamed
      (Reconstruction.dynamicLocalExpLogChartApproximation input disk).toNamed :=
  Equivalence.approximationEquivalent_toNamed
    (Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Equivalence.dynamicLocalExpLog_chart_equivalent input
      disk)
end Purelib.Approximation.Gaussian.Logarithm.Complex.Progressive.Inverse.Equivalence

end
