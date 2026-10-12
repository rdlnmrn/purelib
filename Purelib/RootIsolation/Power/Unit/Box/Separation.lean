module

import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Nat.Positive
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import all Purelib.Geometry.Rational.Box.CenteredSquare

import Purelib.Geometry.Rational.Box.Separation
import Purelib.Geometry.Rational.Box.Square.Centered
import Purelib.Polynomial.Dense.Basic
import Purelib.Polynomial.Dense.Gaussian.Bounds.RootRadius.Box
import Purelib.Polynomial.Dense.Gaussian.Derivative.Separation.Uniqueness
import Purelib.Polynomial.Power.Gaussian
import Purelib.Polynomial.Power.Gaussian.DerivativeSeparation
import Purelib.RootIsolation.Power.Isolation.Track
public import Purelib.RootIsolation.Power.Unit.Box
import Purelib.RootIsolation.Power.Unit.Radius
import Purelib.RootIsolation.Power.Unit.Source
import Purelib.RootIsolation.Power.Unit.Source.Refinement
import Purelib.RootIsolation.Track.Separation.Separated
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Tactic.Ring

open Purelib.Data

open Purelib

open Purelib.Geometry.Rational

open Purelib.RootIsolation

section
@[expose] public section

/-!
# Finite monodromy for `Z^d - w`

This file specializes finite owner monodromy to the displayed power family.
The first layer records the exact off-zero Bézout identity.  It is uniform in
the displayed positive degree and uses only finite dense-polynomial
calculations:

`-w⁻¹ (Z^d-w) + (w⁻¹ d⁻¹ Z) (Z^d-w)' = 1`.

The later layers use that identity to carry every owner around one explicit
rational circuit of the parameter and to calculate the resulting finite
permutation.
-/

namespace Purelib.RootIsolation.Power.Unit.Box.Separation

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Norm.Basic (normSq)

/-- Distinct robust owners are positively separated.  If two closed squares
overlapped, their common displayed overlap point would put the two already
separated source tracks inside one radius-`2r` square, contradicting the
explicit derivative-separation threshold. -/
theorem unitRobustBox_pairwiseSeparated
    {parameter : Gaussian.Basic.Canonical} (parameterNonzero : parameter ≠ 0)
    (parameterUnit : normSq parameter = 1)
    (degree : Data.Nat.Positive.RootDegree) (degreeAtLeastTwo : 2 ≤ degree.value)
    (left right : Fin degree.value) (different : left ≠ right) :
    (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
      left).Separated
        (Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree degreeAtLeastTwo
          right) := open Purelib.Data.Rat in open Purelib.Polynomial in by
  let p := Purelib.Polynomial.Power.Gaussian.rootPolynomial parameter degree
  let ambient := Dense.Gaussian.Bounds.RootRadius.Box.largeSquareBox p
  let separation := Power.Gaussian.DerivativeSeparation.unitParameterDerivativeSeparation parameterUnit degree
    degreeAtLeastTwo ambient
  let r := Power.Unit.Radius.unitRobustRadius parameterUnit degree degreeAtLeastTwo
  let leftBox := Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
    degreeAtLeastTwo left
  let rightBox := Power.Unit.Box.unitRobustBox parameterNonzero parameterUnit degree
    degreeAtLeastTwo right
  by_cases separated : leftBox.Separated rightBox
  · exact separated
  · let overlap := Box.overlapPoint leftBox rightBox
    have overlapInside :=
      Box.contains_overlapPoint_of_not_separated separated
    let common := Box.Square.Centered.Affine.centeredSquare overlap (2 * r)
      (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
        (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le)
    have leftBoxCommon : leftBox.Refines common :=
      Box.CenteredSquare.centeredSquare_refines_double_at_member
        (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
        overlapInside.1
    have rightBoxCommon : rightBox.Refines common :=
      Box.CenteredSquare.centeredSquare_refines_double_at_member
        (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le
        overlapInside.2
    have leftSourceCommon :
        (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo left).box.Refines common :=
      (Power.Unit.Source.Refinement.unitRobustSourceState_refinesBox parameterNonzero parameterUnit degree
        degreeAtLeastTwo left).trans leftBoxCommon
    have rightSourceCommon :
        (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo right).box.Refines common :=
      (Power.Unit.Source.Refinement.unitRobustSourceState_refinesBox parameterNonzero parameterUnit degree
        degreeAtLeastTwo right).trans rightBoxCommon
    have commonSmall : common.diagonalSq <
        Dense.Gaussian.Derivative.Separation.Uniqueness.separatedUniquenessDiagonalThreshold ambient
          separation := by
      calc
        common.diagonalSq = 8 * (2 * r) ^ 2 :=
          Box.Square.Centered.Affine.centeredSquare_diagonalSq overlap
            (Fraction.Order.Arithmetic.mul_nonneg_direct (by decide)
              (Power.Unit.Radius.unitRobustRadius_pos parameterUnit degree degreeAtLeastTwo).le)
        _ = 32 * r ^ 2 := by ring1
        _ < Power.Unit.Radius.unitUniquenessDiagonalThreshold parameterUnit degree
            degreeAtLeastTwo :=
          Power.Unit.Radius.thirtyTwo_mul_unitRobustRadius_sq_lt_uniqueness parameterUnit degree
            degreeAtLeastTwo
    exact False.elim
      (Track.Separation.Separated.separated_tracks_not_supported_in_small_common_box_of_separation
        (by rw [Purelib.Polynomial.Power.Gaussian.rootPolynomial_degree]; exact degree.positive) separation
        (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo left)
        (Power.Isolation.Track.isolatedTrack parameterNonzero degree degreeAtLeastTwo right)
        (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo left)
        (Power.Unit.Source.unitRobustSourceState parameterNonzero parameterUnit degree
          degreeAtLeastTwo right)
        (Power.Unit.Source.Refinement.unitRobustSourceState_pairwiseSeparated parameterNonzero parameterUnit
          degree degreeAtLeastTwo left right different)
        common leftSourceCommon rightSourceCommon commonSmall)
end Purelib.RootIsolation.Power.Unit.Box.Separation

end
