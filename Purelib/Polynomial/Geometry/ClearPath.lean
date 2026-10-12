module

import Purelib.Data.Rat.Fraction
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Components.Basic
import Purelib.Data.Gaussian.Norm.Basic
public import Purelib.Data.Gaussian.Scale
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Polynomial.Clearance.Box.Line.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Mathlib.Algebra.Ring.Defs
import Purelib.Data.Gaussian.Field
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Polynomial.Dense.Evaluation
import Purelib.Tactic.Ring
import Purelib.Tactic.QuotientFreeOmega
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry.Rational

open Purelib.Polynomial

section
@[expose] public section

/-!
# Certified rational branch cuts

The initial isolation boxes come with polynomial-clear coordinate lines across
the one finite ambient square.  Consequently two finite branch boxes can be
joined by a rational L-shaped path: first along the lower edge line of the
left box, then along the left edge line of the right box.  An odd-degree
infinity cut exits along the same clear horizontal line to the right boundary
of the ambient square.  Every segment below stores its finite line-clearance
certificate; there is no appeal to a complement of an infinite point set.
-/

namespace Purelib.Polynomial.Geometry

namespace ClearPath

/-- The dense Gaussian polynomial representation indexing clear segments and paths. -/
abbrev GaussianPolynomial :=
  Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial

end ClearPath

namespace ClearPath

set_option genInjectivity false in
/-- A polynomial-clear rational axis segment inside the common ambient box.
The dependent endpoints make concatenation exact rather than propositional. -/
inductive ClearSegment (polynomial : GaussianPolynomial)
  (ambient : Box) :
    Gaussian.Basic.Canonical -> Gaussian.Basic.Canonical -> Type
  /-- A horizontal segment retaining both endpoint bounds and the original line-clearance certificate. -/ | horizontal
    (xStart xFinish y : Fraction.Rational)
      (startLower : ambient.xLower <= xStart)
      (startUpper : xStart <= ambient.xUpper)
      (finishLower : ambient.xLower <= xFinish)
      (finishUpper : xFinish <= ambient.xUpper)
      (clearance : Clearance.Box.Line.Basic.HorizontalLineClearance
        polynomial ambient y) :
      ClearSegment polynomial ambient (Gaussian.Components.Basic.point xStart y)
        (Gaussian.Components.Basic.point xFinish y)
  /-- A vertical segment retaining both endpoint bounds and the original line-clearance certificate. -/ | vertical (x
    yStart yFinish : Fraction.Rational)
      (startLower : ambient.yLower <= yStart)
      (startUpper : yStart <= ambient.yUpper)
      (finishLower : ambient.yLower <= yFinish)
      (finishUpper : yFinish <= ambient.yUpper)
      (clearance : Clearance.Box.Line.Basic.VerticalLineClearance
        polynomial ambient x) :
      ClearSegment polynomial ambient (Gaussian.Components.Basic.point x yStart)
        (Gaussian.Components.Basic.point x yFinish)

constructive_injectivity ClearSegment

end ClearPath

namespace ClearPath.ClearSegment.horizontal

end ClearPath.ClearSegment.horizontal

namespace ClearPath.ClearSegment.horizontal

end ClearPath.ClearSegment.horizontal

namespace ClearPath.ClearSegment.vertical

end ClearPath.ClearSegment.vertical

namespace ClearPath.ClearSegment.vertical

end ClearPath.ClearSegment.vertical

namespace ClearPath.ClearSegment

/-- The fixed positive squared-modulus lower bound carried by the certified
coordinate line underlying a clear segment. -/
def clearanceBound {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) : Fraction.Rational :=
  match segment with
  | .horizontal _ _ _ _ _ _ _ clearance => clearance.bound
  | .vertical _ _ _ _ _ _ _ clearance => clearance.bound

/-- The line-clearance bound retained by every clear segment is strictly positive. -/
theorem clearanceBound_positive {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) :
    0 < segment.clearanceBound := by
  cases segment with
  | horizontal _ _ _ _ _ _ _ clearance => exact clearance.positive
  | vertical _ _ _ _ _ _ _ clearance => exact clearance.positive

/-- A rational Purelib.Data.Gaussian.Components.Basic.point on the certified ambient portion of the segment's
coordinate line.  This deliberately describes a superset of the oriented
segment, so its exclusion theorem is immediately reusable after subdivision. -/
def OnCertifiedLine {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (value : Gaussian.Basic.Canonical) : Prop :=
  match segment with
  | .horizontal _ _ y _ _ _ _ _ =>
      value.im = y ∧ ambient.xLower <= value.re ∧ value.re <= ambient.xUpper
  | .vertical x _ _ _ _ _ _ _ =>
      value.re = x ∧ ambient.yLower <= value.im ∧ value.im <= ambient.yUpper

/-- The line-clearance number uniformly bounds the polynomial on every
displayed rational Purelib.Data.Gaussian.Components.Basic.point of the certified ambient line. -/
theorem clearanceBound_le_eval_normSq {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish value : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (onLine : segment.OnCertifiedLine value) :
    segment.clearanceBound <=
      Data.Gaussian.Norm.Basic.normSq (polynomial.eval value) := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      rcases onLine with ⟨imaginary, lower, upper⟩
      have bound := clearance.lower value.re lower upper
      have valueEqual : Gaussian.Components.Basic.point value.re y = value := by
        apply Gaussian.Basic.ext
        · rfl
        · exact imaginary.symm
      simpa only [clearanceBound, valueEqual, Gaussian.Norm.Basic.normSq_eq_canonical]
        using bound
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      rcases onLine with ⟨real, lower, upper⟩
      have bound := clearance.lower value.im lower upper
      have valueEqual : Gaussian.Components.Basic.point x value.im = value := by
        apply Gaussian.Basic.ext
        · exact real.symm
        · rfl
      simpa only [clearanceBound, valueEqual, Gaussian.Norm.Basic.normSq_eq_canonical]
        using bound

/-- Rational affine parameterization of a displayed clear segment. -/
def pointAt {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (_segment : ClearSegment polynomial ambient start finish)
    (parameter : Fraction.Rational) : Gaussian.Basic.Canonical :=
  start + Gaussian.Scale.scale parameter (finish - start)

/-- The affine segment parameterization starts at its exact starting-point index. -/
@[simp] theorem pointAt_zero {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) :
    segment.pointAt 0 = start := by
  apply Gaussian.Basic.ext <;>
    simp only [pointAt, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im] <;> ring1

/-- The affine segment parameterization ends at its exact finishing-point index. -/
@[simp] theorem pointAt_one {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) :
    segment.pointAt 1 = finish := by
  apply Gaussian.Basic.ext <;>
    simp only [pointAt, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im,
      Gaussian.Basic.add_re,
      Gaussian.Basic.add_im,
      Gaussian.Basic.sub_re,
      Gaussian.Basic.sub_im] <;> ring1

/-- Every parameter in the rational unit interval stays on the certified
ambient portion of the segment's clearance line. -/
theorem pointAt_onCertifiedLine {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Fraction.Rational)
    (inside : (0 : Fraction.Rational) <= parameter ∧ parameter <= 1) :
    segment.OnCertifiedLine (segment.pointAt parameter) := by
  have oneMinusNonnegative : (0 : Fraction.Rational) <= 1 - parameter :=
    Fraction.Order.Arithmetic.sub_nonneg_direct inside.2
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      have realFormula :
          (Gaussian.Components.Basic.point xStart y +
            Gaussian.Scale.scale parameter
              (Gaussian.Components.Basic.point xFinish y - Gaussian.Components.Basic.point xStart y)).re =
            (1 - parameter) * xStart + parameter * xFinish := by
        simp only [Gaussian.Basic.add_re, Gaussian.Basic.sub_re, Gaussian.Scale.scale_re,
          Gaussian.Components.Basic.point]
        ring1
      refine ⟨?_, ?_, ?_⟩
      · simp only [pointAt, Gaussian.Basic.add_im, Gaussian.Basic.sub_im,
          Gaussian.Scale.scale_im,
          Gaussian.Components.Basic.point]
        ring1
      · change ambient.xLower <=
          (Gaussian.Components.Basic.point xStart y + Gaussian.Scale.scale parameter
            (Gaussian.Components.Basic.point xFinish y - Gaussian.Components.Basic.point xStart y)).re
        rw [realFormula]
        calc
          ambient.xLower =
              (1 - parameter) * ambient.xLower +
                parameter * ambient.xLower := by ring1
          _ <= (1 - parameter) * xStart + parameter * xFinish :=
            add_le_add
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                startLower oneMinusNonnegative)
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                finishLower inside.1)
      · change
          (Gaussian.Components.Basic.point xStart y + Gaussian.Scale.scale parameter
            (Gaussian.Components.Basic.point xFinish y - Gaussian.Components.Basic.point xStart y)).re <= ambient.xUpper
        rw [realFormula]
        calc
          (1 - parameter) * xStart + parameter * xFinish <=
              (1 - parameter) * ambient.xUpper +
                parameter * ambient.xUpper :=
            add_le_add
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                startUpper oneMinusNonnegative)
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                finishUpper inside.1)
          _ = ambient.xUpper := by ring1
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      have imaginaryFormula :
          (Gaussian.Components.Basic.point x yStart +
            Gaussian.Scale.scale parameter
              (Gaussian.Components.Basic.point x yFinish - Gaussian.Components.Basic.point x yStart)).im =
            (1 - parameter) * yStart + parameter * yFinish := by
        simp only [Gaussian.Basic.add_im, Gaussian.Basic.sub_im, Gaussian.Scale.scale_im,
          Gaussian.Components.Basic.point]
        ring1
      refine ⟨?_, ?_, ?_⟩
      · simp only [pointAt, Gaussian.Basic.add_re, Gaussian.Basic.sub_re,
          Gaussian.Scale.scale_re,
          Gaussian.Components.Basic.point]
        ring1
      · change ambient.yLower <=
          (Gaussian.Components.Basic.point x yStart + Gaussian.Scale.scale parameter
            (Gaussian.Components.Basic.point x yFinish - Gaussian.Components.Basic.point x yStart)).im
        rw [imaginaryFormula]
        calc
          ambient.yLower =
              (1 - parameter) * ambient.yLower +
                parameter * ambient.yLower := by ring1
          _ <= (1 - parameter) * yStart + parameter * yFinish :=
            add_le_add
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                startLower oneMinusNonnegative)
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                finishLower inside.1)
      · change
          (Gaussian.Components.Basic.point x yStart + Gaussian.Scale.scale parameter
            (Gaussian.Components.Basic.point x yFinish - Gaussian.Components.Basic.point x yStart)).im <= ambient.yUpper
        rw [imaginaryFormula]
        calc
          (1 - parameter) * yStart + parameter * yFinish <=
              (1 - parameter) * ambient.yUpper +
                parameter * ambient.yUpper :=
            add_le_add
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                startUpper oneMinusNonnegative)
              (Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_left_direct
                finishUpper inside.1)
          _ = ambient.yUpper := by ring1

/-- The segment's fixed coordinate also lies in the ambient box.  Line
clearance itself is meaningful outside the box in that coordinate, so this
geometric fact is recorded separately. -/
def WithinAmbient {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) : Prop :=
  match segment with
  | .horizontal _ _ y _ _ _ _ _ =>
      ambient.yLower <= y ∧ y <= ambient.yUpper
  | .vertical x _ _ _ _ _ _ _ =>
      ambient.xLower <= x ∧ x <= ambient.xUpper

/-- A Purelib.Data.Gaussian.Components.Basic.point on an ambient-contained certified line lies in the ambient box. -/
theorem contains_of_onCertifiedLine {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish value : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (onLine : segment.OnCertifiedLine value) : ambient.Contains value := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      exact ⟨onLine.2.1, onLine.2.2,
        by rw [onLine.1]; exact within.1,
        by rw [onLine.1]; exact within.2⟩
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      exact ⟨by rw [onLine.1]; exact within.1,
        by rw [onLine.1]; exact within.2,
        onLine.2.1, onLine.2.2⟩

/-- Every unit-interval sample of an ambient-contained segment belongs to the original ambient box. -/
theorem pointAt_contains {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (parameter : Fraction.Rational)
    (inside : (0 : Fraction.Rational) <= parameter ∧ parameter <= 1) :
    ambient.Contains (segment.pointAt parameter) :=
  segment.contains_of_onCertifiedLine within
    (segment.pointAt_onCertifiedLine parameter inside)

/-- Difference of two affine samples on the same segment. -/
theorem pointAt_sub_pointAt {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Fraction.Rational) :
    segment.pointAt left - segment.pointAt right =
      Gaussian.Scale.scale (left - right) (finish - start) := by
  apply Gaussian.Basic.ext <;>
    simp only [pointAt, Gaussian.Scale.scale_re, Gaussian.Scale.scale_im,
      Gaussian.Basic.add_re, Gaussian.Basic.add_im, Gaussian.Basic.sub_re, Gaussian.Basic.sub_im] <;> ring1

/-- Sample squared-distance equals squared parameter difference times the original endpoint squared-distance. -/
theorem normSq_pointAt_sub_pointAt {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (left right : Fraction.Rational) :
    Data.Gaussian.Norm.Basic.normSq
        (segment.pointAt left - segment.pointAt right) =
      (left - right) ^ 2 *
        Data.Gaussian.Norm.Basic.normSq (finish - start) := by
  rw [segment.pointAt_sub_pointAt left right, Gaussian.Scale.normSq_scale]

/-- A unit-interval Purelib.Data.Gaussian.Components.Basic.point is no farther from the local start than the full
affine segment displacement. -/
theorem normSq_pointAt_sub_zero_le_full {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Fraction.Rational)
    (inside : (0 : Fraction.Rational) <= parameter ∧ parameter <= 1) :
    Data.Gaussian.Norm.Basic.normSq
        (segment.pointAt parameter - segment.pointAt 0) <=
      Data.Gaussian.Norm.Basic.normSq
        (segment.pointAt 1 - segment.pointAt 0) := by
  have squareLe : parameter ^ 2 <= (1 : Fraction.Rational) ^ 2 :=
    Fraction.Order.Arithmetic.pow_le_pow_direct inside.1 inside.2 2
  have squareDifferenceLe : (parameter - 0) ^ 2 <=
      ((1 : Fraction.Rational) - 0) ^ 2 := by
    convert squareLe using 1 <;> ring1
  rw [segment.normSq_pointAt_sub_pointAt parameter 0,
    segment.normSq_pointAt_sub_pointAt 1 0]
  exact Fraction.Order.Arithmetic.mul_le_mul_of_nonneg_right_direct
    squareDifferenceLe
    (Gaussian.Norm.Basic.normSq_nonneg (finish - start))

/-- Every rational Purelib.Data.Gaussian.Components.Basic.point of a horizontal segment has nonzero polynomial
evaluation.  The interval hypotheses deliberately retain the segment's
orientation-free closed interval. -/
theorem horizontal_eval_ne_zero {polynomial :
  GaussianPolynomial}
    {ambient : Box} {y : Fraction.Rational}
    (clearance : Clearance.Box.Line.Basic.HorizontalLineClearance
      polynomial ambient y)
    (x : Fraction.Rational) (lower : ambient.xLower <= x)
    (upper : x <= ambient.xUpper) :
    polynomial.eval (Gaussian.Components.Basic.point x y) ≠ 0 := by
  intro zero
  have bound := clearance.lower x lower upper
  rw [zero, Gaussian.Basic.Canonical.normSq_zero] at bound
  exact (not_lt_of_ge bound) clearance.positive

/-- Every rational Purelib.Data.Gaussian.Components.Basic.point of a vertical segment has nonzero polynomial
evaluation. -/
theorem vertical_eval_ne_zero {polynomial :
  GaussianPolynomial}
    {ambient : Box} {x : Fraction.Rational}
    (clearance : Clearance.Box.Line.Basic.VerticalLineClearance
      polynomial ambient x)
    (y : Fraction.Rational) (lower : ambient.yLower <= y)
    (upper : y <= ambient.yUpper) :
    polynomial.eval (Gaussian.Components.Basic.point x y) ≠ 0 := by
  intro zero
  have bound := clearance.lower y lower upper
  rw [zero, Gaussian.Basic.Canonical.normSq_zero] at bound
  exact (not_lt_of_ge bound) clearance.positive

/-- Every rational Purelib.Data.Gaussian.Components.Basic.point on the certified line portion—and hence every point
of the displayed segment—avoids every finite branch root. -/
theorem eval_ne_zero {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start finish value : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (onLine : segment.OnCertifiedLine value) :
    polynomial.eval value ≠ 0 := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      rcases onLine with ⟨imaginary, lower, upper⟩
      have nonzero := horizontal_eval_ne_zero clearance value.re lower upper
      have valueEqual : Gaussian.Components.Basic.point value.re y = value := by
        apply Gaussian.Basic.ext
        · rfl
        · exact imaginary.symm
      rw [valueEqual] at nonzero
      exact nonzero
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      rcases onLine with ⟨real, lower, upper⟩
      have nonzero := vertical_eval_ne_zero clearance value.im lower upper
      have valueEqual : Gaussian.Components.Basic.point x value.im = value := by
        apply Gaussian.Basic.ext
        · exact real.symm
        · rfl
      rw [valueEqual] at nonzero
      exact nonzero

/-- Polynomial nonvanishing at every displayed rational unit-interval
parameter of a clear segment. -/
theorem pointAt_eval_ne_zero {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (parameter : Fraction.Rational)
    (inside : (0 : Fraction.Rational) <= parameter ∧ parameter <= 1) :
    polynomial.eval (segment.pointAt parameter) ≠ 0 :=
  segment.eval_ne_zero (segment.pointAt_onCertifiedLine parameter inside)

/-- Join any two displayed points on the same certified line. -/
def betweenOnCertifiedLine {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish left right : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (leftOn : segment.OnCertifiedLine left)
    (rightOn : segment.OnCertifiedLine right) :
    ClearSegment polynomial ambient left right := by
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      have leftEq : Gaussian.Components.Basic.point left.re y = left := by
        apply Gaussian.Basic.ext
        · rfl
        · exact leftOn.1.symm
      have rightEq : Gaussian.Components.Basic.point right.re y = right := by
        apply Gaussian.Basic.ext
        · rfl
        · exact rightOn.1.symm
      rw [← leftEq, ← rightEq]
      exact .horizontal left.re right.re y
        leftOn.2.1 leftOn.2.2 rightOn.2.1 rightOn.2.2 clearance
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      have leftEq : Gaussian.Components.Basic.point x left.im = left := by
        apply Gaussian.Basic.ext
        · exact leftOn.1.symm
        · rfl
      have rightEq : Gaussian.Components.Basic.point x right.im = right := by
        apply Gaussian.Basic.ext
        · exact rightOn.1.symm
        · rfl
      rw [← leftEq, ← rightEq]
      exact .vertical x left.im right.im
        leftOn.2.1 leftOn.2.2 rightOn.2.1 rightOn.2.2 clearance

/-- Transport a clear segment along an equality of starting-point indices, retaining its original line certificate. -/
def castStart {polynomial :
  GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient left finish)
    (equal : left = right) :
    ClearSegment polynomial ambient right finish := by
  subst right
  exact segment

/-- Transport a clear segment along an equality of finishing-point indices, retaining its original line certificate. -/
def castFinish {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start left)
    (equal : left = right) :
    ClearSegment polynomial ambient start right := by
  subst right
  exact segment

/-- Transporting the starting-point index preserves ambient containment. -/
theorem castStart_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient left finish)
    (within : segment.WithinAmbient) (equal : left = right) :
    (segment.castStart equal).WithinAmbient := by
  subst right
  exact within

/-- Transporting the finishing-point index preserves ambient containment. -/
theorem castFinish_withinAmbient
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start left)
    (within : segment.WithinAmbient) (equal : left = right) :
    (segment.castFinish equal).WithinAmbient := by
  subst right
  exact within

/-- Transporting the starting-point index preserves the exact retained clearance bound. -/
@[simp] theorem castStart_clearanceBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient left finish)
    (equal : left = right) :
    (segment.castStart equal).clearanceBound = segment.clearanceBound := by
  subst right
  rfl

/-- Transporting the finishing-point index preserves the exact retained clearance bound. -/
@[simp] theorem castFinish_clearanceBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start left)
    (equal : left = right) :
    (segment.castFinish equal).clearanceBound = segment.clearanceBound := by
  subst right
  rfl

/-- Restrict an ambient-contained clear segment to two unit-interval parameters.

The result retains ambient containment and an equality proving that its line-clearance bound is exactly the original
bound. -/
def restriction {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Fraction.Rational)
    (leftInside : (0 : Fraction.Rational) <= left ∧ left <= 1)
    (rightInside : (0 : Fraction.Rational) <= right ∧ right <= 1) :
    { restricted : ClearSegment polynomial ambient
        (segment.pointAt left) (segment.pointAt right) //
      restricted.WithinAmbient ∧
        restricted.clearanceBound = segment.clearanceBound } := by
  have leftOn := segment.pointAt_onCertifiedLine left leftInside
  have rightOn := segment.pointAt_onCertifiedLine right rightInside
  cases segment with
  | horizontal xStart xFinish y startLower startUpper finishLower finishUpper
      clearance =>
      have leftEq :
          Gaussian.Components.Basic.point
              ((Geometry.ClearPath.ClearSegment.horizontal xStart xFinish y startLower startUpper
                finishLower finishUpper clearance).pointAt left).re y =
            (Geometry.ClearPath.ClearSegment.horizontal xStart xFinish y startLower startUpper
              finishLower finishUpper clearance).pointAt left := by
        apply Gaussian.Basic.ext
        · rfl
        · exact leftOn.1.symm
      have rightEq :
          Gaussian.Components.Basic.point
              ((Geometry.ClearPath.ClearSegment.horizontal xStart xFinish y startLower startUpper
                finishLower finishUpper clearance).pointAt right).re y =
            (Geometry.ClearPath.ClearSegment.horizontal xStart xFinish y startLower startUpper
              finishLower finishUpper clearance).pointAt right := by
        apply Gaussian.Basic.ext
        · rfl
        · exact rightOn.1.symm
      let raw : ClearSegment polynomial ambient
          (Gaussian.Components.Basic.point
            ((Geometry.ClearPath.ClearSegment.horizontal xStart xFinish y startLower startUpper
              finishLower finishUpper clearance).pointAt left).re y)
          (Gaussian.Components.Basic.point
            ((Geometry.ClearPath.ClearSegment.horizontal xStart xFinish y startLower startUpper
              finishLower finishUpper clearance).pointAt right).re y) :=
        .horizontal _ _ y leftOn.2.1 leftOn.2.2
          rightOn.2.1 rightOn.2.2 clearance
      exact ⟨(raw.castStart leftEq).castFinish rightEq,
        castFinish_withinAmbient (raw.castStart leftEq)
          (raw.castStart_withinAmbient within leftEq) rightEq,
        by
          calc
            ((raw.castStart leftEq).castFinish rightEq).clearanceBound =
                (raw.castStart leftEq).clearanceBound :=
              castFinish_clearanceBound (raw.castStart leftEq) rightEq
            _ = raw.clearanceBound := castStart_clearanceBound raw leftEq
            _ = (Geometry.ClearPath.ClearSegment.horizontal xStart xFinish y startLower
                startUpper finishLower finishUpper clearance).clearanceBound :=
              rfl⟩
  | vertical x yStart yFinish startLower startUpper finishLower finishUpper
      clearance =>
      have leftEq :
          Gaussian.Components.Basic.point x
              ((Geometry.ClearPath.ClearSegment.vertical x yStart yFinish startLower startUpper
                finishLower finishUpper clearance).pointAt left).im =
            (Geometry.ClearPath.ClearSegment.vertical x yStart yFinish startLower startUpper
              finishLower finishUpper clearance).pointAt left := by
        apply Gaussian.Basic.ext
        · exact leftOn.1.symm
        · rfl
      have rightEq :
          Gaussian.Components.Basic.point x
              ((Geometry.ClearPath.ClearSegment.vertical x yStart yFinish startLower startUpper
                finishLower finishUpper clearance).pointAt right).im =
            (Geometry.ClearPath.ClearSegment.vertical x yStart yFinish startLower startUpper
              finishLower finishUpper clearance).pointAt right := by
        apply Gaussian.Basic.ext
        · exact rightOn.1.symm
        · rfl
      let raw : ClearSegment polynomial ambient
          (Gaussian.Components.Basic.point x
            ((Geometry.ClearPath.ClearSegment.vertical x yStart yFinish startLower startUpper
              finishLower finishUpper clearance).pointAt left).im)
          (Gaussian.Components.Basic.point x
            ((Geometry.ClearPath.ClearSegment.vertical x yStart yFinish startLower startUpper
              finishLower finishUpper clearance).pointAt right).im) :=
        .vertical x _ _ leftOn.2.1 leftOn.2.2
          rightOn.2.1 rightOn.2.2 clearance
      exact ⟨(raw.castStart leftEq).castFinish rightEq,
        castFinish_withinAmbient (raw.castStart leftEq)
          (raw.castStart_withinAmbient within leftEq) rightEq,
        by
          calc
            ((raw.castStart leftEq).castFinish rightEq).clearanceBound =
                (raw.castStart leftEq).clearanceBound :=
              castFinish_clearanceBound (raw.castStart leftEq) rightEq
            _ = raw.clearanceBound := castStart_clearanceBound raw leftEq
            _ = (Geometry.ClearPath.ClearSegment.vertical x yStart yFinish startLower
                startUpper finishLower finishUpper clearance).clearanceBound :=
              rfl⟩

/-- The segment component of an ambient-contained restriction. -/
def restrict {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Fraction.Rational)
    (leftInside : (0 : Fraction.Rational) <= left ∧ left <= 1)
    (rightInside : (0 : Fraction.Rational) <= right ∧ right <= 1) :
    ClearSegment polynomial ambient
      (segment.pointAt left) (segment.pointAt right) :=
  (segment.restriction within left right leftInside rightInside).1

/-- Restricting the displayed endpoints retains the certified coordinate
line and therefore its cached polynomial-clearance bound exactly. -/
@[simp] theorem restrict_clearanceBound
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Fraction.Rational)
    (leftInside : (0 : Fraction.Rational) <= left ∧ left <= 1)
    (rightInside : (0 : Fraction.Rational) <= right ∧ right <= 1) :
    (segment.restrict within left right leftInside
      rightInside).clearanceBound = segment.clearanceBound :=
  (segment.restriction within left right leftInside rightInside).2.2

/-- The retained segment restriction remains contained in the original ambient box. -/
theorem restrict_withinAmbient {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish)
    (within : segment.WithinAmbient)
    (left right : Fraction.Rational)
    (leftInside : (0 : Fraction.Rational) <= left ∧ left <= 1)
    (rightInside : (0 : Fraction.Rational) <= right ∧ right <= 1) :
    (segment.restrict within left right leftInside rightInside).WithinAmbient :=
  (segment.restriction within left right leftInside rightInside).2.1

/-- The starting endpoint lies on the segment's certified ambient line portion. -/
theorem start_onCertifiedLine {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) :
    segment.OnCertifiedLine start := by
  cases segment with
  | horizontal => exact ⟨rfl, ‹_›, ‹_›⟩
  | vertical => exact ⟨rfl, ‹_›, ‹_›⟩

/-- The finishing endpoint lies on the segment's certified ambient line portion. -/
theorem finish_onCertifiedLine {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) :
    segment.OnCertifiedLine finish := by
  cases segment with
  | horizontal => exact ⟨rfl, ‹_›, ‹_›⟩
  | vertical => exact ⟨rfl, ‹_›, ‹_›⟩

/-- The polynomial is nonzero at the original starting endpoint. -/
theorem start_eval_ne_zero {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) :
    polynomial.eval start ≠ 0 :=
  segment.eval_ne_zero segment.start_onCertifiedLine

/-- The polynomial is nonzero at the original finishing endpoint. -/
theorem finish_eval_ne_zero {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start finish : Gaussian.Basic.Canonical}
    (segment : ClearSegment polynomial ambient start finish) :
    polynomial.eval finish ≠ 0 :=
  segment.eval_ne_zero segment.finish_onCertifiedLine

end ClearPath.ClearSegment

set_option genInjectivity false in
/-- A finite concatenation of certified axis segments. -/
inductive ClearPath (polynomial : Geometry.ClearPath.GaussianPolynomial)
  (ambient : Box) :
    Gaussian.Basic.Canonical -> Gaussian.Basic.Canonical -> Type
  /-- The empty indexed path at a displayed point. -/ | nil (point : Gaussian.Basic.Canonical) :
    ClearPath polynomial ambient point point
  /-- Prepend a clear segment whose finishing index is exactly the tail path's starting index. -/ | cons {start middle
    finish : Gaussian.Basic.Canonical}
      (head : Geometry.ClearPath.ClearSegment polynomial ambient start middle)
      (tail : ClearPath polynomial ambient middle finish) :
      ClearPath polynomial ambient start finish

constructive_injectivity ClearPath

namespace ClearPath.cons

end ClearPath.cons

namespace ClearPath.cons

end ClearPath.cons

namespace ClearPath

/-- Every segment of the finite path has its fixed line coordinate inside
the common ambient box. -/
inductive WithinAmbient {polynomial :
  GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian.Basic.Canonical} →
      ClearPath polynomial ambient start finish → Prop
  /-- The empty path has no segment-containment obligations. -/ | nil (point : Gaussian.Basic.Canonical) :
    WithinAmbient (.nil point)
  /-- Retain ambient containment of the first segment and every segment of the tail. -/ | cons {start middle finish :
    Gaussian.Basic.Canonical}
      {head : ClearSegment polynomial ambient start middle}
      {tail : ClearPath polynomial ambient middle finish}
      (headWithin : head.WithinAmbient)
      (tailWithin : WithinAmbient tail) :
      WithinAmbient (.cons head tail)

namespace WithinAmbient

/-- Read ambient containment of the first retained segment. -/
theorem head {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian.Basic.Canonical}
    {head : ClearSegment polynomial ambient start middle}
    {tail : ClearPath polynomial ambient middle finish}
    (within : WithinAmbient (.cons head tail)) : head.WithinAmbient := by
  cases within with
  | cons headWithin _ => exact headWithin

end WithinAmbient

namespace WithinAmbient

/-- Read ambient containment of the retained tail path. -/
theorem tail {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian.Basic.Canonical}
    {head : ClearSegment polynomial ambient start middle}
    {tail : ClearPath polynomial ambient middle finish}
    (within : WithinAmbient (.cons head tail)) : WithinAmbient
      tail := by
  cases within with
  | cons _ tailWithin => exact tailWithin

end WithinAmbient

/-- Count the segments of the finite indexed clear path. -/
def segmentCount {polynomial :
  GaussianPolynomial} {ambient : Box} :
    {start finish : Gaussian.Basic.Canonical} ->
      ClearPath polynomial ambient start finish -> Nat
  | _, _, .nil _ => 0
  | _, _, .cons _ tail => tail.segmentCount + 1

/-- Concatenate two finite clear paths sharing the exact middle-point index. -/
def append {polynomial : GaussianPolynomial}
  {ambient : Box}
    {start middle finish : Gaussian.Basic.Canonical}
    (first : ClearPath polynomial ambient start middle)
    (second : ClearPath polynomial ambient middle finish) :
    ClearPath polynomial ambient start finish :=
  match first with
  | .nil _ => second
  | .cons head tail => .cons head (tail.append second)

namespace WithinAmbient

/-- Concatenation preserves ambient containment of every original segment. -/
theorem append {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start middle finish : Gaussian.Basic.Canonical}
    {first : ClearPath polynomial ambient start middle}
    {second : ClearPath polynomial ambient middle finish}
    (firstWithin : WithinAmbient first)
    (secondWithin : WithinAmbient second) :
    WithinAmbient (first.append second) := by
  induction firstWithin with
  | nil => exact secondWithin
  | cons headWithin tailWithin inductionHypothesis =>
      exact .cons headWithin (inductionHypothesis secondWithin)

end WithinAmbient

/-- Change only the propositionally equal starting-point index. -/
def castStart {polynomial :
  GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian.Basic.Canonical} (equal : left = right)
    (path : ClearPath polynomial ambient left finish) :
    ClearPath polynomial ambient right finish := by
  subst right
  exact path

/-- Change only the propositionally equal finishing-point index. -/
def castFinish {polynomial :
  GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian.Basic.Canonical} (equal : left = right)
    (path : ClearPath polynomial ambient start left) :
    ClearPath polynomial ambient start right := by
  subst right
  exact path

/-- Transport of starting and finishing indices commutes. -/
@[simp] theorem castStart_castFinish
    {polynomial : GaussianPolynomial} {ambient : Box}
    {startLeft startRight finishLeft finishRight : Gaussian.Basic.Canonical}
    (path : ClearPath polynomial ambient startLeft finishLeft)
    (startEqual : startLeft = startRight)
    (finishEqual : finishLeft = finishRight) :
    (path.castStart startEqual).castFinish finishEqual =
      (path.castFinish finishEqual).castStart startEqual := by
  subst startRight
  subst finishRight
  rfl

/-- Transporting the starting-point index leaves the segment count unchanged. -/
@[simp] theorem segmentCount_castStart
    {polynomial : GaussianPolynomial} {ambient : Box}
    {left right finish : Gaussian.Basic.Canonical} (equal : left = right)
    (path : ClearPath polynomial ambient left finish) :
    (path.castStart equal).segmentCount = path.segmentCount := by
  subst right
  rfl

/-- Transporting the finishing-point index leaves the segment count unchanged. -/
@[simp] theorem segmentCount_castFinish
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start left right : Gaussian.Basic.Canonical} (equal : left = right)
    (path : ClearPath polynomial ambient start left) :
    (path.castFinish equal).segmentCount = path.segmentCount := by
  subst right
  rfl

/-- Finishing-index transport acts on the tail of a nonempty path. -/
@[simp] theorem castFinish_cons
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start middle left right : Gaussian.Basic.Canonical}
    (head : ClearSegment polynomial ambient start middle)
    (tail : ClearPath polynomial ambient middle left)
    (equal : left = right) :
    (cons head tail).castFinish equal =
      .cons head (tail.castFinish equal) := by
  subst right
  rfl

/-- Successive finishing-index transports equal transport along the composed equality. -/
@[simp] theorem castFinish_castFinish
    {polynomial : GaussianPolynomial} {ambient : Box}
    {start first second third : Gaussian.Basic.Canonical}
    (path : ClearPath polynomial ambient start first)
    (firstEqual : first = second) (secondEqual : second = third) :
    (path.castFinish firstEqual).castFinish secondEqual =
      path.castFinish (firstEqual.trans secondEqual) := by
  subst second
  subst third
  rfl

/-- The segment count of a concatenation is the sum of the original counts.

The original first path is traversed structurally. Each retained segment contributes one to the same count, and
concatenation preserves the tail and its dependent endpoints. -/
@[simp] theorem segmentCount_append {polynomial :
  GaussianPolynomial}
    {ambient : Box} {start middle finish : Gaussian.Basic.Canonical}
    (first : ClearPath polynomial ambient start middle)
    (second : ClearPath polynomial ambient middle finish) :
    (first.append second).segmentCount =
      first.segmentCount + second.segmentCount := by
  induction first with
  | nil => exact (Nat.zero_add second.segmentCount).symm
  | cons head tail inductionHypothesis =>
      change (tail.append second).segmentCount + 1 =
        (tail.segmentCount + 1) + second.segmentCount
      rw [inductionHypothesis]
      omega0

end ClearPath
end Purelib.Polynomial.Geometry

end
