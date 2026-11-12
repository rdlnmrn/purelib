module

public import Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range.Strip
public import Purelib.Riemann.RootContinuation.FixedRootBoxPath
import Purelib.Curves.Legendre.Periods.Jets.Variation
import Purelib.Curves.Legendre.Periods.Jets.Variation.Point
import Purelib.Data.Gaussian.Field
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Tactic.Ring

/-! # A parameter path in two original overlapping signed root boxes

The retained budgets belong to two original spatial neighborhoods at one
literal common point. Whole-strip movement pays the entire parameter
interval in both boxes. The exact affine Legendre radicand supplies its
squared Lipschitz scale; no root-name agreement is assumed or inferred.
-/

public section

namespace Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

open Purelib
open Purelib.Curves.Legendre.PicardFuchs
open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat.Fraction (Rational)
open Purelib.Data.Rat.Fraction
open Purelib.Riemann.Normalization.ContinuedInverseRoot (ContinuedNeighborhood)
open Purelib.Riemann.RootContinuation

/-- The original scalar radicand difference retains the exact oriented rational parameter difference. -/
private theorem interpolation_difference (parameter point increment : Canonical) (left right : Rational) :
    (Paths.polynomial (parameter + (⟨left, 0⟩ : Canonical) * increment)).eval point -
      (Paths.polynomial (parameter + (⟨right, 0⟩ : Canonical) * increment)).eval point =
      (⟨right - left, 0⟩ : Canonical) * increment * Polynomials.baseValue point := by
  have embedded : (⟨right - left, 0⟩ : Canonical) =
      (⟨right, 0⟩ : Canonical) - (⟨left, 0⟩ : Canonical) := by
    apply Basic.ext
    · rewrite [Basic.sub_re]
      rfl
    · rewrite [Basic.sub_im]
      change (0 : Rational) = 0 - 0
      ring1
  rewrite [radicand_eq, radicand_eq, Variation.radicand_step, Variation.radicand_step, embedded]
  ring1

/-- The actual affine parameter path has its exact nonnegative squared Lipschitz scale. -/
theorem interpolation_normSq (parameter point increment : Canonical) (left right : Rational) :
    Norm.Basic.normSq
      ((Paths.polynomial (parameter + (⟨left, 0⟩ : Canonical) * increment)).eval point -
        (Paths.polynomial (parameter + (⟨right, 0⟩ : Canonical) * increment)).eval point) =
      (Norm.Basic.normSq increment * Norm.Basic.normSq (Polynomials.baseValue point)) * (right - left) ^ 2 := by
  have embedded : Norm.Basic.normSq (⟨right - left, 0⟩ : Canonical) = (right - left) ^ 2 := by
    rewrite [Norm.Basic.normSq_eq_canonical]
    change (right - left) * (right - left) + 0 * 0 = (right - left) ^ 2
    ring1
  rewrite [interpolation_difference, Norm.Basic.normSq_mul, Norm.Basic.normSq_mul, embedded]
  ring1

variable {parameter point : Canonical} {firstCount lastCount : Nat}
    {firstPatch : ContinuedNeighborhood (Paths.polynomial parameter) firstCount}
    {lastPatch : ContinuedNeighborhood (Paths.polynomial parameter) lastCount}
    (first : Range firstPatch) (last : Range lastPatch)
    (firstBudget : FixedRootBoxBudget.Budget firstPatch.base.seed.owner)
    (firstFactory : firstBudget = first.seedBudget)
    (lastBudget : FixedRootBoxBudget.Budget lastPatch.base.seed.owner)
    (lastFactory : lastBudget = last.seedBudget)
    (firstInside : firstPatch.box.Contains point) (lastInside : lastPatch.box.Contains point)
    (increment : Canonical) (firstPaid : Norm.Basic.normSq increment ≤ first.stripBound)
    (lastPaid : Norm.Basic.normSq increment ≤ last.stripBound)

/-- Construct the original two-budget PathData over the whole actual parameter interval at one shared spatial point.

Each original neighborhood supplies its own nonzero/movement certificate.
The given complete budget factories pay the original positive clearances.
No owner, budget, point observation, member or root comparison is acquired.
-/
def overlapPath : FixedRootBoxPath.PathData firstBudget lastBudget where
  point := fun time => (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval point
  nonzero := fun time inside => first.strip_nonzero firstInside ((⟨time, 0⟩ : Canonical) * increment)
    (first.interpolated_admitted time inside increment firstPaid)
  firstMovement := by
    intro time inside
    have paid := first.seed_movement_le firstInside ((⟨time, 0⟩ : Canonical) * increment)
      (first.interpolated_admitted time inside increment firstPaid)
    rewrite [firstFactory, first.seedBudget_movement]
    rewrite [Norm.Basic.normSq_eq_canonical] at paid
    exact paid
  secondMovement := by
    intro time inside
    have paid := last.seed_movement_le lastInside ((⟨time, 0⟩ : Canonical) * increment)
      (last.interpolated_admitted time inside increment lastPaid)
    rewrite [lastFactory, last.seedBudget_movement]
    rewrite [Norm.Basic.normSq_eq_canonical] at paid
    exact paid
  scale := Norm.Basic.normSq increment * Norm.Basic.normSq (Polynomials.baseValue point)
  scale_nonnegative := Order.Arithmetic.mul_nonneg_direct
    (Norm.Basic.normSq_nonneg increment) (Norm.Basic.normSq_nonneg (Polynomials.baseValue point))
  variation := by
    intro left right _leftInside _rightInside
    rewrite [← Norm.Basic.normSq_eq_canonical, interpolation_normSq]
    exact Order.Basic.le_refl _

/-- The actual PathData retains the original affine Legendre radicand at every rational parameter. -/
theorem overlapPath_point (time : Rational) :
    (first.overlapPath last firstBudget firstFactory lastBudget lastFactory firstInside lastInside
      increment firstPaid lastPaid).point time =
      (Paths.polynomial (parameter + (⟨time, 0⟩ : Canonical) * increment)).eval point := by
  unfold overlapPath
  rfl

/-- The retained path scale uses the actual increment and literal shared spatial coefficient. -/
theorem overlapPath_scale :
    (first.overlapPath last firstBudget firstFactory lastBudget lastFactory firstInside lastInside
      increment firstPaid lastPaid).scale =
      Norm.Basic.normSq increment * Norm.Basic.normSq (Polynomials.baseValue point) := by
  unfold overlapPath
  rfl

end Purelib.Curves.Legendre.Periods.Jets.Variation.Point.Range

end
