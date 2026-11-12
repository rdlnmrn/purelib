module

public import Purelib.Polynomial.Geometry.ClearPath.Distance
import Purelib.Data.Rat.Fraction.Order.Arithmetic
import Purelib.Data.Rat.Fraction.Field
import Purelib.Tactic.Ring

/-! # Half-open points on the original clear path spine

Each original segment contributes its parameters in `[0,1)`. The predicate
recurses over the retained path itself and never constructs a replacement
segment, subdivision, request, continuation owner or observation.
-/

public section

namespace Purelib.Polynomial.Geometry.ClearPath

open Purelib.Data.Gaussian
open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Rat
open Fraction.Order
open Purelib.Geometry.Rational (Box)

/-- The half-open image of each original segment, retaining the original ordered clear path. -/
@[expose] def HalfOpen {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Canonical} → ClearPath polynomial ambient start finish → Canonical → Prop
  | _, _, .nil _, _ => False
  | _, _, .cons head tail, point =>
      (∃ time : Fraction.Rational, 0 ≤ time ∧ time < 1 ∧ point = head.pointAt time) ∨
        HalfOpen tail point

/-- Every retained segment occurrence has distinct actual physical endpoints.

The empty path has no segment obligation. This predicate keeps all original
edge occurrences; it neither removes stationary segments nor changes their
owners or orientation.
-/
@[expose] def Nonstationary {polynomial : GaussianPolynomial} {ambient : Box} :
    {start finish : Canonical} → ClearPath polynomial ambient start finish → Prop
  | _, _, .nil _ => True
  | start, _, .cons (middle := middle) _ tail => start ≠ middle ∧ Nonstationary tail

namespace HalfOpen

/-- A literal half-open visit inherits the original path's pointwise distance payment.

The proof follows the same retained edge occurrences and its actual
parameter witness. It does not select a new edge, trace, source or owner.
-/
theorem pointBound {polynomial : GaussianPolynomial} {ambient : Box}
    {start finish center point : Canonical} {bound : Fraction.Rational}
    {path : ClearPath polynomial ambient start finish}
    (visit : path.HalfOpen point) (paid : PointBound center bound path) :
    Norm.Basic.normSq (center - point) ≤ bound := by
  induction path with
  | nil source => exact visit.elim
  | cons head tail retained =>
      cases visit with
      | inl present =>
          rcases present with ⟨time, lower, upper, same⟩
          have payment := paid.head time ⟨lower, upper.1⟩
          exact Eq.mpr (congrArg (fun value => Norm.Basic.normSq (center - value) ≤ bound) same) payment
      | inr remaining => exact retained remaining paid.tail

end HalfOpen

namespace ClearSegment

variable {polynomial : GaussianPolynomial} {ambient : Box} {start finish : Canonical}
variable (segment : ClearSegment polynomial ambient start finish)

/-- The original affine segment's real reading retains its exact two indexed endpoints. -/
theorem pointAt_re (time : Fraction.Rational) :
    (segment.pointAt time).re = start.re + time * (finish.re - start.re) := rfl

/-- The original affine segment's imaginary reading retains its exact two indexed endpoints. -/
theorem pointAt_im (time : Fraction.Rational) :
    (segment.pointAt time).im = start.im + time * (finish.im - start.im) := rfl

/-- Equal endpoint real coordinates remain unchanged at every original affine parameter. -/
theorem pointAt_re_of_eq (same : start.re = finish.re) (time : Fraction.Rational) :
    (segment.pointAt time).re = start.re := by
  rewrite [pointAt_re, ← same]
  ring1

/-- Equal endpoint imaginary coordinates remain unchanged at every original affine parameter. -/
theorem pointAt_im_of_eq (same : start.im = finish.im) (time : Fraction.Rational) :
    (segment.pointAt time).im = start.im := by
  rewrite [pointAt_im, ← same]
  ring1

/-- Distinct indexed endpoints make the original affine segment parameterization injective.

The proof cancels a nonzero displayed endpoint coordinate difference. It
uses both original endpoints and never replaces the clear segment or its
polynomial, ambient box, line clearance or orientation.
-/
theorem pointAt_injective (nonstationary : start ≠ finish) {first last : Fraction.Rational}
    (same : segment.pointAt first = segment.pointAt last) : first = last := by
  have coordinate_eq (source target : Fraction.Rational) (different : source ≠ target)
      (observed : source + first * (target - source) = source + last * (target - source)) : first = last := by
    have nonzero : target - source ≠ 0 := by
      intro zero
      apply different
      calc
        source = (target - source) + source := by rewrite [zero, Fraction.Field.zero_add]; rfl
        _ = target := by ring1
    apply Fraction.Field.mul_right_cancel_of_ne nonzero
    calc
      first * (target - source) = (source + first * (target - source)) - source := by ring1
      _ = (source + last * (target - source)) - source := congrArg (fun value => value - source) observed
      _ = last * (target - source) := by ring1
  by_cases real : start.re = finish.re
  · have imaginary : start.im ≠ finish.im :=
      fun equal => nonstationary (Basic.ext real equal)
    have observed := congrArg Canonical.im same
    rewrite [pointAt_im, pointAt_im] at observed
    exact coordinate_eq _ _ imaginary observed
  · have observed := congrArg Canonical.re same
    rewrite [pointAt_re, pointAt_re] at observed
    exact coordinate_eq _ _ real observed

/-- A parameter strictly below one cannot equal the endpoint of a nonstationary original affine segment. -/
theorem pointAt_ne_finish (nonstationary : start ≠ finish) {time : Fraction.Rational} (upper : time < 1) :
    segment.pointAt time ≠ finish := by
  intro equal
  have factorNonzero : 1 - time ≠ 0 := (Arithmetic.sub_pos_direct upper).ne'
  have coordinate_eq (first last : Fraction.Rational)
      (observed : first + time * (last - first) = last) : first = last := by
    apply Fraction.mul_left_cancel_of_nonzero factorNonzero
    calc
      _ = (first + time * (last - first)) - time * last := by ring1
      _ = last - time * last := congrArg (fun value => value - time * last) observed
      _ = _ := by ring1
  have real := congrArg Canonical.re equal
  have imaginary := congrArg Canonical.im equal
  rewrite [pointAt_re] at real
  rewrite [pointAt_im] at imaginary
  exact nonstationary (Basic.ext (coordinate_eq _ _ real) (coordinate_eq _ _ imaginary))

end ClearSegment

end Purelib.Polynomial.Geometry.ClearPath

end
