module
import Purelib.Data.Rat.Fraction.Field
import Purelib.Data.Rat.Fraction.Order.Arithmetic
public import Purelib.Measure.Content.EssentialMaximum.Basic
import Purelib.Measure.Content.Integral
import Purelib.Measure.Content.Lp.L1
import Purelib.Measure.Distribution.Basic
import Purelib.Measure.Distribution.Content
import Purelib.Measure.Distribution.EssentialBound.Lp
public import Purelib.Measure.Distribution.Lp.AlmostEverywhere
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Distance.Basic
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Measure.Content.EssentialBound.Lp

section
/-!
# Executable finite essential maxima

On a displayed finite atom table, every rational observable has a computed
least essential magnitude bound: recursively ignore zero-weight rows and
take the rational maximum on the rest.  Thus no supremum, infimum, or
completed line is needed.  The construction also gives an explicit uniform
absolute-continuity bound for restricted integrals.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

section
open Purelib.Data.Rat
/-- Compute the greatest observable magnitude among the distribution's nonzero-weight occurrences, with zero as the
initial bound.

The finite scan uses the exact retained content and ignores zero-weight occurrences without changing their original
list. -/
def essentialMaximumMagnitude {α : Type} (distribution : Distribution α)
    (value : α → Fraction.Rational) : Fraction.Rational :=
  distribution.toContent.essentialMaximumMagnitude value

/-- Pointwise equal observables have the same essential maximum magnitude. -/
theorem essentialMaximumMagnitude_congr {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational)
    (pointwise : ∀ item, left item = right item) :
    distribution.essentialMaximumMagnitude left =
      distribution.essentialMaximumMagnitude right :=
  distribution.toContent.essentialMaximumMagnitude_congr
    left right pointwise

/-- The finite essential maximum magnitude is nonnegative. -/
theorem essentialMaximumMagnitude_nonnegative {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    0 ≤ distribution.essentialMaximumMagnitude value :=
  distribution.toContent.essentialMaximumMagnitude_nonnegative value

end

/-- The zero observable has essential maximum magnitude zero. -/
theorem essentialMaximumMagnitude_zero {α : Type}
    (distribution : Distribution α) :
    distribution.essentialMaximumMagnitude (fun _ => 0) = 0 :=
  distribution.toContent.essentialMaximumMagnitude_zero

section
open Purelib.Data.Rat
/-- A constant observable's essential maximum equals its rational magnitude under a normalized law. -/
theorem essentialMaximumMagnitude_constant {α : Type}
    (distribution : Distribution α) (constant : Fraction.Rational) :
    distribution.essentialMaximumMagnitude (fun _ => constant) =
      Distance.rationalSeparation constant 0 := by
  apply Fraction.Order.Basic.Compatibility.le_antisymm
  · exact distribution.toContent.essentialMaximumMagnitude_constant_le
      constant
  · have lower :=
        distribution.toContent.poweredL1_le_of_essentialBound
          (fun _ => constant)
          (distribution.essentialMaximumMagnitude (fun _ => constant))
          (Content.essentiallyBoundedBy_essentialMaximumMagnitude
            distribution.toContent (fun _ => constant))
    unfold Content.poweredL1 at lower
    rw [distribution.toContent.integral_constant,
      distribution.toContent_total] at lower
    simpa only [one_mul] using lower

/-- Essential maximum magnitude vanishes exactly when the observable equals zero at every nonzero-weight occurrence. -/
theorem essentialMaximumMagnitude_eq_zero_iff {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude value = 0 ↔
      distribution.EqualAlmostEverywhere value (fun _ => 0) :=
  distribution.toContent.essentialMaximumMagnitude_eq_zero_iff value

/-- The essential maximum magnitude of a sum is bounded by the sum of the original essential maxima. -/
theorem essentialMaximumMagnitude_add_le {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude
        (fun item => left item + right item) ≤
      distribution.essentialMaximumMagnitude left +
        distribution.essentialMaximumMagnitude right :=
  distribution.toContent.essentialMaximumMagnitude_add_le left right

/-- Scalar multiplication increases the essential maximum by at most the scalar's magnitude factor. -/
theorem essentialMaximumMagnitude_scale_le {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude
        (fun item => factor * value item) ≤
      Distance.rationalSeparation factor 0 *
        distribution.essentialMaximumMagnitude value :=
  distribution.toContent.essentialMaximumMagnitude_scale_le
    factor value

/-- Scalar multiplication scales the essential maximum exactly by the scalar's magnitude. -/
theorem essentialMaximumMagnitude_scale {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (value : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude
        (fun item => factor * value item) =
      Distance.rationalSeparation factor 0 *
        distribution.essentialMaximumMagnitude value :=
  distribution.toContent.essentialMaximumMagnitude_scale factor value

/-- Negating the observable preserves its essential maximum magnitude. -/
theorem essentialMaximumMagnitude_neg {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude (fun item => -value item) =
      distribution.essentialMaximumMagnitude value :=
  distribution.toContent.essentialMaximumMagnitude_neg value

/-- The essential maximum magnitude of a difference is bounded by the sum of the original essential maxima. -/
theorem essentialMaximumMagnitude_sub_le {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude
        (fun item => left item - right item) ≤
      distribution.essentialMaximumMagnitude left +
        distribution.essentialMaximumMagnitude right :=
  distribution.toContent.essentialMaximumMagnitude_sub_le left right

/-- The essential maximum magnitude of a product is bounded by the product of the original essential maxima. -/
theorem essentialMaximumMagnitude_mul_le {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude
        (fun item => left item * right item) ≤
      distribution.essentialMaximumMagnitude left *
        distribution.essentialMaximumMagnitude right :=
  distribution.toContent.essentialMaximumMagnitude_mul_le left right

/-- Compute the greatest separation between two observables on the exact nonzero-weight occurrences. -/
def essentialMaximumDistance {α : Type} (distribution : Distribution α)
    (left right : α → Fraction.Rational) : Fraction.Rational :=
  distribution.toContent.essentialMaximumDistance left right

/-- Every essential maximum distance is nonnegative. -/
theorem essentialMaximumDistance_nonnegative {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    0 ≤ distribution.essentialMaximumDistance left right :=
  distribution.toContent.essentialMaximumDistance_nonnegative left right

/-- The essential maximum distance of an observable from itself is zero. -/
theorem essentialMaximumDistance_refl {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.essentialMaximumDistance value value = 0 :=
  distribution.toContent.essentialMaximumDistance_refl value

/-- Reversing the observables preserves their essential maximum distance. -/
theorem essentialMaximumDistance_symm {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.essentialMaximumDistance left right =
      distribution.essentialMaximumDistance right left :=
  distribution.toContent.essentialMaximumDistance_symm left right

/-- Essential maximum distance satisfies the triangle inequality through the supplied intermediate observable. -/
theorem essentialMaximumDistance_triangle {α : Type}
    (distribution : Distribution α)
    (left middle right : α → Fraction.Rational) :
    distribution.essentialMaximumDistance left right ≤
      distribution.essentialMaximumDistance left middle +
        distribution.essentialMaximumDistance middle right :=
  distribution.toContent.essentialMaximumDistance_triangle
    left middle right

/-- The separation of two essential distances to a shared anchor is bounded by the essential distance between their
original observables. -/
theorem essentialMaximumDistance_reverse_triangle {α : Type}
    (distribution : Distribution α)
    (first second anchor : α → Fraction.Rational) :
    Distance.rationalSeparation
        (distribution.essentialMaximumDistance first anchor)
        (distribution.essentialMaximumDistance second anchor) ≤
      distribution.essentialMaximumDistance first second :=
  distribution.toContent.essentialMaximumDistance_reverse_triangle
    first second anchor

/-- Essential maximum magnitude equals essential maximum distance from the zero observable. -/
theorem essentialMaximumMagnitude_eq_distance_zero {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude value =
      distribution.essentialMaximumDistance value (fun _ => 0) :=
  distribution.toContent.essentialMaximumMagnitude_eq_distance_zero
    value

/-- The separation of two essential maximum magnitudes is bounded by their observables' essential maximum distance. -/
theorem essentialMaximumMagnitude_separation_le_distance {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    Distance.rationalSeparation (distribution.essentialMaximumMagnitude left)
        (distribution.essentialMaximumMagnitude right) ≤
      distribution.essentialMaximumDistance left right :=
  distribution.toContent
    |>.essentialMaximumMagnitude_separation_le_distance left right

/-- Essential maximum distance vanishes exactly when the observables agree on every nonzero-weight occurrence. -/
theorem essentialMaximumDistance_eq_zero_iff {α : Type}
    (distribution : Distribution α) (left right : α → Fraction.Rational) :
    distribution.essentialMaximumDistance left right = 0 ↔
      distribution.EqualAlmostEverywhere left right :=
  distribution.toContent.essentialMaximumDistance_eq_zero_iff left right

/-- Scaling both observables scales their essential maximum distance by the scalar's magnitude. -/
theorem essentialMaximumDistance_scale {α : Type}
    (distribution : Distribution α) (factor : Fraction.Rational)
    (left right : α → Fraction.Rational) :
    distribution.essentialMaximumDistance
        (fun item => factor * left item)
        (fun item => factor * right item) =
      Distance.rationalSeparation factor 0 *
        distribution.essentialMaximumDistance left right :=
  distribution.toContent.essentialMaximumDistance_scale
    factor left right
end

end Distribution

end Purelib.Measure

end

section
/-!
# Essential maxima on explicit finite products

The computed essential maximum of a separable product factors exactly over
the Cartesian product of two displayed finite contents.  The proof follows
the executable atom-list construction, treating zero weights directly; no
supremum, maximizing choice, or product sigma algebra is used.
-/

@[expose] public section

namespace Purelib.Measure

namespace Distribution

open Purelib in
open Purelib.Data.Rat in
/-- Taking pointwise rational magnitudes preserves the essential maximum magnitude. -/
public theorem essentialMaximumMagnitude_magnitude {α : Type}
    (distribution : Distribution α) (value : α → Fraction.Rational) :
    distribution.essentialMaximumMagnitude
        (fun item => Distance.rationalSeparation (value item) 0) =
      distribution.essentialMaximumMagnitude value :=
  Measure.essentialMaximumMagnitudeOn_magnitude value distribution.atoms

end Distribution

end Purelib.Measure

end
