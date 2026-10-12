module
public import Purelib.Data.Rat.Interval.Basic
import Purelib.Geometry.Rational.Box.Basic
public import Purelib.Geometry.Rational.Box.Content
import Purelib.Data.Rat.Fraction
import Purelib.Data.Rat.Fraction.Arithmetic
import Purelib.Geometry.Rational.Box.Refinement
import Purelib.Tactic.Ring

open Purelib

open Purelib.Data

open Purelib.Data.Rat

open Purelib.Geometry

open Purelib.Geometry.Rational.Box

@[expose] public section

/-!
# Finite rational content of RFAP boxes

Axis-aligned rational boxes have an exact executable area.  Finite covers and
effective nullity are request protocols returning only displayed box lists;
no outer-measure infimum or collection of all covers is formed.
-/

namespace Purelib.Approximation.Box.Content

/-- Zero-to-area rational enclosure attached to one displayed box. -/
def boxContentBound (box : Rational.Box) : Rat.Interval where
  lower := 0
  upper := Content.boxContent box
  valid := Content.boxContent_nonneg box

/-- The zero-to-content enclosure has width exactly equal to the box content. -/
theorem boxContentBound_width (box : Rational.Box) :
    (boxContentBound box).width = Content.boxContent box := by
  dsimp only [boxContentBound, Interval.width]
  ring1

/-- Refining a rational box refines its zero-to-content enclosure. -/
theorem boxContentBound_refines {inner outer : Rational.Box}
    (refines : inner.Refines outer) :
    Interval.Refines
      (boxContentBound inner) (boxContentBound outer) :=
  ⟨le_rfl, Content.boxContent_le_of_refines refines⟩
end Purelib.Approximation.Box.Content

end
