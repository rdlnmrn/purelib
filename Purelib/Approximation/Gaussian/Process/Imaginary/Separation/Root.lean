module

public import Purelib.Approximation.Gaussian.Process.Imaginary.Separation.Basic
import Purelib.Riemann.RootContinuation.CoherentRoot
import Purelib.Data.Rat.Bounds.Square
import Purelib.Data.Rat.Fraction.Order.Arithmetic
meta import Purelib.Elab.ConstructiveInjectivity

/-!
# Imaginary separation from an original isolated-root box

The initial winding-one box belongs to the same retained root track. Its
vertical endpoints provide an unsigned imaginary gap only when the box lies
strictly on one side of the real axis.
-/

public section

namespace Purelib.Approximation.Gaussian.Process.Imaginary.Separation

open Purelib.Data.Rat
open Purelib.Riemann.RootContinuation.CoherentRoot

variable {polynomial : GaussianPolynomial} {ambient : Box}
    {track : WindingOneTrack polynomial ambient}

set_option genInjectivity false in
/-- The exact outcome of checking the original root track's initial vertical interval. -/
inductive RootBox (track : WindingOneTrack polynomial ambient) where
  /-- The initial box is strictly above the real axis. -/
  | above (positive : 0 < track.initial.box.yLower)
  /-- The initial box is not above, and is strictly below, the real axis. -/
  | below (notAbove : ¬ 0 < track.initial.box.yLower) (negative : track.initial.box.yUpper < 0)
  /-- Neither endpoint certifies separation from the real axis. -/
  | crossing (notAbove : ¬ 0 < track.initial.box.yLower) (notBelow : ¬ track.initial.box.yUpper < 0)

constructive_injectivity RootBox

/-- Check the original track's initial vertical endpoints once. -/
@[expose] def inspectRootBox (track : WindingOneTrack polynomial ambient) : RootBox track :=
  if above : 0 < track.initial.box.yLower then .above above
  else if below : track.initial.box.yUpper < 0 then .below above below
  else .crossing above below

/-- A positive original lower endpoint selects the upper-box result. -/
theorem inspectRootBox_above (track : WindingOneTrack polynomial ambient)
    (positive : 0 < track.initial.box.yLower) : inspectRootBox track = .above positive := by
  unfold inspectRootBox
  rewrite [dif_pos positive]
  rfl

/-- A negative upper endpoint selects the lower-box result after the first test fails. -/
theorem inspectRootBox_below (track : WindingOneTrack polynomial ambient)
    (notAbove : ¬ 0 < track.initial.box.yLower) (negative : track.initial.box.yUpper < 0) :
    inspectRootBox track = .below notAbove negative := by
  unfold inspectRootBox
  rewrite [dif_neg notAbove, dif_pos negative]
  rfl

/-- Failed endpoint tests retain the complete inconclusive original interval. -/
theorem inspectRootBox_crossing (track : WindingOneTrack polynomial ambient)
    (notAbove : ¬ 0 < track.initial.box.yLower) (notBelow : ¬ track.initial.box.yUpper < 0) :
    inspectRootBox track = .crossing notAbove notBelow := by
  unfold inspectRootBox
  rewrite [dif_neg notAbove, dif_neg notBelow]
  rfl

/-- An original root box above the real axis supplies its own positive imaginary gap.

Every possible value at the original root state lies in that same initial box;
the retained lower vertical endpoint bounds its squared imaginary coordinate. -/
@[expose] def ofRootAbove (root : CertifiedName track) (positive : 0 < track.initial.box.yLower) :
    Separation root.value :=
  { state := root.value.name.state
    gap := track.initial.box.yLower
    positive := positive
    squared_lower := fun possible => Fraction.Order.Arithmetic.pow_le_pow_direct positive.le
      (root.possible_initial_inside possible).2.2.1 2 }

/-- An original root box below the real axis supplies its own unsigned imaginary gap.

Every possible value at the original root state lies in that same initial box;
the negated upper vertical endpoint bounds its squared imaginary coordinate. -/
@[expose] def ofRootBelow (root : CertifiedName track) (negative : track.initial.box.yUpper < 0) :
    Separation root.value := by
  have positive : 0 < -track.initial.box.yUpper := by
    have reversed := Fraction.Order.Arithmetic.neg_lt_neg_direct negative
    rewrite [neg_zero] at reversed
    exact reversed
  exact
    { state := root.value.name.state
      gap := -track.initial.box.yUpper
      positive := positive
      squared_lower := by
        intro value possible
        apply Bounds.Square.square_lower_of_negative positive
        have upper := (root.possible_initial_inside possible).2.2.2
        rewrite [neg_neg]
        exact upper }

end Purelib.Approximation.Gaussian.Process.Imaginary.Separation

end
