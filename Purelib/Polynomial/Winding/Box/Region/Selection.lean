module

import Purelib.Polynomial.Clearance.Box.Region.Basic
import Purelib.Geometry.Rational.Box.Basic
import Purelib.Polynomial.Dense.Gaussian.Basic
import Purelib.Polynomial.Winding.Box.Basic
public import Purelib.Polynomial.Winding.Box.Region.Sum
import Purelib.Tactic.QuotientFreeOmega
import Mathlib.Data.Int.Order.Basic
import Mathlib.Order.Basic
public import Mathlib.Order.Lattice

import Purelib.Data.Int.Order
import Purelib.Data.Int.Arithmetic
import Purelib.Data.List.Membership
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Geometry.Rational
open Purelib.Polynomial
open Purelib.Data

/-!
# Selecting the first positive clear region

The original finite list scan retains its exact prefix, selected occurrence
and suffix, with the displayed region's positive integer winding.
-/

namespace Purelib.Polynomial.Winding.Box.Region.Selection

set_option genInjectivity false in
/-- Retain the prefix, first positive region and suffix of an ordered list.

The decomposition refers to the same original region occurrences. The selected
region carries its positive raw-winding proof, while the two lists retain the
complete order before and after that occurrence. -/
public structure PositiveSelection
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (regions : List (Clearance.Box.Region.ClearRegion p ambient)) where
  /-- The retained prefix preceding the selected occurrence. -/ before : List (Clearance.Box.Region.ClearRegion p
    ambient)
  /-- The clear region selected from the original ordered list. -/ selected : Clearance.Box.Region.ClearRegion p ambient
  /-- The retained suffix following the selected occurrence. -/ after : List (Clearance.Box.Region.ClearRegion p
    ambient)
  /-- The original list splits exactly into the prefix, selected occurrence and suffix. -/ decomposition : regions =
    before ++ selected :: after
  /-- The selected region has strictly positive raw winding. -/ positive : 0 < Winding.Box.Basic.quadrupledBoxWinding p
    selected.box

constructive_injectivity PositiveSelection

/-- Select the first positive-winding region by the original finite scan.

Every supplied region has nonnegative raw winding and the retained total is
strictly positive. A zero head advances to the same tail; a positive head
returns its exact original position, prefix and suffix. -/
@[expose] public def selectPositive
    {p : Dense.Gaussian.Basic.CanonicalCoefficients.CoefficientPolynomial} {ambient : Box}
    (regions : List (Clearance.Box.Region.ClearRegion p ambient))
    (nonnegative : ∀ region ∈ regions,
      0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box)
    (totalPositive : 0 < Winding.Box.Region.Sum.totalRaw regions) : Winding.Box.Region.Selection.PositiveSelection
      regions := by
  induction regions with
  | nil =>
      simp only [Winding.Box.Region.Sum.totalRaw_nil] at totalPositive
      exact False.elim (Int.Order.lt_irrefl 0 totalPositive)
  | cons head tail inductionHypothesis =>
      by_cases headPositive : 0 < Winding.Box.Basic.quadrupledBoxWinding p head.box
      · exact
          { before := []
            selected := head
            after := tail
            decomposition := rfl
            positive := headPositive }
      · have headNonnegative := nonnegative head (List.Mem.head tail)
        have headZero : Winding.Box.Basic.quadrupledBoxWinding p head.box = 0 :=
          Int.Order.le_antisymm
            (Int.Order.le_of_not_lt headPositive) headNonnegative
        have tailPositive : 0 < Winding.Box.Region.Sum.totalRaw tail := by
          rw [Winding.Box.Region.Sum.totalRaw_cons, headZero] at totalPositive
          rewrite [Int.Arithmetic.zero_add] at totalPositive
          exact totalPositive
        have tailNonnegative : ∀ region ∈ tail,
            0 ≤ Winding.Box.Basic.quadrupledBoxWinding p region.box := by
          intro region member
          exact nonnegative region (List.Mem.tail head member)
        let selected := inductionHypothesis tailNonnegative tailPositive
        exact
          { before := head :: selected.before
            selected := selected.selected
            after := selected.after
            decomposition := by
              simpa only [List.cons_append] using
                congrArg (fun values => head :: values)
                  selected.decomposition
            positive := selected.positive }

end Purelib.Polynomial.Winding.Box.Region.Selection
