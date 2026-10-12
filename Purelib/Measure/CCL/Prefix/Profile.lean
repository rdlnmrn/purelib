module

import Purelib.Data.Rat.Fraction
public import Purelib.Approximation.CCL.Cylinder.Spread
import Purelib.Approximation.Rational.Budget.Dyadic
import Purelib.Data.CCL.Encoding.Block.Basic
import Purelib.Data.CCL.Encoding.Cylinder
public import Purelib.Measure.CCL.Prefix.Content

import Purelib.Tactic.QuotientFreeOmega
import Purelib.Data.Rat.Fraction.Order.Basic
import Purelib.Data.Rat.Fraction.Arithmetic
import Mathlib.Order.Basic
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib.Data.CCL.Encoding (Block)

section
public section

/-!
# Joint finite profile of a completed CCL prefix

A completed-block prefix carries two deliberately separate rational data:

* its fair-bit symbolic cylinder weight, calculated from the raw word; and
* its geometric squared-chordal spread, calculated from block contraction.

Both improve under finite extension, but no theorem identifies them.  A
finite realization certificate also turns the prefix into an inhabited
finite observation, without choosing a point from an eventual intersection.
-/

namespace Purelib.Measure.CCL.Prefix

set_option genInjectivity false in
open Purelib.Data.Rat in
/-- The separate symbolic weight and geometric spread of a completed prefix.

The two rational readings describe the same block prefix but remain distinct quantities with their own extension bounds.
-/
structure PrefixProfile where
  /-- The symbolic dyadic weight reading. -/ symbolicWeight : Fraction.Rational
  /-- The geometric squared-chordal cylinder spread reading. -/ geometricSpread : Fraction.Rational

constructive_injectivity PrefixProfile

section
open Purelib
open Purelib.Data.CCL.Encoding
open Purelib.Measure
/-- Read the exact binary-prefix weight and completed-cylinder spread of the supplied blocks. -/
@[expose] def prefixProfile (blocks : List Block) :
  PrefixProfile where
  symbolicWeight := CCL.Prefix.completedPrefixWeight blocks
  geometricSpread := Approximation.CCL.Cylinder.cylinderSpread blocks

/-- Appending blocks weakly decreases both readings of the retained prefix profile. -/
theorem prefixProfile_append_refines (stem suffix : List Block) :
    (prefixProfile (stem ++ suffix)).symbolicWeight ≤
        (prefixProfile stem).symbolicWeight ∧
      (prefixProfile (stem ++ suffix)).geometricSpread ≤
        (prefixProfile stem).geometricSpread :=
  ⟨CCL.Prefix.completedPrefixWeight_le_of_append stem suffix,
    Approximation.CCL.Cylinder.cylinderSpread_le_of_append stem suffix⟩

end

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Measure in
/-- A completed prefix's exact symbolic weight is at most its geometric cylinder spread. -/
theorem completedPrefixWeight_le_cylinderSpread (blocks : List
  Block) :
    CCL.Prefix.completedPrefixWeight blocks ≤ Approximation.CCL.Cylinder.cylinderSpread blocks := by
  exact Budget.half_pow_antitone (Cylinder.blocks_length_le_rawWord_length blocks)

open Purelib in
open Purelib.Approximation.Rational in
open Purelib.Data.CCL.Encoding in
open Purelib.Data.Rat in
open Purelib.Measure in
/-- The requested block count makes both symbolic weight and geometric spread strictly smaller than the positive target.
-/
theorem completedPrefixProfile_lt_requested
    {blocks : List Block} {target : Fraction.Rational} (positive : 0 < target)
    (enough : Budget.Dyadic.requiredBlockCount target ≤ blocks.length) :
    CCL.Prefix.completedPrefixWeight blocks < target ∧ Approximation.CCL.Cylinder.cylinderSpread blocks < target := by
  have spreadSmall := Approximation.CCL.Cylinder.cylinderSpread_lt_of_requiredBlockCount_le positive enough
  exact ⟨(completedPrefixWeight_le_cylinderSpread blocks).trans_lt spreadSmall,
    spreadSmall⟩

/- Opaque injectivity of the original retained fields. -/

end Purelib.Measure.CCL.Prefix

end
