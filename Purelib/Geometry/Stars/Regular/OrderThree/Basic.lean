module

import Purelib.Algebra.Field.ExplicitField
import Purelib.Geometry.Plane.Line.Basic
import Purelib.Geometry.Plane.Line.Relations
import Purelib.Geometry.Plane.Line.Spread
public import Purelib.Geometry.Plane.Reflection.Line
import Purelib.Geometry.Plane.Reflection.Spread
import Init.Prelude
import Mathlib.Algebra.GroupWithZero.Defs
import Mathlib.Algebra.Ring.Defs
meta import Purelib.Elab.ConstructiveInjectivity

open Purelib

open Purelib.Geometry.Plane

open Purelib.Geometry.Plane.Line

open Purelib.Geometry.Plane.Line.Basic

open Purelib.Geometry.Plane.Reflection

section
public section

/-!
# Divine Proportions, Theorem 95: regular stars of order three

The three-line star is finite data.  Its cyclic rule stores the three
reflection-lineation equations explicitly, and mutual nonparallelism replaces
any appeal to a global collection of lines.
-/

namespace Purelib.Geometry.Stars.Regular.OrderThree.Basic

variable {K : Type*} [Purelib.Algebra.Field.ExplicitField K]

set_option genInjectivity false in
/-- A regular star of order three, spelling out the book's cyclic indexing. -/
structure RegularThreeStar (K : Type*)
  [Algebra.Field.ExplicitField K] [DecidableEq K] where
  /-- The displayed line at cyclic index 0. -/ line₀ : Plane.Line K
  /-- The displayed line at cyclic index 1. -/ line₁ : Plane.Line K
  /-- The displayed line at cyclic index 2. -/ line₂ : Plane.Line K
  /-- The line at cyclic index 0 has nonzero direction quadrance. -/ line₀NonNull : ¬ line₀.IsNull
  /-- The line at cyclic index 1 has nonzero direction quadrance. -/ line₁NonNull : ¬ line₁.IsNull
  /-- The line at cyclic index 2 has nonzero direction quadrance. -/ line₂NonNull : ¬ line₂.IsNull
  /-- The lines at indices 0 and 1 have nonparallel directions. -/ line₀Line₁Nonparallel : ¬ line₀.Parallel line₁
  /-- The lines at indices 1 and 2 have nonparallel directions. -/ line₁Line₂Nonparallel : ¬ line₁.Parallel line₂
  /-- The lines at indices 2 and 0 have nonparallel directions. -/ line₂Line₀Nonparallel : ¬ line₂.Parallel line₀
  /-- Reflecting line 2 in line 0 gives a line equivalent to line 1. -/ reflectAround₀ :
    (Line.reflectLine line₀ line₂ line₀NonNull).Equivalent line₁
  /-- Reflecting line 0 in line 1 gives a line equivalent to line 2. -/ reflectAround₁ :
    (Line.reflectLine line₁ line₀ line₁NonNull).Equivalent line₂
  /-- Reflecting line 1 in line 2 gives a line equivalent to line 0. -/ reflectAround₂ :
    (Line.reflectLine line₂ line₁ line₂NonNull).Equivalent line₀

constructive_injectivity RegularThreeStar

namespace RegularThreeStar

variable [DecidableEq K]

/-- The first two adjacent spreads of a regular three-star are equal. -/
theorem spread₀₁_eq_spread₁₂ (star :
  RegularThreeStar K) :
    Spread.spread star.line₀ star.line₁ star.line₀NonNull star.line₁NonNull =
      Spread.spread star.line₁ star.line₂ star.line₁NonNull star.line₂NonNull := by
  let reflected := Line.reflectLine star.line₁ star.line₀ star.line₁NonNull
  let reflectedNonNull := Line.reflectLine_nonNull star.line₁ star.line₀
    star.line₁NonNull star.line₀NonNull
  have reflectionSpread := Spread.spread_reflectLine_mirror
    star.line₁ star.line₀ star.line₁NonNull star.line₀NonNull
  have representativeSpread := Spread.spread_eq_of_parallel_pairs
    reflected star.line₁ star.line₂ star.line₁
    reflectedNonNull star.line₁NonNull star.line₂NonNull star.line₁NonNull
    (Relations.line_parallel_of_equivalent star.reflectAround₁)
    (Plane.Line.parallel_refl star.line₁)
  calc
    Spread.spread star.line₀ star.line₁ star.line₀NonNull star.line₁NonNull =
        Spread.spread reflected star.line₁ reflectedNonNull star.line₁NonNull :=
          reflectionSpread.symm
    _ = Spread.spread star.line₂ star.line₁ star.line₂NonNull star.line₁NonNull :=
      representativeSpread
    _ = Spread.spread star.line₁ star.line₂ star.line₁NonNull star.line₂NonNull :=
      Spread.spread_symm star.line₂ star.line₁ star.line₂NonNull star.line₁NonNull

/-- The second and third adjacent spreads of a regular three-star are equal. -/
theorem spread₁₂_eq_spread₂₀ (star :
  RegularThreeStar K) :
    Spread.spread star.line₁ star.line₂ star.line₁NonNull star.line₂NonNull =
      Spread.spread star.line₂ star.line₀ star.line₂NonNull star.line₀NonNull := by
  let reflected := Line.reflectLine star.line₂ star.line₁ star.line₂NonNull
  let reflectedNonNull := Line.reflectLine_nonNull star.line₂ star.line₁
    star.line₂NonNull star.line₁NonNull
  have reflectionSpread := Spread.spread_reflectLine_mirror
    star.line₂ star.line₁ star.line₂NonNull star.line₁NonNull
  have representativeSpread := Spread.spread_eq_of_parallel_pairs
    reflected star.line₂ star.line₀ star.line₂
    reflectedNonNull star.line₂NonNull star.line₀NonNull star.line₂NonNull
    (Relations.line_parallel_of_equivalent star.reflectAround₂)
    (Plane.Line.parallel_refl star.line₂)
  calc
    Spread.spread star.line₁ star.line₂ star.line₁NonNull star.line₂NonNull =
        Spread.spread reflected star.line₂ reflectedNonNull star.line₂NonNull :=
          reflectionSpread.symm
    _ = Spread.spread star.line₀ star.line₂ star.line₀NonNull star.line₂NonNull :=
      representativeSpread
    _ = Spread.spread star.line₂ star.line₀ star.line₂NonNull star.line₀NonNull :=
      Spread.spread_symm star.line₀ star.line₂ star.line₀NonNull star.line₂NonNull

end RegularThreeStar
end Purelib.Geometry.Stars.Regular.OrderThree.Basic

end
