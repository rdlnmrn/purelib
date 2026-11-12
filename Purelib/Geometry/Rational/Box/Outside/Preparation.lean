module

public import Purelib.Geometry.Rational.Box.Outside
import Purelib.Data.Gaussian.Basic
import Purelib.Data.Gaussian.Norm.Basic
import Purelib.Data.Rat.Fraction
meta import Purelib.Elab.ConstructiveInjectivity

public section

namespace Purelib.Geometry.Rational.Box

open Purelib.Data.Gaussian.Basic (Canonical)
open Purelib.Data.Gaussian.Norm
open Purelib.Data.Rat.Fraction (Rational)

namespace OutsideSide

set_option genInjectivity false in
/-- One original outside-side witness and its once computed positive squared margin.

The original box and excluded point index both the witness and its readback.
Every contained point satisfies the same cached lower quadrance.
-/
structure Prepared (box : Box) (point : Canonical) where
  /-- The actual coordinate witness excluding the original point. -/
  side : OutsideSide box point
  /-- The once computed squared coordinate distance. -/
  margin : Rational
  /-- The cached margin is the original side's exact squared coordinate gap. -/
  margin_eq : margin = side.margin

constructive_injectivity Prepared

/-- Cache the exact margin of the original outside-side witness. -/
@[expose] def prepare {box : Box} {point : Canonical} (side : OutsideSide box point) : Prepared box point :=
  ⟨side, side.margin, rfl⟩

/-- The retained coordinate distance has strictly positive quadrance. -/
theorem Prepared.positive {box : Box} {point : Canonical} (prepared : Prepared box point) :
    0 < prepared.margin := prepared.margin_eq ▸ prepared.side.margin_pos

/-- The retained margin bounds every contained point's squared distance from the same excluded point. -/
theorem Prepared.lower {box : Box} {point value : Canonical} (prepared : Prepared box point)
    (inside : box.Contains value) : prepared.margin ≤ Basic.normSq (value - point) :=
  prepared.margin_eq ▸ prepared.side.margin_le_normSq_sub inside

end OutsideSide

set_option genInjectivity false in
/-- An original point is excluded with its cached margin or lies in the inspected box.

The second branch proves failure of this sufficient box exclusion. It asserts
no root value or operational pole and leaves refinement available.
-/
inductive PointExclusion (box : Box) (point : Canonical) where
  /-- Retain the actual outside witness and computed margin. -/
  | apart (prepared : OutsideSide.Prepared box point)
  /-- The same rational point lies in the inspected original closed box. -/
  | inconclusive (inside : box.Contains point)

constructive_injectivity PointExclusion

/-- Inspect the original finite coordinate membership test and cache its actual outside margin on success. -/
@[expose] def inspectPoint (box : Box) (point : Canonical) : PointExclusion box point :=
  if inside : box.Contains point then .inconclusive inside
  else .apart (OutsideSide.prepare (outsideSide inside))

end Purelib.Geometry.Rational.Box

end
